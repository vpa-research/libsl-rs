//! Name resolution.

use std::collections::{HashMap, HashSet};
use std::mem;
use std::ops::{Index, IndexMut};

use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap, new_key_type};

use crate::ast::Variance;
use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{
    Def, DefAction, DefAnnotation, DefAutomaton, DefEnum, DefFunction, DefId, DefImport, DefKind,
    DefKindProject, DefPred, DefSemanticTy, DefState, DefStruct, DefTyAlias, DefTyVariable,
    DefVariable, FunctionBody, FunctionBodyUser, FunctionKind, LocalKind, ParamKind, PredKind,
    SemanticTyValue, TyVariableKind, VariableKind,
};
use crate::sema::{Result, Sema};
use crate::{AnnotationId, DeclId, ExprId, FileId, PredId, StmtId, TyExprId, ast};

use super::SemaError;
use super::def::{DefKindTag, FunctionBuiltin};

new_key_type! {
    pub struct ScopeId;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ns {
    Ty,
    Automaton,
    Function,
    Var,
    Annotation,
    Action,
    State,
    Contract,
}

#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub kind: ScopeKind,
    pub defs: HashMap<(Ns, String), DefId>,
    pub functions: HashMap<String, Vec<DefId>>,
}

impl Scope {
    pub fn new(parent: Option<ScopeId>, kind: ScopeKind) -> Self {
        Self {
            parent,
            kind,
            defs: Default::default(),
            functions: Default::default(),
        }
    }

    pub fn is_defined(&self, ns: Ns, name: &str) -> bool {
        match ns {
            Ns::Function => self.functions.contains_key(name),
            _ => self.defs.contains_key(&(ns, name.to_string())),
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct FileScope {
    pub file_id: FileId,
    pub import_scope: ScopeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BlockKind {
    Body(DefId),
    Stmt(StmtId),
    Pred(PredId),
    Var(DeclId),
}

#[derive(Debug, Default, Clone)]
pub enum ScopeKind {
    #[default]
    Dummy,

    Prelude,
    Import(FileId),
    File(FileScope),
    Member(DefId),
    Instance(DefId),
    Params(DefId),
    Block {
        func: DefId,
        kind: BlockKind,
    },
}

impl ScopeKind {
    pub fn as_file_scope(&self) -> Option<&FileScope> {
        match self {
            Self::File(s) => Some(s),
            _ => None,
        }
    }

    pub fn as_file_scope_mut(&mut self) -> Option<&mut FileScope> {
        match self {
            Self::File(s) => Some(s),
            _ => None,
        }
    }
}

/// Resolved names in instantiation expressions.
#[derive(Debug, Clone)]
pub struct InstantiationExprInfo {
    pub automaton: DefId,

    /// Points to either a state or a variable for every argument in the original order.
    pub args: Vec<DefId>,
}

/// Definitions in the prelude scope.
#[derive(Debug, Default, Clone)]
pub struct PreludeDefs {
    pub int8: DefId,
    pub int16: DefId,
    pub int32: DefId,
    pub int64: DefId,
    pub unsigned8: DefId,
    pub unsigned16: DefId,
    pub unsigned32: DefId,
    pub unsigned64: DefId,
    pub float32: DefId,
    pub float64: DefId,
    pub bool: DefId,
    pub char: DefId,
    pub string: DefId,
    pub void: DefId,
    pub any: DefId,
    pub nothing: DefId,
    pub array: DefId,
    pub set: DefId,
    pub pointer: DefId,
    pub intrinsic: DefId,
    pub array_methods: PreludeArrayDefs,
}

#[derive(Debug, Default, Clone)]
pub struct PreludeArrayDefs {
    pub length: DefId,
    pub slice: DefId,
}

impl PreludeDefs {
    pub fn top_level_defs_mut(&mut self) -> impl Iterator<Item = (&'static str, Ns, &mut DefId)> {
        IntoIterator::into_iter([
            ("int8", Ns::Ty, &mut self.int8),
            ("int16", Ns::Ty, &mut self.int16),
            ("int32", Ns::Ty, &mut self.int32),
            ("int64", Ns::Ty, &mut self.int64),
            ("unsigned8", Ns::Ty, &mut self.unsigned8),
            ("unsigned16", Ns::Ty, &mut self.unsigned16),
            ("unsigned32", Ns::Ty, &mut self.unsigned32),
            ("unsigned64", Ns::Ty, &mut self.unsigned64),
            ("float32", Ns::Ty, &mut self.float32),
            ("float64", Ns::Ty, &mut self.float64),
            ("bool", Ns::Ty, &mut self.bool),
            ("char", Ns::Ty, &mut self.char),
            ("string", Ns::Ty, &mut self.string),
            ("void", Ns::Ty, &mut self.void),
            ("any", Ns::Ty, &mut self.any),
            ("nothing", Ns::Ty, &mut self.nothing),
            ("array", Ns::Ty, &mut self.array),
            ("set", Ns::Ty, &mut self.set),
            ("[pointer]", Ns::Ty, &mut self.pointer),
            ("intrinsic", Ns::Annotation, &mut self.intrinsic),
        ])
    }
}

#[derive(Debug, Clone)]
pub struct ExprCtx {
    pub scope_id: ScopeId,
    pub kind: ExprCtxKind,
}

#[derive(Debug, Clone)]
pub enum ExprCtxKind {
    EnumSemanticTyValue(DefId),
    AnnotationParam(DefId),
    AnnotationArg {
        annotation_id: AnnotationId,
        idx: usize,
    },
    VariableInit(DefId),
    FunctionBody(DefId),
}

#[derive(Default, Debug, Clone)]
pub struct StmtCtx {
    /// The [`DefId`] of the function this statement is enclosed in.
    pub enclosing_fn: DefId,
}

#[derive(Debug, Clone)]
pub struct AnnotationCtx {
    /// The [`DefId`] of the annotation used.
    pub def_id: DefId,

    /// The annotated entity.
    pub entity: AnnotatedEntity,

    /// Points to a variable def for every argument in the order they were provided in the use.
    pub args: Vec<DefId>,
}

#[derive(Debug, Clone)]
pub enum AnnotatedEntity {
    /// A [definable entity][Def].
    Def(DefId),
}

/// A registry of definitions.
#[derive(Default, Debug)]
pub struct Defs {
    pub by_id: SlotMap<DefId, Def>,
    pub by_tag: HashMap<DefKindTag, Vec<DefId>>,
}

impl Defs {
    pub fn insert_with_key(&mut self, f: impl FnOnce(DefId) -> Def) -> DefId {
        let def_id = self.by_id.insert_with_key(f);
        let tag = self.by_id[def_id].kind.tag();
        self.by_tag.entry(tag).or_default().push(def_id);

        def_id
    }

    pub fn update_def_kind(
        &mut self,
        def_id: DefId,
        f: impl FnOnce(DefKind) -> DefKind,
    ) -> &mut DefKind {
        let def = &mut self.by_id[def_id];
        let kind = mem::take(&mut def.kind);
        let prev_tag = kind.tag();
        let kind = f(kind);

        if prev_tag != kind.tag() {
            self.by_tag
                .entry(prev_tag)
                .or_default()
                .retain(|&d| d != def_id);
            self.by_tag.entry(kind.tag()).or_default().push(def_id);
        }

        def.kind = kind;

        &mut def.kind
    }
}

impl Index<DefId> for Defs {
    type Output = Def;

    fn index(&self, id: DefId) -> &Self::Output {
        &self.by_id[id]
    }
}

impl IndexMut<DefId> for Defs {
    fn index_mut(&mut self, id: DefId) -> &mut Self::Output {
        &mut self.by_id[id]
    }
}

impl Index<DefKindTag> for Defs {
    type Output = [DefId];

    fn index(&self, tag: DefKindTag) -> &Self::Output {
        match self.by_tag.get(&tag) {
            Some(defs) => defs,
            None => &[],
        }
    }
}

/// Information collected during name resolution.
#[derive(Default, Debug)]
pub struct NameRes {
    /// Entity definitions.
    pub defs: Defs,

    /// Variable scopes.
    pub scopes: SlotMap<ScopeId, Scope>,

    /// Maps each declaration in the AST to its primary [`DefId`].
    pub decl_defs: SecondaryMap<DeclId, DefId>,

    /// Maps each predicate in the AST to its primary [`DefId`].
    pub pred_defs: SecondaryMap<PredId, DefId>,

    /// Maps each file to its top-level scope.
    pub file_scopes: SecondaryMap<FileId, ScopeId>,

    /// Maps entities to their member scopes.
    pub def_member_scopes: SparseSecondaryMap<DefId, ScopeId>,

    /// Maps entities to their instance scopes.
    pub def_instance_scopes: SparseSecondaryMap<DefId, ScopeId>,

    /// Type parameters of generic entities.
    pub generics: SparseSecondaryMap<DefId, Vec<DefId>>,

    /// The prelude scope.
    pub prelude_scope_id: ScopeId,

    /// Definitions in the prelude.
    pub prelude_defs: PreludeDefs,

    /// Maps name type expressions to resolved type constructors.
    pub ty_expr_names: SparseSecondaryMap<TyExprId, DefId>,

    /// Maps name expressions to resolved entities.
    pub expr_names: SparseSecondaryMap<ExprId, DefId>,

    /// Maps action call expressions to resolved actions.
    pub expr_action_calls: SparseSecondaryMap<ExprId, DefId>,

    /// Maps automaton instantiation expressions to resolved automata.
    pub expr_instantiations: SparseSecondaryMap<ExprId, InstantiationExprInfo>,

    /// Maps `has`-concept expressions to resolved automaton concepts.
    pub expr_has_concepts: SparseSecondaryMap<ExprId, DefId>,

    /// Maps expressions to their context.
    pub exprs: SecondaryMap<ExprId, ExprCtx>,

    /// Maps statements to their context.
    pub stmts: SecondaryMap<StmtId, StmtCtx>,

    /// Maps annotation uses to their context.
    pub annotations: SecondaryMap<AnnotationId, AnnotationCtx>,
}

impl NameRes {
    /// If `def_id` is an [import entity][Import], finds the non-import entity it (transitively)
    /// points to. Otherwise returns `def_id`.
    ///
    /// Looks entity definitions up in `defs`. See [`resolve_import`][NameRes::resolve_import] that
    /// supplies [`NameRes::defs`] at the cost of possible borrowing issues.
    pub fn resolve_import_in(defs: &Defs, mut def_id: DefId) -> DefId {
        while let DefKind::Import(import1) = &defs[def_id].kind {
            def_id = import1.resolution_cache.get();

            // halve paths.
            if let DefKind::Import(import2) = &defs[def_id].kind {
                def_id = import2.resolution_cache.get();
                import1.resolution_cache.set(def_id);
            }
        }

        def_id
    }

    pub fn resolve_import(&self, def_id: DefId) -> DefId {
        Self::resolve_import_in(&self.defs, def_id)
    }

    pub fn try_resolve_local(&self, scope_id: ScopeId, ns: Ns, name: &str) -> Option<DefId> {
        let scope = &self.scopes[scope_id];
        let key = (ns, name.to_string());

        scope.defs.get(&key).copied()
    }

    pub(crate) fn make_unresolved_name_error(name: &str, loc: Loc) -> Diag {
        Diag::err()
            .at(loc.clone())
            .with_msg(format!("name `{name}` is not defined"))
            .with_label(Label::primary(loc))
            .build()
    }

    pub fn resolve_local(
        &self,
        diag: &mut impl DiagCtx,
        scope_id: ScopeId,
        ns: Ns,
        name: &str,
        loc: &Loc,
    ) -> Result<DefId> {
        if let Some(def_id) = self.try_resolve_local(scope_id, ns, name) {
            return Ok(def_id);
        }

        diag.emit(Self::make_unresolved_name_error(name, loc.clone()));

        Err(SemaError)
    }

    pub fn try_resolve(&self, mut scope_id: ScopeId, ns: Ns, name: &str) -> Option<DefId> {
        assert_ne!(
            ns,
            Ns::Function,
            "entries in the function namespace cannot be resolved recursively"
        );

        loop {
            if let Some(def_id) = self.try_resolve_local(scope_id, ns, name) {
                return Some(def_id);
            }

            let scope = &self.scopes[scope_id];
            scope_id = scope.parent?;
        }
    }

    pub fn resolve(
        &self,
        diag: &mut impl DiagCtx,
        scope_id: ScopeId,
        ns: Ns,
        name: &str,
        loc: &Loc,
    ) -> Result<DefId> {
        if let Some(def_id) = self.try_resolve(scope_id, ns, name) {
            return Ok(def_id);
        }

        diag.emit(Self::make_unresolved_name_error(name, loc.clone()));

        Err(SemaError)
    }

    pub fn def<T: DefKindProject>(&self, def_id: DefId) -> &T {
        match T::project(&self.defs[def_id].kind) {
            Some(def) => def,

            None => panic!(
                "cannot project {:?} as {}",
                self.defs[def_id].kind,
                std::any::type_name::<T>(),
            ),
        }
    }

    pub fn def_mut<T: DefKindProject>(&mut self, def_id: DefId) -> &mut T {
        if T::project_mut(&mut self.defs[def_id].kind).is_none() {
            panic!(
                "cannot project {:?} as {}",
                self.defs[def_id].kind,
                std::any::type_name::<T>(),
            );
        }

        T::project_mut(&mut self.defs[def_id].kind).unwrap()
    }

    fn add_def_to_scope(
        &mut self,
        scope_id: ScopeId,
        ns: Ns,
        name: String,
        def_id: DefId,
    ) -> Result<(), (DefId, String)> {
        let scope = &mut self.scopes[scope_id];

        match ns {
            Ns::Function => {
                scope.functions.entry(name).or_default().push(def_id);
                self.defs[def_id].scope_id = scope_id;

                Ok(())
            }

            _ => {
                let key = (ns, name);
                let (_, name) = &key;

                if let Some(&prev_def_id) = scope.defs.get(&key) {
                    return Err((prev_def_id, name.clone()));
                }

                scope.defs.insert(key, def_id);
                self.defs[def_id].scope_id = scope_id;

                Ok(())
            }
        }
    }

    pub fn add_def(
        &mut self,
        scope_id: ScopeId,
        ns: Ns,
        name: String,
        loc: Loc,
        kind: DefKind,
    ) -> (DefId, Result<(), (DefId, String)>) {
        let def_id = self.defs.insert_with_key(|id| Def {
            id,
            loc: loc.clone(),
            name: name.clone(),
            scope_id,
            kind,
        });

        (def_id, self.add_def_to_scope(scope_id, ns, name, def_id))
    }

    pub fn add_member_scope(&mut self, def_id: DefId, outer_scope_id: ScopeId) -> ScopeId {
        let member_scope_id = self
            .scopes
            .insert(Scope::new(Some(outer_scope_id), ScopeKind::Member(def_id)));
        self.def_member_scopes.insert(def_id, member_scope_id);

        member_scope_id
    }

    pub fn add_param_scope(&mut self, def_id: DefId, outer_scope_id: ScopeId) -> ScopeId {
        self.scopes
            .insert(Scope::new(Some(outer_scope_id), ScopeKind::Params(def_id)))
    }

    pub fn add_instance_scope(&mut self, def_id: DefId, outer_scope_id: ScopeId) -> ScopeId {
        let instance_scope_id = self.scopes.insert(Scope::new(
            Some(outer_scope_id),
            ScopeKind::Instance(def_id),
        ));
        self.def_instance_scopes.insert(def_id, instance_scope_id);

        instance_scope_id
    }

    pub fn define_special_fn_params(&mut self, def_id: DefId, define_this: bool) {
        let param_scope_id = self.def::<DefFunction>(def_id).param_scope_id;

        self.def_mut::<DefFunction>(def_id).result_def_id = self
            .add_def(
                param_scope_id,
                Ns::Var,
                "result".into(),
                self.defs[def_id].loc.clone(),
                DefVariable::new(
                    None,
                    VariableKind::Param {
                        kind: ParamKind::Result,
                        of: def_id,
                    },
                    true,
                )
                .into(),
            )
            .0;

        if define_this {
            self.def_mut::<DefFunction>(def_id).this_def_id = Some(
                self.add_def(
                    param_scope_id,
                    Ns::Var,
                    "this".into(),
                    self.defs[def_id].loc.clone(),
                    DefVariable::new(
                        None,
                        VariableKind::Param {
                            kind: ParamKind::This,
                            of: def_id,
                        },
                        false,
                    )
                    .into(),
                )
                .0,
            );
        }
    }
}

impl Sema<'_> {
    /// Performs name resolution.
    pub fn resolve_names(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

enum DeclCtx<'a> {
    Global(FileId),
    Struct(DefId),

    Automaton {
        def_id: DefId,
        is_constructor_var: bool,
    },

    FuncBody {
        def_id: DefId,
        scope_id: &'a mut ScopeId,
    },
}

impl DeclCtx<'_> {
    fn outer_def_id(&self) -> Option<DefId> {
        match *self {
            DeclCtx::Global(_) => None,
            DeclCtx::Struct(def_id) => Some(def_id),
            DeclCtx::Automaton { def_id, .. } => Some(def_id),
            DeclCtx::FuncBody { def_id, .. } => Some(def_id),
        }
    }

    fn outer(&self, sema: &Sema<'_>) -> (Option<DefId>, ScopeId) {
        match *self {
            DeclCtx::Global(file_id) => (None, sema.name_res.file_scopes[file_id]),

            DeclCtx::Struct(def_id) | DeclCtx::Automaton { def_id, .. } => {
                (Some(def_id), sema.name_res.def_member_scopes[def_id])
            }

            DeclCtx::FuncBody {
                def_id,
                ref scope_id,
                ..
            } => (Some(def_id), **scope_id),
        }
    }

    fn outer_instance(&self, sema: &Sema<'_>) -> Option<(DefId, ScopeId)> {
        match *self {
            DeclCtx::Global(_) => None,

            DeclCtx::Struct(def_id) | DeclCtx::Automaton { def_id, .. } => {
                Some((def_id, sema.name_res.def_instance_scopes[def_id]))
            }

            DeclCtx::FuncBody { .. } => None,
        }
    }
}

struct Pass<'ast, 's, D> {
    sema: &'s mut Sema<'ast>,
    diag: &'s mut D,
    result: Result,
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn new(sema: &'s mut Sema<'ast>, diag: &'s mut D) -> Self {
        Self {
            sema,
            diag,
            result: Ok(()),
        }
    }

    fn run(mut self) -> Result {
        self.init_root_scopes();
        self.add_prelude_defs();

        self.collect_symbols();
        self.result?;

        self.add_imports();
        self.resolve_defs();

        self.result
    }

    fn init_root_scopes(&mut self) {
        let prelude_scope_id = self
            .sema
            .name_res
            .scopes
            .insert(Scope::new(None, ScopeKind::Prelude));
        self.sema.name_res.prelude_scope_id = prelude_scope_id;

        for file_id in self.sema.libsl.files.keys() {
            let import_scope_id = self.sema.name_res.scopes.insert(Scope::new(
                Some(prelude_scope_id),
                ScopeKind::Import(file_id),
            ));

            let file_scope_id = self.sema.name_res.scopes.insert(Scope::new(
                Some(import_scope_id),
                ScopeKind::File(FileScope {
                    file_id,
                    import_scope: import_scope_id,
                }),
            ));

            self.sema
                .name_res
                .file_scopes
                .insert(file_id, file_scope_id);
        }
    }

    fn add_prelude_defs(&mut self) {
        let prelude_scope = &mut self.sema.name_res.scopes[self.sema.name_res.prelude_scope_id];

        for (name, ns, field) in self.sema.name_res.prelude_defs.top_level_defs_mut() {
            let def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                id,
                loc: Loc::Synthetic,
                name: name.into(),
                scope_id: self.sema.name_res.prelude_scope_id,
                kind: Default::default(),
            });
            prelude_scope.defs.insert((ns, name.into()), def_id);

            *field = def_id;
        }

        self.register_intrinsic_annotation();
        self.register_builtin_methods();
    }

    fn register_intrinsic_annotation(&mut self) {
        let def_id = self.sema.name_res.prelude_defs.intrinsic;
        let mut def = DefAnnotation::new(None);

        def.param_scope_id = self.sema.name_res.scopes.insert(Scope::new(
            Some(self.sema.name_res.prelude_scope_id),
            ScopeKind::Params(def_id),
        ));

        self.sema.name_res.generics.insert(def_id, vec![]);

        self.sema
            .name_res
            .defs
            .update_def_kind(def_id, |_| def.into());
    }

    fn register_builtin_methods(&mut self) {
        self.register_builtin_array_methods();
    }

    #[allow(clippy::too_many_arguments)]
    fn register_builtin_function(
        &mut self,
        scope_id: ScopeId,
        name: String,
        builtin: FunctionBuiltin,
        kind: FunctionKind,
        generics: &[(&str, Variance)],
        define_this: bool,
        params: &[&str],
    ) -> DefId {
        let def_id = self
            .add_def(
                scope_id,
                Ns::Function,
                name,
                Loc::Synthetic,
                DefFunction::new(kind, false, builtin.into()).into(),
            )
            .0;
        let param_scope_id = self.add_param_scope(def_id, scope_id);
        self.def_mut::<DefFunction>(def_id).param_scope_id = param_scope_id;

        let generic_defs = generics
            .iter()
            .enumerate()
            .map(|(idx, (generic, variance))| {
                self.add_def(
                    param_scope_id,
                    Ns::Ty,
                    generic.to_string(),
                    Loc::Synthetic,
                    DefTyVariable::new(
                        TyVariableKind::TyParam { of: def_id, idx },
                        variance.clone(),
                    )
                    .into(),
                )
                .0
            })
            .collect();
        self.sema.name_res.generics.insert(def_id, generic_defs);

        self.sema
            .name_res
            .define_special_fn_params(def_id, define_this);

        for (idx, param) in params.iter().enumerate() {
            let param_def_id = self
                .add_def(
                    param_scope_id,
                    Ns::Var,
                    param.to_string(),
                    Loc::Synthetic,
                    DefVariable::new(
                        None,
                        VariableKind::Param {
                            of: def_id,
                            kind: ParamKind::Explicit { idx },
                        },
                        false,
                    )
                    .into(),
                )
                .0;
            self.def_mut::<DefFunction>(def_id)
                .params
                .push(param_def_id);
        }

        def_id
    }

    fn register_builtin_array_methods(&mut self) {
        let def_id = self.sema.name_res.prelude_defs.array;
        let member_scope_id = self.add_member_scope(def_id, self.sema.name_res.prelude_scope_id);
        let instance_scope_id = self.add_instance_scope(def_id, member_scope_id);

        self.sema.name_res.prelude_defs.array_methods.length = self.register_builtin_function(
            instance_scope_id,
            "length".into(),
            FunctionBuiltin::ArrayLength,
            FunctionKind::Proc {
                of: Some(def_id),
                pure: true,
            },
            &[],
            true,
            &[],
        );

        self.sema.name_res.prelude_defs.array_methods.slice = self.register_builtin_function(
            instance_scope_id,
            "slice".into(),
            FunctionBuiltin::ArraySlice,
            FunctionKind::Proc {
                of: Some(def_id),
                pure: true,
            },
            &[],
            true,
            &["from", "to"],
        );
    }

    fn report_multiple_definition(&mut self, loc: Loc, prev_def_id: DefId, name: String) {
        let prev_def = &self.sema.name_res.defs[prev_def_id];
        self.result = Err(SemaError);
        self.diag.emit(
            Diag::err()
                .at(loc.clone())
                .with_msg(format!("the name `{name}` is defined multiple times"))
                .with_label(Label::primary(loc).with_msg("defined here"))
                .with_label(
                    Label::secondary(prev_def.loc.clone()).with_msg("previously defined here"),
                )
                .build(),
        );
    }

    fn add_def(
        &mut self,
        scope_id: ScopeId,
        ns: Ns,
        name: String,
        loc: Loc,
        kind: DefKind,
    ) -> (DefId, bool) {
        let (def_id, result) = self
            .sema
            .name_res
            .add_def(scope_id, ns, name, loc.clone(), kind);

        match result {
            Ok(()) => (def_id, true),

            Err((prev_def_id, name)) => {
                self.report_multiple_definition(loc, prev_def_id, name);

                (def_id, false)
            }
        }
    }

    fn def<T: DefKindProject>(&self, def_id: DefId) -> &T {
        self.sema.name_res.def(def_id)
    }

    fn def_mut<T: DefKindProject>(&mut self, def_id: DefId) -> &mut T {
        self.sema.name_res.def_mut(def_id)
    }

    fn resolve(&mut self, scope_id: ScopeId, ns: Ns, name: &str, loc: &Loc) -> Result<DefId> {
        match self
            .sema
            .name_res
            .resolve(self.diag, scope_id, ns, name, loc)
        {
            Ok(def_id) => Ok(def_id),

            Err(SemaError) => {
                self.result = Err(SemaError);

                Err(SemaError)
            }
        }
    }
}

// Phase 1: collect globally available symbols.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn collect_symbols(&mut self) {
        for (file_id, file) in &self.sema.libsl.files {
            for &decl_id in &file.decls {
                self.process_decl_symbol(DeclCtx::Global(file_id), decl_id);
            }
        }
    }

    fn add_member_scope(&mut self, def_id: DefId, outer_scope_id: ScopeId) -> ScopeId {
        self.sema.name_res.add_member_scope(def_id, outer_scope_id)
    }

    fn add_param_scope(&mut self, def_id: DefId, outer_scope_id: ScopeId) -> ScopeId {
        self.sema.name_res.add_param_scope(def_id, outer_scope_id)
    }

    fn add_instance_scope(&mut self, def_id: DefId, outer_scope_id: ScopeId) -> ScopeId {
        self.sema
            .name_res
            .add_instance_scope(def_id, outer_scope_id)
    }

    fn add_decl_def(
        &mut self,
        decl_id: DeclId,
        scope_id: ScopeId,
        ns: Ns,
        name: String,
        loc: Loc,
        kind: DefKind,
    ) -> (DefId, bool) {
        let (def_id, result) = self.add_def(scope_id, ns, name, loc, kind);
        self.sema.name_res.decl_defs.insert(decl_id, def_id);

        (def_id, result)
    }

    fn add_ctor_fn(&mut self, scope_id: ScopeId, def_id: DefId) -> DefId {
        let fn_def_id = self
            .add_def(
                scope_id,
                Ns::Function,
                self.sema.name_res.defs[def_id].name.clone(),
                self.sema.name_res.defs[def_id].loc.clone(),
                DefFunction::new(
                    FunctionKind::Proc {
                        of: None,
                        pure: true,
                    },
                    false,
                    FunctionBody::Constructor { of: def_id },
                )
                .into(),
            )
            .0;

        let param_scope_id = self.add_param_scope(fn_def_id, scope_id);
        self.def_mut::<DefFunction>(fn_def_id).param_scope_id = param_scope_id;
        self.sema
            .name_res
            .define_special_fn_params(fn_def_id, false);

        fn_def_id
    }

    fn record_member_function(
        &mut self,
        ctx: DeclCtx<'_>,
        is_static: bool,
        _is_method: bool,
        def_id: DefId,
    ) {
        match ctx {
            DeclCtx::Global(_) => {}

            DeclCtx::Struct(struct_def_id) => {
                let struct_def = self.def_mut::<DefStruct>(struct_def_id);

                // FIXME: this is probably wrong given that there's the *. syntax too.
                if is_static {
                    struct_def.static_methods.push(def_id);
                } else {
                    struct_def.instance_methods.push(def_id);
                }
            }

            DeclCtx::Automaton {
                def_id: automaton_def_id,
                ..
            } => {
                let automaton_def = self.def_mut::<DefAutomaton>(automaton_def_id);

                // FIXME: see above.
                if is_static {
                    automaton_def.static_methods.push(def_id);
                } else {
                    automaton_def.instance_methods.push(def_id);
                }
            }

            DeclCtx::FuncBody { .. } => panic!("cannot register functions in a function body"),
        }
    }

    fn process_decl_symbol(&mut self, ctx: DeclCtx<'_>, decl_id: DeclId) {
        let decl = &self.sema.libsl.decls[decl_id];
        let (outer_def_id, outer_scope_id) = ctx.outer(self.sema);

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),

            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}

            ast::DeclKind::SemanticTy(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Ty,
                        decl.ty_name.ty_name.to_string(),
                        decl.ty_name.ty_name.loc.clone(),
                        DefSemanticTy::new(decl_id).into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefSemanticTy>(def_id).param_scope_id = param_scope_id;

                match &decl.kind {
                    ast::SemanticTyKind::Simple => {}

                    ast::SemanticTyKind::Enumerated(values) => {
                        let member_scope_id = self.add_member_scope(def_id, param_scope_id);

                        for (idx, value) in values.iter().enumerate() {
                            let value_def_id = self
                                .add_def(
                                    member_scope_id,
                                    Ns::Var,
                                    value.name.to_string(),
                                    value.name.loc.clone(),
                                    DefKind::SemanticTyEnumValue {
                                        semantic_ty_def_id: def_id,
                                        variant_idx: idx,
                                    },
                                )
                                .0;

                            self.def_mut::<DefSemanticTy>(def_id)
                                .values
                                .push(SemanticTyValue {
                                    def_id: value_def_id,
                                    name: value.name.to_string(),
                                });
                        }
                    }
                }
            }

            ast::DeclKind::TyAlias(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Ty,
                        decl.ty_name.ty_name.to_string(),
                        decl.ty_name.ty_name.loc.clone(),
                        DefTyAlias::new(decl_id).into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefTyAlias>(def_id).param_scope_id = param_scope_id;
            }

            ast::DeclKind::Struct(decl) => {
                let name = decl.ty_name.ty_name.to_string();

                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Ty,
                        name.clone(),
                        decl.ty_name.ty_name.loc.clone(),
                        DefStruct::new(decl_id).into(),
                    )
                    .0;

                let member_scope_id = self.add_member_scope(def_id, outer_scope_id);
                let param_scope_id = self.add_param_scope(def_id, member_scope_id);
                self.add_instance_scope(def_id, param_scope_id);
                self.def_mut::<DefStruct>(def_id).param_scope_id = param_scope_id;

                for &member_decl_id in &decl.decls {
                    self.process_decl_symbol(DeclCtx::Struct(def_id), member_decl_id);
                }

                self.def_mut::<DefStruct>(def_id).ctor_def_id =
                    self.add_ctor_fn(outer_scope_id, def_id);
            }

            ast::DeclKind::Enum(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Ty,
                        decl.ty_name.ty_name.to_string(),
                        decl.ty_name.ty_name.loc.clone(),
                        DefEnum::new(decl_id).into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefEnum>(def_id).param_scope_id = param_scope_id;
                let member_scope_id = self.add_member_scope(def_id, param_scope_id);

                for (idx, variant) in decl.variants.iter().enumerate() {
                    let variant_def_id = self
                        .add_def(
                            member_scope_id,
                            Ns::Var,
                            variant.name.to_string(),
                            variant.name.loc.clone(),
                            DefVariable::new(
                                Some(decl_id),
                                VariableKind::EnumVariant { of: def_id, idx },
                                false,
                            )
                            .into(),
                        )
                        .0;

                    self.def_mut::<DefEnum>(def_id)
                        .variants
                        .push(variant_def_id);
                }
            }

            ast::DeclKind::Annotation(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Annotation,
                        decl.name.to_string(),
                        decl.name.loc.clone(),
                        DefAnnotation::new(Some(decl_id)).into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefAnnotation>(def_id).param_scope_id = param_scope_id;
            }

            ast::DeclKind::Action(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Action,
                        decl.name.to_string(),
                        decl.name.loc.clone(),
                        DefAction::new(decl_id).into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefAction>(def_id).param_scope_id = param_scope_id;
            }

            ast::DeclKind::Automaton(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Automaton,
                        decl.name.ty_name.to_string(),
                        decl.name.ty_name.loc.clone(),
                        DefAutomaton::new(decl_id, decl.is_concept).into(),
                    )
                    .0;

                let member_scope_id = self.add_member_scope(def_id, outer_scope_id);
                let param_scope_id = self.add_param_scope(def_id, member_scope_id);
                self.add_instance_scope(def_id, param_scope_id);
                self.def_mut::<DefAutomaton>(def_id).param_scope_id = param_scope_id;

                for &var_decl_id in &decl.constructor_variables {
                    self.process_decl_symbol(
                        DeclCtx::Automaton {
                            def_id,
                            is_constructor_var: true,
                        },
                        var_decl_id,
                    );
                }

                for &member_decl_id in &decl.decls {
                    self.process_decl_symbol(
                        DeclCtx::Automaton {
                            def_id,
                            is_constructor_var: false,
                        },
                        member_decl_id,
                    );
                }
            }

            ast::DeclKind::Function(decl) => {
                let scope_id = if decl.is_static {
                    outer_scope_id
                } else {
                    ctx.outer_instance(self.sema)
                        .map(|(_, scope_id)| scope_id)
                        .unwrap_or(outer_scope_id)
                };

                let def_id = self
                    .add_decl_def(
                        decl_id,
                        scope_id,
                        Ns::Function,
                        decl.name.to_string(),
                        decl.name.loc.clone(),
                        DefFunction::new(
                            FunctionKind::Fun {
                                of: ctx.outer_def_id(),
                            },
                            decl.is_method,
                            FunctionBodyUser::new(decl_id).into(),
                        )
                        .into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, scope_id);
                self.def_mut::<DefFunction>(def_id).param_scope_id = param_scope_id;

                self.record_member_function(ctx, decl.is_static, decl.is_method, def_id);
            }

            ast::DeclKind::Variable(decl) => {
                let (scope_id, kind) = match ctx {
                    DeclCtx::Global(_) => (outer_scope_id, VariableKind::Global),

                    DeclCtx::Struct(def_id) => (
                        ctx.outer_instance(self.sema).unwrap().1,
                        VariableKind::Field {
                            of: def_id,
                            idx: self.def::<DefStruct>(def_id).fields.len(),
                        },
                    ),

                    DeclCtx::Automaton {
                        def_id,
                        is_constructor_var: true,
                    } => (
                        ctx.outer_instance(self.sema).unwrap().1,
                        VariableKind::ConstructorVar {
                            of: def_id,
                            idx: self.def::<DefAutomaton>(def_id).constructor_params.len(),
                        },
                    ),

                    DeclCtx::Automaton {
                        def_id,
                        is_constructor_var: false,
                    } => (
                        ctx.outer_instance(self.sema).unwrap().1,
                        VariableKind::Field {
                            of: def_id,
                            idx: self.def::<DefAutomaton>(def_id).fields.len(),
                        },
                    ),

                    DeclCtx::FuncBody { .. } => unreachable!(),
                };

                let def_id = self
                    .add_decl_def(
                        decl_id,
                        scope_id,
                        Ns::Var,
                        decl.name.to_string(),
                        decl.name.loc.clone(),
                        DefVariable::new(Some(decl_id), kind, decl.kind.is_var()).into(),
                    )
                    .0;

                match ctx {
                    DeclCtx::Global(_) => {}

                    DeclCtx::Struct(struct_def_id) => {
                        self.def_mut::<DefStruct>(struct_def_id).fields.push(def_id);
                    }

                    DeclCtx::Automaton {
                        def_id: automaton_def_id,
                        is_constructor_var,
                    } => {
                        let automaton_def = self.def_mut::<DefAutomaton>(automaton_def_id);

                        if is_constructor_var {
                            automaton_def.constructor_params.push(def_id);
                        } else {
                            automaton_def.fields.push(def_id);
                        }
                    }

                    DeclCtx::FuncBody { .. } => unreachable!(),
                }
            }

            ast::DeclKind::State(decl) => {
                let DeclCtx::Automaton {
                    def_id: automaton_def_id,
                    ..
                } = ctx
                else {
                    unreachable!();
                };

                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::State,
                        decl.name.to_string(),
                        decl.name.loc.clone(),
                        DefState::new(
                            Some(decl_id),
                            decl.name.to_string(),
                            automaton_def_id,
                            matches!(decl.kind, ast::StateKind::Final),
                        )
                        .into(),
                    )
                    .0;

                let automaton = self.def_mut::<DefAutomaton>(automaton_def_id);
                automaton.states.push(def_id);

                match decl.kind {
                    ast::StateKind::Initial => automaton.init_states.push(def_id),
                    ast::StateKind::Final => automaton.final_states.push(def_id),
                    ast::StateKind::Regular => {}
                }
            }

            ast::DeclKind::Shift(_) => {
                // state transition is not a def.
            }

            ast::DeclKind::Constructor(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Function,
                        decl.name
                            .as_ref()
                            .map(|name| name.to_string())
                            .unwrap_or_default(),
                        decl.name
                            .as_ref()
                            .map(|name| name.loc.clone())
                            .unwrap_or_else(|| decl.kw_loc.clone()),
                        DefFunction::new(
                            FunctionKind::Constructor {
                                of: outer_def_id.unwrap(),
                            },
                            decl.is_method,
                            FunctionBodyUser::new(decl_id).into(),
                        )
                        .into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefFunction>(def_id).param_scope_id = param_scope_id;

                self.record_member_function(ctx, false, decl.is_method, def_id);
            }

            ast::DeclKind::Destructor(decl) => {
                let def_id = self
                    .add_decl_def(
                        decl_id,
                        outer_scope_id,
                        Ns::Function,
                        decl.name
                            .as_ref()
                            .map(|name| name.to_string())
                            .unwrap_or_default(),
                        decl.name
                            .as_ref()
                            .map(|name| name.loc.clone())
                            .unwrap_or_else(|| decl.kw_loc.clone()),
                        DefFunction::new(
                            FunctionKind::Destructor {
                                of: outer_def_id.unwrap(),
                            },
                            decl.is_method,
                            FunctionBodyUser::new(decl_id).into(),
                        )
                        .into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, outer_scope_id);
                self.def_mut::<DefFunction>(def_id).param_scope_id = param_scope_id;

                self.record_member_function(ctx, false, decl.is_method, def_id);
            }

            ast::DeclKind::Proc(decl) => {
                let scope_id = ctx
                    .outer_instance(self.sema)
                    .map(|(_, scope_id)| scope_id)
                    .unwrap_or(outer_scope_id);

                let def_id = self
                    .add_decl_def(
                        decl_id,
                        scope_id,
                        Ns::Function,
                        decl.name.to_string(),
                        decl.name.loc.clone(),
                        DefFunction::new(
                            FunctionKind::Proc {
                                of: match ctx {
                                    DeclCtx::Global(_) => None,
                                    DeclCtx::FuncBody { .. } => unreachable!(),
                                    DeclCtx::Struct(def_id) | DeclCtx::Automaton { def_id, .. } => {
                                        Some(def_id)
                                    }
                                },
                                pure: decl.is_pure,
                            },
                            decl.is_method,
                            FunctionBodyUser::new(decl_id).into(),
                        )
                        .into(),
                    )
                    .0;

                let param_scope_id = self.add_param_scope(def_id, scope_id);
                self.def_mut::<DefFunction>(def_id).param_scope_id = param_scope_id;

                self.record_member_function(ctx, false, decl.is_method, def_id);
            }
        }
    }
}

// Phase 2: populate import scopes with imported entities while checking for conflicts.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn add_imports(&mut self) {
        for (file_id, file) in &self.sema.libsl.files {
            let file_scope_id = self.sema.name_res.file_scopes[file_id];

            let &FileScope {
                import_scope: import_scope_id,
                ..
            } = self.sema.name_res.scopes[file_scope_id]
                .kind
                .as_file_scope()
                .unwrap();

            for &import_decl_id in &file.decls {
                if !matches!(
                    self.sema.libsl.decls[import_decl_id].kind,
                    ast::DeclKind::Import(_)
                ) {
                    continue;
                }

                let import_loc = self.sema.libsl.decls[import_decl_id].loc.clone();
                let imported_file_id = self.sema.imports[import_decl_id];
                let imported_scope_id = self.sema.name_res.file_scopes[imported_file_id];

                let [import_scope, &mut ref imported_scope] = self
                    .sema
                    .name_res
                    .scopes
                    .get_disjoint_mut([import_scope_id, imported_scope_id])
                    .unwrap();

                for (key @ (_, name), &def_id) in &imported_scope.defs {
                    let resolved_def_id =
                        NameRes::resolve_import_in(&self.sema.name_res.defs, def_id);

                    if let Some(&prev_def_id) = import_scope.defs.get(key) {
                        let DefKind::Import(_) = &self.sema.name_res.defs[prev_def_id].kind else {
                            panic!("a non-import def found in an import scope");
                        };

                        let resolved_prev_def_id =
                            NameRes::resolve_import_in(&self.sema.name_res.defs, prev_def_id);

                        // allow importing the same entity twice by doing nothing.
                        if resolved_prev_def_id != resolved_def_id {
                            let prev_import_loc = self.sema.name_res.defs[prev_def_id].loc.clone();
                            let prev_loc = self.sema.name_res.defs[resolved_def_id].loc.clone();
                            let loc = self.sema.name_res.defs[resolved_prev_def_id].loc.clone();

                            self.result = Err(SemaError);
                            self.diag.emit(
                                Diag::err()
                                    .at(import_loc.clone())
                                    .with_msg(format!("name `{name}` is already imported"))
                                    .with_label(
                                        Label::primary(import_loc.clone())
                                            .with_msg("imported here"),
                                    )
                                    .with_label(
                                        Label::secondary(prev_import_loc)
                                            .with_msg("previously imported here"),
                                    )
                                    .with_label(
                                        Label::secondary(prev_loc)
                                            .with_msg("this entity cannot be imported"),
                                    )
                                    .with_label(Label::secondary(loc).with_msg(
                                        "this entity was imported previously under the same name",
                                    ))
                                    .build(),
                            );
                        }
                    } else {
                        let new_def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                            id,
                            loc: import_loc.clone(),
                            name: name.clone(),
                            scope_id: import_scope_id,
                            kind: DefKind::Import(DefImport::new_resolved(
                                import_decl_id,
                                def_id,
                                resolved_def_id,
                            )),
                        });

                        import_scope.defs.insert(key.clone(), new_def_id);
                    }
                }

                for (name, imported_overloads) in &imported_scope.functions {
                    let overloads = import_scope.functions.entry(name.clone()).or_default();
                    let mut resolved_overloads = overloads
                        .iter()
                        .copied()
                        .map(|def_id| NameRes::resolve_import_in(&self.sema.name_res.defs, def_id))
                        .collect::<HashSet<_>>();

                    for &overload in imported_overloads {
                        let resolved_def_id =
                            NameRes::resolve_import_in(&self.sema.name_res.defs, overload);

                        if !resolved_overloads.insert(resolved_def_id) {
                            continue;
                        }

                        let new_def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                            id,
                            loc: import_loc.clone(),
                            name: name.clone(),
                            scope_id: import_scope_id,
                            kind: DefKind::Import(DefImport::new_resolved(
                                import_decl_id,
                                overload,
                                resolved_def_id,
                            )),
                        });

                        overloads.push(new_def_id);
                    }
                }
            }
        }
    }
}

// Phase 3: walk definitions, adding local scopes.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn resolve_defs(&mut self) {
        for (file_id, file) in &self.sema.libsl.files {
            for &decl_id in &file.decls {
                self.process_decl(DeclCtx::Global(file_id), decl_id);
            }
        }
    }

    fn process_generics(
        &mut self,
        def_id: DefId,
        param_scope_id: ScopeId,
        generics: &[ast::Generic],
    ) {
        let mut generic_defs = vec![];

        for (idx, generic) in generics.iter().enumerate() {
            let param_def_id = self
                .add_def(
                    param_scope_id,
                    Ns::Ty,
                    generic.name.to_string(),
                    generic.name.loc.clone(),
                    DefTyVariable::new(
                        TyVariableKind::TyParam { of: def_id, idx },
                        generic.variance.clone().unwrap_or(Variance::Invariant),
                    )
                    .into(),
                )
                .0;

            generic_defs.push(param_def_id);
        }

        self.sema.name_res.generics.insert(def_id, generic_defs);
    }

    fn process_annotations(
        &mut self,
        def_id: DefId,
        annotations: &[AnnotationId],
    ) -> Vec<AnnotationId> {
        let scope_id = self.sema.name_res.defs[def_id].scope_id;

        for &annotation_id in annotations {
            self.process_annotation(
                AnnotatedEntity::Def(def_id),
                scope_id,
                &self.sema.libsl.annotations[annotation_id],
            );
        }

        annotations.to_vec()
    }

    fn process_annotation(
        &mut self,
        entity: AnnotatedEntity,
        scope_id: ScopeId,
        annotation: &'ast ast::Annotation,
    ) {
        let name = annotation.name.to_string();
        let def_id = self
            .resolve(scope_id, Ns::Annotation, &name, &annotation.name.loc)
            .map(|def_id| self.sema.name_res.resolve_import(def_id))
            .ok();
        let param_scope_id = def_id.map(|def_id| self.def::<DefAnnotation>(def_id).param_scope_id);

        if let Some(def_id) = def_id {
            self.def_mut::<DefAnnotation>(def_id)
                .users
                .push(annotation.id);
        }

        let args = annotation
            .args
            .iter()
            .enumerate()
            .map(|(idx, arg)| {
                let param_def_id = match &arg.name {
                    Some(name) => param_scope_id.and_then(|param_scope_id| {
                        self.resolve(param_scope_id, Ns::Var, &name.to_string(), &name.loc)
                            .map(|def_id| self.sema.name_res.resolve_import(def_id))
                            .ok()
                    }),

                    None => def_id.and_then(|def_id| {
                        self.def::<DefAnnotation>(def_id).params.get(idx).copied()
                    }),
                };

                self.process_expr(
                    ExprCtx {
                        scope_id,
                        kind: ExprCtxKind::AnnotationArg {
                            annotation_id: annotation.id,
                            idx,
                        },
                    },
                    arg.expr,
                );

                param_def_id.unwrap_or_default()
            })
            .collect();

        self.sema.name_res.annotations.insert(
            annotation.id,
            AnnotationCtx {
                def_id: def_id.unwrap_or_default(),
                entity,
                args,
            },
        );
    }

    fn process_function_params(
        &mut self,
        define_this: bool,
        def_id: DefId,
        param_scope_id: ScopeId,
        params: &[ast::FunctionParam],
    ) {
        self.sema
            .name_res
            .define_special_fn_params(def_id, define_this);

        for (idx, param) in params.iter().enumerate() {
            let name = param.name.to_string();

            let param_def_id = self
                .add_def(
                    param_scope_id,
                    Ns::Var,
                    name,
                    param.name.loc.clone(),
                    DefVariable::new(
                        None,
                        VariableKind::Param {
                            kind: ParamKind::Explicit { idx },
                            of: def_id,
                        },
                        true,
                    )
                    .into(),
                )
                .0;

            self.def_mut::<DefVariable>(param_def_id).annotations =
                self.process_annotations(param_def_id, &param.annotations);

            self.def_mut::<DefFunction>(def_id)
                .params
                .push(param_def_id);

            self.process_ty_expr(param_scope_id, param.ty_expr);
        }

        // TODO: process type constraints.
    }

    fn process_function_body(&mut self, func_def_id: DefId, body: &'ast ast::FunctionBody) {
        let param_scope_id = self.def::<DefFunction>(func_def_id).param_scope_id;
        let scope_id = self.sema.name_res.scopes.insert(Scope::new(
            Some(param_scope_id),
            ScopeKind::Block {
                func: func_def_id,
                kind: BlockKind::Body(func_def_id),
            },
        ));

        self.def_mut::<DefFunction>(func_def_id)
            .body
            .as_user_mut()
            .unwrap()
            .body_scope_id = scope_id;

        for contract in &body.contracts {
            self.process_contract(func_def_id, contract);
        }

        let mut current_scope_id = scope_id;

        for &stmt_id in &body.stmts {
            self.process_stmt(func_def_id, &mut current_scope_id, stmt_id);
        }
    }
}

// Phase 3, declarations.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_decl(&mut self, ctx: DeclCtx<'_>, decl_id: DeclId) {
        let decl = &self.sema.libsl.decls[decl_id];

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),
            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}

            ast::DeclKind::SemanticTy(decl) => self.process_decl_semantic_ty(ctx, decl_id, decl),
            ast::DeclKind::TyAlias(decl) => self.process_decl_ty_alias(ctx, decl_id, decl),
            ast::DeclKind::Struct(decl) => self.process_decl_struct(ctx, decl_id, decl),
            ast::DeclKind::Enum(decl) => self.process_decl_enum(ctx, decl_id, decl),
            ast::DeclKind::Annotation(decl) => self.process_decl_annotation(ctx, decl_id, decl),
            ast::DeclKind::Action(decl) => self.process_decl_action(ctx, decl_id, decl),
            ast::DeclKind::Automaton(decl) => self.process_decl_automaton(ctx, decl_id, decl),
            ast::DeclKind::Function(decl) => self.process_decl_function(ctx, decl_id, decl),
            ast::DeclKind::Variable(decl) => self.process_decl_variable(ctx, decl_id, decl),
            ast::DeclKind::State(decl) => self.process_decl_state(ctx, decl_id, decl),
            ast::DeclKind::Shift(decl) => self.process_decl_shift(ctx, decl_id, decl),
            ast::DeclKind::Constructor(decl) => self.process_decl_constructor(ctx, decl_id, decl),
            ast::DeclKind::Destructor(decl) => self.process_decl_destructor(ctx, decl_id, decl),
            ast::DeclKind::Proc(decl) => self.process_decl_proc(ctx, decl_id, decl),
        }
    }

    fn process_decl_semantic_ty(
        &mut self,
        _ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclSemanticTy,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefSemanticTy>(def_id).param_scope_id;

        self.def_mut::<DefSemanticTy>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.ty_name.generics);

        self.process_ty_expr(param_scope_id, decl.real_ty);

        match &decl.kind {
            ast::SemanticTyKind::Simple => {}
            ast::SemanticTyKind::Enumerated(values) => {
                let member_scope_id = self.sema.name_res.def_member_scopes[def_id];

                for (idx, value) in values.iter().enumerate() {
                    let value_def_id =
                        self.sema.name_res.def::<DefSemanticTy>(def_id).values[idx].def_id;

                    self.process_expr(
                        ExprCtx {
                            scope_id: member_scope_id,
                            kind: ExprCtxKind::EnumSemanticTyValue(value_def_id),
                        },
                        value.expr,
                    );
                }
            }
        }
    }

    fn process_decl_ty_alias(
        &mut self,
        _ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclTyAlias,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefTyAlias>(def_id).param_scope_id;

        self.process_generics(def_id, param_scope_id, &decl.ty_name.generics);
        self.def_mut::<DefTyAlias>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);

        self.process_ty_expr(param_scope_id, decl.ty_expr);
    }

    fn process_decl_struct(
        &mut self,
        _ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclStruct,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefStruct>(def_id).param_scope_id;

        self.def_mut::<DefStruct>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.ty_name.generics);

        if let Some(is_ty) = decl.is_ty {
            self.process_ty_expr(param_scope_id, is_ty);
        }

        for &for_ty in &decl.for_tys {
            self.process_ty_expr(param_scope_id, for_ty);
        }

        // TODO: type constraints.

        for &member_decl_id in &decl.decls {
            self.process_decl(DeclCtx::Struct(def_id), member_decl_id);
        }

        let fields = self.def::<DefStruct>(def_id).fields.clone();
        let ctor_def_id = self.def::<DefStruct>(def_id).ctor_def_id;
        let ctor_param_scope_id = self.def::<DefFunction>(ctor_def_id).param_scope_id;

        self.sema
            .name_res
            .generics
            .insert(ctor_def_id, self.sema.name_res.generics[def_id].clone());

        for (idx, field) in fields.into_iter().enumerate() {
            // if we have problems here, we should've already reported them when we registered the
            // field, which is why we use the non-reporting `add_def` version.
            let param_def_id = self
                .sema
                .name_res
                .add_def(
                    ctor_param_scope_id,
                    Ns::Var,
                    self.sema.name_res.defs[field].name.clone(),
                    self.sema.name_res.defs[field].loc.clone(),
                    DefVariable::new(
                        None,
                        VariableKind::Param {
                            of: ctor_def_id,
                            kind: ParamKind::Explicit { idx },
                        },
                        false,
                    )
                    .into(),
                )
                .0;

            self.def_mut::<DefFunction>(ctor_def_id)
                .params
                .push(param_def_id);
        }
    }

    fn process_decl_enum(&mut self, _ctx: DeclCtx<'_>, decl_id: DeclId, decl: &'ast ast::DeclEnum) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefEnum>(def_id).param_scope_id;

        self.def_mut::<DefEnum>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.ty_name.generics);
    }

    fn process_decl_annotation(
        &mut self,
        _ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclAnnotation,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefAnnotation>(def_id).param_scope_id;

        for (idx, param) in decl.params.iter().enumerate() {
            let param_def_id = self
                .add_def(
                    param_scope_id,
                    Ns::Var,
                    param.name.to_string(),
                    param.name.loc.clone(),
                    DefVariable::new(
                        None,
                        VariableKind::Param {
                            of: def_id,
                            kind: ParamKind::Explicit { idx },
                        },
                        true,
                    )
                    .into(),
                )
                .0;

            self.def_mut::<DefAnnotation>(def_id)
                .params
                .push(param_def_id);

            self.process_ty_expr(param_scope_id, param.ty_expr);

            if let Some(expr_id) = param.default {
                self.process_expr(
                    ExprCtx {
                        scope_id: param_scope_id,
                        kind: ExprCtxKind::AnnotationParam(param_def_id),
                    },
                    expr_id,
                );
            }
        }
    }

    fn process_decl_action(
        &mut self,
        _ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclAction,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefAction>(def_id).param_scope_id;

        self.def_mut::<DefAction>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.generics);

        for (idx, param) in decl.params.iter().enumerate() {
            let param_def_id = self
                .add_def(
                    param_scope_id,
                    Ns::Var,
                    param.name.to_string(),
                    param.name.loc.clone(),
                    DefVariable::new(
                        None,
                        VariableKind::Param {
                            of: def_id,
                            kind: ParamKind::Explicit { idx },
                        },
                        true,
                    )
                    .into(),
                )
                .0;

            self.def_mut::<DefVariable>(param_def_id).annotations =
                self.process_annotations(def_id, &param.annotations);

            self.def_mut::<DefAction>(def_id).params.push(param_def_id);
            self.process_ty_expr(param_scope_id, param.ty_expr);
        }

        if let Some(ty_expr_id) = decl.ret_ty_expr {
            self.process_ty_expr(param_scope_id, ty_expr_id);
        }
    }

    fn process_decl_automaton(
        &mut self,
        _ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclAutomaton,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefAutomaton>(def_id).param_scope_id;

        self.def_mut::<DefAutomaton>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.name.generics);

        for &var_decl_id in &decl.constructor_variables {
            self.process_decl(
                DeclCtx::Automaton {
                    def_id,
                    is_constructor_var: true,
                },
                var_decl_id,
            );
        }

        self.process_ty_expr(param_scope_id, decl.ty_expr);

        // TODO: resolve implemented concepts?

        for &member_decl_id in &decl.decls {
            self.process_decl(
                DeclCtx::Automaton {
                    def_id,
                    is_constructor_var: false,
                },
                member_decl_id,
            );
        }
    }

    fn process_decl_function(
        &mut self,
        ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclFunction,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefFunction>(def_id).param_scope_id;

        // TODO: handle extension methods.

        self.def_mut::<DefFunction>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.generics);

        self.process_function_params(
            ctx.outer_def_id().is_some(),
            def_id,
            param_scope_id,
            &decl.params,
        );

        if let Some(ty_expr_id) = decl.ret_ty_expr {
            self.process_ty_expr(param_scope_id, ty_expr_id);
        }

        if let Some(body) = &decl.body {
            self.process_function_body(def_id, body);
        }
    }

    fn process_decl_variable(
        &mut self,
        ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclVariable,
    ) {
        let (_, scope_id) = ctx.outer(self.sema);

        let (def_id, needs_registering) = match ctx {
            DeclCtx::Global(_) | DeclCtx::Struct(_) | DeclCtx::Automaton { .. } => {
                // already registered in phase 1.
                (self.sema.name_res.decl_defs[decl_id], false)
            }

            DeclCtx::FuncBody {
                def_id: func_def_id,
                ..
            } => {
                let ScopeKind::Block {
                    kind: block_kind, ..
                } = &self.sema.name_res.scopes[scope_id].kind
                else {
                    unreachable!("a local variable is defined in a non-block scope");
                };

                let local_kind = match *block_kind {
                    BlockKind::Body(_) | BlockKind::Stmt(_) => LocalKind::Stmt,
                    BlockKind::Pred(_) => LocalKind::Contract,

                    BlockKind::Var(decl_id) => {
                        let VariableKind::Local { kind, .. } = self
                            .def::<DefVariable>(self.sema.name_res.decl_defs[decl_id])
                            .kind
                        else {
                            unreachable!();
                        };

                        kind
                    }
                };

                let def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                    id,
                    loc: decl.name.loc.clone(),
                    name: decl.name.to_string(),
                    scope_id,
                    kind: DefVariable::new(
                        Some(decl_id),
                        VariableKind::Local {
                            of: func_def_id,
                            kind: local_kind,
                        },
                        decl.kind.is_var(),
                    )
                    .into(),
                });

                self.sema.name_res.decl_defs.insert(decl_id, def_id);

                (def_id, true)
            }
        };

        self.sema
            .name_res
            .def_mut::<DefVariable>(def_id)
            .annotations = self.process_annotations(def_id, &decl.annotations);

        if let Some(ty_expr_id) = decl.ty_expr {
            self.process_ty_expr(scope_id, ty_expr_id);
        }

        if let Some(expr_id) = decl.init {
            self.process_expr(
                ExprCtx {
                    scope_id,
                    kind: ExprCtxKind::VariableInit(def_id),
                },
                expr_id,
            );
        }

        if needs_registering {
            let DeclCtx::FuncBody {
                def_id: func_def_id,
                scope_id,
            } = ctx
            else {
                unreachable!()
            };

            *scope_id = self.sema.name_res.scopes.insert(Scope::new(
                Some(*scope_id),
                ScopeKind::Block {
                    func: func_def_id,
                    kind: BlockKind::Var(decl_id),
                },
            ));

            if let Err((prev_def_id, name)) = self.sema.name_res.add_def_to_scope(
                *scope_id,
                Ns::Var,
                decl.name.to_string(),
                def_id,
            ) {
                self.report_multiple_definition(decl.name.loc.clone(), prev_def_id, name);
            }
        }
    }

    fn process_decl_state(
        &mut self,
        _ctx: DeclCtx<'_>,
        _decl_id: DeclId,
        _decl: &'ast ast::DeclState,
    ) {
        // do nothing.
    }

    fn process_decl_shift(
        &mut self,
        _ctx: DeclCtx<'_>,
        _decl_id: DeclId,
        _decl: &'ast ast::DeclShift,
    ) {
        // do nothing.
    }

    fn process_decl_constructor(
        &mut self,
        ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclConstructor,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefFunction>(def_id).param_scope_id;

        self.def_mut::<DefFunction>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);

        self.process_function_params(
            ctx.outer_def_id().is_some(),
            def_id,
            param_scope_id,
            &decl.params,
        );

        if let Some(ty_expr_id) = decl.ret_ty_expr {
            self.process_ty_expr(param_scope_id, ty_expr_id);
        }

        if let Some(body) = &decl.body {
            self.process_function_body(def_id, body);
        }
    }

    fn process_decl_destructor(
        &mut self,
        ctx: DeclCtx<'_>,
        decl_id: DeclId,
        decl: &'ast ast::DeclDestructor,
    ) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefFunction>(def_id).param_scope_id;

        self.def_mut::<DefFunction>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);

        self.process_function_params(
            ctx.outer_def_id().is_some(),
            def_id,
            param_scope_id,
            &decl.params,
        );

        if let Some(ty_expr_id) = decl.ret_ty_expr {
            self.process_ty_expr(param_scope_id, ty_expr_id);
        }

        if let Some(body) = &decl.body {
            self.process_function_body(def_id, body);
        }
    }

    fn process_decl_proc(&mut self, ctx: DeclCtx<'_>, decl_id: DeclId, decl: &'ast ast::DeclProc) {
        let def_id = self.sema.name_res.decl_defs[decl_id];
        let param_scope_id = self.def::<DefFunction>(def_id).param_scope_id;

        self.def_mut::<DefFunction>(def_id).annotations =
            self.process_annotations(def_id, &decl.annotations);
        self.process_generics(def_id, param_scope_id, &decl.generics);

        self.process_function_params(
            ctx.outer_def_id().is_some(),
            def_id,
            param_scope_id,
            &decl.params,
        );

        if let Some(ty_expr_id) = decl.ret_ty_expr {
            self.process_ty_expr(param_scope_id, ty_expr_id);
        }

        if let Some(body) = &decl.body {
            self.process_function_body(def_id, body);
        }
    }
}

// Phase 3, contracts and predicates.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_contract(&mut self, func_def_id: DefId, contract: &'ast ast::Contract) {
        let scope_id = self
            .def::<DefFunction>(func_def_id)
            .body
            .as_user()
            .unwrap()
            .body_scope_id;

        match contract {
            ast::Contract::Requires(contract) => {
                self.process_contract_requires(func_def_id, scope_id, contract)
            }

            ast::Contract::Ensures(contract) => {
                self.process_contract_ensures(func_def_id, scope_id, contract)
            }

            ast::Contract::Assigns(contract) => {
                self.process_contract_assigns(func_def_id, scope_id, contract)
            }
        }
    }

    fn process_contract_requires(
        &mut self,
        func_def_id: DefId,
        scope_id: ScopeId,
        contract: &'ast ast::ContractRequires,
    ) {
        let mut current_scope_id = scope_id;

        self.process_pred(
            func_def_id,
            &mut current_scope_id,
            PredKind::ContractRequires,
            contract.pred,
        );
    }

    fn process_contract_ensures(
        &mut self,
        func_def_id: DefId,
        scope_id: ScopeId,
        contract: &'ast ast::ContractEnsures,
    ) {
        let mut current_scope_id = scope_id;

        self.process_pred(
            func_def_id,
            &mut current_scope_id,
            PredKind::ContractEnsures,
            contract.pred,
        );
    }

    fn process_contract_assigns(
        &mut self,
        func_def_id: DefId,
        scope_id: ScopeId,
        contract: &'ast ast::ContractAssigns,
    ) {
        // NOTE: names are skipped because it's unclear what they mean.

        self.process_expr(
            ExprCtx {
                scope_id,
                kind: ExprCtxKind::FunctionBody(func_def_id),
            },
            contract.expr,
        );
    }

    fn process_pred(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        kind: PredKind,
        pred_id: PredId,
    ) {
        let pred = &self.sema.libsl.preds[pred_id];

        match &pred.kind {
            ast::PredKind::Dummy => unreachable!(),

            ast::PredKind::Block(pred) => {
                self.process_pred_block(func_def_id, scope_id, kind, pred_id, pred)
            }

            ast::PredKind::Named(pred) => {
                self.process_pred_named(func_def_id, scope_id, kind, pred_id, pred)
            }

            &ast::PredKind::Decl(decl_id) => {
                self.process_pred_var(func_def_id, scope_id, kind, pred_id, decl_id)
            }

            ast::PredKind::If(pred) => {
                self.process_pred_if(func_def_id, scope_id, kind, pred_id, pred)
            }

            &ast::PredKind::Expr(expr_id) => {
                self.process_pred_expr(func_def_id, scope_id, kind, pred_id, expr_id)
            }
        }
    }

    fn process_pred_block(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _kind: PredKind,
        pred_id: PredId,
        pred: &'ast ast::PredBlock,
    ) {
        let mut scope_id = self.sema.name_res.scopes.insert(Scope::new(
            Some(*scope_id),
            ScopeKind::Block {
                func: func_def_id,
                kind: BlockKind::Pred(pred_id),
            },
        ));

        for &pred_id in &pred.preds {
            self.process_pred(func_def_id, &mut scope_id, PredKind::Nested, pred_id);
        }
    }

    fn process_pred_named(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        kind: PredKind,
        pred_id: PredId,
        pred: &'ast ast::PredNamed,
    ) {
        let body_scope_id = self
            .def::<DefFunction>(func_def_id)
            .body
            .as_user()
            .unwrap()
            .body_scope_id;
        let def_id = self
            .add_def(
                body_scope_id,
                Ns::Contract,
                pred.name.to_string(),
                pred.name.loc.clone(),
                DefPred::new(pred_id, func_def_id, kind).into(),
            )
            .0;
        self.sema.name_res.pred_defs.insert(pred_id, def_id);

        self.process_pred(func_def_id, scope_id, PredKind::Nested, pred.pred);
    }

    fn process_pred_var(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _kind: PredKind,
        _pred_id: PredId,
        decl_id: DeclId,
    ) {
        self.process_decl(
            DeclCtx::FuncBody {
                def_id: func_def_id,
                scope_id,
            },
            decl_id,
        );
    }

    fn process_pred_if(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _kind: PredKind,
        pred_id: PredId,
        pred: &'ast ast::PredIf,
    ) {
        self.process_expr(
            ExprCtx {
                scope_id: *scope_id,
                kind: ExprCtxKind::FunctionBody(func_def_id),
            },
            pred.cond,
        );

        let mut then_scope_id = self.sema.name_res.scopes.insert(Scope::new(
            Some(*scope_id),
            ScopeKind::Block {
                func: func_def_id,
                kind: BlockKind::Pred(pred_id),
            },
        ));

        self.process_pred(
            func_def_id,
            &mut then_scope_id,
            PredKind::Nested,
            pred.then_branch,
        );

        if let Some(else_pred_id) = pred.else_branch {
            let mut else_scope_id = self.sema.name_res.scopes.insert(Scope::new(
                Some(*scope_id),
                ScopeKind::Block {
                    func: func_def_id,
                    kind: BlockKind::Pred(pred_id),
                },
            ));

            self.process_pred(
                func_def_id,
                &mut else_scope_id,
                PredKind::Nested,
                else_pred_id,
            );
        }
    }

    fn process_pred_expr(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _kind: PredKind,
        _pred_id: PredId,
        expr_id: ExprId,
    ) {
        self.process_expr(
            ExprCtx {
                scope_id: *scope_id,
                kind: ExprCtxKind::FunctionBody(func_def_id),
            },
            expr_id,
        );
    }
}

// Phase 3, statements.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_stmt(&mut self, func_def_id: DefId, scope_id: &mut ScopeId, stmt_id: StmtId) {
        let stmt = &self.sema.libsl.stmts[stmt_id];

        self.sema.name_res.stmts.insert(
            stmt_id,
            StmtCtx {
                enclosing_fn: func_def_id,
            },
        );

        match &stmt.kind {
            ast::StmtKind::Dummy => unreachable!(),

            &ast::StmtKind::Decl(decl_id) => {
                self.process_stmt_decl(func_def_id, scope_id, stmt_id, decl_id)
            }

            ast::StmtKind::If(stmt) => self.process_stmt_if(func_def_id, scope_id, stmt_id, stmt),

            ast::StmtKind::Assign(stmt) => {
                self.process_stmt_assign(func_def_id, scope_id, stmt_id, stmt)
            }

            ast::StmtKind::Cancel(stmt) => {
                self.process_stmt_cancel(func_def_id, scope_id, stmt_id, stmt)
            }

            &ast::StmtKind::Expr(expr_id) => {
                self.process_stmt_expr(func_def_id, scope_id, stmt_id, expr_id)
            }
        }
    }

    fn process_stmt_decl(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _stmt_id: StmtId,
        decl_id: DeclId,
    ) {
        self.process_decl(
            DeclCtx::FuncBody {
                def_id: func_def_id,
                scope_id,
            },
            decl_id,
        );
    }

    fn process_stmt_if(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        stmt_id: StmtId,
        stmt: &'ast ast::StmtIf,
    ) {
        self.process_expr(
            ExprCtx {
                scope_id: *scope_id,
                kind: ExprCtxKind::FunctionBody(func_def_id),
            },
            stmt.cond,
        );

        let mut then_scope_id = self.sema.name_res.scopes.insert(Scope::new(
            Some(*scope_id),
            ScopeKind::Block {
                func: func_def_id,
                kind: BlockKind::Stmt(stmt_id),
            },
        ));

        for &then_stmt_id in &stmt.then_branch {
            self.process_stmt(func_def_id, &mut then_scope_id, then_stmt_id);
        }

        if !stmt.else_branch.is_empty() {
            let mut else_scope_id = self.sema.name_res.scopes.insert(Scope::new(
                Some(*scope_id),
                ScopeKind::Block {
                    func: func_def_id,
                    kind: BlockKind::Stmt(stmt_id),
                },
            ));

            for &else_stmt_id in &stmt.else_branch {
                self.process_stmt(func_def_id, &mut else_scope_id, else_stmt_id);
            }
        }
    }

    fn process_stmt_assign(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _stmt_id: StmtId,
        stmt: &'ast ast::StmtAssign,
    ) {
        let ctx = ExprCtx {
            scope_id: *scope_id,
            kind: ExprCtxKind::FunctionBody(func_def_id),
        };

        self.process_expr(ctx.clone(), stmt.lhs);
        self.process_expr(ctx.clone(), stmt.rhs);
    }

    fn process_stmt_cancel(
        &mut self,
        _func_def_id: DefId,
        _scope_id: &mut ScopeId,
        _stmt_id: StmtId,
        _stmt: &'ast ast::StmtCancel,
    ) {
        // do nothing.
    }

    fn process_stmt_expr(
        &mut self,
        func_def_id: DefId,
        scope_id: &mut ScopeId,
        _stmt_id: StmtId,
        expr_id: ExprId,
    ) {
        self.process_expr(
            ExprCtx {
                scope_id: *scope_id,
                kind: ExprCtxKind::FunctionBody(func_def_id),
            },
            expr_id,
        );
    }
}

// Phase 3, type expressions.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_ty_expr(&mut self, scope_id: ScopeId, ty_expr_id: TyExprId) {
        let ty_expr = &self.sema.libsl.ty_exprs[ty_expr_id];

        match &ty_expr.kind {
            ast::TyExprKind::Dummy => unreachable!(),

            ast::TyExprKind::PrimitiveLit(ty_expr) => {
                self.process_ty_expr_primitive_lit(scope_id, ty_expr_id, ty_expr)
            }

            ast::TyExprKind::Name(ty_expr) => {
                self.process_ty_expr_name(scope_id, ty_expr_id, ty_expr)
            }

            ast::TyExprKind::Pointer(ty_expr) => {
                self.process_ty_expr_pointer(scope_id, ty_expr_id, ty_expr)
            }

            ast::TyExprKind::Intersection(ty_expr) => {
                self.process_ty_expr_intersection(scope_id, ty_expr_id, ty_expr)
            }

            ast::TyExprKind::Union(ty_expr) => {
                self.process_ty_expr_union(scope_id, ty_expr_id, ty_expr)
            }
        }
    }

    fn process_ty_expr_primitive_lit(
        &mut self,
        _scope_id: ScopeId,
        _ty_expr_id: TyExprId,
        _ty_expr: &'ast ast::TyExprPrimitiveLit,
    ) {
        // do nothing.
    }

    fn process_ty_expr_name(
        &mut self,
        scope_id: ScopeId,
        ty_expr_id: TyExprId,
        ty_expr: &'ast ast::TyExprName,
    ) {
        let ty_name = ty_expr.ty_name.to_string();

        if let Ok(ctor_def_id) = self.resolve(scope_id, Ns::Ty, &ty_name, &ty_expr.ty_name.loc) {
            let ctor_def_id = self.sema.name_res.resolve_import(ctor_def_id);
            self.sema
                .name_res
                .ty_expr_names
                .insert(ty_expr_id, ctor_def_id);
        }

        if let Some(args) = &ty_expr.generics {
            for arg in args {
                self.process_ty_arg(scope_id, arg);
            }
        }
    }

    fn process_ty_expr_pointer(
        &mut self,
        scope_id: ScopeId,
        _ty_expr_id: TyExprId,
        ty_expr: &'ast ast::TyExprPointer,
    ) {
        self.process_ty_expr(scope_id, ty_expr.base);
    }

    fn process_ty_expr_intersection(
        &mut self,
        scope_id: ScopeId,
        _ty_expr_id: TyExprId,
        ty_expr: &'ast ast::TyExprIntersection,
    ) {
        self.process_ty_expr(scope_id, ty_expr.lhs);
        self.process_ty_expr(scope_id, ty_expr.rhs);
    }

    fn process_ty_expr_union(
        &mut self,
        scope_id: ScopeId,
        _ty_expr_id: TyExprId,
        ty_expr: &'ast ast::TyExprUnion,
    ) {
        self.process_ty_expr(scope_id, ty_expr.lhs);
        self.process_ty_expr(scope_id, ty_expr.rhs);
    }

    fn process_ty_arg(&mut self, scope_id: ScopeId, ty_arg: &'ast ast::TyArg) {
        match *ty_arg {
            ast::TyArg::TyExpr(_, ty_expr_id) => self.process_ty_expr(scope_id, ty_expr_id),
            ast::TyArg::Wildcard(_) => {}
        }
    }
}

// Phase 3, expressions and access expressions.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_expr(&mut self, ctx: ExprCtx, expr_id: ExprId) {
        let expr = &self.sema.libsl.exprs[expr_id];
        self.sema.name_res.exprs.insert(expr_id, ctx.clone());

        match &expr.kind {
            ast::ExprKind::Dummy => unreachable!(),

            ast::ExprKind::PrimitiveLit(expr) => {
                self.process_expr_primitive_lit(ctx, expr_id, expr)
            }

            ast::ExprKind::ArrayLit(expr) => self.process_expr_array_lit(ctx, expr_id, expr),

            ast::ExprKind::SetLit(expr) => self.process_expr_set_lit(ctx, expr_id, expr),

            ast::ExprKind::ProcCall(expr) => self.process_expr_proc_call(ctx, expr_id, expr),

            ast::ExprKind::ActionCall(expr) => self.process_expr_action_call(ctx, expr_id, expr),

            ast::ExprKind::Instantiate(expr) => self.process_expr_instantiate(ctx, expr_id, expr),

            ast::ExprKind::Name(expr) => self.process_expr_name(ctx, expr_id, expr),

            ast::ExprKind::Prev(expr) => self.process_expr_prev(ctx, expr_id, expr),

            ast::ExprKind::Field(expr) => self.process_expr_field(ctx, expr_id, expr),

            ast::ExprKind::Deref(expr) => self.process_expr_deref(ctx, expr_id, expr),

            ast::ExprKind::Index(expr) => self.process_expr_index(ctx, expr_id, expr),

            ast::ExprKind::HasConcept(expr) => self.process_expr_has_concept(ctx, expr_id, expr),

            ast::ExprKind::Cast(expr) => self.process_expr_cast(ctx, expr_id, expr),

            ast::ExprKind::TyCompare(expr) => self.process_expr_ty_compare(ctx, expr_id, expr),

            ast::ExprKind::Unary(expr) => self.process_expr_unary(ctx, expr_id, expr),

            ast::ExprKind::Binary(expr) => self.process_expr_binary(ctx, expr_id, expr),
        }
    }

    fn process_expr_primitive_lit(
        &mut self,
        _ctx: ExprCtx,
        _expr_id: ExprId,
        _expr: &'ast ast::ExprPrimitiveLit,
    ) {
        // do nothing.
    }

    fn process_expr_array_lit(
        &mut self,
        ctx: ExprCtx,
        _expr_id: ExprId,
        expr: &'ast ast::ExprArrayLit,
    ) {
        for &elem in &expr.elems {
            self.process_expr(ctx.clone(), elem);
        }
    }

    fn process_expr_set_lit(
        &mut self,
        ctx: ExprCtx,
        _expr_id: ExprId,
        expr: &'ast ast::ExprSetLit,
    ) {
        for &elem in &expr.elems {
            self.process_expr(ctx.clone(), elem);
        }
    }

    fn process_expr_proc_call(
        &mut self,
        ctx: ExprCtx,
        _expr_id: ExprId,
        expr: &'ast ast::ExprProcCall,
    ) {
        if let Some(recv) = expr.recv {
            self.process_expr(ctx.clone(), recv);
        }

        if let Some(ty_args) = &expr.generics {
            for ty_arg in ty_args {
                self.process_ty_arg(ctx.scope_id, ty_arg);
            }
        }

        for &arg in &expr.args {
            self.process_expr(ctx.clone(), arg);
        }
    }

    fn process_expr_action_call(
        &mut self,
        ctx: ExprCtx,
        expr_id: ExprId,
        expr: &'ast ast::ExprActionCall,
    ) {
        if let Ok(def_id) = self.resolve(
            ctx.scope_id,
            Ns::Action,
            &expr.name.to_string(),
            &expr.name.loc,
        ) {
            let def_id = self.sema.name_res.resolve_import(def_id);
            self.sema.name_res.expr_action_calls.insert(expr_id, def_id);
        }

        if let Some(ty_args) = &expr.generics {
            for ty_arg in ty_args {
                self.process_ty_arg(ctx.scope_id, ty_arg);
            }
        }

        for &arg in &expr.args {
            self.process_expr(ctx.clone(), arg);
        }
    }

    fn process_expr_instantiate(
        &mut self,
        ctx: ExprCtx,
        expr_id: ExprId,
        expr: &'ast ast::ExprInstantiate,
    ) {
        let automaton = self
            .resolve(
                ctx.scope_id,
                Ns::Automaton,
                &expr.name.to_string(),
                &expr.name.loc,
            )
            .map(|def_id| self.sema.name_res.resolve_import(def_id))
            .ok();

        if let Some(ty_args) = &expr.generics {
            for ty_arg in ty_args {
                self.process_ty_arg(ctx.scope_id, ty_arg);
            }
        }

        let args = expr
            .args
            .iter()
            .map(|arg| match arg {
                ast::ConstructorArg::State(_, name) => automaton
                    .and_then(|automaton| {
                        let scope_id = self.sema.name_res.def_member_scopes[automaton];

                        self.resolve(scope_id, Ns::State, &name.to_string(), &name.loc)
                            .map(|def_id| self.sema.name_res.resolve_import(def_id))
                            .ok()
                    })
                    .unwrap_or_default(),

                ast::ConstructorArg::Var(_, name, arg_expr_id) => {
                    let def_id = automaton
                        .and_then(|automaton| {
                            let scope_id = self.sema.name_res.def_member_scopes[automaton];

                            self.resolve(scope_id, Ns::Var, &name.to_string(), &name.loc)
                                .map(|def_id| self.sema.name_res.resolve_import(def_id))
                                .ok()
                                .and_then(|def_id| {
                                    let def = self.def::<DefAutomaton>(automaton);

                                    if def.constructor_params.contains(&def_id) {
                                        Some(def_id)
                                    } else {
                                        self.result = Err(SemaError);
                                        self.diag.emit(
                                            Diag::err()
                                                .at(name.loc.clone())
                                                .with_msg(format!(
                                                    "`{name}` is not a constructor parameter"
                                                ))
                                                .with_label(Label::primary(name.loc.clone()))
                                                .build(),
                                        );

                                        None
                                    }
                                })
                        })
                        .unwrap_or_default();

                    self.process_expr(ctx.clone(), *arg_expr_id);

                    def_id
                }
            })
            .collect();

        let automaton = automaton.unwrap_or_default();

        self.sema
            .name_res
            .expr_instantiations
            .insert(expr_id, InstantiationExprInfo { automaton, args });
    }

    fn process_expr_name(&mut self, _ctx: ExprCtx, _expr_id: ExprId, _expr: &'ast ast::ExprName) {
        // resolved during tyck.
    }

    fn process_expr_prev(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprPrev) {
        self.process_expr(ctx.clone(), expr.base);
    }

    fn process_expr_field(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprField) {
        self.process_expr(ctx.clone(), expr.base);

        // the field is resolved during tyck.
    }

    fn process_expr_deref(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprDeref) {
        self.process_expr(ctx.clone(), expr.base);
    }

    fn process_expr_index(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprIndex) {
        self.process_expr(ctx.clone(), expr.base);
        self.process_expr(ctx.clone(), expr.index);
    }

    fn process_expr_has_concept(
        &mut self,
        ctx: ExprCtx,
        expr_id: ExprId,
        expr: &'ast ast::ExprHasConcept,
    ) {
        self.process_expr(ctx.clone(), expr.scrutinee);

        if let Ok(def_id) = self.resolve(
            ctx.scope_id,
            Ns::Automaton,
            &expr.concept.to_string(),
            &expr.concept.loc,
        ) {
            let def_id = self.sema.name_res.resolve_import(def_id);
            self.sema.name_res.expr_has_concepts.insert(expr_id, def_id);
        }
    }

    fn process_expr_cast(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprCast) {
        self.process_expr(ctx.clone(), expr.expr);
        self.process_ty_expr(ctx.scope_id, expr.ty_expr);
    }

    fn process_expr_ty_compare(
        &mut self,
        ctx: ExprCtx,
        _expr_id: ExprId,
        expr: &'ast ast::ExprTyCompare,
    ) {
        self.process_expr(ctx.clone(), expr.expr);
        self.process_ty_expr(ctx.scope_id, expr.ty_expr);
    }

    fn process_expr_unary(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprUnary) {
        self.process_expr(ctx.clone(), expr.expr);
    }

    fn process_expr_binary(&mut self, ctx: ExprCtx, _expr_id: ExprId, expr: &'ast ast::ExprBinary) {
        self.process_expr(ctx.clone(), expr.lhs);
        self.process_expr(ctx.clone(), expr.rhs);
    }
}
