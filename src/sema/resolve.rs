//! Scope resolution.

use std::collections::HashMap;

use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap, new_key_type};

use crate::diag::{Diag, DiagCtx, Label};
use crate::loc::Loc;
use crate::sema::def::{
    Def, DefAction, DefAnnotation, DefAutomaton, DefEnum, DefFunction, DefId, DefImport, DefKind,
    DefSemanticTy, DefStruct, DefTyAlias, DefVariable, FunctionKind, SemanticTyValue, VariableKind,
};
use crate::sema::{Result, Sema};
use crate::{DeclId, ExprId, FileId, TyExprId, ast};

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
}

#[derive(Debug, Default)]
pub struct FileScope {
    pub file_id: FileId,
    pub import_scope: ScopeId,
}

#[derive(Debug, Default)]
pub enum ScopeKind {
    #[default]
    Dummy,

    Prelude,
    Import(FileId),
    File(FileScope),
    SemanticTyEnum(DefId),
    Struct(DefId),
    Enum(DefId),
    Automaton(DefId),
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
}

impl PreludeDefs {
    pub fn defs_mut(&mut self) -> impl Iterator<Item = (&'static str, Ns, &mut DefId)> {
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
        ])
    }
}

/// Information collected during name resolution.
#[derive(Debug, Default)]
pub struct NameRes {
    /// Entity definitions.
    pub defs: SlotMap<DefId, Def>,

    /// Variable scopes.
    pub scopes: SlotMap<ScopeId, Scope>,

    /// Maps each declaration in the AST to its primary [`DefId`].
    pub decl_defs: SecondaryMap<DeclId, DefId>,

    /// Maps each file to its top-level scope.
    pub file_scopes: SecondaryMap<FileId, ScopeId>,

    /// Maps entities to scopes for their members.
    pub def_member_scopes: SparseSecondaryMap<DefId, ScopeId>,

    /// The prelude scope.
    pub prelude_scope_id: ScopeId,

    /// Definitions in the prelude.
    pub prelude_defs: PreludeDefs,
}

impl NameRes {
    /// If `def_id` is an [import entity][Import], finds the non-import entity it (transitively)
    /// points to. Otherwise returns `def_id`.
    ///
    /// Looks entity definitions up in `defs`. See [`resolve_import`][NameRes::resolve_import] that
    /// supplies [`NameRes::defs`] at the cost of possible borrowing issues.
    pub fn resolve_import_in(defs: &SlotMap<DefId, Def>, mut def_id: DefId) -> DefId {
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
}

impl Sema<'_> {
    /// Initializes scopes and collects definitions.
    ///
    /// Does not resolve name expressions or types.
    pub fn resolve_scopes(&mut self, diag: &mut impl DiagCtx) -> Result {
        Pass::new(self, diag).run()
    }
}

enum DeclCtx {
    Global(FileId),
    Struct(DefId),

    Automaton {
        def_id: DefId,
        is_constructor_var: bool,
    },
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

        for (name, ns, field) in self.sema.name_res.prelude_defs.defs_mut() {
            let def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                id,
                loc: Loc::Synthetic,
                kind: Default::default(),
            });
            prelude_scope.defs.insert((ns, name.into()), def_id);

            *field = def_id;
        }
    }

    fn add_def(
        &mut self,
        scope_id: ScopeId,
        ns: Ns,
        name: String,
        loc: Loc,
        kind: DefKind,
    ) -> Result<DefId> {
        let scope = &mut self.sema.name_res.scopes[scope_id];

        match ns {
            Ns::Function => {
                let def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                    id,
                    loc: loc.clone(),
                    kind,
                });

                scope.functions.entry(name).or_default().push(def_id);

                Ok(def_id)
            }

            _ => {
                let key = (ns, name);

                if let Some((key, &prev_def_id)) = scope.defs.get_key_value(&key) {
                    let prev_def = &self.sema.name_res.defs[prev_def_id];
                    self.result = Err(());

                    self.diag.emit(
                        Diag::err()
                            .at(loc.clone())
                            .with_msg(format!("the name `{}` is defined multiple times", key.1))
                            .with_label(Label::primary(loc).with_msg("defined here"))
                            .with_label(
                                Label::secondary(prev_def.loc.clone())
                                    .with_msg("previously defined here"),
                            )
                            .build(),
                    );

                    return Err(());
                }

                let def_id = self.sema.name_res.defs.insert_with_key(|id| Def {
                    id,
                    loc: loc.clone(),
                    kind,
                });

                scope.defs.insert(key, def_id);

                Ok(def_id)
            }
        }
    }

    fn def_mut(&mut self, def_id: DefId) -> &mut Def {
        &mut self.sema.name_res.defs[def_id]
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

    fn add_member_scope(
        &mut self,
        def_id: DefId,
        outer_scope_id: ScopeId,
        kind: ScopeKind,
    ) -> ScopeId {
        let member_scope_id = self
            .sema
            .name_res
            .scopes
            .insert(Scope::new(Some(outer_scope_id), kind));
        self.sema
            .name_res
            .def_member_scopes
            .insert(def_id, member_scope_id);

        member_scope_id
    }

    fn add_decl_def(
        &mut self,
        decl_id: DeclId,
        scope_id: ScopeId,
        ns: Ns,
        name: String,
        loc: Loc,
        kind: DefKind,
    ) -> Result<DefId> {
        let def_id = self.add_def(scope_id, ns, name, loc, kind)?;
        self.sema.name_res.decl_defs.insert(decl_id, def_id);

        Ok(def_id)
    }

    fn process_decl_symbol(&mut self, ctx: DeclCtx, decl_id: DeclId) {
        let decl = &self.sema.libsl.decls[decl_id];

        let (outer_def_id, outer_scope_id) = match ctx {
            DeclCtx::Global(file_id) => (None, self.sema.name_res.file_scopes[file_id]),

            DeclCtx::Struct(def_id) | DeclCtx::Automaton { def_id, .. } => {
                (Some(def_id), self.sema.name_res.def_member_scopes[def_id])
            }
        };

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),

            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}

            ast::DeclKind::SemanticTy(decl) => {
                let Ok(def_id) = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefSemanticTy::new(decl_id).into(),
                ) else {
                    return;
                };

                match &decl.kind {
                    ast::SemanticTyKind::Simple => {}

                    ast::SemanticTyKind::Enumerated(values) => {
                        let member_scope_id = self.add_member_scope(
                            def_id,
                            outer_scope_id,
                            ScopeKind::SemanticTyEnum(def_id),
                        );

                        for (idx, value) in values.iter().enumerate() {
                            let Ok(value_def_id) = self.add_def(
                                member_scope_id,
                                Ns::Var,
                                value.name.to_string(),
                                value.name.loc.clone(),
                                DefKind::SemanticTyEnumValue {
                                    semantic_ty_def_id: def_id,
                                    variant_idx: idx,
                                },
                            ) else {
                                continue;
                            };

                            let DefKind::SemanticTy(def) = &mut self.def_mut(def_id).kind else {
                                unreachable!()
                            };
                            def.values.push(SemanticTyValue {
                                def_id: value_def_id,
                                name: value.name.to_string(),
                            });
                        }
                    }
                }
            }

            ast::DeclKind::TyAlias(decl) => {
                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefTyAlias::new(decl_id).into(),
                );
            }

            ast::DeclKind::Struct(decl) => {
                let Ok(def_id) = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefStruct::new(decl_id).into(),
                ) else {
                    return;
                };

                self.add_member_scope(def_id, outer_scope_id, ScopeKind::Struct(def_id));

                for &member_decl_id in &decl.decls {
                    self.process_decl_symbol(DeclCtx::Struct(def_id), member_decl_id);
                }
            }

            ast::DeclKind::Enum(decl) => {
                let Ok(def_id) = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefEnum::new(decl_id).into(),
                ) else {
                    return;
                };

                let member_scope_id =
                    self.add_member_scope(def_id, outer_scope_id, ScopeKind::Enum(def_id));

                for (idx, variant) in decl.variants.iter().enumerate() {
                    let _ = self.add_def(
                        member_scope_id,
                        Ns::Var,
                        variant.name.to_string(),
                        variant.name.loc.clone(),
                        DefKind::EnumVariant {
                            enum_def_id: def_id,
                            variant_idx: idx,
                        },
                    );
                }
            }

            ast::DeclKind::Annotation(decl) => {
                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Annotation,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefAnnotation::new(decl_id).into(),
                );
            }

            ast::DeclKind::Action(decl) => {
                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Action,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefAction::new(decl_id).into(),
                );
            }

            ast::DeclKind::Automaton(decl) => {
                let Ok(def_id) = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Automaton,
                    decl.name.ty_name.to_string(),
                    decl.name.ty_name.loc.clone(),
                    DefAutomaton::new(decl_id).into(),
                ) else {
                    return;
                };

                self.add_member_scope(def_id, outer_scope_id, ScopeKind::Automaton(def_id));

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
                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Function,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefFunction::new(
                        decl_id,
                        FunctionKind::Fun {
                            of: match ctx {
                                DeclCtx::Global(_) => None,
                                DeclCtx::Struct(def_id) | DeclCtx::Automaton { def_id, .. } => {
                                    Some(def_id)
                                }
                            },
                        },
                        decl.is_method,
                    )
                    .into(),
                );
            }

            ast::DeclKind::Variable(decl) => {
                let kind = match ctx {
                    DeclCtx::Global(_) => VariableKind::Global,
                    DeclCtx::Struct(def_id) => VariableKind::Field { of: def_id },

                    DeclCtx::Automaton {
                        def_id,
                        is_constructor_var: true,
                    } => VariableKind::ConstructorVar { of: def_id },

                    DeclCtx::Automaton {
                        def_id,
                        is_constructor_var: false,
                    } => VariableKind::Field { of: def_id },
                };

                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Var,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefVariable::new(decl_id, kind).into(),
                );
            }

            ast::DeclKind::State(decl) => {
                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::State,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefKind::State(decl_id),
                );
            }

            ast::DeclKind::Shift(_) => {
                // state transition is not a def.
            }

            ast::DeclKind::Constructor(decl) => {
                let _ = self.add_decl_def(
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
                        decl_id,
                        FunctionKind::Constructor {
                            of: outer_def_id.unwrap(),
                        },
                        decl.is_method,
                    )
                    .into(),
                );
            }

            ast::DeclKind::Destructor(decl) => {
                let _ = self.add_decl_def(
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
                        decl_id,
                        FunctionKind::Destructor {
                            of: outer_def_id.unwrap(),
                        },
                        decl.is_method,
                    )
                    .into(),
                );
            }

            ast::DeclKind::Proc(decl) => {
                let _ = self.add_decl_def(
                    decl_id,
                    outer_scope_id,
                    Ns::Function,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefFunction::new(
                        decl_id,
                        FunctionKind::Proc {
                            of: match ctx {
                                DeclCtx::Global(_) => None,
                                DeclCtx::Struct(def_id) | DeclCtx::Automaton { def_id, .. } => {
                                    Some(def_id)
                                }
                            },
                        },
                        decl.is_method,
                    )
                    .into(),
                );
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

                for (key @ &(_, ref name), &def_id) in &imported_scope.defs {
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

                            self.result = Err(());
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
                            kind: DefKind::Import(DefImport::new_resolved(
                                import_decl_id,
                                def_id,
                                resolved_def_id,
                            )),
                        });

                        import_scope.defs.insert(key.clone(), new_def_id);
                    }
                }
            }
        }
    }
}

// Phase 3: walk function bodies and add local scopes.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn resolve_defs(&mut self) {
        for (file_id, file) in &self.sema.libsl.files {
            let file_scope_id = self.sema.name_res.file_scopes[file_id];

            for &decl_id in &file.decls {
                let decl = &self.sema.libsl.decls[decl_id];

                match &decl.kind {
                    ast::DeclKind::Dummy => unreachable!(),
                    ast::DeclKind::Import(_) => {}
                    ast::DeclKind::Include(_) => {}

                    ast::DeclKind::SemanticTy(decl) => self.process_decl_semantic_ty(decl_id, decl),
                    ast::DeclKind::TyAlias(decl) => self.process_decl_ty_alias(decl_id, decl),
                    ast::DeclKind::Struct(decl) => self.process_decl_struct(decl_id, decl),
                    ast::DeclKind::Enum(decl) => self.process_decl_enum(decl_id, decl),
                    ast::DeclKind::Annotation(decl) => self.process_decl_annotation(decl_id, decl),
                    ast::DeclKind::Action(decl) => self.process_decl_action(decl_id, decl),
                    ast::DeclKind::Automaton(decl) => self.process_decl_automaton(decl_id, decl),
                    ast::DeclKind::Function(decl) => self.process_decl_function(decl_id, decl),
                    ast::DeclKind::Variable(decl) => self.process_decl_variable(decl_id, decl),
                    ast::DeclKind::State(_) => unreachable!(),
                    ast::DeclKind::Shift(_) => unreachable!(),
                    ast::DeclKind::Constructor(_) => unreachable!(),
                    ast::DeclKind::Destructor(_) => unreachable!(),
                    ast::DeclKind::Proc(decl) => self.process_decl_proc(decl_id, decl),
                }
            }
        }
    }

    fn process_generics(&mut self, generics: &[ast::Generic]) -> Result<Vec<DefId>> {
        todo!()
    }
}

// Phase 3, declarations.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_decl_semantic_ty(&mut self, decl_id: DeclId, decl: &'ast ast::DeclSemanticTy) {
        let def_id = self.sema.name_res.decl_defs[decl_id];

        // TODO: annotations.

        if let Ok(generics) = self.process_generics(&decl.ty_name.generics) {
            self.def_mut(def_id)
                .kind
                .as_semantic_ty_mut()
                .unwrap()
                .generics = generics;
        }

        self.process_ty_expr(decl.real_ty);

        match &decl.kind {
            ast::SemanticTyKind::Simple => {}
            ast::SemanticTyKind::Enumerated(values) => todo!(),
        }
    }

    fn process_decl_ty_alias(&mut self, decl_id: DeclId, decl: &'ast ast::DeclTyAlias) {
        todo!()
    }

    fn process_decl_struct(&mut self, decl_id: DeclId, decl: &'ast ast::DeclStruct) {
        todo!()
    }

    fn process_decl_enum(&mut self, decl_id: DeclId, decl: &'ast ast::DeclEnum) {
        todo!()
    }

    fn process_decl_annotation(&mut self, decl_id: DeclId, decl: &'ast ast::DeclAnnotation) {
        todo!()
    }

    fn process_decl_action(&mut self, decl_id: DeclId, decl: &'ast ast::DeclAction) {
        todo!()
    }

    fn process_decl_automaton(&mut self, decl_id: DeclId, decl: &'ast ast::DeclAutomaton) {
        todo!()
    }

    fn process_decl_function(&mut self, decl_id: DeclId, decl: &'ast ast::DeclFunction) {
        todo!()
    }

    fn process_decl_variable(&mut self, decl_id: DeclId, decl: &'ast ast::DeclVariable) {
        todo!()
    }

    fn process_decl_proc(&mut self, decl_id: DeclId, decl: &'ast ast::DeclProc) {
        todo!()
    }
}

// Phase 3, type expressions.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_ty_expr(&mut self, ty_expr_id: TyExprId) {
        todo!()
    }
}

// Phase 3, expressions.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn process_expr(&mut self, expr_id: ExprId) {
        todo!()
    }
}
