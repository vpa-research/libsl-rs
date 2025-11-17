//! Scope resolution.

use std::collections::HashMap;

use slotmap::{SecondaryMap, SlotMap, SparseSecondaryMap, new_key_type};

use crate::diag::DiagCtx;
use crate::loc::Loc;
use crate::sema::def::{Def, DefId, DefKind, Variable, VariableKind};
use crate::sema::{Result, Sema};
use crate::{DeclId, FileId, ast};

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

    /// Maps each file to its top-level scope (note that .
    pub file_scopes: SecondaryMap<FileId, ScopeId>,

    /// Maps entities to scopes for their members.
    pub def_member_scopes: SparseSecondaryMap<DefId, ScopeId>,

    /// The prelude scope.
    pub prelude_scope_id: ScopeId,

    /// Definitions in the prelude.
    pub prelude_defs: PreludeDefs,
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
}

impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn new(sema: &'s mut Sema<'ast>, diag: &'s mut D) -> Self {
        Self { sema, diag }
    }

    fn run(mut self) -> Result {
        self.init_root_scopes();
        self.add_prelude_defs();

        let mut result = Ok(());
        result = result.and(self.collect_symbols());
        result = result.and(self.add_imports());
        result = result.and(self.resolve_defs());

        result
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
        todo!()
    }
}

// Phase 1: collect globally available symbols.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn collect_symbols(&mut self) -> Result {
        let mut result = Ok(());

        for (file_id, file) in &self.sema.libsl.files {
            for &decl_id in &file.decls {
                result = result.and(self.process_decl_symbol(DeclCtx::Global(file_id), decl_id));
            }
        }

        result
    }

    fn process_decl_symbol(&mut self, ctx: DeclCtx, decl_id: DeclId) -> Result {
        let decl = &self.sema.libsl.decls[decl_id];

        let outer_scope_id = match ctx {
            DeclCtx::Global(file_id) => self.sema.name_res.file_scopes[file_id],
            DeclCtx::Struct(def_id) => self.sema.name_res.def_member_scopes[def_id],
            DeclCtx::Automaton { def_id, .. } => self.sema.name_res.def_member_scopes[def_id],
        };

        let mut result = Ok(());

        match &decl.kind {
            ast::DeclKind::Dummy => unreachable!(),

            ast::DeclKind::Import(_) => {}
            ast::DeclKind::Include(_) => {}

            ast::DeclKind::SemanticTy(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefKind::SemanticTy(decl_id),
                )?;

                self.sema.name_res.decl_defs.insert(decl_id, def_id);

                match &decl.kind {
                    ast::SemanticTyKind::Simple => {}
                    ast::SemanticTyKind::Enumerated(values) => {
                        let decl_scope_id = self.sema.name_res.scopes.insert(Scope::new(
                            Some(outer_scope_id),
                            ScopeKind::SemanticTyEnum(def_id),
                        ));
                        self.sema
                            .name_res
                            .def_member_scopes
                            .insert(def_id, decl_scope_id);

                        for (idx, value) in values.iter().enumerate() {
                            result = result.and(
                                self.add_def(
                                    decl_scope_id,
                                    Ns::Var,
                                    value.name.to_string(),
                                    value.name.loc.clone(),
                                    DefKind::SemanticTyEnumValue {
                                        semantic_ty_def_id: def_id,
                                        variant_idx: idx,
                                    },
                                )
                                .map(drop),
                            );
                        }
                    }
                }
            }

            ast::DeclKind::TyAlias(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefKind::TyAlias(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);
            }

            ast::DeclKind::Struct(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefKind::Struct(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);

                let decl_scope_id = self
                    .sema
                    .name_res
                    .scopes
                    .insert(Scope::new(Some(outer_scope_id), ScopeKind::Struct(def_id)));
                self.sema
                    .name_res
                    .def_member_scopes
                    .insert(def_id, decl_scope_id);

                for &member_decl_id in &decl.decls {
                    result = result
                        .and(self.process_decl_symbol(DeclCtx::Struct(def_id), member_decl_id));
                }
            }

            ast::DeclKind::Enum(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Ty,
                    decl.ty_name.ty_name.to_string(),
                    decl.ty_name.ty_name.loc.clone(),
                    DefKind::Enum(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);

                let decl_scope_id = self
                    .sema
                    .name_res
                    .scopes
                    .insert(Scope::new(Some(outer_scope_id), ScopeKind::Enum(def_id)));
                self.sema
                    .name_res
                    .def_member_scopes
                    .insert(def_id, decl_scope_id);

                for (idx, variant) in decl.variants.iter().enumerate() {
                    result = result.and(
                        self.add_def(
                            decl_scope_id,
                            Ns::Var,
                            variant.name.to_string(),
                            variant.name.loc.clone(),
                            DefKind::EnumVariant {
                                enum_def_id: def_id,
                                variant_idx: idx,
                            },
                        )
                        .map(drop),
                    );
                }
            }

            ast::DeclKind::Annotation(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Annotation,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefKind::Annotation(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);
            }

            ast::DeclKind::Action(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Action,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefKind::Action(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);
            }

            ast::DeclKind::Automaton(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Automaton,
                    decl.name.ty_name.to_string(),
                    decl.name.ty_name.loc.clone(),
                    DefKind::Automaton(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);

                let decl_scope_id = self.sema.name_res.scopes.insert(Scope::new(
                    Some(outer_scope_id),
                    ScopeKind::Automaton(def_id),
                ));
                self.sema
                    .name_res
                    .def_member_scopes
                    .insert(def_id, decl_scope_id);

                for &var_decl_id in &decl.constructor_variables {
                    result = result.and(self.process_decl_symbol(
                        DeclCtx::Automaton {
                            def_id,
                            is_constructor_var: true,
                        },
                        var_decl_id,
                    ))
                }

                for &member_decl_id in &decl.decls {
                    result = result.and(self.process_decl_symbol(
                        DeclCtx::Automaton {
                            def_id,
                            is_constructor_var: false,
                        },
                        member_decl_id,
                    ));
                }
            }

            ast::DeclKind::Function(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Function,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefKind::Function(decl_id),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);
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

                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::Var,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefKind::Variable(Variable { decl_id, kind }),
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);
            }

            ast::DeclKind::State(decl) => {
                let def_id = self.add_def(
                    outer_scope_id,
                    Ns::State,
                    decl.name.to_string(),
                    decl.name.loc.clone(),
                    DefKind::State(decl_id)
                )?;
                self.sema.name_res.decl_defs.insert(decl_id, def_id);
            }

            ast::DeclKind::Shift(decl) => todo!(),
            ast::DeclKind::Constructor(decl) => todo!(),
            ast::DeclKind::Destructor(decl) => todo!(),
            ast::DeclKind::Proc(decl) => todo!(),
        }

        result
    }
}

// Phase 2: populate import scopes with imported entities while checking for conflicts.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn add_imports(&mut self) -> Result {
        todo!()
    }
}

// Phase 3: walk function bodies and add local scopes.
impl<'ast, 's, D: DiagCtx> Pass<'ast, 's, D> {
    fn resolve_defs(&mut self) -> Result {
        todo!()
    }
}
