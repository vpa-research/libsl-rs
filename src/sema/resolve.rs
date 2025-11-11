//! Scope resolution.

use std::collections::HashMap;

use slotmap::{SecondaryMap, SlotMap, new_key_type};

use crate::diag::DiagCtx;
use crate::loc::Loc;
use crate::sema::ty::TyId;
use crate::sema::{Result, Sema};
use crate::{DeclId, FileId};

new_key_type! {
    pub struct DefId;
    pub struct ScopeId;
}

#[derive(Debug)]
pub struct Def {
    pub id: DefId,
    pub loc: Loc,
    pub kind: DefKind,
}

#[derive(Debug, Default)]
pub enum DefKind {
    #[default]
    Dummy,

    Import(Import),
    Ty(TyId),
}

#[derive(Debug, Clone)]
pub struct Import {
    pub import_decl_id: DeclId,
    pub imported: DefId,
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

    fn collect_symbols(&mut self) -> Result {
        todo!()
    }

    fn resolve_defs(&mut self) -> Result {
        todo!()
    }
}
