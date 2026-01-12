//! Entity definitions.

use std::cell::Cell;

use slotmap::new_key_type;

use crate::DeclId;
use crate::loc::Loc;
use crate::sema::ty::TyId;

new_key_type! {
    pub struct DefId;
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

    SemanticTy(SemanticTy),

    SemanticTyEnumValue {
        semantic_ty_def_id: DefId,
        variant_idx: usize,
    },

    TyAlias(TyAlias),

    Struct(Struct),

    Enum(Enum),

    EnumVariant {
        enum_def_id: DefId,
        variant_idx: usize,
    },

    Annotation(Annotation),

    Action(Action),

    Automaton(Automaton),

    Function(Function),

    Variable(Variable),

    State(DeclId),
}

impl From<Import> for DefKind {
    fn from(entity: Import) -> Self {
        Self::Import(entity)
    }
}

impl From<TyId> for DefKind {
    fn from(ty_id: TyId) -> Self {
        Self::Ty(ty_id)
    }
}

impl From<SemanticTy> for DefKind {
    fn from(entity: SemanticTy) -> Self {
        Self::SemanticTy(entity)
    }
}

impl From<TyAlias> for DefKind {
    fn from(entity: TyAlias) -> Self {
        Self::TyAlias(entity)
    }
}

impl From<Struct> for DefKind {
    fn from(entity: Struct) -> Self {
        Self::Struct(entity)
    }
}

impl From<Enum> for DefKind {
    fn from(entity: Enum) -> Self {
        Self::Enum(entity)
    }
}

impl From<Annotation> for DefKind {
    fn from(entity: Annotation) -> Self {
        Self::Annotation(entity)
    }
}

impl From<Action> for DefKind {
    fn from(entity: Action) -> Self {
        Self::Action(entity)
    }
}

impl From<Automaton> for DefKind {
    fn from(entity: Automaton) -> Self {
        Self::Automaton(entity)
    }
}

impl From<Function> for DefKind {
    fn from(entity: Function) -> Self {
        Self::Function(entity)
    }
}

impl From<Variable> for DefKind {
    fn from(entity: Variable) -> Self {
        Self::Variable(entity)
    }
}

#[derive(Debug, Clone)]
pub struct Import {
    pub import_decl_id: DeclId,
    pub imports: DefId,
    pub(super) resolution_cache: Cell<DefId>,
}

impl Import {
    pub fn new(import_decl_id: DeclId, imports: DefId) -> Self {
        Self {
            import_decl_id,
            imports,
            resolution_cache: Cell::new(imports),
        }
    }

    pub fn new_resolved(import_decl_id: DeclId, imports: DefId, resolved: DefId) -> Self {
        Self {
            import_decl_id,
            imports,
            resolution_cache: Cell::new(resolved),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SemanticTy {
    pub decl_id: DeclId,
}

impl SemanticTy {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TyAlias {
    pub decl_id: DeclId,
}

impl TyAlias {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Struct {
    pub decl_id: DeclId,
}

impl Struct {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct Enum {
    pub decl_id: DeclId,
}

impl Enum {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct Annotation {
    pub decl_id: DeclId,
}

impl Annotation {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct Action {
    pub decl_id: DeclId,
}

impl Action {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct Automaton {
    pub decl_id: DeclId,
}

impl Automaton {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub decl_id: DeclId,
    pub kind: VariableKind,
}

impl Variable {
    pub fn new(decl_id: DeclId, kind: VariableKind) -> Self {
        Self { decl_id, kind }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Global,
    Local,
    Field { of: DefId },
    ConstructorVar { of: DefId },
}

#[derive(Debug, Clone)]
pub struct Function {
    pub decl_id: DeclId,
    pub kind: FunctionKind,
    pub is_method: bool,
}

impl Function {
    pub fn new(decl_id: DeclId, kind: FunctionKind, is_method: bool) -> Self {
        Self {
            decl_id,
            kind,
            is_method,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionKind {
    Fun { of: Option<DefId> },
    Proc { of: Option<DefId> },
    Constructor { of: DefId },
    Destructor { of: DefId },
}
