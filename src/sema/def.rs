//! Entity definitions.

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

    SemanticTy(DeclId),

    SemanticTyEnumValue {
        semantic_ty_def_id: DefId,
        variant_idx: usize,
    },

    TyAlias(DeclId),

    Struct(DeclId),

    Enum(DeclId),

    EnumVariant {
        enum_def_id: DefId,
        variant_idx: usize,
    },

    Annotation(DeclId),

    Action(DeclId),

    Automaton(DeclId),

    Function(DeclId),

    Variable(Variable),

    State(DeclId),
}

#[derive(Debug, Clone)]
pub struct Import {
    pub import_decl_id: DeclId,
    pub imported: DefId,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub decl_id: DeclId,
    pub kind: VariableKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Global,
    Local,
    Field { of: DefId },
    ConstructorVar { of: DefId },
}
