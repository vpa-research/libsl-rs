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

    Import(DefImport),

    Ty(TyId),

    SemanticTy(DefSemanticTy),

    SemanticTyEnumValue {
        semantic_ty_def_id: DefId,
        variant_idx: usize,
    },

    TyAlias(DefTyAlias),

    Struct(DefStruct),

    Enum(DefEnum),

    EnumVariant {
        enum_def_id: DefId,
        variant_idx: usize,
    },

    Annotation(DefAnnotation),

    Action(DefAction),

    Automaton(DefAutomaton),

    Function(DefFunction),

    Variable(DefVariable),

    State(DeclId),

    TyVariable(DefTyVariable),
}

impl DefKind {
    pub fn as_import(&self) -> Option<&DefImport> {
        match self {
            Self::Import(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_import_mut(&mut self) -> Option<&mut DefImport> {
        match self {
            Self::Import(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_semantic_ty(&self) -> Option<&DefSemanticTy> {
        match self {
            Self::SemanticTy(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_semantic_ty_mut(&mut self) -> Option<&mut DefSemanticTy> {
        match self {
            Self::SemanticTy(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_ty_alias(&self) -> Option<&DefTyAlias> {
        match self {
            Self::TyAlias(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_ty_alias_mut(&mut self) -> Option<&mut DefTyAlias> {
        match self {
            Self::TyAlias(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_struct(&self) -> Option<&DefStruct> {
        match self {
            Self::Struct(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_struct_mut(&mut self) -> Option<&mut DefStruct> {
        match self {
            Self::Struct(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_enum(&self) -> Option<&DefEnum> {
        match self {
            Self::Enum(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_enum_mut(&mut self) -> Option<&mut DefEnum> {
        match self {
            Self::Enum(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_annotation(&self) -> Option<&DefAnnotation> {
        match self {
            Self::Annotation(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_annotation_mut(&mut self) -> Option<&mut DefAnnotation> {
        match self {
            Self::Annotation(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_action(&self) -> Option<&DefAction> {
        match self {
            Self::Action(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_action_mut(&mut self) -> Option<&mut DefAction> {
        match self {
            Self::Action(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_automaton(&self) -> Option<&DefAutomaton> {
        match self {
            Self::Automaton(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_automaton_mut(&mut self) -> Option<&mut DefAutomaton> {
        match self {
            Self::Automaton(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_function(&self) -> Option<&DefFunction> {
        match self {
            Self::Function(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_function_mut(&mut self) -> Option<&mut DefFunction> {
        match self {
            Self::Function(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_variable(&self) -> Option<&DefVariable> {
        match self {
            Self::Variable(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_variable_mut(&mut self) -> Option<&mut DefVariable> {
        match self {
            Self::Variable(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_ty_variable(&self) -> Option<&DefTyVariable> {
        match self {
            Self::TyVariable(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_ty_variable_mut(&mut self) -> Option<&mut DefTyVariable> {
        match self {
            Self::TyVariable(def) => Some(def),
            _ => None,
        }
    }
}

impl From<DefImport> for DefKind {
    fn from(entity: DefImport) -> Self {
        Self::Import(entity)
    }
}

impl From<TyId> for DefKind {
    fn from(ty_id: TyId) -> Self {
        Self::Ty(ty_id)
    }
}

impl From<DefSemanticTy> for DefKind {
    fn from(entity: DefSemanticTy) -> Self {
        Self::SemanticTy(entity)
    }
}

impl From<DefTyAlias> for DefKind {
    fn from(entity: DefTyAlias) -> Self {
        Self::TyAlias(entity)
    }
}

impl From<DefStruct> for DefKind {
    fn from(entity: DefStruct) -> Self {
        Self::Struct(entity)
    }
}

impl From<DefEnum> for DefKind {
    fn from(entity: DefEnum) -> Self {
        Self::Enum(entity)
    }
}

impl From<DefAnnotation> for DefKind {
    fn from(entity: DefAnnotation) -> Self {
        Self::Annotation(entity)
    }
}

impl From<DefAction> for DefKind {
    fn from(entity: DefAction) -> Self {
        Self::Action(entity)
    }
}

impl From<DefAutomaton> for DefKind {
    fn from(entity: DefAutomaton) -> Self {
        Self::Automaton(entity)
    }
}

impl From<DefFunction> for DefKind {
    fn from(entity: DefFunction) -> Self {
        Self::Function(entity)
    }
}

impl From<DefVariable> for DefKind {
    fn from(entity: DefVariable) -> Self {
        Self::Variable(entity)
    }
}

#[derive(Debug, Clone)]
pub struct DefImport {
    pub import_decl_id: DeclId,
    pub imports: DefId,
    pub(super) resolution_cache: Cell<DefId>,
}

impl DefImport {
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
pub struct DefSemanticTy {
    pub decl_id: DeclId,
    pub values: Vec<SemanticTyValue>,
    pub generics: Vec<DefId>,
}

impl DefSemanticTy {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            values: Default::default(),
            generics: Default::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SemanticTyValue {
    pub def_id: DefId,
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct DefTyAlias {
    pub decl_id: DeclId,
}

impl DefTyAlias {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct DefStruct {
    pub decl_id: DeclId,
}

impl DefStruct {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct DefEnum {
    pub decl_id: DeclId,
}

impl DefEnum {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct DefAnnotation {
    pub decl_id: DeclId,
}

impl DefAnnotation {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct DefAction {
    pub decl_id: DeclId,
}

impl DefAction {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct DefAutomaton {
    pub decl_id: DeclId,
}

impl DefAutomaton {
    pub fn new(decl_id: DeclId) -> Self {
        Self { decl_id }
    }
}

#[derive(Debug, Clone)]
pub struct DefVariable {
    pub decl_id: DeclId,
    pub kind: VariableKind,
}

impl DefVariable {
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
pub struct DefFunction {
    pub decl_id: DeclId,
    pub kind: FunctionKind,
    pub is_method: bool,
}

impl DefFunction {
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

#[derive(Debug, Clone)]
pub struct DefTyVariable {
    pub kind: TyVariableKind,
}

#[derive(Debug, Clone)]
pub enum TyVariableKind {
    TyParam { of: DefId, idx: usize },
}
