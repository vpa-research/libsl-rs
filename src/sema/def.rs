//! Entity definitions.

use std::cell::Cell;

use slotmap::new_key_type;

use crate::loc::Loc;
use crate::sema::resolve::ScopeId;
use crate::sema::ty::BuiltinTyCtor;
use crate::{DeclId, PredId};

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

    BuiltinCtor(BuiltinTyCtor),

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

    Param {
        of: DefId,
        idx: usize,
    },

    Pred(DefPred),
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

    pub fn as_pred(&self) -> Option<&DefPred> {
        match self {
            Self::Pred(def) => Some(def),
            _ => None,
        }
    }

    pub fn as_pred_mut(&mut self) -> Option<&mut DefPred> {
        match self {
            Self::Pred(def) => Some(def),
            _ => None,
        }
    }
}

impl From<DefImport> for DefKind {
    fn from(entity: DefImport) -> Self {
        Self::Import(entity)
    }
}

impl From<BuiltinTyCtor> for DefKind {
    fn from(entity: BuiltinTyCtor) -> Self {
        Self::BuiltinCtor(entity)
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

impl From<DefTyVariable> for DefKind {
    fn from(entity: DefTyVariable) -> Self {
        Self::TyVariable(entity)
    }
}

impl From<DefPred> for DefKind {
    fn from(entity: DefPred) -> Self {
        Self::Pred(entity)
    }
}

pub trait DefKindProject {
    fn project(kind: &DefKind) -> Option<&Self>;

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self>;
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

impl DefKindProject for DefImport {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_import()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_import_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefSemanticTy {
    pub decl_id: DeclId,
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
    pub values: Vec<SemanticTyValue>,
}

impl DefSemanticTy {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            param_scope_id: Default::default(),
            generics: Default::default(),
            values: Default::default(),
        }
    }
}

impl DefKindProject for DefSemanticTy {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_semantic_ty()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_semantic_ty_mut()
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
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
}

impl DefTyAlias {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            param_scope_id: Default::default(),
            generics: Default::default(),
        }
    }
}

impl DefKindProject for DefTyAlias {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_ty_alias()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_ty_alias_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefStruct {
    pub decl_id: DeclId,
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
    pub fields: Vec<DefId>,
    pub instance_methods: Vec<DefId>,
    pub static_methods: Vec<DefId>,
}

impl DefStruct {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            param_scope_id: Default::default(),
            generics: Default::default(),
            fields: Default::default(),
            instance_methods: Default::default(),
            static_methods: Default::default(),
        }
    }
}

impl DefKindProject for DefStruct {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_struct()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_struct_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefEnum {
    pub decl_id: DeclId,
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
}

impl DefEnum {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            param_scope_id: Default::default(),
            generics: Default::default(),
        }
    }
}

impl DefKindProject for DefEnum {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_enum()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_enum_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefAnnotation {
    pub decl_id: DeclId,
    pub param_scope_id: ScopeId,
    pub params: Vec<DefId>,
}

impl DefAnnotation {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            param_scope_id: Default::default(),
            params: Default::default(),
        }
    }
}

impl DefKindProject for DefAnnotation {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_annotation()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_annotation_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefAction {
    pub decl_id: DeclId,
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
    pub params: Vec<DefId>,
}

impl DefAction {
    pub fn new(decl_id: DeclId) -> Self {
        Self {
            decl_id,
            param_scope_id: Default::default(),
            generics: Default::default(),
            params: Default::default(),
        }
    }
}

impl DefKindProject for DefAction {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_action()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_action_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefAutomaton {
    pub decl_id: DeclId,
    pub is_concept: bool,
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
    pub constructor_params: Vec<DefId>,
    pub fields: Vec<DefId>,
    pub instance_methods: Vec<DefId>,
    pub static_methods: Vec<DefId>,
    pub states: Vec<DefId>,
    pub init_states: Vec<DefId>,
    pub final_states: Vec<DefId>,
}

impl DefAutomaton {
    pub fn new(decl_id: DeclId, is_concept: bool) -> Self {
        Self {
            decl_id,
            is_concept,
            param_scope_id: Default::default(),
            generics: Default::default(),
            constructor_params: Default::default(),
            fields: Default::default(),
            instance_methods: Default::default(),
            static_methods: Default::default(),
            states: Default::default(),
            init_states: Default::default(),
            final_states: Default::default(),
        }
    }
}

impl DefKindProject for DefAutomaton {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_automaton()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_automaton_mut()
    }
}

#[derive(Debug, Clone)]
pub struct DefVariable {
    pub decl_id: DeclId,
    pub kind: VariableKind,
    pub mutable: bool,
}

impl DefVariable {
    pub fn new(decl_id: DeclId, kind: VariableKind, mutable: bool) -> Self {
        Self {
            decl_id,
            kind,
            mutable,
        }
    }
}

impl DefKindProject for DefVariable {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_variable()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_variable_mut()
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
    pub param_scope_id: ScopeId,
    pub generics: Vec<DefId>,
    pub params: Vec<DefId>,
    pub body_scope_id: ScopeId,
}

impl DefFunction {
    pub fn new(decl_id: DeclId, kind: FunctionKind, is_method: bool) -> Self {
        Self {
            decl_id,
            kind,
            is_method,
            param_scope_id: Default::default(),
            generics: Default::default(),
            params: Default::default(),
            body_scope_id: Default::default(),
        }
    }
}

impl DefKindProject for DefFunction {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_function()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_function_mut()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionKind {
    Fun { of: Option<DefId> },
    Proc { of: Option<DefId>, pure: bool },
    Constructor { of: DefId },
    Destructor { of: DefId },
}

#[derive(Debug, Clone)]
pub struct DefTyVariable {
    pub kind: TyVariableKind,
}

impl DefKindProject for DefTyVariable {
    fn project(kind: &DefKind) -> Option<&Self> {
        kind.as_ty_variable()
    }

    fn project_mut(kind: &mut DefKind) -> Option<&mut Self> {
        kind.as_ty_variable_mut()
    }
}

#[derive(Debug, Clone)]
pub enum TyVariableKind {
    TyParam { of: DefId, idx: usize },
}

#[derive(Debug, Clone)]
pub struct DefPred {
    pub pred_id: PredId,
    pub func_def_id: DefId,
    pub kind: PredKind,
}

impl DefPred {
    pub fn new(pred_id: PredId, func_def_id: DefId, kind: PredKind) -> Self {
        Self {
            pred_id,
            func_def_id,
            kind,
        }
    }
}

#[derive(Debug, Clone)]
pub enum PredKind {
    ContractEnsures,
    ContractRequires,
    Nested,
}
