//! AST node definitions.
//!
//! The top-level struct is [`File`]; all other nodes are descendants of it.

use derive_more::From;

use crate::loc::Loc;
use crate::{DeclId, ExprId, QualifiedAccessId, StmtId, TyExprId, WithLibSl};

/// A single LibSL file.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct File {
    /// The file's location in the source text.
    pub loc: Loc,

    /// The LibSL header declaration.
    pub header: Option<Header>,

    /// The top-level declarations in the file.
    pub decls: Vec<DeclId>,
}

impl WithLibSl for File {}

/// A LibSL header declaration.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct Header {
    /// The header's location in the source text.
    pub loc: Loc,

    /// The specified LibSL version.
    ///
    /// LibSL export requires this to be a valid LibSL string.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub libsl_version: String,

    /// The name of the library described by this specification.
    ///
    /// LibSL export requires this to be a valid LibSL identifier.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub library_name: String,

    /// The version of the library described by this specification.
    ///
    /// LibSL export requires this to be a valid LibSL string.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub version: Option<String>,

    /// The language the library described by this specification is implemented in.
    ///
    /// LibSL export requires this to be a valid LibSL string.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub language: Option<String>,

    /// The URL to the library.
    ///
    /// LibSL export requires this to be a valid LibSL string. Otherwise, no requirements on URL
    /// validity are imposed.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub url: Option<String>,
}

impl WithLibSl for Header {}

/// An entity declaration.
#[derive(Debug, Default, Clone)]
pub struct Decl {
    /// A unique identifier for this declaration, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional information with the declaration as well as refer to it
    /// without violating borrowing rules.
    pub id: DeclId,

    /// The declaration's location in the source text.
    pub loc: Loc,

    /// What kind of declaration this is.
    ///
    /// The variants hold data specific to each declaration kind.
    pub kind: DeclKind,
}

impl WithLibSl for Decl {}

/// An enumeration of all possible declaration kinds.
#[derive(From, Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum DeclKind {
    /// A dummy declaration, the default value of `DeclKind`.
    ///
    /// Allows using `mem::take` to take ownership of the value.
    #[default]
    Dummy,

    /// An import declaration.
    Import(DeclImport),

    /// An include declaration.
    Include(DeclInclude),

    /// A semantic type declared in a `types` section.
    SemanticTy(DeclSemanticTy),

    /// A type alias declaration.
    TyAlias(DeclTyAlias),

    /// A structure type declaration.
    Struct(DeclStruct),

    /// An enum type declaration.
    Enum(DeclEnum),

    /// An annotation declaration.
    Annotation(DeclAnnotation),

    /// An action declaration.
    Action(DeclAction),

    /// An automaton declaration.
    Automaton(DeclAutomaton),

    /// A function declaration.
    Function(DeclFunction),

    /// A variable declaration.
    Variable(DeclVariable),

    /// An automaton state declaration.
    State(DeclState),

    /// An automaton state transfer function declaration.
    Shift(DeclShift),

    /// An automaton constructor declaration.
    Constructor(DeclConstructor),

    /// An automaton destructor declaration.
    Destructor(DeclDestructor),

    /// An automaton procedure declaration.
    Proc(DeclProc),
}

impl WithLibSl for DeclKind {}

/// An import declaration.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct DeclImport {
    /// An interpreted import path.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub path: String,
}

impl WithLibSl for DeclImport {}

/// An include declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclInclude {
    /// An uninterpreted include path.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub path: String,
}

impl WithLibSl for DeclInclude {}

/// A semantic type declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclSemanticTy {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// The name of the semantic type.
    pub ty_name: QualifiedTyName,

    /// The underlying type representation.
    pub real_ty: TyExprId,

    /// The specific kind of semantic type.
    pub kind: SemanticTyKind,
}

impl WithLibSl for DeclSemanticTy {}

/// An enumeration of possible semantic type kinds.
#[derive(Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum SemanticTyKind {
    /// A simple semantic type.
    #[default]
    Simple,

    /// A semantic type with enumerated named values.
    Enumerated(Vec<SemanticTyEnumValue>),
}

impl WithLibSl for SemanticTyKind {}

/// A named value of an enumerated semantic type.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct SemanticTyEnumValue {
    /// The name of the semantic type's value.
    pub name: Name,

    /// The underlying value represented by this entry.
    pub expr: ExprId,
}

impl WithLibSl for SemanticTyEnumValue {}

/// A type alias declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclTyAlias {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// The alias's name.
    pub ty_name: QualifiedTyName,

    /// The type represented by this alias.
    pub ty_expr: TyExprId,
}

impl WithLibSl for DeclTyAlias {}

/// A structure type declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclStruct {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// The declared type's name.
    pub ty_name: QualifiedTyName,

    /// The type expression specified after the `is` keyword in the type declaration.
    pub is_ty: Option<TyExprId>,

    /// The type expressions specified after the `for` keyword in the type declaration.
    pub for_tys: Vec<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,

    /// Entities (variables and functions) defined as members of this type.
    pub decls: Vec<DeclId>,
}

impl WithLibSl for DeclStruct {}

/// An enum type declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclEnum {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// The declared type's name.
    pub ty_name: QualifiedTyName,

    /// Possibles values of the type.
    pub variants: Vec<EnumVariant>,
}

impl WithLibSl for DeclEnum {}

/// An enum type variant.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct EnumVariant {
    /// The name of the variant.
    pub name: Name,

    /// The value of the variant.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub value: IntLit,
}

impl WithLibSl for EnumVariant {}

/// An annotation declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclAnnotation {
    /// The name of the annotation.
    pub name: Name,

    /// A list of parameters declared for this annotation.
    pub params: Vec<AnnotationParam>,
}

impl WithLibSl for DeclAnnotation {}

/// An annotation parameter.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct AnnotationParam {
    /// The name of the parameter.
    pub name: Name,

    /// The type of the parameter.
    pub ty_expr: TyExprId,

    /// The default value for the parameter.
    pub default: Option<ExprId>,
}

impl WithLibSl for AnnotationParam {}

/// An action declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclAction {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// A list of type parameter (generic) declarations.
    pub generics: Vec<Generic>,

    /// The name of the action.
    pub name: Name,

    /// A list of parameters declared for this action.
    pub params: Vec<ActionParam>,

    /// The action's return type.
    pub ret_ty_expr: Option<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,
}

impl WithLibSl for DeclAction {}

/// An action parameter.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ActionParam {
    /// A list of annotations for this parameter declaration.
    pub annotations: Vec<Annotation>,

    /// The name of the parameter.
    pub name: Name,

    /// The type of the parameter.
    pub ty_expr: TyExprId,
}

impl WithLibSl for ActionParam {}

/// An automaton declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclAutomaton {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// Whether this is an automaton concept declaration.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub is_concept: bool,

    /// The name of the automaton, possibly qualified with type parameter (generic) declarations.
    pub name: QualifiedTyName,

    /// Automaton constructor variable declarations.
    pub constructor_variables: Vec<DeclId>,

    /// The type modelled by this automaton.
    pub ty_expr: TyExprId,

    /// A list of concepts implemented by this automaton.
    pub implemented_concepts: Vec<Name>,

    /// Entities defines as members of this automaton.
    pub decls: Vec<DeclId>,
}

impl WithLibSl for DeclAutomaton {}

/// A function declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclFunction {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// Whether the function has a `static` modifier.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub is_static: bool,

    /// If present, signifies an extension function for an automaton with the specified name.
    pub extension_for: Option<FullName>,

    /// Whether the function is a method (uses `*.` in its name).
    #[cfg_attr(feature = "serde", no_wrap)]
    pub is_method: bool,

    /// The function's name.
    pub name: Name,

    /// A list of type parameter (generic) declarations.
    pub generics: Vec<Generic>,

    /// A list of the function's parameters.
    pub params: Vec<FunctionParam>,

    /// The function's return type.
    pub ret_ty_expr: Option<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,

    /// The function's body.
    pub body: Option<FunctionBody>,
}

impl WithLibSl for DeclFunction {}

/// A variable declaration.
///
/// Depending on the context, it could be any of the following:
///
/// - a global variable
/// - an automaton constructor variable
/// - a type's member variable
/// - or a local variable
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclVariable {
    /// A list of annotations for this declarations.
    pub annotations: Vec<Annotation>,

    /// The kind of variable: `var` or `val`.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub kind: VariableKind,

    /// The name of the variable.
    pub name: Name,

    /// The type of the variable.
    pub ty_expr: TyExprId,

    /// An optional variable initializer expression.
    pub init: Option<ExprId>,
}

impl WithLibSl for DeclVariable {}

/// The mutability of a variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum VariableKind {
    /// A mutable variable declaration (`var`).
    Var,

    /// An immutable variable declaration (`val`).
    Val,
}

impl WithLibSl for VariableKind {}

impl VariableKind {
    /// Returns `true` if this is a mutable variable declaration (`var`).
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var)
    }

    /// Returns `true` if this is an immutable variable declaration (`val`).
    pub fn is_val(&self) -> bool {
        matches!(self, Self::Val)
    }
}

/// An automaton state declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclState {
    /// The kind of state declaration.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub kind: StateKind,

    /// The name of the state.
    pub name: Name,
}

impl WithLibSl for DeclState {}

/// An enumeration of possible state declaration kinds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum StateKind {
    /// An initial state declaration.
    Initial,

    /// A regular state declaration (neither initial nor final).
    Regular,

    /// A final state declaration.
    Final,
}

impl WithLibSl for StateKind {}

/// An automaton state transfer function declaration.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct DeclShift {
    /// A list of previous states covered by this declaration.
    pub from: Vec<Name>,

    /// A target state for this declaration.
    pub to: Name,

    /// A list of functions that trigger this transition.
    pub by: Vec<QualifiedFunctionName>,
}

impl WithLibSl for DeclShift {}

/// A function name or its specific overload.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct QualifiedFunctionName {
    /// The name of the function.
    pub name: Name,

    /// Optional parameter type qualification to disambiguate overloads.
    pub params: Option<Vec<TyExprId>>,
}

impl WithLibSl for QualifiedFunctionName {}

/// An automaton constructor declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclConstructor {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// Whether the constructor is a method (uses `*.` in its name).
    #[cfg_attr(feature = "serde", no_wrap)]
    pub is_method: bool,

    /// The constructor's name.
    pub name: Option<Name>,

    /// A list of the constructor's parameters.
    pub params: Vec<FunctionParam>,

    /// The constructor's return type.
    pub ret_ty_expr: Option<TyExprId>,

    /// The constructor's body.
    pub body: Option<FunctionBody>,
}

impl WithLibSl for DeclConstructor {}

/// An automaton destructor declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclDestructor {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// Whether the destructor is a method (uses `*.` in its name).
    #[cfg_attr(feature = "serde", no_wrap)]
    pub is_method: bool,

    /// The destructor's name.
    pub name: Option<Name>,

    /// A list of the destructor's parameters.
    pub params: Vec<FunctionParam>,

    /// The destructor's return type.
    pub ret_ty_expr: Option<TyExprId>,

    /// The destructor's body.
    pub body: Option<FunctionBody>,
}

impl WithLibSl for DeclDestructor {}

/// An automaton procedure declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct DeclProc {
    /// A list of annotations for this declaration.
    pub annotations: Vec<Annotation>,

    /// Whether the procedure has a `static` modifier.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub is_method: bool,

    /// The procedure's name.
    pub name: Name,

    /// A list of type parameter (generic) declarations.
    pub generics: Vec<Generic>,

    /// A list of the procedure's parameters.
    pub params: Vec<FunctionParam>,

    /// The procedure's return type.
    pub ret_ty_expr: Option<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,

    /// The procedure's body.
    pub body: Option<FunctionBody>,
}

impl WithLibSl for DeclProc {}

/// A function parameter declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct FunctionParam {
    /// A list of annotations for this parameter declaration.
    pub annotations: Vec<Annotation>,

    /// The name of the parameter.
    pub name: Name,

    /// The type of the parameter.
    pub ty_expr: TyExprId,
}

impl WithLibSl for FunctionParam {}

/// The body of a function.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct FunctionBody {
    /// The function's contract specifications.
    pub contracts: Vec<Contract>,

    /// A list of statements comprising the body of the function.
    pub stmts: Vec<StmtId>,
}

impl WithLibSl for FunctionBody {}

/// A function contract specification.
#[derive(From, Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum Contract {
    /// A precondition specification.
    Requires(ContractRequires),

    /// A postcondition specification.
    Ensures(ContractEnsures),

    /// A write set specification.
    Assigns(ContractAssigns),
}

impl WithLibSl for Contract {}

/// A precondition specification.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ContractRequires {
    /// The contract's name.
    pub name: Option<Name>,

    /// The contract expression.
    pub expr: ExprId,
}

impl WithLibSl for ContractRequires {}

/// A postcondition specification.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ContractEnsures {
    /// The contract's name.
    pub name: Option<Name>,

    /// The contract expression.
    pub expr: ExprId,
}

impl WithLibSl for ContractEnsures {}

/// A write set specification.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ContractAssigns {
    /// The contract's name.
    pub name: Option<Name>,

    /// The contract expression.
    pub expr: ExprId,
}

impl WithLibSl for ContractAssigns {}

/// An annotation use.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct Annotation {
    /// The name of the annotation.
    pub name: Name,

    /// A list of arguments to this annotation.
    pub args: Vec<AnnotationArg>,
}

impl WithLibSl for Annotation {}

/// An annotation argument supplied at the point of an annotation's use.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct AnnotationArg {
    /// The name of the parameter.
    pub name: Option<Name>,

    /// The argument expression.
    pub expr: ExprId,
}

impl WithLibSl for AnnotationArg {}

/// A type name qualified with type parameter declarations.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct QualifiedTyName {
    /// The name of the type.
    pub ty_name: FullName,

    /// A list of type parameter (generic) declarations.
    pub generics: Vec<Generic>,
}

impl WithLibSl for QualifiedTyName {}

/// A full name to an entity, consisting of several components separated with a period.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct FullName {
    /// A list of the name's components.
    ///
    /// Each component is a single identifier in the period-separated sequence.
    pub components: Vec<Name>,
}

impl WithLibSl for FullName {}

/// A name in the source file paired with its location information.
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
#[derive(Debug, Clone)]
pub struct Name {
    /// The name's location in the source text.
    pub loc: Loc,

    /// The name string.
    ///
    /// For LibSL export, must be a valid LibSL identifier.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub name: String,
}

impl WithLibSl for Name {}

/// A constraint on a type parameter.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct TyConstraint {
    /// The name of the type parameter bounded by this constraint.
    pub param: Name,

    /// An explicit variance specification, if any.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub variance: Option<Variance>,

    /// The bound for the type parameter.
    pub bound: TyArg,
}

impl WithLibSl for TyConstraint {}

/// A type parameter (generic) declaration.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct Generic {
    /// An explicit variance specification, if any.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub variance: Option<Variance>,

    /// The name of the type parameter.
    pub name: Name,
}

impl WithLibSl for Generic {}

/// An enumeration of possible variance specifications.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum Variance {
    /// Covariant: `U <: V` implies `T[U] <: T[V]`.
    ///
    /// Corresponds to TypeScript's `out` variance specifier.
    Covariant,

    /// Contravariant: `U <: V` implies `T[U] >: T[V]`.
    ///
    /// Corresponds to TypeScript's `in` variance specifier.
    Contravariant,

    /// Invariant: a subtype relation between `U` and `V` does not imply anything about the subtype
    /// relation between `T[U]` and `T[V]`.
    ///
    /// Corresponds to TypeScript's `in out` variance specifier.
    Invariant,
}

impl WithLibSl for Variance {}

/// A type expression, denoting a particular type in the type system.
#[derive(Debug, Default, Clone)]
pub struct TyExpr {
    /// A unique identifier for this type expression, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional information with the type expression as well as refer to
    /// it without violating borrowing rules.
    pub id: TyExprId,

    /// The type expression's location in the source text.
    pub loc: Loc,

    /// What kind of type expression this is.
    ///
    /// The variants hold data specific to each type expression kind.
    pub kind: TyExprKind,
}

impl WithLibSl for TyExpr {}

/// An enumeration of all possible type expression kinds.
#[derive(From, Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum TyExprKind {
    /// A dummy type expression, the default value of `TyExprKind`.
    ///
    /// Allows using `mem::take` to take ownership of the value.
    #[default]
    Dummy,

    /// A literal expression of a primitive type.
    PrimitiveLit(TyExprPrimitiveLit),

    /// A type name expression.
    Name(TyExprName),

    /// A pointer type expression.
    Pointer(TyExprPointer),

    /// An intersection type expression.
    Intersection(TyExprIntersection),

    /// A union type expression.
    Union(TyExprUnion),
}

impl WithLibSl for TyExprKind {}

/// A literal expression of a primitive type.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct TyExprPrimitiveLit {
    /// The primitive literal comprising this type expression.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub lit: PrimitiveLit,
}

impl WithLibSl for TyExprPrimitiveLit {}

/// A type name expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct TyExprName {
    /// The referred type's name.
    pub ty_name: FullName,

    /// A list of type arguments for the referred type.
    pub generics: Vec<TyArg>,
}

impl WithLibSl for TyExprName {}

/// A pointer type expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct TyExprPointer {
    /// A base type the pointer refers to.
    pub base: TyExprId,
}

impl WithLibSl for TyExprPointer {}

/// An intersection type expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct TyExprIntersection {
    /// The left type expression.
    pub lhs: TyExprId,

    /// The right type expression.
    pub rhs: TyExprId,
}

impl WithLibSl for TyExprIntersection {}

/// A union type expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct TyExprUnion {
    /// The left type expression.
    pub lhs: TyExprId,

    /// The right type expression.
    pub rhs: TyExprId,
}

impl WithLibSl for TyExprUnion {}

/// A type argument for a generic type's type parameter.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum TyArg {
    /// An arbitrary type expression.
    TyExpr(TyExprId),

    /// A type wildcard, useful in situations where the exact type for the parameter is not
    /// required.
    Wildcard(Loc),
}

impl WithLibSl for TyArg {}

/// A statement in a function body.
#[derive(Debug, Default, Clone)]
pub struct Stmt {
    /// A unique identifier for this statement, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional information with the statement as well as refer to it
    /// without violating borrowing rules.
    pub id: StmtId,

    /// The statement's location in the source text.
    pub loc: Loc,

    /// What kind of statement this is.
    ///
    /// The variants hold data specific to each declaration kind.
    pub kind: StmtKind,
}

impl WithLibSl for Stmt {}

/// An enumeration of all possible statement kinds.
#[derive(From, Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum StmtKind {
    /// A dummy statement, the default value of `StmtKind`.
    /// Allows using `mem::take` to take ownership of the value.
    #[default]
    Dummy,

    /// A variable declaration.
    Decl(DeclId),

    /// A conditional statement.
    If(StmtIf),

    /// A variable assignment statement.
    Assign(StmtAssign),

    /// An expression statement.
    Expr(ExprId),
}

impl WithLibSl for StmtKind {}

/// A conditional statement.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct StmtIf {
    /// The if statement's condition.
    pub cond: ExprId,

    /// A sequence of statements evaluated when the condition is true.
    pub then_branch: Vec<StmtId>,

    /// A sequence of statements evaluated when the condition is false.
    pub else_branch: Vec<StmtId>,
}

impl WithLibSl for StmtIf {}

/// A variable assignment statement.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct StmtAssign {
    /// The place this statement assigns to.
    pub lhs: QualifiedAccessId,

    /// An optional in-place update operator.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub in_place_op: Option<InPlaceOp>,

    /// The expression assigned to the place.
    pub rhs: ExprId,
}

impl WithLibSl for StmtAssign {}

/// An in-place update operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum InPlaceOp {
    /// Addition.
    Add,

    /// Subtraction.
    Sub,

    /// Multiplication.
    Mul,

    /// Division.
    Div,

    /// Modulus.
    Mod,

    /// Bitwise and.
    BitAnd,

    /// Bitwise or.
    BitOr,

    /// Bitwise xor.
    BitXor,

    /// Arithmetic (signed) left shift.
    Sal,

    /// Arithmetic (signed) right shift.
    Sar,
}

impl WithLibSl for InPlaceOp {}

/// A LibSL expression.
#[derive(Debug, Default, Clone)]
pub struct Expr {
    /// A unique identifier for this expression, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional informatino with the expression as well as refer to it
    /// without violating borrowing rule.
    pub id: ExprId,

    /// The expression's location in the source text.
    pub loc: Loc,

    /// What kind of expression this is.
    ///
    /// The variants hold data specific to each expression kind.
    pub kind: ExprKind,
}

impl WithLibSl for Expr {}

/// An enumeration of all possible expression kinds.
#[derive(From, Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum ExprKind {
    /// A dummy expression, the default value of `ExprKind`.
    ///
    /// Allows using `mem::take` to take ownership of the value.
    #[default]
    Dummy,

    /// A literal expression of a primitive type.
    PrimitiveLit(ExprPrimitiveLit),

    /// An array literal expression.
    ArrayLit(ExprArrayLit),

    /// A qualified variable/element access expression.
    QualifiedAccess(ExprQualifiedAccess),

    /// A previous-state value expression.
    Prev(ExprPrev),

    /// A procedure call expression.
    ProcCall(ExprProcCall),

    /// An action invocation expression.
    ActionCall(ExprActionCall),

    /// An automaton instantiation expression.
    Instantiate(ExprInstantiate),

    /// A `has`-concept expression.
    HasConcept(ExprHasConcept),

    /// A cast expression.
    Cast(ExprCast),

    /// A type comparison expression.
    TyCompare(ExprTyCompare),

    /// A unary arithmetic/logical expression.
    Unary(ExprUnary),

    /// A binary arithmetic/logical expression.
    Binary(ExprBinary),
}

impl WithLibSl for ExprKind {}

/// A literal expression of a primitive type.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprPrimitiveLit {
    /// The primitive literal comprising this expression.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub lit: PrimitiveLit,
}

impl WithLibSl for ExprPrimitiveLit {}

/// An array literal expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprArrayLit {
    /// A list of array elements.
    pub elems: Vec<ExprId>,
}

impl WithLibSl for ExprArrayLit {}

/// A qualified variable/element access expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprQualifiedAccess {
    /// The variable/element accessed by this expression.
    pub access: QualifiedAccessId,
}

impl WithLibSl for ExprQualifiedAccess {}

/// A previous-state value expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprPrev {
    /// The variable/element referred to by this expression.
    pub access: QualifiedAccessId,
}

impl WithLibSl for ExprPrev {}

/// A procedure call expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprProcCall {
    /// The procedure called in this expression.
    pub callee: QualifiedAccessId,

    /// A list of type arguments for the callee.
    pub generics: Vec<TyArg>,

    /// A list of arguments to the procedure call.
    pub args: Vec<ExprId>,
}

impl WithLibSl for ExprProcCall {}

/// An action invocation expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprActionCall {
    /// The action invoked in this expression.
    pub name: Name,

    /// A list of type arguments for the action.
    pub generics: Vec<TyArg>,

    /// A list of arguments to the action invocation.
    pub args: Vec<ExprId>,
}

impl WithLibSl for ExprActionCall {}

/// An automaton instantiation expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprInstantiate {
    /// The name of an automaton.
    pub name: FullName,

    /// A list of type arguments for the automaton.
    pub generics: Vec<TyArg>,

    /// A list of arguments to the automaton's constructor.
    pub args: Vec<ConstructorArg>,
}

impl WithLibSl for ExprInstantiate {}

/// An argument for an automaton instantiation expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum ConstructorArg {
    /// An automaton state assignment.
    State(ExprId),

    /// A value for a constructor variable.
    Var(Name, ExprId),
}

impl WithLibSl for ConstructorArg {}

/// A `has`-concept expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprHasConcept {
    /// An entity this expression tests for.
    pub scrutinee: QualifiedAccessId,

    /// A concept the scrutinee is tested for.
    pub concept: Name,
}

impl WithLibSl for ExprHasConcept {}

/// A cast expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprCast {
    /// The expression being cast.
    pub expr: ExprId,

    /// A type the expression is cast to.
    pub ty_expr: TyExprId,
}

impl WithLibSl for ExprCast {}

/// An type comparison expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprTyCompare {
    /// The expression whose type is tested for.
    pub expr: ExprId,

    /// An expected expression type.
    pub ty_expr: TyExprId,
}

impl WithLibSl for ExprTyCompare {}

/// A unary arithmetic or logical expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprUnary {
    /// A unary operator.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub op: UnOp,

    /// The operand of the unary operator.
    pub expr: ExprId,
}

impl WithLibSl for ExprUnary {}

/// An enumeration of all unary operators that can be used in [`ExprUnary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum UnOp {
    /// Unary plus.
    Plus,

    /// Negation (unary minus).
    Neg,

    /// Bitwise negation.
    BitNot,

    /// Logical negation.
    Not,
}

impl WithLibSl for UnOp {}

/// A binary arithmetic or logical expression.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct ExprBinary {
    /// The left operand of the operator.
    pub lhs: ExprId,

    /// A binary operator.
    #[cfg_attr(feature = "serde", no_wrap)]
    pub op: BinOp,

    /// The right operand of the operator.
    pub rhs: ExprId,
}

impl WithLibSl for ExprBinary {}

/// An enumeration of all binary operators that can be used in [`ExprBinary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum BinOp {
    /// Multiplication.
    Mul,

    /// Division.
    Div,

    /// Modulus.
    Mod,

    /// Addition.
    Add,

    /// Subtraction.
    Sub,

    /// Arithmetic (signed) left shift.
    Sal,

    /// Arithmetic (signed) right shift.
    Sar,

    /// Logical (unsigned) left shift.
    Shl,

    /// Logical (unsigned) right shift.
    Shr,

    /// Bitwise or.
    BitOr,

    /// Bitwise xor.
    BitXor,

    /// Bitwise and.
    BitAnd,

    /// Less than.
    Lt,

    /// Less than or equal to.
    Le,

    /// Greater than.
    Gt,

    /// Greater than or equal to.
    Ge,

    /// Equals.
    Eq,

    /// Not equals.
    Ne,

    /// Logical or.
    Or,

    /// Logical and.
    And,
}

impl WithLibSl for BinOp {}

/// A literal of a primitive type, usable in both expression and type expression contexts.
#[derive(From, Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum PrimitiveLit {
    /// An integer literal.
    Int(IntLit),

    /// A floating-point number literal.
    Float(FloatLit),

    /// A string literal.
    String(String),

    /// A character literal.
    Char(u32),

    /// A boolean literal.
    Bool(bool),

    /// The `null` literal.
    Null,
}

impl WithLibSl for PrimitiveLit {}

/// An integer literal.
#[derive(From, Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum IntLit {
    /// A signed byte literal (suffix `x`).
    I8(i8),

    /// An unsigned byte literal (suffix `ux`).
    U8(u8),

    /// A signed short integer literal (suffix `s`).
    I16(i16),

    /// An unsigned short integer literal (suffix `us`).
    U16(u16),

    /// A signed integer literal (no suffix).
    I32(i32),

    /// An unsigned integer literal (suffix `u`).
    U32(u32),

    /// A signed long integer literal (suffix `l`/`L`).
    I64(i64),

    /// An unsigned long integer literal (suffix `uL`).
    U64(u64),
}

impl WithLibSl for IntLit {}

/// A floating-point number literal.
#[derive(Debug, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize))]
pub enum FloatLit {
    /// A float literal (suffix `f`).
    F32(f32),

    /// A double literal (no suffix / suffix `d`).
    F64(f64),
}

impl WithLibSl for FloatLit {}

/// A qualified variable/element access.
#[derive(Debug, Default, Clone)]
pub struct QualifiedAccess {
    /// A unique identifier for this qualified access, usable as a (secondary) slotmap key.
    ///
    /// This allwos to assicated additional information with the qualified access as well as refer
    /// to it without violating borrowing rules.
    pub id: QualifiedAccessId,

    /// The qualified access's location in the source text.
    pub loc: Loc,

    /// What kind of qualified access this is.
    ///
    /// The variants hold data specific to each qualified access kind.
    pub kind: QualifiedAccessKind,
}

impl WithLibSl for QualifiedAccess {}

/// An enumeration of all possible qualified access kinds.
#[derive(From, Debug, Default, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub enum QualifiedAccessKind {
    /// A dummy qualified access, the default value of `QualifiedAccessKind`.
    ///
    /// Allows using `mem::take` to take ownership of the value.
    #[default]
    Dummy,

    /// A plain identifier.
    Name(QualifiedAccessName),

    /// A freshly-created automaton's variable.
    AutomatonVar(QualifiedAccessAutomatonVar),

    /// A field of an outer entity.
    Field(QualifiedAccessField),

    /// An indexed element of an outer entity: the `[42]` in `foo[42]`.
    Index(QualifiedAccessIndex),
}

impl WithLibSl for QualifiedAccessKind {}

/// An access referring to a plain identifier, such as `foo`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct QualifiedAccessName {
    /// The name this qualified access refers to.
    pub name: Name,
}

impl WithLibSl for QualifiedAccessName {}

/// An access referring to a variable of a freshly-created automaton, such as `A(x).foo`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct QualifiedAccessAutomatonVar {
    /// An automaton name.
    pub automaton: Name,

    /// A list of type arguments for the automaton.
    pub generics: Vec<TyArg>,

    /// The qualified access serving as an argument to the automaton.
    pub arg: QualifiedAccessId,

    /// The automaton's field this qualified access refers to.
    pub field: Name,
}

impl WithLibSl for QualifiedAccessAutomatonVar {}

/// An access referring to a field of a base entity, such as `foo.bar`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct QualifiedAccessField {
    /// The base part of the qualified access (preceding the dot).
    pub base: QualifiedAccessId,

    /// The field this qualified access refers to.
    pub field: Name,
}

impl WithLibSl for QualifiedAccessField {}

/// An access referring to an element of an indexed collection, such as `foo[42]`.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(libsl_derive::Serialize))]
pub struct QualifiedAccessIndex {
    /// The base part of the qualified access (preceding the brackets).
    pub base: QualifiedAccessId,

    /// An index of the element this qualified access refers to.
    pub index: ExprId,
}

impl WithLibSl for QualifiedAccessIndex {}
