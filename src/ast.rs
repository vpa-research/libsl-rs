use derive_more::From;

use crate::loc::Loc;
use crate::{DeclId, ExprId, QualifiedAccessId, StmtId, TyExprId};

/// A single LibSL file.
#[derive(Debug, Clone)]
pub struct File {
    pub loc: Loc,
    pub header: Option<Header>,
    pub decls: Vec<DeclId>,
}

/// A LibSL header declaration.
#[derive(Debug, Clone)]
pub struct Header {
    pub loc: Loc,
    pub libsl_version: String,
    pub library_name: String,
    pub version: Option<String>,
    pub language: Option<String>,
    pub url: Option<String>,
}

/// An entity declaration.
#[derive(Debug, Default, Clone)]
pub struct Decl {
    /// A unique identifier for this declaration, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional information with the declaration as well as refer to it
    /// without violating borrowing rules.
    pub id: DeclId,

    pub loc: Loc,
    pub kind: DeclKind,
}

#[derive(From, Debug, Default, Clone)]
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

/// An import declaration.
#[derive(Debug, Clone)]
pub struct DeclImport {
    /// An interpreted import path.
    pub path: String,
}

/// An include declaration.
#[derive(Debug, Clone)]
pub struct DeclInclude {
    /// An uninterpreted include path.
    pub path: String,
}

/// A semantic type declaration.
#[derive(Debug, Clone)]
pub struct DeclSemanticTy {
    pub annotations: Vec<Annotation>,

    /// The name of the semantic type.
    pub ty_name: QualifiedTyName,

    /// The underlying type representation.
    pub real_ty: TyExprId,

    pub kind: SemanticTyKind,
}

#[derive(Debug, Default, Clone)]
pub enum SemanticTyKind {
    /// A simple semantic type.
    #[default]
    Simple,

    /// A semantic type with enumerated special values.
    Enumerated(Vec<SemanticTyEnumValue>),
}

#[derive(Debug, Clone)]
pub struct SemanticTyEnumValue {
    /// The name of the semantic type's value.
    pub name: Name,

    /// The underlying value represented by this entry.
    pub expr: ExprId,
}

/// A type alias declaration.
#[derive(Debug, Clone)]
pub struct DeclTyAlias {
    pub annotations: Vec<Annotation>,

    /// The alias's name.
    pub ty_name: QualifiedTyName,

    /// The type represented by this alias.
    pub ty_expr: TyExprId,
}

/// A structure type declaration.
#[derive(Debug, Clone)]
pub struct DeclStruct {
    pub annotations: Vec<Annotation>,

    /// The declared type's name.
    pub ty_name: QualifiedTyName,

    // TODO: what do these two fields even mean?
    pub is_ty: Option<TyExprId>,
    pub for_tys: Vec<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,

    /// Entities (variables and functions) defined as members of this type.
    pub decls: Vec<DeclId>,
}

/// An enum type declaration.
#[derive(Debug, Clone)]
pub struct DeclEnum {
    pub annotations: Vec<Annotation>,

    /// The declared type's name.
    pub ty_name: QualifiedTyName,

    /// Possibles values of the type.
    pub variants: Vec<EnumVariant>,
}

/// An enum type variant.
#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Name,
    pub value: IntLit,
}

/// An annotation declaration.
#[derive(Debug, Clone)]
pub struct DeclAnnotation {
    pub name: Name,
    pub params: Vec<AnnotationParam>,
}

#[derive(Debug, Clone)]
pub struct AnnotationParam {
    pub name: Name,
    pub ty_expr: TyExprId,

    /// The default value for the parameter.
    pub default: Option<ExprId>,
}

/// An action declaration.
#[derive(Debug, Clone)]
pub struct DeclAction {
    pub annotations: Vec<Annotation>,
    pub generics: Vec<Generic>,
    pub name: Name,
    pub params: Vec<ActionParam>,
    pub ret_ty_expr: Option<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,
}

#[derive(Debug, Clone)]
pub struct ActionParam {
    pub annotations: Vec<Annotation>,
    pub name: Name,
    pub ty_expr: TyExprId,
}

/// An automaton declaration.
#[derive(Debug, Clone)]
pub struct DeclAutomaton {
    pub annotations: Vec<Annotation>,
    pub is_concept: bool,
    pub name: QualifiedTyName,

    /// Automaton constructor declarations.
    pub constructor_variables: Vec<DeclId>,

    /// The type modelled by this automaton.
    pub ty_expr: TyExprId,

    pub implemented_concepts: Vec<Name>,

    /// Entities defines as members of this automaton.
    pub decls: Vec<DeclId>,
}

/// A function declaration.
#[derive(Debug, Clone)]
pub struct DeclFunction {
    pub annotations: Vec<Annotation>,
    pub is_static: bool,

    /// If present, signifies an extension function for an automaton with the specified name.
    pub extension_for: Option<FullName>,

    pub is_method: bool,
    pub name: Name,
    pub generics: Vec<Generic>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,

    pub body: Option<FunctionBody>,
}

/// A variable declaration.
///
/// Depending on the context, it could be any of the following:
///
/// - a global variable
/// - an automaton constructor variable
/// - a type's member variable
/// - or a local variable
#[derive(Debug, Clone)]
pub struct DeclVariable {
    pub annotations: Vec<Annotation>,
    pub kind: VariableKind,
    pub name: Name,
    pub ty_expr: TyExprId,

    /// An optional variable initializer expression.
    pub init: Option<ExprId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Var,
    Val,
}

impl VariableKind {
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var)
    }

    pub fn is_val(&self) -> bool {
        matches!(self, Self::Val)
    }
}

/// An automaton state declaration.
#[derive(Debug, Clone)]
pub struct DeclState {
    pub kind: StateKind,
    pub name: Name,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StateKind {
    Initial,
    Regular,
    Final,
}

/// An automaton state transfer function declaration.
#[derive(Debug, Clone)]
pub struct DeclShift {
    /// A list of previous states covered by this declaration.
    pub from: Vec<Name>,

    /// A target state for this declaration.
    pub to: Name,

    /// A list of functions that trigger this transition.
    pub by: Vec<QualifiedFunctionName>,
}

/// A function name or its specific overload.
#[derive(Debug, Clone)]
pub struct QualifiedFunctionName {
    pub name: Name,

    /// Optional parameter type qualification to disambiguate overloads.
    pub params: Option<Vec<TyExprId>>,
}

/// An automaton constructor declaration.
#[derive(Debug, Clone)]
pub struct DeclConstructor {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Option<Name>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExprId>,
    pub body: Option<FunctionBody>,
}

/// An automaton destructor declaration.
#[derive(Debug, Clone)]
pub struct DeclDestructor {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Option<Name>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExprId>,
    pub body: Option<FunctionBody>,
}

/// An automaton procedure declaration.
#[derive(Debug, Clone)]
pub struct DeclProc {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Name,
    pub generics: Vec<Generic>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExprId>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone)]
pub struct FunctionParam {
    pub annotations: Vec<Annotation>,
    pub name: Name,
    pub ty_expr: TyExprId,
}

#[derive(Debug, Clone)]
pub struct FunctionBody {
    /// The function's contract specifications.
    pub contracts: Vec<Contract>,

    pub stmts: Vec<StmtId>,
}

/// A function contract specification.
#[derive(From, Debug, Clone)]
pub enum Contract {
    /// A precondition specification.
    Requires(ContractRequires),

    /// A postcondition specification.
    Ensures(ContractEnsures),

    /// A write set specification.
    Assigns(ContractAssigns),
}

/// A precondition specification.
#[derive(Debug, Clone)]
pub struct ContractRequires {
    pub name: Option<Name>,
    pub expr: ExprId,
}

/// A postcondition specification.
#[derive(Debug, Clone)]
pub struct ContractEnsures {
    pub name: Option<Name>,
    pub expr: ExprId,
}

/// A write set specification.
#[derive(Debug, Clone)]
pub struct ContractAssigns {
    pub name: Option<Name>,
    pub expr: ExprId,
}

/// An annotation use.
#[derive(Debug, Clone)]
pub struct Annotation {
    pub name: Name,
    pub args: Vec<AnnotationArg>,
}

#[derive(Debug, Clone)]
pub struct AnnotationArg {
    pub name: Option<Name>,
    pub expr: ExprId,
}

/// A type name qualified with type parameter declarations.
#[derive(Debug, Clone)]
pub struct QualifiedTyName {
    pub ty_name: FullName,
    pub generics: Vec<Generic>,
}

/// A full name to an entity, consisting of several components separated with a period.
#[derive(Debug, Clone)]
pub struct FullName {
    pub components: Vec<Name>,
}

/// A name in the source file paired with its location information.
#[derive(Debug, Clone)]
pub struct Name {
    pub loc: Loc,
    pub name: String,
}

/// A constraint on a type parameter.
#[derive(Debug, Clone)]
pub struct TyConstraint {
    pub param: Name,
    pub bound: TyArg,
}

/// A type parameter (generic) declaration.
#[derive(Debug, Clone)]
pub struct Generic {
    /// An explicit variance specification, if any.
    pub variance: Option<Variance>,

    /// The name of the type parameter.
    pub name: Name,
}

#[derive(Debug, Clone)]
pub enum Variance {
    /// Corresponds to TypeScript's `out` variance specifier.
    Covariant,

    /// Corresponds to TypeScript's `in` variance specifier.
    Contravariant,

    /// Corresponds to TypeScript's `in out` variance specifier.
    Invariant,
}

/// A type expression, denoting a particular type in the type system.
#[derive(Debug, Default, Clone)]
pub struct TyExpr {
    /// A unique identifier for this type expression, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional information with the type expression as well as refer to
    /// it without violating borrowing rules.
    pub id: TyExprId,

    pub loc: Loc,
    pub kind: TyExprKind,
}

#[derive(From, Debug, Default, Clone)]
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

/// A literal expression of a primitive type.
#[derive(Debug, Clone)]
pub struct TyExprPrimitiveLit {
    pub lit: PrimitiveLit,
}

/// A type name expression.
#[derive(Debug, Clone)]
pub struct TyExprName {
    pub ty_name: FullName,
    pub generics: Vec<TyArg>,
}

/// A pointer type expression.
#[derive(Debug, Clone)]
pub struct TyExprPointer {
    /// A base type the pointer refers to.
    pub base: TyExprId,
}

/// An intersection type expression.
#[derive(Debug, Clone)]
pub struct TyExprIntersection {
    pub lhs: TyExprId,
    pub rhs: TyExprId,
}

/// A union type expression.
#[derive(Debug, Clone)]
pub struct TyExprUnion {
    pub lhs: TyExprId,
    pub rhs: TyExprId,
}

/// A type argument applied to a generic type's type parameter.
#[derive(Debug, Clone)]
pub enum TyArg {
    /// An arbitrary type expression.
    TyExpr(TyExprId),

    /// A type wildcard, useful in situations where the exact type for the parameter is not
    /// required.
    Wildcard(Loc),
}

/// A statement in a function body.
#[derive(Debug, Default, Clone)]
pub struct Stmt {
    /// A unique identifier for this statement, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional information with the statement as well as refer to it
    /// without violating borrowing rules.
    pub id: StmtId,

    pub loc: Loc,
    pub kind: StmtKind,
}

#[derive(From, Debug, Default, Clone)]
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

/// A conditional statement.
#[derive(Debug, Clone)]
pub struct StmtIf {
    pub cond: ExprId,
    pub then_branch: Vec<StmtId>,
    pub else_branch: Vec<StmtId>,
}

/// A variable assignment statement.
#[derive(Debug, Clone)]
pub struct StmtAssign {
    pub lhs: QualifiedAccessId,

    /// An optional in-place update operator.
    pub in_place_op: Option<InPlaceOp>,

    pub rhs: ExprId,
}

/// An in-place update operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// A LibSL expression.
#[derive(Debug, Default, Clone)]
pub struct Expr {
    /// A unique identifier for this expression, usable as a (secondary) slotmap key.
    ///
    /// This allows to associate additional informatino with the expression as well as refer to it
    /// without violating borrowing rule.
    pub id: ExprId,

    pub loc: Loc,
    pub kind: ExprKind,
}

#[derive(From, Debug, Default, Clone)]
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

/// A literal expression of a primitive type.
#[derive(Debug, Clone)]
pub struct ExprPrimitiveLit {
    pub lit: PrimitiveLit,
}

/// An array literal expression.
#[derive(Debug, Clone)]
pub struct ExprArrayLit {
    pub elems: Vec<ExprId>,
}

/// A qualified variable/element access expression.
#[derive(Debug, Clone)]
pub struct ExprQualifiedAccess {
    pub access: QualifiedAccessId,
}

/// A previous-state value expression.
#[derive(Debug, Clone)]
pub struct ExprPrev {
    pub access: QualifiedAccessId,
}

/// A procedure call expression.
#[derive(Debug, Clone)]
pub struct ExprProcCall {
    pub callee: QualifiedAccessId,
    pub generics: Vec<TyArg>,
    pub args: Vec<ExprId>,
}

/// An action invocation expression.
#[derive(Debug, Clone)]
pub struct ExprActionCall {
    pub name: Name,
    pub generics: Vec<TyArg>,
    pub args: Vec<ExprId>,
}

/// An automaton instantiation expression.
#[derive(Debug, Clone)]
pub struct ExprInstantiate {
    /// The name of an automaton.
    pub name: FullName,

    pub generics: Vec<TyArg>,
    pub args: Vec<ConstructorArg>,
}

/// An argument for an automaton instantiation expression.
#[derive(Debug, Clone)]
pub enum ConstructorArg {
    /// An automaton state assignment.
    State(ExprId),

    /// A value for a constructor variable.
    Var(Name, ExprId),
}

/// A `has`-concept expression.
#[derive(Debug, Clone)]
pub struct ExprHasConcept {
    /// The entity this expression tests for.
    pub scrutinee: QualifiedAccessId,

    pub concept: Name,
}

/// A cast expression.
#[derive(Debug, Clone)]
pub struct ExprCast {
    pub expr: ExprId,
    pub ty_expr: TyExprId,
}

/// An type comparison expression.
#[derive(Debug, Clone)]
pub struct ExprTyCompare {
    pub expr: ExprId,
    pub ty_expr: TyExprId,
}

/// A unary arithmetic or logical expression.
#[derive(Debug, Clone)]
pub struct ExprUnary {
    pub op: UnOp,
    pub expr: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// A binary arithmetic or logical expression.
#[derive(Debug, Clone)]
pub struct ExprBinary {
    pub lhs: ExprId,
    pub op: BinOp,
    pub rhs: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// A literal of a primitive type, usable in both expression and type expression contexts.
#[derive(From, Debug, Clone)]
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

/// An integer literal.
#[derive(From, Debug, Clone, Copy)]
pub enum IntLit {
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
}

/// A floating-point number literal.
#[derive(Debug, Clone, Copy)]
pub enum FloatLit {
    F32(f32),
    F64(f64),
}

/// A qualified variable/element access.
#[derive(Debug, Default, Clone)]
pub struct QualifiedAccess {
    /// A unique identifier for this qualified access, usable as a (secondary) slotmap key.
    ///
    /// This allwos to assicated additional information with the qualified access as well as refer
    /// to it without violating borrowing rules.
    pub id: QualifiedAccessId,

    pub loc: Loc,
    pub kind: QualifiedAccessKind,
}

#[derive(From, Debug, Default, Clone)]
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

/// An access referring to a plain identifier, such as `foo`.
#[derive(Debug, Clone)]
pub struct QualifiedAccessName {
    pub name: Name,
}

/// An access referring to a variable of a freshly-created automaton, such as `A(x).foo`.
#[derive(Debug, Clone)]
pub struct QualifiedAccessAutomatonVar {
    pub automaton: Name,
    pub generics: Vec<TyArg>,
    pub arg: QualifiedAccessId,
    pub variable: Name,
}

/// An access referring to a field of a base entity, such as `foo.bar`.
#[derive(Debug, Clone)]
pub struct QualifiedAccessField {
    pub base: QualifiedAccessId,
    pub field: Name,
}

/// An access referring to an element of an indexed collection, such as `foo[42]`.
#[derive(Debug, Clone)]
pub struct QualifiedAccessIndex {
    pub base: QualifiedAccessId,
    pub index: ExprId,
}
