use slotmap::new_key_type;

use crate::loc::Loc;

new_key_type! {
    pub struct DeclId;
    pub struct TyExprId;
    pub struct ExprId;
    pub struct StmtId;
    pub struct QualifiedAccessId;
}

/// A single LibSL file.
#[derive(Debug, Clone)]
pub struct File {
    pub loc: Loc,
    pub header: Option<Header>,
    pub decls: Vec<Decl>,
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

#[derive(Debug, Default, Clone)]
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
    pub real_ty: TyExpr,

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
    pub expr: Expr,
}

/// A type alias declaration.
#[derive(Debug, Clone)]
pub struct DeclTyAlias {
    pub annotations: Vec<Annotation>,

    /// The alias's name.
    pub ty_name: QualifiedTyName,

    /// The type represented by this alias.
    pub ty_expr: TyExpr,
}

/// A structure type declaration.
#[derive(Debug, Clone)]
pub struct DeclStruct {
    pub annotations: Vec<Annotation>,

    /// The declared type's name.
    pub ty_name: QualifiedTyName,

    // TODO: what do these two fields even mean?
    pub is_ty: TyExpr,
    pub for_tys: Vec<TyExpr>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,

    /// Entities (variables and functions) defines as members of this type.
    pub decls: Vec<Decl>,
}

/// An enum type declaration.
#[derive(Debug, Clone)]
pub struct DeclEnum {
    pub annotations: Vec<Annotation>,

    /// The declared type's name.
    pub name: QualifiedTyName,

    /// Possibles values of the type.
    pub variants: Vec<EnumVariant>,
}

/// An enum type variant.
#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Name,
    pub value: i64,
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
    pub ty_expr: TyExpr,

    /// The default value for the parameter.
    pub default: Option<Expr>,
}

/// An action declaration.
#[derive(Debug, Clone)]
pub struct DeclAction {
    pub annotations: Vec<Annotation>,
    pub generics: Vec<Generic>,
    pub name: Name,
    pub params: Vec<ActionParam>,
    pub ret_ty_expr: Option<TyExpr>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,
}

#[derive(Debug, Clone)]
pub struct ActionParam {
    pub annotations: Vec<Annotation>,
    pub name: Name,
    pub ty_expr: TyExpr,
}

/// An automaton declaration.
#[derive(Debug, Clone)]
pub struct DeclAutomaton {
    pub annotations: Vec<Annotation>,
    pub is_concept: bool,
    pub name: QualifiedTyName,

    /// Automaton constructor declarations.
    pub constructor_variables: Vec<Decl>,

    /// The type modelled by this automaton.
    pub ty_expr: TyExpr,

    pub implemented_concepts: Vec<Name>,

    /// Entities defines as members of this automaton.
    pub decls: Vec<Decl>,
}

/// A function declaration.
#[derive(Debug, Clone)]
pub struct DeclFunction {
    pub annotations: Vec<Annotation>,
    pub is_static: bool,

    /// If present, signifies an extension function for an automaton with the specified name.
    pub extension_for: Option<Name>,

    pub is_method: bool,
    pub name: Name,
    pub generics: Vec<Generic>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,

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
    pub ty_expr: TyExpr,

    /// An optional variable initializer expression.
    pub init: Option<Expr>,
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
    pub params: Option<Vec<TyExpr>>,
}

/// An automaton constructor declaration.
#[derive(Debug, Clone)]
pub struct DeclConstructor {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Option<Name>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,
    pub body: Option<FunctionBody>,
}

/// An automaton destructor declaration.
#[derive(Debug, Clone)]
pub struct DeclDestructor {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Option<Name>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,
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
    pub ret_ty_expr: Option<TyExpr>,

    /// Type parameter constraints, specified in a `where`-clause.
    pub ty_constraints: Vec<TyConstraint>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone)]
pub struct FunctionParam {
    pub annotations: Vec<Annotation>,
    pub name: Name,
    pub ty_expr: TyExpr,
}

#[derive(Debug, Clone)]
pub struct FunctionBody {
    /// The function's contract specifications.
    pub contracts: Vec<Contract>,

    pub stmts: Vec<Stmt>,
}

/// A function contract specification.
#[derive(Debug, Clone)]
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
    pub expr: Expr,
}

/// A postcondition specification.
#[derive(Debug, Clone)]
pub struct ContractEnsures {
    pub name: Option<Name>,
    pub expr: Expr,
}

/// A write set specification.
#[derive(Debug, Clone)]
pub struct ContractAssigns {
    pub name: Option<Name>,
    pub expr: Expr,
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
    pub expr: Expr,
}

/// A type name qualified with type parameter declarations.
#[derive(Debug, Clone)]
pub struct QualifiedTyName {
    pub ty_name: Name,
    pub generics: Vec<Generic>,
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
    pub bound: TyExpr,
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

#[derive(Debug, Default, Clone)]
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
    Union(TyExprUnion), // TODO: or is it sum?
}

/// A literal expression of a primitive type.
#[derive(Debug, Clone)]
pub struct TyExprPrimitiveLit {
    pub lit: PrimitiveLit,
}

/// A type name expression.
#[derive(Debug, Clone)]
pub struct TyExprName {
    pub name: Name,
    pub generics: Vec<TyArg>,
}

/// A pointer type expression.
#[derive(Debug, Clone)]
pub struct TyExprPointer {
    /// A base type the pointer refers to.
    pub base: Box<TyExpr>,
}

/// An intersection type expression.
#[derive(Debug, Clone)]
pub struct TyExprIntersection {
    pub lhs: Box<TyExpr>,
    pub rhs: Box<TyExpr>,
}

/// A union type expression.
#[derive(Debug, Clone)]
pub struct TyExprUnion {
    pub lhs: Box<TyExpr>,
    pub rhs: Box<TyExpr>,
}

/// A type argument applied to a generic type's type parameter.
#[derive(Debug, Clone)]
pub enum TyArg {
    /// An arbitrary type expression.
    TyExpr(TyExpr),

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

#[derive(Debug, Default, Clone)]
pub enum StmtKind {
    /// A dummy statement, the default value of `StmtKind`.
    /// Allows using `mem::take` to take ownership of the value.
    #[default]
    Dummy,

    /// A variable declaration.
    Decl(Box<Decl>),

    /// A conditional statement.
    If(StmtIf),

    /// A variable assignment statement.
    Assign(StmtAssign),

    /// An expression statement.
    Expr(Expr),
}

/// A conditional statement.
#[derive(Debug, Clone)]
pub struct StmtIf {
    pub cond: Expr,
    pub then_branch: Vec<Stmt>,
    pub else_branch: Vec<Stmt>,
}

/// A variable assignment statement.
#[derive(Debug, Clone)]
pub struct StmtAssign {
    pub lhs: QualifiedAccess,

    /// An optional in-place update operator.
    pub in_place_op: Option<InPlaceOp>,

    pub rhs: Expr,
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

#[derive(Debug, Default, Clone)]
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
    pub elems: Vec<Expr>,
}

/// A qualified variable/element access expression.
#[derive(Debug, Clone)]
pub struct ExprQualifiedAccess {
    pub access: QualifiedAccess,
}

/// A previous-state value expression.
#[derive(Debug, Clone)]
pub struct ExprPrev {
    pub access: QualifiedAccess,
}

/// A procedure call expression.
#[derive(Debug, Clone)]
pub struct ExprProcCall {
    pub callee: QualifiedAccess,
    pub generics: Vec<TyArg>,
    pub args: Vec<Expr>,
}

/// An action invocation expression.
#[derive(Debug, Clone)]
pub struct ExprActionCall {
    pub name: Name,
    pub generics: Vec<TyArg>,
    pub args: Vec<Expr>,
}

/// An automaton instantiation expression.
#[derive(Debug, Clone)]
pub struct ExprInstantiate {
    /// The name of an automaton.
    pub name: Name,

    pub generics: Vec<TyArg>,
    pub args: Vec<ConstructorArg>,
}

/// An argument for an automaton instantiation expression.
#[derive(Debug, Clone)]
pub enum ConstructorArg {
    /// An automaton state assignment.
    State(Expr),

    /// A value for a constructor variable.
    Var(Name, Expr),
}

/// A `has`-concept expression.
#[derive(Debug, Clone)]
pub struct ExprHasConcept {
    /// The entity this expression tests for.
    pub scrutinee: QualifiedAccess,

    pub concept: Name,
}

/// A cast expression.
#[derive(Debug, Clone)]
pub struct ExprCast {
    pub expr: Box<Expr>,
    pub ty_expr: TyExpr,
}

/// An type comparison expression.
#[derive(Debug, Clone)]
pub struct ExprTyCompare {
    pub expr: Box<Expr>,
    pub ty_expr: TyExpr,
}

/// A unary arithmetic or logical expression.
#[derive(Debug, Clone)]
pub struct ExprUnary {
    pub op: UnOp,
    pub expr: Box<Expr>,
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
    pub lhs: Box<Expr>,
    pub op: BinOp,
    pub rhs: Box<Expr>,
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
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Default, Clone)]
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
    pub arg: Box<QualifiedAccess>,
    pub variable: Name,
}

/// An access referring to a field of a base entity, such as `foo.bar`.
#[derive(Debug, Clone)]
pub struct QualifiedAccessField {
    pub base: Box<QualifiedAccess>,
    pub field: Name,
}

/// An access referring to an element of an indexed collection, such as `foo[42]`.
#[derive(Debug, Clone)]
pub struct QualifiedAccessIndex {
    pub base: Box<QualifiedAccess>,
    pub index: Box<Expr>,
}
