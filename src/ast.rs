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

#[derive(Debug, Default, Clone)]
pub struct Decl {
    pub id: DeclId,
    pub loc: Loc,
    pub kind: DeclKind,
}

#[derive(Debug, Default, Clone)]
pub enum DeclKind {
    /// A dummy declaration, the default value of `DeclKind`.
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

    /// An enumeration type declaration.
    Enum(DeclEnum),

    /// An annotation declaration.
    Annotation(DeclAnnotation),

    /// An action declaration.
    Action(DeclAction),

    /// An automaton declaration.
    Automaton(DeclAutomaton),

    /// A function declaration.
    Function(DeclFunction),

    /// A declaration of:
    ///
    /// - a global variable
    /// - an automaton constructor variable
    /// - a type's member variable
    /// - or a local variable
    Varable(DeclVariable),

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

#[derive(Debug, Clone)]
pub struct DeclImport {
    pub path: String,
}

#[derive(Debug, Clone)]
pub struct DeclInclude {
    pub path: String,
}

#[derive(Debug, Clone)]
pub struct DeclSemanticTy {
    pub annotations: Vec<Annotation>,
    pub ty_name: QualifiedTyName,
    pub real_ty: TyExpr,
    pub kind: SemanticTyKind,
}

#[derive(Debug, Default, Clone)]
pub enum SemanticTyKind {
    #[default]
    Simple,

    Enumerated(Vec<SemanticTyEnumValue>),
}

#[derive(Debug, Clone)]
pub struct SemanticTyEnumValue {
    pub name: Name,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct DeclTyAlias {
    pub annotations: Vec<Annotation>,
    pub ty_name: QualifiedTyName,
    pub ty_expr: TyExpr,
}

#[derive(Debug, Clone)]
pub struct DeclStruct {
    pub annotations: Vec<Annotation>,
    pub ty_name: QualifiedTyName,

    // TODO: what do these two fields even mean?
    pub is_ty: TyExpr,
    pub for_tys: Vec<TyExpr>,

    pub ty_constraints: Vec<TyConstraint>,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone)]
pub struct DeclEnum {
    pub annotations: Vec<Annotation>,
    pub name: QualifiedTyName,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub name: Name,
    pub value: i64,
}

#[derive(Debug, Clone)]
pub struct DeclAnnotation {
    pub name: Name,
    pub params: Vec<AnnotationParam>,
}

#[derive(Debug, Clone)]
pub struct AnnotationParam {
    pub name: Name,
    pub ty_expr: TyExpr,
    pub init: Option<Expr>,
}

#[derive(Debug, Clone)]
pub struct DeclAction {
    pub annotations: Vec<Annotation>,
    pub generics: Vec<Generic>,
    pub name: Name,
    pub params: Vec<ActionParam>,
    pub ret_ty_expr: Option<TyExpr>,
    pub ty_constraints: Vec<TyConstraint>,
}

#[derive(Debug, Clone)]
pub struct ActionParam {
    pub annotations: Vec<Annotation>,
    pub name: Name,
    pub ty_expr: TyExpr,
}

#[derive(Debug, Clone)]
pub struct DeclAutomaton {
    pub annotations: Vec<Annotation>,
    pub is_concept: bool,
    pub name: UnqualifiedTyName,
    pub constructor_variables: Vec<Decl>,
    pub ty_expr: TyExpr,
    pub implemented_concepts: Vec<String>,
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone)]
pub struct DeclFunction {
    pub annotations: Vec<Annotation>,
    pub is_static: bool,
    pub extension_for: Option<UnqualifiedTyName>,
    pub is_method: bool,
    pub name: Name,
    pub generics: Vec<Generic>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,
    pub ty_constraints: Vec<TyConstraint>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone)]
pub struct DeclVariable {
    pub annotations: Vec<Annotation>,
    pub kind: VariableKind,
    pub name: Name,
    pub ty_expr: TyExpr,
    pub init: Option<Expr>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VariableKind {
    Var,
    Val,
}

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

#[derive(Debug, Clone)]
pub struct DeclShift {
    pub from: Vec<String>,
    pub to: Vec<String>,
    pub by: Vec<QualifiedFunctionName>,
}

#[derive(Debug, Clone)]
pub struct QualifiedFunctionName {
    pub name: Name,

    /// Optional parameter type qualification to disambiguate overloads.
    pub params: Option<Vec<TyExpr>>,
}

#[derive(Debug, Clone)]
pub struct DeclConstructor {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Option<String>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone)]
pub struct DeclDestructor {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Option<String>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,
    pub body: Option<FunctionBody>,
}

#[derive(Debug, Clone)]
pub struct DeclProc {
    pub annotations: Vec<Annotation>,
    pub is_method: bool,
    pub name: Name,
    pub generics: Vec<Generic>,
    pub params: Vec<FunctionParam>,
    pub ret_ty_expr: Option<TyExpr>,
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
    pub contracts: Vec<Contract>,
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub enum Contract {
    Requires(ContractRequires),
    Ensures(ContractEnsures),
    Assigns(ContractAssigns),
}

#[derive(Debug, Clone)]
pub struct ContractRequires {
    pub name: Option<Name>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ContractEnsures {
    pub name: Option<Name>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct ContractAssigns {
    pub name: Option<Name>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct Annotation {
    pub name: Name,
    pub args: Vec<AnnotationArg>,
}

#[derive(Debug, Clone)]
pub struct AnnotationArg {
    pub name: Option<String>,
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct QualifiedTyName {
    pub ty_name: UnqualifiedTyName,
    pub generics: Vec<Generic>,
}

#[derive(Debug, Clone)]
pub enum UnqualifiedTyName {
    Unbound(Loc),
    Bound(Name),
}

impl Default for UnqualifiedTyName {
    fn default() -> Self {
        Self::Unbound(Default::default())
    }
}

#[derive(Debug, Clone)]
pub struct Name {
    pub loc: Loc,
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct TyConstraint {
    pub param: Name,
    pub bound: TyExpr,
}

#[derive(Debug, Clone)]
pub struct Generic {
    pub variance: Variance,
    pub name: Name,
}

#[derive(Debug, Default, Clone)]
pub enum Variance {
    #[default]
    Unspecified,

    /// Corresponds to TypeScript's `out` variance specifier.
    Covariant,

    /// Corresponds to TypeScript's `in` variance specifier.
    Contravariant,

    /// Corresponds to TypeScript's `in out` variance specifier.
    Invariant,
}

#[derive(Debug, Default, Clone)]
pub struct TyExpr {
    pub id: TyExprId,
    pub loc: Loc,
    pub kind: TyExprKind,
}

#[derive(Debug, Default, Clone)]
pub enum TyExprKind {
    #[default]
    Dummy,

    Name(TyExprName),
    Pointer(TyExprPointer),
    Intersection(TyExprIntersection),
    Union(TyExprUnion), // TODO: or is it sum?
}

#[derive(Debug, Clone)]
pub struct TyExprName {
    pub name: UnqualifiedTyName,
    pub generics: Vec<TyExpr>,
}

#[derive(Debug, Clone)]
pub struct TyExprPointer {
    pub ty_expr: Box<TyExpr>,
}

#[derive(Debug, Clone)]
pub struct TyExprIntersection {
    pub lhs: Box<TyExpr>,
    pub rhs: Box<TyExpr>,
}

#[derive(Debug, Clone)]
pub struct TyExprUnion {
    pub lhs: Box<TyExpr>,
    pub rhs: Box<TyExpr>,
}

#[derive(Debug, Default, Clone)]
pub struct Stmt {
    pub id: StmtId,
    pub loc: Loc,
    pub kind: StmtKind,
}

#[derive(Debug, Default, Clone)]
pub enum StmtKind {
    #[default]
    Dummy,

    Decl(Box<Decl>),
    If(StmtIf),
    Assign(StmtAssign),
    Expr(Expr),
}

#[derive(Debug, Clone)]
pub struct StmtIf {
    pub cond: Expr,
    pub then_branch: Vec<Stmt>,
    pub else_branch: Vec<Stmt>,
}

#[derive(Debug, Clone)]
pub struct StmtAssign {
    pub lhs: QualifiedAccess,
    pub in_place_op: Option<InPlaceOp>,
    pub expr: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InPlaceOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    LShift,
    RShift,
}

#[derive(Debug, Default, Clone)]
pub struct Expr {
    pub id: ExprId,
    pub loc: Loc,
    pub kind: ExprKind,
}

#[derive(Debug, Default, Clone)]
pub enum ExprKind {
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

    /// A procedure call.
    ProcCall(ExprProcCall),

    /// An action invocation.
    ActionCall(ExprActionCall),

    /// An automaton instantiation.
    Instantiate(ExprInstantiate),

    /// A `has`-concept expression.
    HasConcept(ExprHasConcept),

    /// A cast expression.
    Cast(ExprCast),

    /// An `is`-type expression.
    IsTy(ExprIsTy),

    /// A unary arithmetic/logical expression.
    Unary(ExprUnary),

    /// A binary arithmetic/logical expression.
    Binary(ExprBinary),
}

#[derive(Debug, Clone)]
pub struct ExprPrimitiveLit {
    pub lit: PrimitiveLit,
}

#[derive(Debug, Clone)]
pub struct ExprArrayLit {
    pub elems: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprQualifiedAccess {
    pub access: QualifiedAccess,
}

#[derive(Debug, Clone)]
pub struct ExprPrev {
    pub access: QualifiedAccess,
}

#[derive(Debug, Clone)]
pub struct ExprProcCall {
    pub base: QualifiedAccess,
    pub generics: Vec<TyExpr>,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprActionCall {
    pub name: Name,
    pub generics: Vec<TyExpr>,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExprInstantiate {
    pub automaton: UnqualifiedTyName,
    pub generics: Vec<TyExpr>,
    pub args: Vec<ConstructorArg>,
}

#[derive(Debug, Clone)]
pub enum ConstructorArg {
    State(Expr),
    Var(Name, Expr),
}

#[derive(Debug, Clone)]
pub struct ExprHasConcept {
    pub access: QualifiedAccess,
    pub concept: Name,
}

#[derive(Debug, Clone)]
pub struct ExprCast {
    pub expr: Box<Expr>,
    pub ty_expr: TyExpr,
}

#[derive(Debug, Clone)]
pub struct ExprIsTy {
    pub expr: Box<Expr>,
    pub ty_expr: TyExpr,
}

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

#[derive(Debug, Clone)]
pub enum PrimitiveLit {
    Int(IntLit),
    Float(FloatLit),
    String(String),
    Char(u32),
    Bool(bool),
    Null,
}

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

#[derive(Debug, Clone, Copy)]
pub enum FloatLit {
    F32(f32),
    F64(f64),
}

#[derive(Debug, Default, Clone)]
pub struct QualifiedAccess {
    pub id: QualifiedAccessId,
    pub loc: Loc,
    pub kind: QualifiedAccessKind,
}

#[derive(Debug, Default, Clone)]
pub enum QualifiedAccessKind {
    #[default]
    Dummy,

    /// A plain identifier, such as `foo`.
    Name(QualifiedAccessName),

    /// A freshly-created automaton's variable, such as `A(x).foo`.
    AutomatonVar(QualifiedAccessAutomatonVar),

    /// A field of an outer entity: the `.bar` in `foo.bar`.
    Field(QualifiedAccessField),

    /// An indexed element of an outer entity: the `[42]` in `foo[42]`.
    Index(QualifiedAccessIndex),
}

#[derive(Debug, Clone)]
pub struct QualifiedAccessName {
    pub name: Name,
}

#[derive(Debug, Clone)]
pub struct QualifiedAccessAutomatonVar {
    pub automaton: Name,
    pub generics: Vec<TyExpr>,
    pub arg: Box<QualifiedAccess>,
    pub variable: Name,
}

#[derive(Debug, Clone)]
pub struct QualifiedAccessField {
    pub base: Box<QualifiedAccess>,
    pub field: Name,
}

#[derive(Debug, Clone)]
pub struct QualifiedAccessIndex {
    pub base: Box<QualifiedAccess>,
    pub index: usize,
}
