use slotmap::{new_key_type, SlotMap};

pub mod ast;
pub mod grammar;
pub mod loc;
mod parse;

new_key_type! {
    pub struct DeclId;
    pub struct TyExprId;
    pub struct ExprId;
    pub struct StmtId;
    pub struct QualifiedAccessId;
}

#[derive(Clone)]
pub struct LibSl {
    file_names: Vec<String>,
    pub decls: SlotMap<DeclId, ast::Decl>,
    pub ty_exprs: SlotMap<TyExprId, ast::TyExpr>,
    pub exprs: SlotMap<ExprId, ast::Expr>,
    pub stmts: SlotMap<StmtId, ast::Stmt>,
    pub qualified_accesses: SlotMap<QualifiedAccessId, ast::QualifiedAccess>,
}
