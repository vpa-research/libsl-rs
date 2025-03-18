use loc::FileId;
use slotmap::{SlotMap, new_key_type};

pub mod ast;
pub mod dump;
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

#[derive(Debug, Clone)]
pub struct LibSl {
    file_names: Vec<String>,
    pub decls: SlotMap<DeclId, ast::Decl>,
    pub ty_exprs: SlotMap<TyExprId, ast::TyExpr>,
    pub exprs: SlotMap<ExprId, ast::Expr>,
    pub stmts: SlotMap<StmtId, ast::Stmt>,
    pub qualified_accesses: SlotMap<QualifiedAccessId, ast::QualifiedAccess>,
}

impl LibSl {
    pub fn filename_by_id(&self, id: FileId) -> &str {
        &self.file_names[id.0]
    }
}
