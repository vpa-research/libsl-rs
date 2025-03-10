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
    decls: SlotMap<DeclId, ()>,
    ty_exprs: SlotMap<TyExprId, ()>,
    exprs: SlotMap<ExprId, ()>,
    stmts: SlotMap<StmtId, ()>,
    qualified_accesses: SlotMap<QualifiedAccessId, ()>,
}
