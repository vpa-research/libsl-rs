#[allow(unused_parens)]
#[allow(clippy::all)]
pub mod lexer;
#[allow(unused_imports)]
use lexer as libsllexer;

#[allow(unused_parens)]
#[allow(clippy::all)]
pub mod parser;
#[allow(unused_imports)]
use parser as libslparser;

#[allow(unused_parens)]
#[allow(clippy::all)]
pub mod parser_listener;
#[allow(unused_imports)]
use parser_listener as libslparserlistener;
