//! A raw LibSL parser generated from the ANTLR grammar.
//!
//! [`LibSl::parse_file`][crate::LibSl::parse_file] uses this to construct an initial parse tree.
//! In most cases, you'll want to use that method instead of this module, as you get an AST that's
//! much easier to work with.
#![allow(missing_docs)]
#![allow(missing_debug_implementations)]

include!(concat!(env!("OUT_DIR"), "/grammar/mod.rs"));

pub use libsllexer as lexer;
pub use libslparser as parser;
pub use libslparserlistener as parser_listener;
