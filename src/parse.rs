use std::cell::RefCell;
use std::num::NonZeroUsize;
use std::rc::Rc;

use antlr_rust::common_token_stream::CommonTokenStream;
use antlr_rust::error_listener::ErrorListener;
use antlr_rust::errors::ANTLRError;
use antlr_rust::parser_rule_context::ParserRuleContext;
use antlr_rust::token::CommonToken;
use antlr_rust::token_factory::TokenFactory;
use antlr_rust::{InputStream, Parser};
use thiserror::Error;

use crate::grammar::lexer::LibSLLexer;
use crate::grammar::libslparser::{FileContextAttrs, GlobalStatementContextAll, HeaderContextAll};
use crate::grammar::parser::{FileContextAll, LibSLParser};
use crate::loc::{Loc, Span};
use crate::{LibSl, ast};

pub type Result<T, E = ParseError> = std::result::Result<T, E>;

fn strip_surrounding(s: &str, prefix: char, suffix: char) -> &str {
    s.strip_prefix(prefix)
        .and_then(|s| s.strip_suffix(suffix))
        .unwrap_or(s)
}

fn parse_string_lit(token: &CommonToken<'_>) -> String {
    strip_surrounding(&token.text, '"', '"').into()
}

fn parse_ident(token: &CommonToken<'_>) -> String {
    strip_surrounding(&token.text, '`', '`').into()
}

#[derive(Error, Debug, Clone)]
pub enum ParseError {
    #[error("encountered a syntax error at L{line}:{column}: {msg}")]
    SyntaxError {
        line: isize,
        column: isize,
        msg: String,
    },
}

#[derive(Debug, Clone)]
struct ErrorCollector(Rc<RefCell<Vec<ParseError>>>);

impl ErrorCollector {
    fn new() -> (Self, Rc<RefCell<Vec<ParseError>>>) {
        let errors: Rc<RefCell<Vec<ParseError>>> = Default::default();

        (Self(errors.clone()), errors)
    }
}

impl<'input, T: Parser<'input>> ErrorListener<'input, T> for ErrorCollector {
    fn syntax_error(
        &self,
        _recognizer: &T,
        _offending_symbol: Option<&<<T>::TF as TokenFactory<'input>>::Inner>,
        line: isize,
        column: isize,
        msg: &str,
        _error: Option<&ANTLRError>,
    ) {
        self.0.borrow_mut().push(ParseError::SyntaxError {
            line,
            column,
            msg: msg.into(),
        });
    }
}

impl LibSl {
    pub fn parse_file(&mut self, file_name: String, contents: &str) -> Result<ast::File> {
        let input_stream = InputStream::new(contents);
        let lexer = LibSLLexer::new(input_stream);
        let token_stream = CommonTokenStream::new(lexer);
        let mut parser = LibSLParser::new(token_stream);
        parser.remove_error_listeners();
        let (error_listener, errors) = ErrorCollector::new();
        parser.add_error_listener(Box::new(error_listener));

        let tree = match parser.file() {
            Ok(tree) => tree,

            Err(e) => {
                let mut errors = errors.borrow_mut();

                if errors.is_empty() {
                    // the error listener didn't get a call but we still ended up with an error.
                    // we'll assume it's an internal error and panic.
                    panic!(
                        "got an error parsing `{file_name}` with no errors collected by the listener: {e}"
                    );
                }

                return Err(errors.swap_remove(0));
            }
        };

        AstConstructor::new(self, file_name).construct(&tree)
    }
}

struct AstConstructor<'a> {
    libsl: &'a mut LibSl,
    file_idx: usize,
}

impl<'a> AstConstructor<'a> {
    fn new(libsl: &'a mut LibSl, file_name: String) -> Self {
        let file_idx = libsl.file_names.len();
        libsl.file_names.push(file_name);

        Self { libsl, file_idx }
    }

    fn get_loc(&self, start: &CommonToken<'_>, stop: &CommonToken<'_>) -> Loc {
        let line = (start.line > 0).then_some(NonZeroUsize::new(start.line as usize).unwrap());
        let col = (start.column > 0).then_some(NonZeroUsize::new(start.column as usize).unwrap());

        Span {
            start: start.start as usize,
            len: (stop.stop as usize).saturating_sub(start.start as usize),
            file: self.file_idx,
            line,
            col,
        }
        .into()
    }

    fn construct(mut self, tree: &FileContextAll<'_>) -> Result<ast::File> {
        let loc = self.get_loc(&tree.start(), &tree.stop());
        let header = tree
            .header()
            .map(|header| self.process_header(&header))
            .transpose()?;
        let decls = tree
            .globalStatement_all()
            .into_iter()
            .map(|gs| self.process_global_stmt(&gs))
            .collect::<Result<Vec<_>>>()?;

        Ok(ast::File { loc, header, decls })
    }

    fn process_header(&mut self, ctx: &HeaderContextAll<'_>) -> Result<ast::Header> {
        let loc = self.get_loc(&ctx.start(), &ctx.stop());

        let libsl_version = ctx
            .lslver
            .as_ref()
            .map(|t| parse_string_lit(t))
            .unwrap_or_default();
        let library_name = ctx
            .libraryName
            .as_ref()
            .map(|t| parse_ident(t))
            .unwrap_or_default();
        let version = ctx.ver.as_ref().map(|t| parse_string_lit(t));
        let language = ctx.lang.as_ref().map(|t| parse_string_lit(t));
        let url = ctx.link.as_ref().map(|t| parse_string_lit(t));

        Ok(ast::Header {
            loc,
            libsl_version,
            library_name,
            version,
            language,
            url,
        })
    }

    fn process_global_stmt(&mut self, ctx: &GlobalStatementContextAll<'_>) -> Result<ast::Decl> {
        todo!()
    }
}
