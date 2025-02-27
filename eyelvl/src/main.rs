use std::fmt::Write;
use std::fs;
use std::path::PathBuf;

use antlr_rust::{InputStream, Parser};
use antlr_rust::common_token_stream::CommonTokenStream;
use antlr_rust::token::Token;
use antlr_rust::tree::{ErrorNode, ParseTreeListener, TerminalNode};
use args::Command;
use color_eyre::eyre::{Context, Result, eyre};
use libsl::grammar::lexer::{LibSLLexer, LocalTokenFactory};
use libsl::grammar::parser::{LibSLParser, LibSLParserContext, LibSLParserContextType};
use libsl::grammar::parser_listener::LibSLParserListener;

mod args;

#[derive(Default)]
struct PrintListener {
    level: usize,
}

impl PrintListener {
    fn print_indent(&self) {
        for _ in 0..self.level {
            print!("  ");
        }
    }
}

// Making it explicit so that `printer-java` would have the same format.
fn escape_str(s: &str) -> String {
    let mut result = "\"".to_owned();

    for c in s.chars() {
        match c {
            '\0' => result.push_str("\\0"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            '"' | '\\' => {
                result.push('\\');
                result.push(c);
            }
            '\0'..' ' | '\x7f' => write!(result, "\\x{:02x}", c as u32).unwrap(),
            _ => result.push(c),
        }
    }

    result.push('"');

    result
}

impl<'input> ParseTreeListener<'input, LibSLParserContextType> for PrintListener {
    fn visit_terminal(&mut self, node: &TerminalNode<'input, LibSLParserContextType>) {
        self.print_indent();
        println!("Terminal {} {}", node.symbol, escape_str(node.symbol.get_text()));
    }

    fn enter_every_rule(&mut self, ctx: &(dyn LibSLParserContext<'input> + 'input)) {
        self.print_indent();
        println!(
            "Entered rule `{}`",
            libsl::grammar::parser::ruleNames
                .get(ctx.get_rule_index())
                .copied()
                .unwrap_or("error"),
        );

        self.level += 1;
    }

    fn exit_every_rule(&mut self, _ctx: &(dyn LibSLParserContext<'input> + 'input)) {
        self.level -= 1;
    }

    fn visit_error_node(&mut self, node: &ErrorNode<'input, LibSLParserContextType>) {
        self.print_indent();
        println!("Entered an error node: {}", node.symbol);
    }
}

impl LibSLParserListener<'_> for PrintListener {}

fn print_parse_tree(path: PathBuf) -> Result<()> {
    let contents = fs::read_to_string(&path)
        .with_context(|| format!("could not read `{}`", path.display()))?;
    let input_stream = InputStream::new(contents.as_str());
    let tf = LocalTokenFactory::default();
    let lexer = LibSLLexer::new_with_token_factory(input_stream, &tf);
    let token_stream = CommonTokenStream::new(lexer);
    let mut parser = LibSLParser::new(token_stream);
    parser.add_parse_listener(Box::new(PrintListener::default()));
    parser.remove_error_listeners();
    parser.build_parse_trees = false;
    parser
        .file()
        .map_err(|e| eyre!("could not parse `{}`: {e}", path.display()))?;

    Ok(())
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let args = args::parse();

    match args.command {
        Command::ParseTree { path } => print_parse_tree(path),
    }
}
