use std::fmt::{self, Display, Write};
use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use antlr_rust::common_token_stream::CommonTokenStream;
use antlr_rust::token::{TOKEN_EOF, Token};
use antlr_rust::tree::{ErrorNode, ParseTreeListener, TerminalNode};
use antlr_rust::{InputStream, Parser, TokenSource};
use args::Command;
use color_eyre::eyre::{Context, Result, eyre};
use libsl::LibSl;
use libsl::grammar::lexer::LibSLLexer;
use libsl::grammar::parser::{LibSLParser, LibSLParserContext, LibSLParserContextType};
use libsl::grammar::parser_listener::LibSLParserListener;
use similar::{ChangeTag, TextDiff};
use yansi::{Paint, Style};

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

fn print_diff(old: &str, new: &str) {
    struct LineNr(Option<usize>, usize);

    impl Display for LineNr {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.0 {
                Some(n) => write!(f, "{:>width$}", n + 1, width = self.1),
                None => write!(f, "{:width$}", "", width = self.1),
            }
        }
    }

    let diff = TextDiff::configure()
        .algorithm(similar::Algorithm::Patience)
        .diff_lines(old, new);

    let old_lines = old.split('\n').count();
    let new_lines = new.split('\n').count();

    let old_line_nr_width = old_lines.ilog10() + 1;
    let new_line_nr_width = new_lines.ilog10() + 1;

    for change in diff.iter_all_changes() {
        let (sign, style) = match change.tag() {
            ChangeTag::Equal => (" ", Style::new().dim()),
            ChangeTag::Delete => ("-", Style::new().red()),
            ChangeTag::Insert => ("+", Style::new().green()),
        };

        let line = change.to_string_lossy();
        let line = line.trim_end_matches('\n');
        let ws_start = line
            .rfind(|c: char| !c.is_whitespace())
            .map(|idx| idx + 1)
            .unwrap_or(0);

        println!(
            "{} {} |{}{}{}",
            LineNr(change.old_index(), old_line_nr_width as usize).paint(style),
            LineNr(change.new_index(), new_line_nr_width as usize).paint(style),
            sign.paint(style),
            line[..ws_start].paint(style),
            line[ws_start..].paint(style.invert()),
        );
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
        println!(
            "Terminal {} {}",
            node.symbol,
            escape_str(node.symbol.get_text())
        );
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
    let lexer = LibSLLexer::new(input_stream);
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

fn print_tokens(path: PathBuf) -> Result<()> {
    let contents = fs::read_to_string(&path)
        .with_context(|| format!("could not read `{}`", path.display()))?;
    let input_stream = InputStream::new(contents.as_str());
    let mut lexer = LibSLLexer::new(input_stream);

    for idx in 0.. {
        let token = lexer.next_token();
        println!(
            "Token {idx}: channel {}, type {}, {token}",
            usize::try_from(token.get_channel())
                .ok()
                .and_then(|idx| libsl::grammar::lexer::channelNames.get(idx).copied())
                .unwrap_or("[unknown]"),
            lexer
                .get_vocabulary()
                .get_symbolic_name(token.get_token_type())
                .unwrap_or("[unknown]"),
        );

        if token.get_token_type() == TOKEN_EOF {
            break;
        }
    }

    Ok(())
}

fn ouroboros(path: PathBuf, emit_diff: bool) -> Result<()> {
    let contents = fs::read_to_string(&path)
        .with_context(|| format!("could not read `{}`", path.display()))?;
    let mut libsl = LibSl::new();
    let file = libsl
        .parse_file(path.display().to_string(), &contents)
        .with_context(|| eyre!("could not parse `{}`", path.display()))?;
    let dump = file.display(&libsl).to_string();

    if !emit_diff {
        println!("{dump}");

        return Ok(());
    }

    print_diff(&contents, &dump);

    Ok(())
}

fn check_idempotence(path: PathBuf) -> Result<ExitCode> {
    let contents = fs::read_to_string(&path)
        .with_context(|| format!("could not read `{}`", path.display()))?;
    let mut libsl = LibSl::new();
    let first_dump = libsl
        .parse_file(path.display().to_string(), &contents)
        .with_context(|| eyre!("could not parse `{}`", path.display()))?
        .display(&libsl)
        .to_string();
    let second_dump = libsl
        .parse_file(path.display().to_string(), &contents)
        .context("could not parse the first dump")?
        .display(&libsl)
        .to_string();

    if first_dump == second_dump {
        println!("{}", "The dumps are equal".bright_green());

        return Ok(ExitCode::SUCCESS);
    }

    println!("{}", "The dumps differ!".bright_red());
    print_diff(&first_dump, &second_dump);

    Ok(ExitCode::FAILURE)
}

fn main() -> ExitCode {
    color_eyre::install().unwrap();

    let args = args::parse();

    match match args.command {
        Command::ParseTree { path } => print_parse_tree(path).map(|_| ExitCode::SUCCESS),
        Command::Tokens { path } => print_tokens(path).map(|_| ExitCode::SUCCESS),
        Command::Ouroboros { path, diff } => ouroboros(path, diff).map(|_| ExitCode::SUCCESS),
        Command::CheckIdempotence { path } => check_idempotence(path),
    } {
        Ok(code) => code,

        Err(e) => {
            eprintln!("{e:?}");

            ExitCode::FAILURE
        }
    }
}
