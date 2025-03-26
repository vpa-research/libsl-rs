use std::path::PathBuf;

/// A debug tool for libsl-rs.
#[derive(clap::Parser, Debug)]
pub struct Args {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(clap::Subcommand, Debug)]
pub enum Command {
    /// Parse a file and prints its ANTLR parse tree.
    ParseTree {
        /// A path to the input LibSL file.
        path: PathBuf,
    },

    /// Split a file into tokens and print them.
    Tokens {
        /// A path to the input LibSL file.
        path: PathBuf,
    },

    /// Parse a file and convert it back to LibSL source text.
    Ouroboros {
        /// A path to the input LibSL file.
        path: PathBuf,

        /// Whether to emit a diff instead of the reformatted output.
        #[arg(short = 'd', long)]
        diff: bool,
    },

    /// Parse a file, dump back to LibSL, parse that, dump again, and compare the two dumps for
    /// equality (thus establishing that the composition of parsing and dumping is idempotent).
    CheckIdempotence {
        /// A path to the input LibSL file.
        path: PathBuf,
    },
}

pub fn parse() -> Args {
    clap::Parser::parse()
}
