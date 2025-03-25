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

    /// Parse a file, convert it back to LibSL source text, and diff it against the input.
    Ouroboros {
        /// A path to the input LibSL file.
        path: PathBuf,
    },
}

pub fn parse() -> Args {
    clap::Parser::parse()
}
