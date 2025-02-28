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

    /// Splits a file into tokens and prints them.
    Tokens {
        /// A path to the input LibSL file.
        path: PathBuf,
    }
}

pub fn parse() -> Args {
    clap::Parser::parse()
}
