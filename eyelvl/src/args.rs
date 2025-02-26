use std::path::PathBuf;

/// A debug tool for libsl-rs.
#[derive(clap::Parser, Debug)]
pub struct Args {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(clap::Subcommand, Debug)]
pub enum Command {
    ParseTree {
        /// A path to the input LibSL file.
        path: PathBuf,
    },
}

pub fn parse() -> Args {
    clap::Parser::parse()
}
