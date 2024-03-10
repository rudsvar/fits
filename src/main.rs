use std::{error::Error, path::PathBuf};

use clap::Parser;

#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Clone, Parser)]
enum Command {
    /// Print the AST of a program.
    Parse {
        /// The file to process.
        path: PathBuf,
    },
    /// Typecheck a program.
    #[clap(alias = "tc")]
    TypeCheck {
        /// The file to process.
        path: PathBuf,
    },
    /// Run a program.
    Run {
        /// The file to process.
        path: PathBuf,
    },
    /// Format a program.
    #[clap(alias = "fmt")]
    Format {
        /// The file to process.
        path: PathBuf,
        #[clap(short)]
        in_place: bool,
    },
}

fn main() -> Result<(), Box<dyn Error>> {
    fits::init_logging();

    let args = Args::parse();

    match args.command {
        Command::Parse { path } => {
            let input = std::fs::read_to_string(path)?;
            let program = fits::parse(&input)?;
            println!("{:#?}", program);
        }
        Command::TypeCheck { path } => {
            let input = std::fs::read_to_string(path)?;
            let program = fits::parse(&input)?;
            fits::typecheck(&program)?;
        }
        Command::Run { path } => {
            let input = std::fs::read_to_string(path)?;
            fits::run(&input)?;
        }
        Command::Format { path, in_place } => {
            let input = std::fs::read_to_string(&path)?;
            let program = fits::parse(&input)?;
            let pretty = program.to_string();
            let program2 = fits::parse(&pretty)?;
            if program != program2 {
                eprintln!("bug: AST changed after formatting");
                std::process::exit(1);
            }
            if in_place {
                std::fs::write(path, pretty)?;
            } else {
                print!("{}", pretty);
            }
        }
    }

    Ok(())
}
