use std::{fmt::Display, io::stderr, sync::OnceLock};

use env::Env;
use expr::{Expr, Function, RuntimeError};
use parse::ParseError;
use record::Record;
use statement::Stmt;
use tracing_subscriber::EnvFilter;
use typecheck::TypeError;
use value::Value;

pub mod env;
pub mod expr;
pub mod parse;
pub mod parse2;
pub mod record;
pub mod statement;
pub mod typecheck;
pub mod value;

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum Error {
    #[error("{0}")]
    ParseError(#[from] ParseError),
    #[error("{0}")]
    TypeError(#[from] TypeError),
    #[error("{0}")]
    RuntimeError(#[from] RuntimeError),
}

pub fn init_logging() {
    static LOGGING: OnceLock<()> = OnceLock::new();
    LOGGING.get_or_init(|| {
        tracing_subscriber::fmt()
            .with_writer(stderr)
            .with_env_filter(EnvFilter::from_default_env())
            .init()
    });
}

#[derive(Debug, PartialEq, Eq)]
pub struct Program {
    pub stmts: Vec<Stmt>,
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

pub fn parse(input: &str) -> Result<Program, ParseError> {
    let (_, program) = parse::program(input)?;
    Ok(program)
}

pub fn typecheck(program: &Program) -> Result<(), TypeError> {
    typecheck::typecheck_stmts(&program.stmts, &mut Env::default())
}

pub fn execute(program: Program) -> Result<(), RuntimeError> {
    statement::exec(program.stmts, &mut Env::default())
}

pub fn run(input: &str) -> Result<(), Error> {
    let program = parse(input)?;
    typecheck(&program)?;
    execute(program)?;
    Ok(())
}
