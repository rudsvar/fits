use std::{fmt::Display, io::stderr, sync::OnceLock};

use env::Env;
use expr::{Expr, Function};
use record::Record;
use statement::Stmt;
use tracing_subscriber::EnvFilter;
use typecheck::Type;
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
    #[error("duplicate field: {0}")]
    DuplicateField(String),
    #[error("already defined: {0}")]
    AlreadyDefined(String),
    #[error("not defined: {0}")]
    NotDefined(String),
    #[error("not a type: {0}")]
    NotType(String),
    #[error("no such field: {0}")]
    NoSuchField(String),
    #[error("expected type {expected:?}, got {actual:?}")]
    TypeError { expected: Type, actual: Type },
    #[error("expected type {0:?}")]
    ExpectedType(Type),
    #[error("expected {expected} args, got {actual}")]
    WrongNumberOfArgs { expected: usize, actual: usize },
    #[error("parse error: {0}")]
    ParseError(#[from] nom::Err<String>),
    #[error("{0}")]
    Custom(String),
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
    stmts: Vec<Stmt>,
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }
        Ok(())
    }
}

pub fn parse(input: &str) -> Result<Program, nom::Err<String>> {
    let (_, program) = parse::program(input).map_err(|e| e.map(|s| s.to_string()))?;
    Ok(program)
}

pub fn typecheck(program: &Program) -> Result<(), Error> {
    typecheck::typecheck_stmts(&program.stmts, &mut Env::default())
}

pub fn execute(program: Program) -> Result<(), Error> {
    statement::exec(program.stmts, &mut Env::default())
}

pub fn run(input: &str) -> Result<(), Error> {
    let program = parse(input)?;
    typecheck(&program)?;
    execute(program)?;
    Ok(())
}
