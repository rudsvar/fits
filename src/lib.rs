use std::{io::stderr, sync::OnceLock};

use env::Env;
use expr::{Expr, Function};
use record::Record;
use statement::Stmt;
use tracing_subscriber::EnvFilter;
use typecheck::Type;
use value::Value;

pub mod env;
pub mod expr;
pub mod record;
pub mod statement;
pub mod typecheck;
pub mod value;

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    DuplicateField(String),
    AlreadyDefined(String),
    NotDefined(String),
    NotType(String),
    NoSuchField(String),
    TypeError { expected: Type, actual: Type },
    ExpectedType(Type),
    WrongNumberOfArgs { expected: usize, actual: usize },
    Custom(String),
}

pub struct Program {
    stmts: Vec<Stmt>,
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

pub fn run(program: Program) -> Result<(), Error> {
    typecheck::typecheck_stmts(&program.stmts, &mut Env::default())?;
    statement::exec(program.stmts, &mut Env::default())?;
    Ok(())
}
