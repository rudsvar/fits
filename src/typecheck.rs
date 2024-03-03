use std::collections::BTreeMap;

use crate::{Expr, Fun, Record, Type};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BExpr {
    Bool(bool),
    Lt(Box<IExpr>, Box<IExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IExpr {
    Int(i128),
    Add(Box<IExpr>, Box<IExpr>),
    Sub(Box<IExpr>, Box<IExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExpr {
    String(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypedExpr {
    BExpr(BExpr),
    IExpr(IExpr),
    SExpr(SExpr),
    // Var
    Var(String, Type),
    // Record
    Record(Record<(Expr, Type)>),
    FieldAccess(Box<Expr>, String),
    // Control flow
    If(Box<BExpr>, Box<TypedExpr>, Box<TypedExpr>),
    // Functions
    Fun(String, Fun),
    FunCall(String, Vec<Expr>),
}

pub struct TyEnv {
    ty_env: BTreeMap<String, Type>,
}

pub enum TypeError {}

pub fn typecheck(e: Expr, env: &TyEnv) -> Result<TypedExpr, TypeError> {
    todo!()
}
