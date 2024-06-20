use std::fmt::Display;

use serde::{Deserialize, Serialize};

use crate::{env::Env, record::Record, typecheck::TypeError, value::Value};

#[derive(Debug, thiserror::Error)]
pub enum RuntimeError {
    #[error("dynamic type error: {0}")]
    TypeError(#[from] TypeError),
    #[error("assertion error: {0}")]
    AssertionError(String),
    #[error("io error: {0}")]
    IoError(#[from] std::io::Error),
}

impl PartialEq for RuntimeError {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RuntimeError::TypeError(a), RuntimeError::TypeError(b)) => a == b,
            (RuntimeError::AssertionError(a), RuntimeError::AssertionError(b)) => a == b,
            (RuntimeError::IoError(a), RuntimeError::IoError(b)) => a.to_string() == b.to_string(),
            _ => false,
        }
    }
}

impl Eq for RuntimeError {}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Function {
    pub name: String,
    pub params: Vec<(String, String)>,
    pub return_ty: String,
    pub body: Box<Expr>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (name, ty) in &self.params {
            write!(f, "{name}: {ty}")?;
        }
        write!(f, "): {} = {}", self.return_ty, self.body)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Expr {
    // Unit
    Unit,
    // Bool
    Bool(bool),
    Lt(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Neq(Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    // Int
    Int(i128),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
    // String
    String(String),
    // Var
    Var(String),
    // Record
    Record(Record<Expr>),
    FieldAccess(Box<Expr>, String),
    // Control flow
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    // Functions
    Function(Function),
    Call(String, Vec<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Unit => write!(f, "()"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Int(i) => write!(f, "{i}"),
            Expr::Lt(a, b) => write!(f, "{a} < {b}"),
            Expr::Eq(a, b) => write!(f, "{a} == {b}"),
            Expr::Neq(a, b) => write!(f, "{a} != {b}"),
            Expr::And(a, b) => write!(f, "{a} && {b}"),
            Expr::Add(a, b) => write!(f, "{a} + {b}"),
            Expr::Sub(a, b) => write!(f, "{a} - {b}"),
            Expr::Mul(a, b) => write!(f, "{a} * {b}"),
            Expr::Mod(a, b) => write!(f, "{a} % {b}"),
            Expr::String(s) => write!(f, "{s}"),
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Record(r) => write!(f, "{r}"),
            Expr::FieldAccess(a, b) => write!(f, "{a}.{b}"),
            Expr::If(b, e1, e2) => write!(f, "if {b} then {e1} else {e2}"),
            Expr::Function(fun) => write!(f, "{fun}"),
            Expr::Call(fun, args) => {
                let args = args
                    .iter()
                    .map(|e| e.to_string())
                    .collect::<Vec<_>>()
                    .join(",");
                write!(f, "{fun}({})", args)
            }
        }
    }
}

impl Expr {
    /// Evaluates an expression and tries to extract the value as the specified type.
    pub fn eval_as<T: TryFrom<Value, Error = TypeError>>(
        self,
        env: &Env<Value>,
    ) -> Result<T, RuntimeError> {
        let value = self.eval(env)?;
        Ok(value.try_into()?)
    }

    #[tracing::instrument(skip_all, ret)]
    pub fn eval(self, env: &Env<Value>) -> Result<Value, RuntimeError> {
        Ok(match self {
            Expr::Unit => Value::Unit,
            Expr::Bool(b) => Value::Bool(b),
            Expr::Lt(e1, e2) => Value::Bool(e1.eval_as::<i128>(env)? < e2.eval_as::<i128>(env)?),
            Expr::Eq(e1, e2) => Value::Bool(e1.eval(env)? == e2.eval(env)?),
            Expr::Neq(e1, e2) => Value::Bool(e1.eval(env)? != e2.eval(env)?),
            Expr::And(e1, e2) => Value::Bool(e1.eval_as::<bool>(env)? && e2.eval_as::<bool>(env)?),
            Expr::Int(i) => Value::Int(i),
            Expr::Add(e1, e2) => Value::Int(e1.eval_as::<i128>(env)? + e2.eval_as::<i128>(env)?),
            Expr::Sub(e1, e2) => Value::Int(e1.eval_as::<i128>(env)? - e2.eval_as::<i128>(env)?),
            Expr::Mul(e1, e2) => Value::Int(e1.eval_as::<i128>(env)? * e2.eval_as::<i128>(env)?),
            Expr::Mod(e1, e2) => Value::Int(e1.eval_as::<i128>(env)? % e2.eval_as::<i128>(env)?),
            Expr::String(s) => Value::String(s),
            Expr::Var(v) => env.get(&v)?,
            Expr::Record(r) => Value::Record(r.map(|e| e.eval(env)).transpose()?),
            Expr::FieldAccess(e, field) => e.eval(env)?.get_field(&field)?,
            Expr::If(b, e1, e2) => {
                if b.eval_as(env)? {
                    e1.eval(env)?
                } else {
                    e2.eval(env)?
                }
            }
            // Nothing to evaluate until called.
            // For instance, `let x = f` doesn't evaluate `f`.
            Expr::Function(f) => Value::Function(f),
            // Evaluate arguments, evaluate fun body in env with parameters
            Expr::Call(f_name, args) => {
                tracing::info!("Evaluating function call {}({:?})", f_name, args);
                // Look up function to call
                let f = env.get(&f_name)?;
                // Check that it is a function
                let Value::Function(f) = f else {
                    return Err(TypeError::Custom("Expected function".to_string()))?;
                };
                tracing::info!("{f_name} is a function");
                // Prepare function env
                let mut fun_env = env.filtered();
                for ((param_name, _), arg) in f.params.into_iter().zip(args) {
                    let arg_val = arg.eval(env)?;
                    fun_env.put(param_name, arg_val);
                }
                // Evaluate function body in new env
                f.body.eval(&fun_env)?
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::init_logging;

    use super::*;

    #[test]
    fn eval_int() {
        init_logging();
        assert_eq!(Ok(Value::Int(7)), Expr::Int(7).eval(&Env::default()));
    }

    #[test]
    fn eval_string() {
        init_logging();
        assert_eq!(
            Ok(Value::String("hello".to_string())),
            Expr::String("hello".to_string()).eval(&Env::default())
        );
    }
    #[test]
    fn if_three_lt_five_gives_yes() {
        let expr = Expr::If(
            Box::new(Expr::Lt(Box::new(Expr::Int(3)), Box::new(Expr::Int(5)))),
            Box::new(Expr::String("yes".to_string())),
            Box::new(Expr::String("no".to_string())),
        );
        assert_eq!(
            Ok(Value::String("yes".to_string())),
            expr.eval(&Env::default())
        );
    }

    #[test]
    fn if_five_lt_three_gives_no() {
        let expr = Expr::If(
            Box::new(Expr::Lt(Box::new(Expr::Int(5)), Box::new(Expr::Int(3)))),
            Box::new(Expr::String("yes".to_string())),
            Box::new(Expr::String("no".to_string())),
        );
        assert_eq!(
            Ok(Value::String("no".to_string())),
            expr.eval(&Env::default())
        );
    }

    #[test]
    fn two_plus_three_equals_five() {
        let expr = Expr::Add(Box::new(Expr::Int(2)), Box::new(Expr::Int(3)));
        assert_eq!(Ok(Value::Int(5)), expr.eval(&Env::default()));
    }
}
