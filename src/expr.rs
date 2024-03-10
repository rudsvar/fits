use std::fmt::Display;

use crate::{env::Env, record::Record, value::Value, Error};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    // Unit
    Unit,
    // Bool
    Bool(bool),
    // Int
    Int(i128),
    Lt(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
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
    FunctionCall(String, Vec<Expr>),
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Unit => write!(f, "()"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Int(i) => write!(f, "{i}"),
            Expr::Lt(a, b) => write!(f, "{a} < {b}"),
            Expr::Add(a, b) => write!(f, "{a} + {b}"),
            Expr::Sub(a, b) => write!(f, "{a} - {b}"),
            Expr::Mul(a, b) => write!(f, "{a} * {b}"),
            Expr::String(s) => write!(f, "{s}"),
            Expr::Var(v) => write!(f, "{v}"),
            Expr::Record(r) => write!(f, "{r}"),
            Expr::FieldAccess(a, b) => write!(f, "{a}.{b}"),
            Expr::If(b, e1, e2) => write!(f, "if {b} then {e1} else {e2}"),
            Expr::Function(fun) => write!(f, "{fun}"),
            Expr::FunctionCall(fun, args) => {
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

/// Evaluates an expression and tries to extract the value as the specified type.
pub fn eval_as<T: TryFrom<Value, Error = Error>>(expr: Expr, env: &Env<Value>) -> Result<T, Error> {
    eval(expr, env)?.try_into()
}

#[tracing::instrument(skip_all, ret)]
pub fn eval(expr: Expr, env: &Env<Value>) -> Result<Value, Error> {
    Ok(match expr {
        Expr::Unit => Value::Unit,
        Expr::Bool(b) => Value::Bool(b),
        Expr::Int(i) => Value::Int(i),
        Expr::Lt(e1, e2) => Value::Bool(eval_as::<i128>(*e1, env)? < eval_as::<i128>(*e2, env)?),
        Expr::Add(e1, e2) => Value::Int(eval_as::<i128>(*e1, env)? + eval_as::<i128>(*e2, env)?),
        Expr::Sub(e1, e2) => Value::Int(eval_as::<i128>(*e1, env)? - eval_as::<i128>(*e2, env)?),
        Expr::Mul(e1, e2) => Value::Int(eval_as::<i128>(*e1, env)? * eval_as::<i128>(*e2, env)?),
        Expr::String(s) => Value::String(s),
        Expr::Var(v) => env.get(&v)?,
        Expr::Record(r) => Value::Record(r.map(|e| eval(e, env)).transpose()?),
        Expr::FieldAccess(e, field) => eval(*e, env)?.get_field(&field)?,
        Expr::If(b, e1, e2) => {
            if eval_as(*b, env)? {
                eval(*e1, env)?
            } else {
                eval(*e2, env)?
            }
        }
        // Nothing to evaluate until called.
        // For instance, `let x = f` doesn't evaluate `f`.
        Expr::Function(f) => Value::Function(f),
        // Evaluate arguments, evaluate fun body in env with parameters
        Expr::FunctionCall(f_name, args) => {
            tracing::info!("Evaluating function call {}({:?})", f_name, args);
            // Look up function to call
            let f = env.get(&f_name)?;
            // Check that it is a function
            let Value::Function(f) = f else {
                return Err(Error::Custom("Expected function".to_string()));
            };
            tracing::info!("{f_name} is a function");
            // Prepare function env
            let mut fun_env = env.filtered();
            for ((param_name, _), arg) in f.params.into_iter().zip(args) {
                let arg_val = eval(arg, env)?;
                fun_env.put(param_name, arg_val)?;
            }
            // Evaluate function body in new env
            eval(*f.body, &fun_env)?
        }
    })
}

#[cfg(test)]
mod tests {
    use crate::init_logging;

    use super::*;

    #[test]
    fn eval_int() {
        init_logging();
        assert_eq!(Ok(Value::Int(7)), eval(Expr::Int(7), &Env::default()));
    }

    #[test]
    fn eval_string() {
        init_logging();
        assert_eq!(
            Ok(Value::String("hello".to_string())),
            eval(Expr::String("hello".to_string()), &Env::default())
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
            eval(expr, &Env::default())
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
            eval(expr, &Env::default())
        );
    }

    #[test]
    fn two_plus_three_equals_five() {
        let expr = Expr::Add(Box::new(Expr::Int(2)), Box::new(Expr::Int(3)));
        assert_eq!(Ok(Value::Int(5)), eval(expr, &Env::default()));
    }
}
