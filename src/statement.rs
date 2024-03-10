use std::fmt::Display;

use crate::{
    env::Env,
    expr::{eval, Expr, Function},
    record::Record,
    value::Value,
    Error,
};

#[derive(Debug, PartialEq, Eq)]
pub enum Stmt {
    VarDef(String, Option<String>, Expr),
    TypeDef(String, Record<String>),
    FunDef(Function),
    PrintLn(Expr),
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::VarDef(name, ty, e) => {
                write!(f, "let {name}{} = {e};", ty.as_deref().unwrap_or_default())
            }
            Stmt::TypeDef(name, r) => write!(f, "type {name} = {r};"),
            Stmt::FunDef(fun) => write!(f, "{fun};"),
            Stmt::PrintLn(e) => write!(f, "println({e});"),
        }
    }
}

/// Executes a single statement.
#[tracing::instrument(skip_all, ret)]
pub fn step(stmt: Stmt, env: &mut Env<Value>) -> Result<(), Error> {
    match stmt {
        // Ignore optional type annotation during execution.
        Stmt::VarDef(name, _, e) => env.put(name, eval(e, env)?)?,
        // Ignore type definitions during execution.
        Stmt::TypeDef(name, r) => {
            let r = r.map(|v| env.get(&v)).transpose()?;
            env.put(name, Value::Record(r))?;
        }
        Stmt::FunDef(f) => env.put(f.name.clone(), Value::Function(f))?,
        Stmt::PrintLn(e) => println!("{}", eval(e, env)?),
    }
    Ok(())
}

/// Executes multiple statements.
pub fn exec(stmts: Vec<Stmt>, env: &mut Env<Value>) -> Result<(), Error> {
    for stmt in stmts {
        step(stmt, env)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{init_logging, record::Record};

    use super::*;

    #[test]
    fn variable_declaration_leaves_var_in_env() {
        init_logging();
        let mut env = Env::default();
        let stmt = Stmt::VarDef("a".to_string(), None, Expr::Int(0));
        step(stmt, &mut env).unwrap();
        assert_eq!(Value::Int(0), env.get("a").unwrap())
    }

    #[test]
    fn variable_usage_finds_var_in_env() {
        init_logging();
        let stmts = vec![
            Stmt::VarDef("a".to_string(), None, Expr::Int(0)),
            Stmt::PrintLn(Expr::Var("a".to_string())),
        ];
        exec(stmts, &mut Env::default()).unwrap();
    }

    #[test]
    fn variable_usage_does_not_find_var_in_env() {
        init_logging();
        let stmts = vec![Stmt::PrintLn(Expr::Var("a".to_string()))];
        assert_eq!(
            Err(Error::NotDefined("a".to_string())),
            exec(stmts, &mut Env::default())
        );
    }

    #[test]
    fn can_access_field_of_record() {
        let program = vec![
            Stmt::TypeDef(
                "Foo".to_string(),
                Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), "Int".to_string());
                        fields.insert("s".to_string(), "String".to_string());
                        fields
                    },
                },
            ),
            Stmt::VarDef(
                "foo".to_string(),
                Some("Foo".to_string()),
                Expr::Record(Record {
                    fields: vec![
                        ("i".to_string(), Expr::Int(5)),
                        ("s".to_string(), Expr::String("hello".to_string())),
                    ]
                    .into_iter()
                    .collect(),
                }),
            ),
            Stmt::PrintLn(Expr::FieldAccess(
                Box::new(Expr::Var("foo".to_string())),
                "i".to_string(),
            )),
        ];
        assert_eq!(Ok(()), exec(program, &mut Env::default()));
    }

    #[test]
    fn cannot_access_invalid_field_of_record() {
        let program = vec![
            Stmt::TypeDef(
                "Foo".to_string(),
                Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), "Int".to_string());
                        fields.insert("s".to_string(), "String".to_string());
                        fields
                    },
                },
            ),
            Stmt::VarDef(
                "foo".to_string(),
                Some("Foo".to_string()),
                Expr::Record(Record {
                    fields: vec![
                        ("i".to_string(), Expr::Int(5)),
                        ("s".to_string(), Expr::String("hello".to_string())),
                    ]
                    .into_iter()
                    .collect(),
                }),
            ),
            Stmt::PrintLn(Expr::FieldAccess(
                Box::new(Expr::Var("foo".to_string())),
                "invalid".to_string(),
            )),
        ];
        assert_eq!(
            Err(Error::NoSuchField("invalid".to_string())),
            exec(program, &mut Env::default())
        );
    }

    #[test]
    fn cannot_access_field_of_int() {
        init_logging();
        let program = vec![Stmt::PrintLn(Expr::FieldAccess(
            Box::new(Expr::Int(0)),
            "i".to_string(),
        ))];
        assert_eq!(
            Err(Error::NoSuchField("i".to_string())),
            exec(program, &mut Env::default())
        );
    }

    #[test]
    fn empty_program_runs() {
        init_logging();
        exec(vec![], &mut Env::default()).unwrap();
    }

    #[test]
    fn program_with_print_runs() {
        init_logging();
        let program = vec![Stmt::PrintLn(Expr::Int(0))];
        exec(program, &mut Env::default()).unwrap();
    }

    fn define_fibonacci() -> Vec<Stmt> {
        vec![Stmt::FunDef(Function {
            name: "fib".to_string(),
            params: vec![("n".to_string(), "Int".to_string())],
            return_ty: "Int".to_string(),
            body: Box::new(Expr::If(
                // If n < 2
                Box::new(Expr::Lt(
                    Box::new(Expr::Var("n".to_string())),
                    Box::new(Expr::Int(2)),
                )),
                // evaluate to n
                Box::new(Expr::Var("n".to_string())),
                // else evaluate to fib(n-1) + fib(n-1)
                Box::new(Expr::Add(
                    Box::new(Expr::FunctionCall(
                        "fib".to_string(),
                        vec![Expr::Sub(
                            Box::new(Expr::Var("n".to_string())),
                            Box::new(Expr::Int(1)),
                        )],
                    )),
                    Box::new(Expr::FunctionCall(
                        "fib".to_string(),
                        vec![Expr::Sub(
                            Box::new(Expr::Var("n".to_string())),
                            Box::new(Expr::Int(2)),
                        )],
                    )),
                )),
            )),
        })]
    }

    fn call_fibonacci(n: i128) -> Expr {
        Expr::FunctionCall("fib".to_string(), vec![Expr::Int(n)])
    }

    #[test]
    fn fib_0_is_0() {
        let mut env = Env::default();
        exec(define_fibonacci(), &mut env).unwrap();
        assert_eq!(Ok(Value::Int(0)), eval(call_fibonacci(0), &env));
    }

    #[test]
    fn fib_1_is_1() {
        let mut env = Env::default();
        exec(define_fibonacci(), &mut env).unwrap();
        assert_eq!(Ok(Value::Int(1)), eval(call_fibonacci(1), &env));
    }

    #[test]
    fn fib_10_is_55() {
        let mut env = Env::default();
        exec(define_fibonacci(), &mut env).unwrap();
        assert_eq!(Ok(Value::Int(55)), eval(call_fibonacci(10), &env));
    }
}
