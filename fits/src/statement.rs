use std::{fmt::Display, io::Write};

use serde::{Deserialize, Serialize};

use crate::{
    env::Env,
    expr::{Expr, Function, RuntimeError},
    record::Record,
    value::Value,
};

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Stmt {
    VarDef(String, Option<String>, Expr),
    Assign(String, Expr),
    TypeDef(String, Record<String>),
    FunDef(Function),
    PrintLn(Expr),
    Assert(Expr),
    Block(Vec<Stmt>),
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.pretty_print(f, 0)
    }
}

impl Stmt {
    fn pretty_print(&self, f: &mut std::fmt::Formatter<'_>, depth: usize) -> std::fmt::Result {
        match self {
            Stmt::VarDef(name, ty, e) => {
                write!(
                    f,
                    "let {name}{} = {e};",
                    ty.as_deref()
                        .map(|ty| format!(": {}", ty))
                        .unwrap_or_default()
                )
            }
            Stmt::Assign(name, e) => {
                write!(f, "{name} = {e};")
            }
            Stmt::TypeDef(name, r) => write!(f, "type {name} = {r};"),
            Stmt::FunDef(fun) => write!(f, "{fun};"),
            Stmt::PrintLn(e) => write!(f, "println({e});"),
            Stmt::Assert(e) => write!(f, "assert({e});"),
            Stmt::Block(stmts) => {
                writeln!(f, "{{")?;
                for stmt in stmts {
                    writeln!(f, "{}{}", "    ".repeat(depth), stmt)?;
                }
                writeln!(f, "}}")?;
                Ok(())
            }
        }
    }
}

/// Executes a single statement.
#[tracing::instrument(skip_all, ret)]
pub fn step(stmt: Stmt, env: &mut Env<Value>, output: &mut impl Write) -> Result<(), RuntimeError> {
    match stmt {
        // Ignore optional type annotation during execution.
        Stmt::VarDef(name, _, e) => env.put(name, e.eval(env)?),
        Stmt::Assign(name, e) => {
            // Find existing entry in env and update value
            *env.get_mut(&name)? = e.eval(env)?;
        }
        // Ignore type definitions during execution.
        Stmt::TypeDef(name, r) => {
            let r = r.map(|v| env.get(&v)).transpose()?;
            env.put(name, Value::Record(r));
        }
        Stmt::FunDef(f) => env.put(f.name.clone(), Value::Function(f)),
        Stmt::PrintLn(e) => writeln!(output, "{}", e.eval(env)?)?,
        Stmt::Assert(e) => {
            let v = e.clone().eval(env)?;
            if !matches!(v, Value::Bool(true)) {
                return Err(RuntimeError::AssertionError(e.to_string()));
            }
        }
        Stmt::Block(stmts) => {
            env.open();
            exec(stmts, env, output)?;
            env.close();
        }
    }
    Ok(())
}

/// Executes multiple statements.
pub fn exec(
    stmts: Vec<Stmt>,
    env: &mut Env<Value>,
    output: &mut impl Write,
) -> Result<(), RuntimeError> {
    for stmt in stmts {
        step(stmt, env, output)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::{
        init_logging,
        record::{Record, RecordError},
        typecheck::TypeError,
    };

    use super::*;

    #[test]
    fn variable_declaration_leaves_var_in_env() {
        init_logging();
        let mut env = Env::default();
        let stmt = Stmt::VarDef("a".to_string(), None, Expr::Int(0));
        step(stmt, &mut env, &mut std::io::stdout()).unwrap();
        assert_eq!(Value::Int(0), env.get("a").unwrap())
    }

    #[test]
    fn variable_usage_finds_var_in_env() {
        init_logging();
        let stmts = vec![
            Stmt::VarDef("a".to_string(), None, Expr::Int(0)),
            Stmt::PrintLn(Expr::Var("a".to_string())),
        ];
        exec(stmts, &mut Env::default(), &mut std::io::stdout()).unwrap();
    }

    #[test]
    fn variable_usage_does_not_find_var_in_env() {
        init_logging();
        let stmts = vec![Stmt::PrintLn(Expr::Var("a".to_string()))];
        assert_eq!(
            Err(TypeError::NotDefined("a".to_string()).into()),
            exec(stmts, &mut Env::default(), &mut std::io::stdout())
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
        assert_eq!(
            Ok(()),
            exec(program, &mut Env::default(), &mut std::io::stdout())
        );
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
            Err(TypeError::RecordError(RecordError::NoSuchField("invalid".to_string())).into()),
            exec(program, &mut Env::default(), &mut std::io::stdout())
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
            Err(TypeError::NoSuchFieldOnNonRecord("i".to_string()).into()),
            exec(program, &mut Env::default(), &mut std::io::stdout())
        );
    }

    #[test]
    fn empty_program_runs() {
        init_logging();
        exec(vec![], &mut Env::default(), &mut std::io::stdout()).unwrap();
    }

    #[test]
    fn program_with_print_runs() {
        init_logging();
        let program = vec![Stmt::PrintLn(Expr::Int(0))];
        exec(program, &mut Env::default(), &mut std::io::stdout()).unwrap();
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
                    Box::new(Expr::Call(
                        "fib".to_string(),
                        vec![Expr::Sub(
                            Box::new(Expr::Var("n".to_string())),
                            Box::new(Expr::Int(1)),
                        )],
                    )),
                    Box::new(Expr::Call(
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
        Expr::Call("fib".to_string(), vec![Expr::Int(n)])
    }

    #[test]
    fn fib_0_is_0() {
        let mut env = Env::default();
        exec(define_fibonacci(), &mut env, &mut std::io::stdout()).unwrap();
        assert_eq!(Ok(Value::Int(0)), call_fibonacci(0).eval(&env));
    }

    #[test]
    fn fib_1_is_1() {
        let mut env = Env::default();
        exec(define_fibonacci(), &mut env, &mut std::io::stdout()).unwrap();
        assert_eq!(Ok(Value::Int(1)), call_fibonacci(1).eval(&env));
    }

    #[test]
    fn fib_10_is_55() {
        let mut env = Env::default();
        exec(define_fibonacci(), &mut env, &mut std::io::stdout()).unwrap();
        assert_eq!(Ok(Value::Int(55)), call_fibonacci(10).eval(&env));
    }
}
