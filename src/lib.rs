use std::{collections::BTreeMap, io::stderr, sync::OnceLock};

use env::Env;
use tracing_subscriber::EnvFilter;
use typecheck::Type;
use value::Value;

pub mod env;
pub mod expr;
pub mod typecheck;
pub mod value;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record<T> {
    fields: BTreeMap<String, T>,
}

impl<T> Default for Record<T> {
    fn default() -> Self {
        Self {
            fields: BTreeMap::default(),
        }
    }
}

impl<T: Clone> Record<T> {
    pub fn put(&mut self, field: String, value: T) -> Result<(), Error> {
        if self.fields.contains_key(&field) {
            return Err(Error::DuplicateField(field));
        }
        self.fields.insert(field, value);
        Ok(())
    }

    pub fn get(&self, field: &str) -> Result<T, Error> {
        self.fields
            .get(field)
            .cloned()
            .ok_or_else(|| Error::NoSuchField(field.to_string()))
    }
}

impl<T> Record<T> {
    pub fn as_ref(&self) -> Record<&T> {
        Record {
            fields: self.fields.iter().map(|(k, v)| (k.clone(), v)).collect(),
        }
    }
    pub fn map<U: PartialEq, F: Fn(T) -> U>(self, f: F) -> Record<U> {
        Record {
            fields: self.fields.into_iter().map(|(k, v)| (k, f(v))).collect(),
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = (&String, &T)> {
        self.fields.iter()
    }
}

impl<T, E> Record<Result<T, E>> {
    fn transpose(self) -> Result<Record<T>, E> {
        let mut fields = BTreeMap::default();
        for (f, v) in self.fields {
            fields.insert(f, v?);
        }
        Ok(Record { fields })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    // Bool
    Bool(bool),
    // Int
    Int(i128),
    Lt(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    name: String,
    params: Vec<(String, String)>,
    return_ty: String,
    body: Box<Expr>,
}

#[derive(Debug)]
pub struct TypeDef {
    name: String,
    ty: Type,
}

#[derive(Debug)]
pub enum Stmt {
    VarDef(String, Option<String>, Expr),
    TypeDef(TypeDef),
    FunDef(Function),
    PrintLn(Expr),
}

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

/// Evaluates an expression and tries to extract the value as the specified type.
pub fn eval_as<T: TryFrom<Value, Error = Error>>(expr: Expr, env: &Env<Value>) -> Result<T, Error> {
    eval(expr, env)?.try_into()
}

#[tracing::instrument(skip_all, ret)]
pub fn eval(expr: Expr, env: &Env<Value>) -> Result<Value, Error> {
    Ok(match expr {
        Expr::Bool(b) => Value::Bool(b),
        Expr::Int(i) => Value::Int(i),
        Expr::Lt(e1, e2) => Value::Bool(eval_as::<i128>(*e1, env)? < eval_as::<i128>(*e2, env)?),
        Expr::Add(e1, e2) => Value::Int(eval_as::<i128>(*e1, env)? + eval_as::<i128>(*e2, env)?),
        Expr::Sub(e1, e2) => Value::Int(eval_as::<i128>(*e1, env)? - eval_as::<i128>(*e2, env)?),
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
        // Nothing to evaluate until called
        Expr::Function(f) => Value::Fun(f),
        // Evaluate arguments, evaluate fun body in env with parameters
        Expr::FunctionCall(f_name, args) => {
            tracing::info!("Evaluating function call {}({:?})", f_name, args);
            // Look up function to call
            let f = env.get(&f_name)?;
            // Check that it is a function
            let Value::Fun(f) = f else {
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

#[tracing::instrument(skip_all, ret)]
pub fn step(stmt: Stmt, env: &mut Env<Value>) -> Result<(), Error> {
    match stmt {
        // If specified, `e` must satisfy type `ty`.
        Stmt::VarDef(name, _, e) => env.put(name, eval(e, env)?)?,
        Stmt::TypeDef(ty) => env.put(ty.name, Value::Type(ty.ty))?,
        Stmt::FunDef(f) => {
            tracing::info!("Defining function {}", f.name);
            env.put(f.name.clone(), Value::Fun(f))?;
        }
        Stmt::PrintLn(e) => match eval(e, env)? {
            Value::Bool(b) => println!("{b}"),
            Value::Int(i) => println!("{i}"),
            Value::String(s) => println!("{s}"),
            Value::Type(t) => println!("{t:?}"),
            Value::Record(o) => println!("{o:?}"),
            Value::Fun(f) => println!("{:?} -> {:?}", f.params, f.return_ty),
        },
    }
    Ok(())
}

pub fn exec(stmts: Vec<Stmt>, env: &mut Env<Value>) -> Result<(), Error> {
    for stmt in stmts {
        step(stmt, env)?;
    }
    Ok(())
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
    exec(program.stmts, &mut Env::default())?;
    Ok(())
}

#[cfg(test)]
mod tests {
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
            Stmt::TypeDef(TypeDef {
                name: "Foo".to_string(),
                ty: Type::Record(Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), Type::Int);
                        fields.insert("s".to_string(), Type::String);
                        fields
                    },
                }),
            }),
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
            Stmt::TypeDef(TypeDef {
                name: "Foo".to_string(),
                ty: Type::Record(Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), Type::Int);
                        fields.insert("s".to_string(), Type::String);
                        fields
                    },
                }),
            }),
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
