use std::{
    collections::{BTreeMap, HashMap},
    io::stderr,
    sync::OnceLock,
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Fields {
    fields: BTreeMap<String, Value>,
}

impl Fields {
    pub fn put(&mut self, field: String, v: Value) -> Result<(), Error> {
        if self.fields.contains_key(&field) {
            return Err(Error::AlreadyDefined(field));
        }
        self.fields.insert(field, v);
        Ok(())
    }
    pub fn get(&self, field: &str) -> Result<Value, Error> {
        self.fields
            .get(field)
            .cloned()
            .ok_or_else(|| Error::NoSuchField(field.to_string()))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Object {
    fields: Fields,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Int(i128),
    String(String),
    Type(Type),
    Object(Object),
}

#[derive(Debug)]
pub struct Record {
    fields: Vec<(String, Expr)>,
}

#[derive(Debug)]
pub enum Expr {
    Int(i128),
    String(String),
    Var(String),
    Record(Record),
    FieldAccess(Box<Expr>, String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Int,
    String,
    Type,
    Custom { fields: HashMap<String, Type> },
}

#[derive(Debug)]
pub enum Stmt {
    VarDecl(String, Option<String>, Expr),
    TypeDef(String, Type),
    PrintLn(Expr),
}

#[derive(Debug, Default)]
pub struct Program {
    stmts: Vec<Stmt>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    AlreadyDefined(String),
    NotDefined(String),
    NotType(String),
    NoFields(String),
    NoSuchField(String),
    TypeError { expected: Type, actual: Type },
}

#[derive(Debug)]
pub struct Env {
    env: HashMap<String, (Type, Value)>,
}

impl Default for Env {
    fn default() -> Self {
        let mut env = HashMap::default();
        env.insert("Int".to_string(), (Type::Type, Value::Type(Type::Int)));
        env.insert(
            "String".to_string(),
            (Type::Type, Value::Type(Type::String)),
        );
        Self { env }
    }
}

impl Env {
    fn put(&mut self, name: String, ty: Type, v: Value) -> Result<(), Error> {
        if self.env.contains_key(&name) {
            return Err(Error::AlreadyDefined(name));
        }
        self.env.insert(name, (ty, v));
        Ok(())
    }

    fn get(&self, s: &str) -> Result<(Type, Value), Error> {
        self.env
            .get(s)
            .cloned()
            .ok_or(Error::NotDefined(s.to_string()))
    }
}

#[tracing::instrument(ret)]
pub fn eval(expr: Expr, env: &Env) -> Result<Value, Error> {
    Ok(match expr {
        Expr::Int(i) => Value::Int(i),
        Expr::String(s) => Value::String(s),
        Expr::Var(v) => env.get(&v)?.1,
        Expr::Record(r) => {
            let mut fields = Fields::default();
            for f in r.fields {
                let v = eval(f.1, env)?;
                fields.put(f.0, v)?;
            }
            Value::Object(Object { fields })
        }
        Expr::FieldAccess(e, field) => match eval(*e, env)? {
            Value::Object(o) => o.fields.get(&field)?,
            _ => Err(Error::NoFields(field))?,
        },
    })
}

fn type_of(expr: &Expr, env: &Env) -> Result<Type, Error> {
    let ty = match expr {
        Expr::Int(_) => Type::Int,
        Expr::String(_) => Type::String,
        Expr::Record(r) => {
            let mut fields = HashMap::new();
            for f in &r.fields {
                let f_ty = type_of(&f.1, env)?;
                fields.insert(f.0.clone(), f_ty);
            }
            Type::Custom { fields }
        }
        Expr::Var(v) => env.get(v)?.0,
        Expr::FieldAccess(e, f) => {
            // Check type of expression
            let e_ty = type_of(e, env)?;
            match e_ty {
                // Must be a custom type to have fields
                Type::Custom { fields } => {
                    // Get type of the field we're accessing
                    fields
                        .get(f)
                        .cloned()
                        .ok_or_else(|| Error::NoSuchField(f.to_string()))?
                }
                _ => Err(Error::NoFields(f.to_string()))?,
            }
        }
    };
    Ok(ty)
}

fn satisfies_type(expected: &Type, actual: &Type) -> Result<(), Error> {
    match (expected, actual) {
        (
            Type::Custom {
                fields: expected_fields,
            },
            Type::Custom {
                fields: actual_fields,
            },
        ) => {
            for (expected_f, expected_f_ty) in expected_fields.iter() {
                let actual_f_ty =
                    actual_fields
                        .get(expected_f)
                        .ok_or_else(|| Error::TypeError {
                            expected: expected.clone(),
                            actual: actual.clone(),
                        })?;
                satisfies_type(expected_f_ty, actual_f_ty)?;
            }
            Ok(())
        }
        (expected, actual) => {
            if expected == actual {
                Ok(())
            } else {
                Err(Error::TypeError {
                    expected: expected.clone(),
                    actual: actual.clone(),
                })
            }
        }
    }
}

#[tracing::instrument(ret)]
pub fn step(stmt: Stmt, env: &mut Env) -> Result<(), Error> {
    match stmt {
        // If specified, `e` must satisfy type `ty`.
        Stmt::VarDecl(name, required_ty, e) => {
            let real_type = type_of(&e, env)?;
            if let Some(required_ty) = required_ty {
                match env.get(&required_ty)? {
                    (Type::Type, Value::Type(required_ty)) => {
                        satisfies_type(&required_ty, &real_type)?;
                    }
                    _ => Err(Error::NotType(required_ty))?,
                };
            }
            env.put(name, real_type, eval(e, env)?)?;
        }
        Stmt::TypeDef(name, ty) => env.put(name, Type::Type, Value::Type(ty))?,
        Stmt::PrintLn(e) => match eval(e, env)? {
            Value::Int(i) => println!("{i}"),
            Value::String(s) => println!("{s}"),
            Value::Type(t) => println!("{t:?}"),
            Value::Object(o) => println!("{o:?}"),
        },
    }
    Ok(())
}

#[tracing::instrument(ret)]
fn exec(stmts: Vec<Stmt>, env: &mut Env) -> Result<(), Error> {
    for stmt in stmts {
        step(stmt, env)?;
    }
    Ok(())
}

fn init_logging() {
    static LOGGING: OnceLock<()> = OnceLock::new();
    LOGGING.get_or_init(|| tracing_subscriber::fmt().with_writer(stderr).init());
}

fn main() {
    init_logging();

    let program = vec![];
    let mut env = Env::default();
    if let Err(e) = exec(program, &mut env) {
        eprintln!("{e:?}");
    }
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
        let stmt = Stmt::VarDecl("a".to_string(), None, Expr::Int(0));
        step(stmt, &mut env).unwrap();
        assert_eq!((Type::Int, Value::Int(0)), env.get("a").unwrap())
    }

    #[test]
    fn variable_declaration_with_wrong_type_fails() {
        init_logging();
        let mut env = Env::default();
        let stmt = Stmt::VarDecl("a".to_string(), Some("String".to_string()), Expr::Int(0));
        assert_eq!(
            Err(Error::TypeError {
                expected: Type::String,
                actual: Type::Int
            }),
            step(stmt, &mut env)
        );
    }

    #[test]
    fn variable_usage_finds_var_in_env() {
        init_logging();
        let stmts = vec![
            Stmt::VarDecl("a".to_string(), None, Expr::Int(0)),
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
}
