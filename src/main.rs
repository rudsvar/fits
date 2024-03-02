use std::{
    collections::{BTreeMap, HashMap},
    io::stderr,
    sync::OnceLock,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i128),
    String(String),
    Type(Type),
    Record(Record<Value>),
}

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
    pub fn map<U: PartialEq, F: Fn(&T) -> U>(&self, f: F) -> Record<U> {
        let mut fields = BTreeMap::default();
        for (k, v) in &self.fields {
            fields.insert(k.clone(), f(v));
        }
        Record { fields }
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

#[derive(Debug)]
pub enum Expr {
    // Bool
    Bool(bool),
    // Int
    Int(i128),
    Lt(Box<Expr>, Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    // String
    String(String),
    // Var
    Var(String),
    // Record
    Record(Record<Expr>),
    FieldAccess(Box<Expr>, String),
    // Control flow
    If(Box<Expr>, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Bool,
    Int,
    String,
    Type,
    Record(Record<Type>),
}

#[derive(Debug)]
pub enum Stmt {
    VarDecl(String, Option<String>, Expr),
    TypeDef(String, Type),
    PrintLn(Expr),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    DuplicateField(String),
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

impl Env {
    pub fn empty() -> Self {
        Self {
            env: HashMap::new(),
        }
    }
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
            return Err(Error::DuplicateField(name));
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

#[tracing::instrument(skip(env), ret)]
pub fn eval(expr: Expr, env: &Env) -> Result<Value, Error> {
    Ok(match expr {
        Expr::Bool(b) => Value::Bool(b),
        Expr::Int(i) => Value::Int(i),
        Expr::Lt(e1, e2) => match (eval(*e1, env)?, eval(*e2, env)?) {
            (Value::Int(a), Value::Int(b)) => Value::Bool(a < b),
            _ => panic!("Lt type error"),
        },
        Expr::Add(e1, e2) => match (eval(*e1, env)?, eval(*e2, env)?) {
            (Value::Int(a), Value::Int(b)) => Value::Int(a + b),
            _ => panic!("Add type error"),
        },
        Expr::String(s) => Value::String(s),
        Expr::Var(v) => env.get(&v)?.1,
        Expr::Record(r) => {
            let mut record = Record::default();
            for (f, e) in r.fields {
                let v = eval(e, env)?;
                record.put(f, v)?;
            }
            Value::Record(record)
        }
        Expr::FieldAccess(e, field) => match eval(*e, env)? {
            Value::Record(r) => r.get(&field)?,
            _ => Err(Error::NoFields(field))?,
        },
        Expr::If(b, e1, e2) => match eval(*b, env)? {
            Value::Bool(true) => eval(*e1, env)?,
            Value::Bool(false) => eval(*e2, env)?,
            _ => panic!("If type error"),
        },
    })
}

fn type_of(expr: &Expr, env: &Env) -> Result<Type, Error> {
    let ty = match expr {
        Expr::Bool(_) => Type::Bool,
        Expr::Int(_) => Type::Int,
        Expr::Lt(e1, e2) => {
            assert_type(&Type::Int, &type_of(e1, env)?)?;
            assert_type(&Type::Int, &type_of(e2, env)?)?;
            Type::Bool
        }
        Expr::Add(e1, e2) => {
            assert_type(&Type::Int, &type_of(e1, env)?)?;
            assert_type(&Type::Int, &type_of(e2, env)?)?;
            Type::Int
        }
        Expr::String(_) => Type::String,
        Expr::Record(r) => {
            let r = r.map(|e| type_of(e, env)).transpose()?;
            Type::Record(r)
        }
        Expr::Var(v) => env.get(v)?.0,
        Expr::FieldAccess(e, f) => {
            // Check type of expression
            let e_ty = type_of(e, env)?;
            match e_ty {
                // Must be a custom type to have fields
                Type::Record(r) => r.get(f)?,
                _ => Err(Error::NoFields(f.to_string()))?,
            }
        }
        Expr::If(b, e1, e2) => {
            let b_ty = type_of(b, env)?;
            assert_type(&Type::Bool, &b_ty)?;
            let e1_ty = type_of(e1, env)?;
            let e2_ty = type_of(e2, env)?;
            if e1_ty != e2_ty {
                return Err(Error::TypeError {
                    expected: e1_ty,
                    actual: e2_ty,
                });
            }
            e1_ty
        }
    };
    Ok(ty)
}

fn assert_type(expected: &Type, actual: &Type) -> Result<(), Error> {
    match (expected, actual) {
        // If record, we just need the required fields
        (a @ Type::Record(expected), b @ Type::Record(actual)) => {
            for (expected_f, expected_f_ty) in expected.iter() {
                // If a field isn't there, the type isn't satisfied
                let Ok(actual_f_ty) = actual.get(expected_f) else {
                    return Err(Error::TypeError {
                        expected: a.clone(),
                        actual: b.clone(),
                    });
                };
                assert_type(expected_f_ty, &actual_f_ty)?;
            }
            Ok(())
        }
        // Otherwise, type must be equal
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

#[tracing::instrument(skip(env), ret)]
pub fn step(stmt: Stmt, env: &mut Env) -> Result<(), Error> {
    match stmt {
        // If specified, `e` must satisfy type `ty`.
        Stmt::VarDecl(name, required_ty, e) => {
            let real_type = type_of(&e, env)?;
            if let Some(required_ty) = required_ty {
                match env.get(&required_ty)? {
                    (Type::Type, Value::Type(required_ty)) => {
                        assert_type(&required_ty, &real_type)?;
                    }
                    _ => Err(Error::NotType(required_ty))?,
                };
            }
            env.put(name, real_type, eval(e, env)?)?;
        }
        Stmt::TypeDef(name, ty) => env.put(name, Type::Type, Value::Type(ty))?,
        Stmt::PrintLn(e) => match eval(e, env)? {
            Value::Bool(b) => println!("{b}"),
            Value::Int(i) => println!("{i}"),
            Value::String(s) => println!("{s}"),
            Value::Type(t) => println!("{t:?}"),
            Value::Record(o) => println!("{o:?}"),
        },
    }
    Ok(())
}

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

    let program = vec![
        Stmt::TypeDef(
            "Foo".to_string(),
            Type::Record(Record {
                fields: {
                    let mut fields = BTreeMap::new();
                    fields.insert("i".to_string(), Type::Int);
                    fields.insert("s".to_string(), Type::String);
                    fields
                },
            }),
        ),
        Stmt::VarDecl(
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
        Stmt::PrintLn(Expr::Var("foo".to_string())),
        Stmt::PrintLn(Expr::FieldAccess(
            Box::new(Expr::Var("foo".to_string())),
            "i".to_string(),
        )),
        Stmt::PrintLn(Expr::FieldAccess(
            Box::new(Expr::Var("foo".to_string())),
            "s".to_string(),
        )),
    ];
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
    fn can_access_field_of_record() {
        let program = vec![
            Stmt::TypeDef(
                "Foo".to_string(),
                Type::Record(Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), Type::Int);
                        fields.insert("s".to_string(), Type::String);
                        fields
                    },
                }),
            ),
            Stmt::VarDecl(
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
                Type::Record(Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), Type::Int);
                        fields.insert("s".to_string(), Type::String);
                        fields
                    },
                }),
            ),
            Stmt::VarDecl(
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
        let program = vec![Stmt::PrintLn(Expr::FieldAccess(
            Box::new(Expr::Int(0)),
            "i".to_string(),
        ))];
        assert_eq!(
            Err(Error::NoFields("i".to_string())),
            exec(program, &mut Env::default())
        );
    }

    #[test]
    fn record_must_have_all_fields_of_type() {
        let program = vec![
            Stmt::TypeDef(
                "Foo".to_string(),
                Type::Record(Record {
                    fields: {
                        let mut fields = BTreeMap::new();
                        fields.insert("i".to_string(), Type::Int);
                        fields.insert("s".to_string(), Type::String);
                        fields
                    },
                }),
            ),
            Stmt::VarDecl(
                "foo".to_string(),
                Some("Foo".to_string()),
                Expr::Record(Record {
                    fields: vec![("i".to_string(), Expr::Int(5))].into_iter().collect(),
                }),
            ),
        ];
        let expected = Type::Record(Record {
            fields: [
                ("i".to_string(), Type::Int),
                ("s".to_string(), Type::String),
            ]
            .into_iter()
            .collect(),
        });
        let actual = Type::Record(Record {
            fields: [("i".to_string(), Type::Int)].into_iter().collect(),
        });
        assert_eq!(
            Err(Error::TypeError { expected, actual }),
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
}
