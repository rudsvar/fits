use std::fmt::Display;

use crate::{record::RecordError, Env, Expr, Record, Stmt};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Unit,
    Bool,
    Int,
    String,
    Record(Record<Type>),
    Function(Vec<Type>, Box<Type>),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Unit => write!(f, "()"),
            Type::Bool => write!(f, "Bool"),
            Type::Int => write!(f, "Int"),
            Type::String => write!(f, "String"),
            Type::Record(r) => write!(f, "{r}"),
            Type::Function(param_tys, return_ty) => write!(
                f,
                "fn({}): {}",
                param_tys
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                return_ty,
            ),
        }
    }
}

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum TypeError {
    #[error("{0}")]
    RecordError(#[from] RecordError),
    #[error("expected type {expected}, actual {actual}")]
    ExpectedActual { expected: Type, actual: Type },
    #[error("expected type {0}")]
    Expected(Type),
    #[error("no such field on non-record: {0}")]
    NoSuchFieldOnNonRecord(String),
    #[error("expected function")]
    ExpectedFunction(String),
    #[error("expected {expected} args, got {actual}")]
    WrongNumberOfArgs { expected: usize, actual: usize },
    #[error("already defined: {0}")]
    AlreadyDefined(String),
    #[error("not defined: {0}")]
    NotDefined(String),
    #[error("{0}")]
    Custom(String),
}

impl Type {
    pub fn fits(&self, expected: &Type) -> Result<(), TypeError> {
        match (expected, self) {
            // If record, we just need the required fields
            (expected @ Type::Record(expected_record), actual @ Type::Record(actual_record)) => {
                // Each field in expected record must match field from actual record
                for (expected_f, expected_f_ty) in expected_record.iter() {
                    // If a field isn't there, the type isn't satisfied
                    let Ok(actual_f_ty) = actual_record.get(expected_f) else {
                        return Err(TypeError::ExpectedActual {
                            expected: expected.clone(),
                            actual: actual.clone(),
                        });
                    };
                    actual_f_ty.fits(expected_f_ty)?;
                }
                Ok(())
            }
            // Otherwise, type must be equal
            (expected, actual) => {
                if expected != actual {
                    return Err(TypeError::ExpectedActual {
                        expected: expected.clone(),
                        actual: actual.clone(),
                    });
                }
                Ok(())
            }
        }
    }
}

impl Type {
    /// Returns the field if the type is a record.
    fn get_field(&self, field: &str) -> Result<Type, TypeError> {
        match self {
            Type::Record(record) => Ok(record.get(field)?),
            _ => Err(TypeError::NoSuchFieldOnNonRecord(field.to_string())),
        }
    }
}

pub fn assert_type(e: &Expr, env: &Env<Type>, ty: &Type) -> Result<(), TypeError> {
    type_of(e, env)?.fits(ty)
}

/// Returns the type of an expression.
fn type_of(expr: &Expr, env: &Env<Type>) -> Result<Type, TypeError> {
    let ty = match expr {
        Expr::Unit => Type::Unit,
        Expr::Bool(_) => Type::Bool,
        Expr::Int(_) => Type::Int,
        Expr::Lt(e1, e2) => {
            assert_type(e1, env, &Type::Int)?;
            assert_type(e2, env, &Type::Int)?;
            Type::Bool
        }
        Expr::Eq(e1, e2) => {
            let t1 = type_of(e1, env)?;
            let t2 = type_of(e2, env)?;
            if t1 != t2 {
                return Err(TypeError::ExpectedActual {
                    expected: t1,
                    actual: t2,
                });
            }
            Type::Bool
        }
        Expr::And(e1, e2) => {
            assert_type(e1, env, &Type::Bool)?;
            assert_type(e2, env, &Type::Bool)?;
            Type::Bool
        }
        Expr::Add(e1, e2) => {
            assert_type(e1, env, &Type::Int)?;
            assert_type(e2, env, &Type::Int)?;
            Type::Int
        }
        Expr::Sub(e1, e2) => {
            type_of(e1, env)?.fits(&Type::Int)?;
            type_of(e2, env)?.fits(&Type::Int)?;
            Type::Int
        }
        Expr::Mul(e1, e2) => {
            type_of(e1, env)?.fits(&Type::Int)?;
            type_of(e2, env)?.fits(&Type::Int)?;
            Type::Int
        }
        Expr::Mod(e1, e2) => {
            type_of(e1, env)?.fits(&Type::Int)?;
            type_of(e2, env)?.fits(&Type::Int)?;
            Type::Int
        }
        Expr::String(_) => Type::String,
        Expr::Record(r) => Type::Record(r.as_ref().map(|e| type_of(e, env)).transpose()?),
        Expr::Var(v) => env.get(v)?,
        Expr::FieldAccess(e, field) => type_of(e, env)?.get_field(field)?,
        Expr::If(b, e1, e2) => {
            let b_ty = type_of(b, env)?;
            b_ty.fits(&Type::Bool)?;
            let e1_ty = type_of(e1, env)?;
            let e2_ty = type_of(e2, env)?;
            if e1_ty != e2_ty {
                return Err(TypeError::ExpectedActual {
                    expected: e1_ty,
                    actual: e2_ty,
                });
            }
            e1_ty
        }
        Expr::Function(f) => {
            tracing::info!("Type checking function");
            let param_types: Vec<Type> = f
                .params
                .iter()
                .map(|(_, param_ty_name)| env.get(param_ty_name))
                .collect::<Result<_, _>>()?;
            tracing::info!("Parameter types: {param_types:?}");
            let return_type = env.get(&f.return_ty)?;
            tracing::info!("Return type: {return_type:?}");
            // Assume params defined with correct types.
            let mut fun_env = Env::default();
            for ((param_name, _), param_ty) in f.params.iter().zip(&param_types) {
                // TODO: Placeholder value is unnecessary for type checking.
                fun_env.put(param_name.clone(), param_ty.clone());
            }
            // Put function itself in env to enable recursion
            fun_env.put(
                f.name.to_string(),
                Type::Function(param_types.clone(), Box::new(return_type.clone())),
            );
            // Type check in new env
            let body_type = type_of(&f.body, &fun_env)?;
            tracing::info!("Body type: {:?}", body_type);
            body_type.fits(&return_type)?;
            Type::Function(param_types, Box::new(return_type))
        }
        Expr::Call(f_name, args) => {
            tracing::info!("Type checking function call to {f_name}");
            // Look up function to call
            let f = env.get(f_name)?;
            // Check that it is a function
            let Type::Function(params, return_ty) = f else {
                return Err(TypeError::ExpectedFunction(f.to_string()));
            };
            tracing::info!("It's a function at least");
            // Check number of args.
            if args.len() != params.len() {
                return Err(TypeError::WrongNumberOfArgs {
                    expected: params.len(),
                    actual: args.len(),
                });
            }
            tracing::info!("Called with the correct number of arguments");
            // Arguments must satisfy parameter types
            // TODO: Custom type definitions will not be included. Separate env or keep?
            for (i, (param_ty, arg)) in params.into_iter().zip(args).enumerate() {
                tracing::info!("Parameter {i} has type {param_ty:?}");
                let arg_ty = type_of(arg, env)?;
                tracing::info!("Corresponding argument has type {arg_ty:?}");
                arg_ty.fits(&param_ty)?;
            }
            // Type of function call is same as return type
            tracing::info!("Return type is {return_ty:?}");
            *return_ty
        }
    };
    Ok(ty)
}

#[tracing::instrument(skip_all, ret)]
pub fn typecheck_stmt(stmt: &Stmt, env: &mut Env<Type>) -> Result<(), TypeError> {
    match stmt {
        Stmt::VarDef(name, required_ty_name, e) => {
            let actual_ty = type_of(e, env)?;
            match required_ty_name {
                // let x: T = ...
                Some(required_ty_name) => {
                    let required_ty = env.get(required_ty_name)?;
                    // Make sure actual type fits required
                    actual_ty.fits(&required_ty)?;
                    env.put(name.clone(), required_ty);
                }
                // let x = ...
                None => {
                    env.put(name.clone(), actual_ty);
                }
            }
            Ok(())
        }
        Stmt::Assign(name, e) => {
            let variable_type = env.get(name)?;
            let expression_type = type_of(e, env)?;
            expression_type.fits(&variable_type)?;
            Ok(())
        }
        Stmt::TypeDef(name, r) => {
            let mut ty = Record::default();
            for (field, ty_name) in &r.fields {
                let field_ty = env.get(ty_name)?;
                ty.fields.insert(field.clone(), field_ty);
            }
            tracing::info!("type {name} = {r}");
            env.put(name.clone(), Type::Record(ty));
            Ok(())
        }
        Stmt::FunDef(f) => {
            let f_ty = type_of(&Expr::Function(f.clone()), env)?;
            env.put(f.name.clone(), f_ty);
            Ok(())
        }
        Stmt::PrintLn(e) => {
            type_of(e, env)?;
            Ok(())
        }
        Stmt::Block(stmts) => {
            env.open();
            typecheck_stmts(stmts, env)?;
            env.close();
            Ok(())
        }
    }
}

#[tracing::instrument(skip_all, ret)]
pub fn typecheck_stmts(stmts: &Vec<Stmt>, env: &mut Env<Type>) -> Result<(), TypeError> {
    for stmt in stmts {
        typecheck_stmt(stmt, env)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {

    use std::collections::BTreeMap;

    use crate::Record;

    use super::*;

    #[test]
    fn variable_declaration_with_wrong_type_fails() {
        crate::init_logging();
        let mut env = Env::default();
        let stmt = Stmt::VarDef("a".to_string(), Some("String".to_string()), Expr::Int(0));
        assert_eq!(
            Err(TypeError::ExpectedActual {
                expected: Type::String,
                actual: Type::Int
            }),
            typecheck_stmt(&stmt, &mut env)
        );
    }

    #[test]
    fn record_must_have_all_fields_of_type() {
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
            Err(TypeError::ExpectedActual { expected, actual }),
            typecheck_stmts(&program, &mut Env::default())
        );
    }
}
