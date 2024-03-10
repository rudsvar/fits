use std::fmt::Display;

use crate::{Env, Error, Expr, Record, Stmt};

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

impl Type {
    pub fn fits(&self, expected: &Type) -> Result<(), Error> {
        match (expected, self) {
            // If record, we just need the required fields
            (a @ Type::Record(expected), b @ Type::Record(actual)) => {
                // Each field in expected record must match field from actual record
                for (expected_f, expected_f_ty) in expected.iter() {
                    // If a field isn't there, the type isn't satisfied
                    let Ok(actual_f_ty) = actual.get(expected_f) else {
                        return Err(Error::TypeError {
                            expected: a.clone(),
                            actual: b.clone(),
                        });
                    };
                    actual_f_ty.fits(expected_f_ty)?;
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
}

impl Type {
    /// Returns the field if the type is a record.
    fn get_field(&self, field: &str) -> Result<Type, Error> {
        match self {
            Type::Record(record) => Ok(record.get(field)?),
            _ => Err(Error::NoSuchField(field.to_string())),
        }
    }
}

/// Returns the type of an expression.
fn type_of(expr: &Expr, env: &Env<Type>) -> Result<Type, Error> {
    let ty = match expr {
        Expr::Unit => Type::Unit,
        Expr::Bool(_) => Type::Bool,
        Expr::Int(_) => Type::Int,
        Expr::Lt(e1, e2) => {
            type_of(e1, env)?.fits(&Type::Int)?;
            type_of(e2, env)?.fits(&Type::Int)?;
            Type::Bool
        }
        Expr::Add(e1, e2) => {
            type_of(e1, env)?.fits(&Type::Int)?;
            type_of(e2, env)?.fits(&Type::Int)?;
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
                return Err(Error::TypeError {
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
                .collect::<Result<Vec<Type>, Error>>()?;
            tracing::info!("Parameter types: {param_types:?}");
            let return_type = env.get(&f.return_ty)?;
            tracing::info!("Return type: {return_type:?}");
            // Assume params defined with correct types.
            let mut fun_env = Env::default();
            for ((param_name, _), param_ty) in f.params.iter().zip(&param_types) {
                // TODO: Placeholder value is unnecessary for type checking.
                fun_env.put(param_name.clone(), param_ty.clone())?;
            }
            // Put function itself in env to enable recursion
            fun_env.put(
                f.name.to_string(),
                Type::Function(param_types.clone(), Box::new(return_type.clone())),
            )?;
            // Type check in new env
            let body_type = type_of(&f.body, &fun_env)?;
            tracing::info!("Body type: {:?}", body_type);
            body_type.fits(&return_type)?;
            Type::Function(param_types, Box::new(return_type))
        }
        Expr::FunctionCall(f_name, args) => {
            tracing::info!("Type checking function call to {f_name}");
            // Look up function to call
            let f = env.get(f_name)?;
            // Check that it is a function
            let Type::Function(params, return_ty) = f else {
                return Err(Error::Custom("Expected function".to_string()));
            };
            tracing::info!("It's a function at least");
            // Check number of args.
            if args.len() != params.len() {
                return Err(Error::WrongNumberOfArgs {
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
pub fn typecheck_stmt(stmt: &Stmt, env: &mut Env<Type>) -> Result<(), Error> {
    match stmt {
        Stmt::VarDef(name, required_ty_name, e) => {
            let actual_ty = type_of(e, env)?;
            match required_ty_name {
                // let x: T = ...
                Some(required_ty_name) => {
                    let required_ty = env.get(required_ty_name)?;
                    // Make sure actual type fits required
                    actual_ty.fits(&required_ty)?;
                    env.put(name.clone(), required_ty)?;
                }
                // let x = ...
                None => {
                    env.put(name.clone(), actual_ty)?;
                }
            }
            Ok(())
        }
        Stmt::TypeDef(name, r) => {
            let mut ty = Record::default();
            for (field, ty_name) in &r.fields {
                let field_ty = env.get(ty_name)?;
                ty.fields.insert(field.clone(), field_ty);
            }
            tracing::info!("type {name} = {r}");
            env.put(name.clone(), Type::Record(ty))?;
            Ok(())
        }
        Stmt::FunDef(f) => env.put(f.name.clone(), type_of(&Expr::Function(f.clone()), env)?),
        Stmt::PrintLn(e) => {
            type_of(e, env)?;
            Ok(())
        }
    }
}

#[tracing::instrument(skip_all, ret)]
pub fn typecheck_stmts(stmts: &Vec<Stmt>, env: &mut Env<Type>) -> Result<(), Error> {
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
            Err(Error::TypeError {
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
            Err(Error::TypeError { expected, actual }),
            typecheck_stmts(&program, &mut Env::default())
        );
    }
}
