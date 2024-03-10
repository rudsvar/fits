use std::fmt::Display;

use crate::{typecheck::Type, Error, Function, Record};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Unit,
    Bool(bool),
    Int(i128),
    String(String),
    Type(Type),
    Record(Record<Value>),
    Function(Function),
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Int(i) => write!(f, "{i}"),
            Value::String(s) => write!(f, "{s}"),
            Value::Type(t) => write!(f, "{t}"),
            Value::Record(r) => write!(f, "{r}"),
            Value::Function(fun) => write!(f, "{fun}"),
        }
    }
}

impl Value {
    pub fn get_field(&self, field: &str) -> Result<Value, Error> {
        match self {
            Value::Record(record) => Ok(record.get(field)?),
            _ => Err(Error::NoSuchField(field.to_string())),
        }
    }
}

impl TryFrom<Value> for bool {
    type Error = Error;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Bool(b) => Ok(b),
            _ => Err(Error::ExpectedType(Type::Bool)),
        }
    }
}

impl TryFrom<Value> for i128 {
    type Error = Error;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::Int(i) => Ok(i),
            _ => Err(Error::ExpectedType(Type::Int)),
        }
    }
}

impl TryFrom<Value> for String {
    type Error = Error;
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value::String(s) => Ok(s),
            _ => Err(Error::ExpectedType(Type::String)),
        }
    }
}
