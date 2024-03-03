use crate::{typecheck::Type, Error, Function, Record};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i128),
    String(String),
    Type(Type),
    Record(Record<Value>),
    Function(Function),
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
