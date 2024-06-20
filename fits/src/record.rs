use std::{collections::BTreeMap, fmt::Display};

use serde::{Deserialize, Serialize};

/// A general record-like structure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Record<T> {
    pub fields: BTreeMap<String, T>,
}

#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum RecordError {
    #[error("duplicate field: {0}")]
    DuplicateField(String),
    #[error("no such field: {0}")]
    NoSuchField(String),
}

impl<T> Default for Record<T> {
    fn default() -> Self {
        Self {
            fields: BTreeMap::default(),
        }
    }
}

impl<T: Clone> Record<T> {
    pub fn put(&mut self, field: String, value: T) -> Result<(), RecordError> {
        if self.fields.contains_key(&field) {
            return Err(RecordError::DuplicateField(field));
        }
        self.fields.insert(field, value);
        Ok(())
    }

    pub fn get(&self, field: &str) -> Result<T, RecordError> {
        self.fields
            .get(field)
            .cloned()
            .ok_or_else(|| RecordError::NoSuchField(field.to_string()))
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
    pub fn transpose(self) -> Result<Record<T>, E> {
        let mut fields = BTreeMap::default();
        for (f, v) in self.fields {
            fields.insert(f, v?);
        }
        Ok(Record { fields })
    }
}

impl<T: Display> Display for Record<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for (k, v) in self.fields.iter() {
            writeln!(f, "  {k}: {v}")?;
        }
        write!(f, "}}")
    }
}
