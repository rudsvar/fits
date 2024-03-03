use std::collections::HashMap;

use crate::{typecheck::Type, Error, Value};

#[derive(Debug)]
pub struct Env<T> {
    env: HashMap<String, T>,
}

impl<T> Env<T> {
    pub fn empty() -> Self {
        Self {
            env: HashMap::new(),
        }
    }
}

impl Env<Value> {
    pub fn filtered(&self) -> Env<Value> {
        let mut filtered_env = HashMap::new();
        for (k, v) in &self.env {
            // Keep function definitions
            if let Value::Fun(_) = v {
                filtered_env.insert(k.clone(), v.clone());
            };
        }
        Env { env: filtered_env }
    }
}

impl Env<Type> {
    pub fn filtered(&self) -> Env<Type> {
        let mut filtered_env = HashMap::new();
        for (k, v) in &self.env {
            // Keep function definitions
            if let Type::Fun(_, _) = v {
                filtered_env.insert(k.clone(), v.clone());
            };
        }
        Env { env: filtered_env }
    }
}

impl Default for Env<Value> {
    fn default() -> Self {
        let mut env = HashMap::default();
        env.insert("ZERO".to_string(), Value::Int(0));
        Self { env }
    }
}

impl Default for Env<Type> {
    fn default() -> Self {
        let mut env = HashMap::default();
        env.insert("Int".to_string(), Type::Int);
        env.insert("String".to_string(), Type::String);
        Self { env }
    }
}

impl<T: Clone> Env<T> {
    pub fn put(&mut self, name: String, t: T) -> Result<(), Error> {
        if self.env.contains_key(&name) {
            return Err(Error::AlreadyDefined(name));
        }
        self.env.insert(name, t);
        Ok(())
    }

    pub fn get(&self, s: &str) -> Result<T, Error> {
        self.env
            .get(s)
            .cloned()
            .ok_or(Error::NotDefined(s.to_string()))
    }
}
