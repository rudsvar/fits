use crate::{
    typecheck::{Type, TypeError},
    Value,
};

#[derive(Debug)]
pub struct Env<T> {
    scopes: Vec<Vec<(String, T)>>,
}

impl<T> Env<T> {
    pub fn empty() -> Self {
        Self {
            scopes: vec![vec![]],
        }
    }
    pub fn open(&mut self) {
        self.scopes.push(vec![]);
    }
    pub fn close(&mut self) {
        self.scopes.pop();
    }
}

impl Env<Value> {
    pub fn filtered(&self) -> Env<Value> {
        let mut filtered_env = Env::empty();
        for scope in &self.scopes {
            filtered_env.open();
            for (k, v) in scope {
                if let Value::Function(_) = v {
                    filtered_env.put(k.clone(), v.clone());
                };
            }
        }
        filtered_env
    }
}

impl Env<Type> {
    pub fn filtered(&self) -> Env<Type> {
        let mut filtered_env = Env::empty();
        for scope in &self.scopes {
            filtered_env.open();
            for (k, v) in scope {
                // Keep function definitions
                if let Type::Function(_, _) = v {
                    filtered_env.put(k.clone(), v.clone());
                };
            }
        }
        filtered_env
    }
}

impl Default for Env<Value> {
    fn default() -> Self {
        let mut env = Env::empty();
        env.put("ZERO".to_string(), Value::Int(0));
        env.put("Int".to_string(), Value::Type(Type::Int));
        env.put("String".to_string(), Value::Type(Type::String));
        env
    }
}

impl Default for Env<Type> {
    fn default() -> Self {
        let mut env = Env::empty();
        env.put("Int".to_string(), Type::Int);
        env.put("String".to_string(), Type::String);
        env
    }
}

impl<T: Clone> Env<T> {
    pub fn put(&mut self, name: String, t: T) {
        self.scopes
            .last_mut()
            .expect("bug, no open scope")
            .push((name, t));
    }

    pub fn get(&self, s: &str) -> Result<T, TypeError> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|scope| scope.iter().rev())
            .find(|(k, _)| k == s)
            .map(|(_, v)| v)
            .cloned()
            .ok_or(TypeError::NotDefined(s.to_string()))
    }
}
