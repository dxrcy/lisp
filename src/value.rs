use std::{cmp, fmt, ops};

use crate::RuntimeError;

#[derive(Clone, Default, PartialEq)]
pub enum Value {
    #[default]
    Null,
    Text(String),
    Number(Number),
    Bool(bool),
    List(Vec<Value>),
}
type Number = f32;

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Text(a) => write!(f, "\"{}\"", a),
            Value::Number(a) => write!(f, "{}", a),
            Value::Bool(a) => write!(f, "<{}>", a),
            Value::Null => write!(f, "<null>"),
            Value::List(list) => {
                write!(f, "[")?;
                for (i, item) in list.into_iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}", item)?;
                }
                write!(f, "]")
            }
        }
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Text(a) => write!(f, "{}", a),
            Value::Number(a) => write!(f, "\x1b[33m{}\x1b[0m", a),
            Value::Bool(a) => write!(f, "\x1b[1;33m{}\x1b[0m", a),
            Value::Null => write!(f, "\x1b[31mnull\x1b[0m"),
            Value::List(_) => {
                write!(f, "\x1b[32m[...]\x1b[0m")
            }
        }
    }
}

impl ops::Add for Value {
    type Output = Result<Self, RuntimeError>;
    fn add(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (self, rhs) {
            (V::Number(a), V::Number(b)) => Ok(V::Number(a + b)),
            (V::Text(a), V::Text(b)) => Ok(V::Text(a + &b)),
            (V::List(mut a), b) => {
                a.push(b);
                Ok(V::List(a))
            }
            (a, b) => Err(RuntimeError::TypeMismatch(a, b)),
        }
    }
}
impl ops::Sub for Value {
    type Output = Result<Self, RuntimeError>;
    fn sub(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (&self, &rhs) {
            (V::Number(a), V::Number(b)) => Ok(V::Number(a - b)),
            _ => Err(RuntimeError::TypeMismatch(self, rhs)),
        }
    }
}
impl ops::Mul for Value {
    type Output = Result<Self, RuntimeError>;
    fn mul(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (&self, &rhs) {
            (V::Number(a), V::Number(b)) => Ok(V::Number(a * b)),
            (V::Text(a), V::Number(b)) => {
                Ok(V::Text(a.repeat((*b as isize).try_into().unwrap_or(0))))
            }
            _ => Err(RuntimeError::TypeMismatch(self, rhs)),
        }
    }
}
impl ops::Div for Value {
    type Output = Result<Self, RuntimeError>;
    fn div(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (&self, &rhs) {
            (V::Number(a), V::Number(b)) => Ok(V::Number(a / b)),
            _ => Err(RuntimeError::TypeMismatch(self, rhs)),
        }
    }
}
impl ops::Rem for Value {
    type Output = Result<Self, RuntimeError>;
    fn rem(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (&self, &rhs) {
            (V::Number(a), V::Number(b)) => Ok(V::Number(a % b)),
            _ => Err(RuntimeError::TypeMismatch(self, rhs)),
        }
    }
}
impl cmp::PartialOrd for Value {
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        use Value as V;
        match (self, rhs) {
            (V::Number(a), V::Number(b)) => a.partial_cmp(b),
            _ => panic!("type mismatch"),
        }
    }
}

impl Value {
    pub fn number(self) -> Result<Number, RuntimeError> {
        match self {
            Value::Number(a) => Ok(a),
            _ => Err(RuntimeError::ExpectedType("number", self)),
        }
    }
    pub fn bool(self) -> Result<bool, RuntimeError> {
        match self {
            Value::Bool(a) => Ok(a),
            _ => Err(RuntimeError::ExpectedType("bool", self)),
        }
    }
    pub fn text(self) -> Result<String, RuntimeError> {
        match self {
            Value::Text(a) => Ok(a),
            _ => Err(RuntimeError::ExpectedType("text", self)),
        }
    }
    pub fn list(self) -> Result<Vec<Value>, RuntimeError> {
        match self {
            Value::List(a) => Ok(a),
            Value::Text(a) => Ok(a.chars().map(|ch| Value::Text(ch.to_string())).collect()),
            _ => Err(RuntimeError::ExpectedType("list", self)),
        }
    }

    pub fn as_number(self) -> Self {
        match self {
            Value::Number(_) => self,
            Value::Text(a) => match a.parse() {
                Ok(a) => Value::Number(a),
                _ => Value::Null,
            },
            _ => Value::Null,
        }
    }

    pub fn length(self) -> Option<usize> {
        match self {
            Value::Number(a) => Some(a.to_string().len()),
            Value::Text(a) => Some(a.len()),
            Value::Bool(_) => None,
            Value::Null => None,
            Value::List(a) => Some(a.len()),
        }
    }
}
