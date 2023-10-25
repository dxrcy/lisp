mod lex;
mod parse;
mod run;
mod value;

use crate::lex::lex;
use crate::parse::parse;
use crate::run::run;
pub use crate::value::Value;

pub fn run_file(file: String) -> Result<Value, RuntimeError> {
    let tree = lex(file);
    let tree = parse(tree);
    let result = run(tree);
    result
}

#[derive(Debug, thiserror::Error)]
pub enum RuntimeError {
    #[error("cannot use this operation with these types\n   left: {0:?}\n  right: {1:?}")]
    TypeMismatch(Value, Value),
    #[error("the expected type was not given\n  expected: {{{0}}}\n    actual: {1:?}")]
    ExpectedType(&'static str, Value),
}
