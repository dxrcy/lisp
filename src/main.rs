use std::{cmp, collections::HashMap, fmt, fs, ops, process, str::Chars};

fn main() {
    let file = fs::read_to_string("example").unwrap();

    let tree = lex(file);
    // println!("{:#?}", tree);

    let tree = parse(tree);
    // println!("{:#?}", tree);

    let result = run(tree);
    match result {
        Ok(result) => {
            if result != Value::Null {
                println!(">> {}", result);
            }
        }
        Err(err) => {
            eprintln!("\x1b[31mRuntime error: \x1b[33m{:?}\x1b[0m", err);
            eprintln!("{}", err);
        }
    }
}

#[derive(Clone, Default, PartialEq)]
enum Value {
    #[default]
    Null,
    Text(String),
    Number(Number),
    Bool(bool),
}
type Number = f32;

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Text(a) => write!(f, "\"{}\"", a),
            Value::Number(a) => write!(f, "{}", a),
            Value::Bool(a) => write!(f, "<{}>", a),
            Value::Null => write!(f, "<null>"),
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
        }
    }
}

impl ops::Add for Value {
    type Output = Result<Self, RuntimeError>;
    fn add(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (&self, &rhs) {
            (V::Number(a), V::Number(b)) => Ok(V::Number(a + b)),
            (V::Text(a), V::Text(b)) => Ok(V::Text(a.clone() + b)),
            _ => Err(RuntimeError::TypeMismatch(self, rhs)),
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
// impl cmp::PartialEq for Value {
//     fn eq(&self, rhs: &Self) -> bool {
//         use Value as V;
//         match (self, rhs) {
//             (V::Text(a), V::Text(b)) => a == b,
//             (V::Number(a), V::Number(b)) => a == b,
//             (V::Bool(a), V::Bool(b)) => a == b,
//             (V::Null, V::Null) => true,
//             _ => false,
//         }
//     }
// }
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
    fn number(self) -> Result<Number, RuntimeError> {
        match self {
            Value::Number(a) => Ok(a),
            _ => Err(RuntimeError::ExpectedType("number", self)),
        }
    }
    fn bool(self) -> Result<bool, RuntimeError> {
        match self {
            Value::Bool(a) => Ok(a),
            _ => Err(RuntimeError::ExpectedType("bool", self)),
        }
    }
}

#[derive(Debug, thiserror::Error)]
enum RuntimeError {
    #[error("cannot use this operation with these types\n   left: {0:?}\n  right: {1:?}")]
    TypeMismatch(Value, Value),
    #[error("the expected type was not given\n  expected: {{{0}}}\n    actual: {1:?}")]
    ExpectedType(&'static str, Value),
}

type Variables = HashMap<String, Value>;

fn run(expr: Expr) -> Result<Value, RuntimeError> {
    let mut vars = Variables::new();
    run_part(expr, &mut vars, 0)
}

fn run_part(expr: Expr, vars: &mut Variables, depth: usize) -> Result<Value, RuntimeError> {
    Ok(match expr {
        Expr::Method(Method { name, args }) => {
            // println!("{}:: {:?}", "  ".repeat(depth), name);
            // println!("{:?}", args);
            // println!("{:?}", vars);

            let mut args = args.into_iter();

            /// Get next argument, without evaluating (lazy)
            macro_rules! arg {
                () => {
                    args.next().expect("missing argument")
                };
            }
            /// Evaluate an expression
            macro_rules! eval {
                () => {
                    compile_error!("what to evaluate?")
                };
                ( $expr:expr ) => {
                    run_part($expr, vars, depth + 1)?
                };
            }
            /// Get next argument, and evaluate
            macro_rules! eval_arg {
                () => {
                    eval!(arg!())
                };
            }
            macro_rules! eval_all {
                ( $args:expr ) => {{
                    let mut last = Value::default();
                    for arg in $args {
                        last = run_part(arg, vars, depth + 1)?;
                    }
                    last
                }};
            }

            match name.as_str() {
                "do" => eval_all!(args),
                "exit" => {
                    let code = match args.next() {
                        Some(arg) => eval!(arg).number()? as i32,
                        None => 0,
                    };
                    process::exit(code)
                }

                "put" => {
                    for arg in args {
                        print!("{}", eval!(arg));
                    }
                    Value::Null
                }
                "putl" => {
                    for arg in args {
                        print!("{}", eval!(arg));
                    }
                    println!();
                    Value::Null
                }
                "+" => return eval_arg!() + eval_arg!(),
                "-" => return eval_arg!() - eval_arg!(),
                "*" => return eval_arg!() * eval_arg!(),
                "/" => return eval_arg!() / eval_arg!(),
                "%" => return eval_arg!() % eval_arg!(),
                "==" => Value::Bool(eval_arg!() == eval_arg!()),
                "!=" => Value::Bool(eval_arg!() != eval_arg!()),
                "<" => Value::Bool(eval_arg!() < eval_arg!()),
                ">" => Value::Bool(eval_arg!() > eval_arg!()),
                "<=" => Value::Bool(eval_arg!() <= eval_arg!()),
                ">=" => Value::Bool(eval_arg!() >= eval_arg!()),
                "and" => Value::Bool(eval_arg!().bool()? && eval_arg!().bool()?),
                "or" => Value::Bool(eval_arg!().bool()? || eval_arg!().bool()?),
                "not" => Value::Bool(!eval_arg!().bool()?),
                "set" | "=" => {
                    let Expr::Variable(name) = arg!() else {
                        panic!("variable name must be string");
                    };
                    let value = eval_arg!();
                    vars.insert(name, value);
                    Value::Null
                }
                "+=" => {
                    let Expr::Variable(name) = arg!() else {
                        panic!("variable name must be string");
                    };
                    let rhs = eval_arg!();
                    let value = vars.get_mut(&name).expect("variable not set");
                    *value = (value.clone() + rhs)?;
                    Value::Null
                }
                "if" => {
                    let condition = eval_arg!();
                    let happy = arg!();
                    let unhappy = args.next();
                    if condition == Value::Bool(true) {
                        eval!(happy)
                    } else {
                        if let Some(arg) = unhappy {
                            eval!(arg)
                        } else {
                            Value::Null
                        }
                    }
                }
                "while" => {
                    let condition = arg!();

                    let mut last = Value::Null;
                    while eval!(condition.clone()) == Value::Bool(true) {
                        last = eval_all!(args.clone());
                    }
                    last
                }
                "for" => {
                    let _ = eval_arg!();
                    let condition = arg!();
                    let run_each = arg!();

                    let mut last = Value::Null;
                    while eval!(condition.clone()) == Value::Bool(true) {
                        last = eval_all!(args.clone());
                        eval!(run_each.clone());
                    }
                    last
                }
                "sqrt" => {
                    let a = eval_arg!().number()?;
                    Value::Number(a.sqrt())
                }
                "^2" => {
                    let a = eval_arg!().number()?;
                    Value::Number(a.powi(2))
                }
                _ => panic!("unknown method `{}`", name),
            }
        }
        Expr::Literal(value) => value,
        Expr::Variable(name) => match name.as_str() {
            "COLS" => Value::Number(terminal_size().0 as f32),
            "ROWS" => Value::Number(terminal_size().1 as f32),
            _ => vars
                .get(&name)
                .cloned()
                .expect(&format!("undefined variable `{}`", name)),
        },
    })
}

fn terminal_size() -> (usize, usize) {
    term_size::dimensions().expect("failed to get terminal size")
}

#[derive(Clone, Debug)]
enum Expr {
    Method(Method),
    Literal(Value),
    Variable(String),
}

#[derive(Clone, Debug)]
struct Method {
    name: String,
    args: Vec<Expr>,
}

fn parse(tree: TokenTree) -> Expr {
    let mut tokens = tree.0.into_iter();
    let Some(token) = tokens.next() else {
        panic!("no tokens!");
    };
    if let Token::Text(_) = token {
        panic!("top level token must be a group");
    }
    assert!(tokens.next().is_none(), "too many tokens");
    parse_part(token, 0).expect("nothing here to run!")
}

fn parse_part(token: Token, depth: usize) -> Option<Expr> {
    assert!(depth < 20, "max depth");

    match token {
        Token::Text(text) => Some(parse_text_token(text)),
        Token::Group(tree) => {
            let mut tokens = tree.0.into_iter();
            let name = tokens.next().expect("empty group");
            let Token::Text(name) = name else {
                panic!("group must start with name");
            };
            if name.starts_with('#') {
                return None;
            }
            let args = tokens
                .map(|arg| parse_part(arg, depth + 1))
                .flatten()
                .collect();
            return Some(Expr::Method(Method { name, args }));
        }
    }
}

fn parse_text_token(text: String) -> Expr {
    match text.as_str() {
        "null" => return Expr::Literal(Value::Null),
        "true" => return Expr::Literal(Value::Bool(true)),
        "false" => return Expr::Literal(Value::Bool(false)),
        _ => (),
    }
    if text.starts_with('"') && text.ends_with('"') {
        let mut chars = text.chars();
        chars.next();
        chars.next_back();
        return Expr::Literal(Value::Text(replace_escaped_chars(chars.as_str())));
    }
    if let Ok(number) = text.parse() {
        return Expr::Literal(Value::Number(number));
    }
    if is_valid_variable_name(&text) {
        return Expr::Variable(text);
    }
    panic!("unexpected token `{}`", text)
}

fn replace_escaped_chars(text: &str) -> String {
    const ESCAPABLE_CHARS: &[[char; 2]] = &[['n', '\n'], ['t', '\t']];

    let mut out = String::new();
    let mut is_escaped = false;
    'a: for ch in text.chars() {
        if is_escaped {
            for [old, new] in ESCAPABLE_CHARS {
                if old == &ch {
                    out.push(*new);
                    is_escaped = false;
                    continue 'a;
                }
            }
            panic!("unknown special character `\\{}`", ch);
        } else if ch == '\\' {
            is_escaped = true;
            continue 'a;
        }
        out.push(ch);
    }
    out
}

fn is_valid_variable_name(text: &str) -> bool {
    for (i, ch) in text.chars().enumerate() {
        match ch {
            'a'..='z' | 'A'..='Z' | '_' | '$' => (),
            '0'..='9' if i > 0 => (),
            _ => return false,
        }
    }
    true
}

#[derive(Debug)]
struct TokenTree(Vec<Token>);
#[derive(Debug)]
enum Token {
    Group(TokenTree),
    Text(String),
}

fn lex(file: String) -> TokenTree {
    let mut chars = file.chars();
    lex_part(&mut chars, 0)
}

fn lex_part(chars: &mut Chars, depth: usize) -> TokenTree {
    assert!(depth < 20, "max depth");

    let mut tree = Vec::new();
    let mut current_text = String::new();
    let mut in_quote = false;
    let mut is_escaped = false;

    while let Some(ch) = chars.next() {
        if in_quote {
            if !is_escaped {
                if ch == '\\' {
                    is_escaped = true;
                } else if ch == '"' {
                    in_quote = false;
                }
            } else {
                is_escaped = false;
            }
        } else {
            match ch {
                '"' => in_quote = true,
                '(' => {
                    if !current_text.is_empty() {
                        tree.push(Token::Text(current_text));
                        current_text = String::new();
                    }
                    tree.push(Token::Group(lex_part(chars, depth + 1)));
                    continue;
                }
                ')' => {
                    assert!(depth > 0, "unexpected closing bracket");
                    if !current_text.is_empty() {
                        tree.push(Token::Text(current_text));
                    }
                    return TokenTree(tree);
                }
                ' ' | '\n' => {
                    if !current_text.is_empty() {
                        tree.push(Token::Text(current_text));
                        current_text = String::new();
                    }
                    continue;
                }
                _ => (),
            }
        }

        current_text.push(ch);
    }

    assert!(!in_quote, "missing closing quote");
    assert!(depth == 0, "missing closing bracket");

    if !current_text.is_empty() {
        tree.push(Token::Text(current_text));
    }
    TokenTree(tree)
}
