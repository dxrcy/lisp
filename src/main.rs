use std::{
    cmp,
    collections::HashMap,
    fmt, fs,
    io::{stdin, stdout, Write},
    ops, process,
    str::Chars,
};

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

#[derive(Debug, Default)]
struct State {
    variables: HashMap<String, Value>,
    methods: HashMap<String, CustomMethod>,
}

#[derive(Clone, Debug)]
struct CustomMethod {
    parameters: Vec<String>,
    body: Vec<Expr>,
}

fn run(expr: Expr) -> Result<Value, RuntimeError> {
    let mut state = State::default();
    run_part(expr, &mut state, 0)
}

fn run_part(expr: Expr, state: &mut State, depth: usize) -> Result<Value, RuntimeError> {
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
                    run_part($expr, state, depth + 1)?
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
                        last = run_part(arg, state, depth + 1)?;
                    }
                    last
                }};
            }
            macro_rules! no_more {
                () => {
                    if args.next().is_some() {
                        panic!("too many arguments!");
                    }
                };
            }
            macro_rules! arith2 {
                ( $op:tt ) => {{
                    let a = eval_arg!();
                    let b = eval_arg!();
                    no_more!();
                    return a $op b;
                }};
            }
            macro_rules! comp2 {
                ( $op:tt ) => {{
                    let a = eval_arg!();
                    let b = eval_arg!();
                    no_more!();
                    Value::Bool(a $op b)
                }};
            }
            macro_rules! logic2 {
                ( $op:tt ) => {{
                    let a = eval_arg!().bool()?;
                    let b = eval_arg!().bool()?;
                    no_more!();
                    Value::Bool(a $op b)
                }};
            }
            macro_rules! func1 {
                ( $($tt:tt)* ) => {{
                    let a = eval_arg!();
                    no_more!();
                    Value::Number(a.number()?.$($tt)*)
                }};
            }

            match name.as_str() {
                "+" => arith2!(+),
                "-" => arith2!(-),
                "*" => arith2!(*),
                "/" => arith2!(/),
                "%" => arith2!(%),
                "==" => comp2!(==),
                "!=" => comp2!(!=),
                "<" => comp2!(<),
                ">" => comp2!(>),
                "<=" => comp2!(<=),
                ">=" => comp2!(>=),
                "and" => logic2!(&&),
                "or" => logic2!(||),
                "sqrt" => func1!(sqrt()),
                "^2" => func1!(powi(2)),
                "round" => func1!(round()),
                "floor" => func1!(floor()),
                "ceil" => func1!(ceil()),
                "not" => {
                    let a = eval_arg!().bool()?;
                    no_more!();
                    Value::Bool(!a)
                }
                "do" => eval_all!(args),
                "exit" => {
                    let code = match args.next() {
                        Some(arg) => eval!(arg).number()? as i32,
                        None => 0,
                    };
                    no_more!();
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
                "set" | "=" => {
                    let Expr::Variable(name) = arg!() else {
                        panic!("variable name must be string");
                    };
                    let value = eval_arg!();
                    no_more!();
                    state.variables.insert(name, value);
                    Value::Null
                }
                "+=" => {
                    let Expr::Variable(name) = arg!() else {
                        panic!("variable name must be string");
                    };
                    let rhs = eval_arg!();
                    no_more!();
                    let value = state.variables.get_mut(&name).expect("variable not set");
                    *value = (value.clone() + rhs)?;
                    Value::Null
                }
                "if" => {
                    let condition = eval_arg!();
                    let happy = arg!();
                    let unhappy = args.next();
                    no_more!();
                    if condition == Value::Bool(true) {
                        eval!(happy)
                    } else {
                        if let Some(unhappy) = unhappy {
                            eval!(unhappy)
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
                "read" => {
                    no_more!();
                    Value::Text(read_input())
                }
                "def" => {
                    let Expr::Method(Method {
                        name,
                        args: param_exprs,
                    }) = arg!()
                    else {
                        panic!("method name must be group with name");
                    };
                    let mut parameters = Vec::new();
                    for param in param_exprs {
                        let Expr::Variable(param) = param else {
                            panic!("method parameter name must be string ");
                        };
                        parameters.push(param);
                    }
                    let body = args.collect();
                    state
                        .methods
                        .insert(name, CustomMethod { parameters, body });
                    Value::Null
                }
                _ => {
                    let method = state.methods.get(&name).cloned();
                    match method {
                        Some(CustomMethod { parameters, body }) => {
                            for param in parameters {
                                let arg = match args.next() {
                                    Some(arg) => eval!(arg),
                                    None => Value::Null,
                                };
                                state.variables.insert(param, arg);
                            }
                            let mut last = Value::Null;
                            for expr in body {
                                last = eval!(expr);
                            }
                            last
                        }
                        None => panic!("unknown method `{}`", name),
                    }
                }
            }
        }
        Expr::Literal(value) => value,
        Expr::Variable(name) => match name.as_str() {
            "COLS" => Value::Number(terminal_size().0 as f32),
            "ROWS" => Value::Number(terminal_size().1 as f32),
            _ => state
                .variables
                .get(&name)
                .cloned()
                .expect(&format!("undefined variable `{}`", name)),
        },
    })
}

fn read_input() -> String {
    let mut s = String::new();
    let _ = stdout().flush();
    stdin()
        .read_line(&mut s)
        .expect("Did not enter a correct string");
    if let Some('\n') = s.chars().next_back() {
        s.pop();
    }
    if let Some('\r') = s.chars().next_back() {
        s.pop();
    }
    s
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
