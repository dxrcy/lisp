use rand::Rng;
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
    fn text(self) -> Result<String, RuntimeError> {
        match self {
            Value::Text(a) => Ok(a),
            _ => Err(RuntimeError::ExpectedType("text", self)),
        }
    }
    fn list(self) -> Result<Vec<Value>, RuntimeError> {
        match self {
            Value::List(a) => Ok(a),
            Value::Text(a) => Ok(a.chars().map(|ch| Value::Text(ch.to_string())).collect()),
            _ => Err(RuntimeError::ExpectedType("list", self)),
        }
    }

    fn as_number(self) -> Self {
        match self {
            Value::Number(_) => self,
            Value::Text(a) => match a.parse() {
                Ok(a) => Value::Number(a),
                _ => Value::Null,
            },
            _ => Value::Null,
        }
    }

    fn length(self) -> Option<usize> {
        match self {
            Value::Number(a) => Some(a.to_string().len()),
            Value::Text(a) => Some(a.len()),
            Value::Bool(_) => None,
            Value::Null => None,
            Value::List(a) => Some(a.len()),
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

#[derive(Clone, Debug, Default)]
struct State {
    variables: HashMap<String, Value>,
    methods: HashMap<String, CustomMethod>,
    do_break: bool,
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
    let value = match expr {
        Expr::Method(Method { name, args }) => {
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
                        if state.do_break {
                            break;
                        }
                    }
                    // println!("after loop {}", okay_break);
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
                    (a $op b)?
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
                "inspect" => {
                    for arg in args {
                        println!("{:?}", eval!(arg));
                    }
                    Value::Null
                }
                "=" => {
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
                "do" => {
                    // println!("forever");
                    eval_all!(args)
                }
                "forever" => {
                    // println!("forever");
                    let mut last;
                    loop {
                        last = eval_all!(args.clone());
                        if state.do_break {
                            state.do_break = false;
                            break;
                        }
                    }
                    last
                }
                "while" => {
                    // println!("while");
                    let condition = arg!();

                    let mut last = Value::Null;
                    while eval!(condition.clone()) == Value::Bool(true) {
                        last = eval_all!(args.clone());
                        if state.do_break {
                            state.do_break = false;
                            break;
                        }
                    }
                    last
                }
                "for" => {
                    // println!("for");
                    let _ = eval_arg!();
                    let condition = arg!();
                    let run_each = arg!();

                    let mut last = Value::Null;
                    while eval!(condition.clone()) == Value::Bool(true) {
                        last = eval_all!(args.clone());
                        if state.do_break {
                            state.do_break = false;
                            break;
                        }
                        eval!(run_each.clone());
                    }
                    last
                }
                "break" => {
                    state.do_break = true;
                    // println!("call break");
                    Value::Null
                }
                "read" => {
                    no_more!();
                    Value::Text(read_input())
                }
                "num" => {
                    let a = eval_arg!();
                    no_more!();
                    a.as_number()
                }
                "fopen" => {
                    let Value::Text(filename) = eval_arg!() else {
                        panic!("filename argument must be string");
                    };
                    no_more!();
                    let file = fs::read_to_string(filename).expect("Failed to open file");
                    Value::Text(file)
                }
                "split" => {
                    let delim = eval_arg!().text()?;
                    let input = eval_arg!().text()?;
                    no_more!();
                    Value::List(
                        input
                            .split(&delim)
                            .map(|text| Value::Text(text.to_string()))
                            .collect(),
                    )
                }
                "len" => {
                    let a = eval_arg!();
                    no_more!();
                    match a.length() {
                        Some(len) => Value::Number(len as f32),
                        None => Value::Null,
                    }
                }
                "get" => {
                    let index = eval_arg!().number()?;
                    let list = eval_arg!().list()?;
                    match list.get(index as usize) {
                        Some(item) => item.to_owned(),
                        None => Value::Null,
                    }
                }
                "random" => {
                    let mut rng = rand::thread_rng();
                    Value::Number(rng.gen_range(0.0..=1.0))
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
                            let old_state = state.clone();
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
                            *state = old_state;
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
    };

    Ok(value)
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
    if text == "[]" {
        return Expr::Literal(Value::List(Vec::new()));
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
