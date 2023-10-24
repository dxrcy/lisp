use std::{cmp, collections::HashMap, fmt, fs, ops, str::Chars};

fn main() {
    let file = fs::read_to_string("example").unwrap();

    let tree = lex(file);
    // println!("{:#?}", tree);

    let tree = parse(tree);
    // println!("{:#?}", tree);

    let result = run(tree);
    if result != Value::Null {
        println!(">> {}", result);
    }
}

#[derive(Clone, Debug, Default, PartialEq)]
enum Value {
    #[default]
    Null,
    Text(String),
    Number(i32),
    Bool(bool),
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

impl ops::Mul for Value {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (self, rhs) {
            (V::Number(a), V::Number(b)) => V::Number(a * b),
            _ => panic!("type mismatch"),
        }
    }
}
impl ops::Add for Value {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        use Value as V;
        match (self, rhs) {
            (V::Number(a), V::Number(b)) => V::Number(a + b),
            _ => panic!("type mismatch"),
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

type Variables = HashMap<String, Value>;

fn run(expr: Expr) -> Value {
    let mut vars = Variables::new();
    run_part(expr, &mut vars, 0)
}

fn run_part(expr: Expr, vars: &mut Variables, depth: usize) -> Value {
    match expr {
        Expr::Method(Method { name, args }) => {
            // println!("{}:: {:?}", "  ".repeat(depth), name);
            // println!("{:?}", vars);

            let mut args = args.into_iter();

            /// Get next argument, without evaluating (lazy)
            macro_rules! arg_expr {
                () => {
                    args.next().expect("missing argument")
                };
            }
            /// Evaluate an expression
            macro_rules! eval {
                ( $expr:expr ) => {
                    run_part($expr, vars, depth + 1)
                };
            }
            /// Get next argument, and evaluate
            macro_rules! arg {
                () => {
                    eval!(arg_expr!())
                };
            }
            macro_rules! eval_all {
                ( $args:expr ) => {
                    $args.map(|arg| eval!(arg)).last().unwrap_or_default()
                };
            }

            match name.as_str() {
                "do" => eval_all!(args),
                "print" => {
                    for arg in args {
                        print!("{}", eval!(arg));
                    }
                    println!();
                    Value::Null
                }
                "*" => arg!() * arg!(),
                "+" => arg!() + arg!(),
                "<" => Value::Bool(arg!() < arg!()),
                "set" | "=" => {
                    let Expr::Variable(name) = arg_expr!() else {
                        panic!("variable name must be string");
                    };
                    let value = arg!();
                    vars.insert(name, value);
                    Value::Null
                }
                "+=" => {
                    let Expr::Variable(name) = arg_expr!() else {
                        panic!("variable name must be string");
                    };
                    let rhs = arg!();
                    let value = vars.get_mut(&name).expect("variable not set");
                    *value = value.clone() + rhs;
                    Value::Null
                }
                "while" => {
                    let condition = arg_expr!();

                    let mut last = Value::Null;
                    while eval!(condition.clone()) == Value::Bool(true) {
                        last = eval_all!(args.clone());
                    }
                    last
                }
                "for" => {
                    let _ = arg!();
                    let condition = arg_expr!();
                    let run_each = arg_expr!();

                    let mut last = Value::Null;
                    while eval!(condition.clone()) == Value::Bool(true) {
                        last = eval_all!(args.clone());
                        eval!(run_each.clone());
                    }
                    last
                }
                _ => panic!("unknown method `{}`", name),
            }
        }
        Expr::Literal(value) => value,
        Expr::Variable(name) => vars
            .get(&name)
            .cloned()
            .expect(&format!("undefined variable `{}`", name)),
    }
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
    parse_part(token, 0)
}

fn parse_part(token: Token, depth: usize) -> Expr {
    assert!(depth < 20, "max depth");

    match token {
        Token::Text(text) => parse_text_token(text),
        Token::Group(tree) => {
            let mut tokens = tree.0.into_iter();
            let name = tokens.next().expect("empty group");
            let Token::Text(name) = name else {
                panic!("group must start with name");
            };
            let args = tokens.map(|arg| parse_part(arg, depth + 1)).collect();
            return Expr::Method(Method { name, args });
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
        return Expr::Literal(Value::Text(chars.as_str().to_string()));
    }
    if let Ok(number) = text.parse() {
        return Expr::Literal(Value::Number(number));
    }
    if is_valid_variable_name(&text) {
        return Expr::Variable(text);
    }
    panic!("unexpected token `{}`", text)
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

    while let Some(ch) = chars.next() {
        if ch == '"' {
            in_quote ^= true;
        } else if !in_quote {
            match ch {
                '(' => {
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
                    }
                    current_text = String::new();
                    continue;
                }
                _ => (),
            }
        }

        current_text.push(ch);
    }

    if !current_text.is_empty() {
        tree.push(Token::Text(current_text));
    }
    TokenTree(tree)
}
