use std::{fmt, fs, ops, str::Chars};

fn main() {
    let file = fs::read_to_string("example").unwrap();
    let tree = lex(file);
    println!("{:#?}", tree);
    let tree = parse(tree);
    println!("{:#?}", tree);
    let result = run(tree);
    println!("result: {:?}", result);
}

#[derive(Debug)]
enum Value {
    Text(String),
    Number(i32),
    Null,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Text(a) => write!(f, "{}", a),
            Value::Number(a) => write!(f, "\x1b[32m{}\x1b[0m", a),
            Value::Null => write!(f, "\x1b[31null\x1b[0m"),
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

fn run(expr: Expr) -> Value {
    run_part(expr, 0)
}

fn run_part(expr: Expr, depth: usize) -> Value {
    match expr {
        Expr::Method(Method { name, args }) => {
            println!("{}:: {:?}", "  ".repeat(depth), name);
            let mut args = args.into_iter().map(|arg| run_part(arg, depth + 1));

            macro_rules! arg {
                () => {
                    args.next().expect("missing argument")
                };
            }

            match name.as_str() {
                "print" => {
                    for arg in args {
                        print!("{}", arg);
                    }
                    println!();
                    Value::Null
                }
                "*" => arg!() * arg!(),
                "+" => arg!() + arg!(),
                _ => panic!("unknown method `{}`", name),
            }
        }
        Expr::Literal(value) => value,
        _ => todo!(),
    }
}

#[derive(Debug)]
enum Expr {
    Method(Method),
    Literal(Value),
    Variable(String),
}

#[derive(Debug)]
struct Method {
    name: String,
    args: Vec<Expr>,
}

fn parse(tree: TokenTree) -> Expr {
    let token = Token::Group(tree);
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
    if text == "null" {
        return Expr::Literal(Value::Null);
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
