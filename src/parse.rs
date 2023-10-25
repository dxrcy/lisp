use crate::{
    lex::{Token, TokenTree},
    Value,
};

#[derive(Clone, Debug)]
pub enum Expr {
    Method(Method),
    Literal(Value),
    Variable(String),
}

#[derive(Clone, Debug)]
pub struct Method {
    pub name: String,
    pub args: Vec<Expr>,
}

pub fn parse(mut tree: TokenTree) -> Expr {
    // Wrap in `do` group, so multiple methods can be executed
    tree.tokens.insert(0, Token::Text("do".to_string()));
    parse_part(Token::Group(tree), 0).expect("nothing here to run!")
}

fn parse_part(token: Token, depth: usize) -> Option<Expr> {
    assert!(depth < 20, "max depth");

    match token {
        Token::Text(text) => Some(parse_text_token(text)),
        Token::Group(tree) => {
            let mut tokens = tree.tokens.into_iter();
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
        ".n" | "null" => return Expr::Literal(Value::Null),
        ".t" | "true" => return Expr::Literal(Value::Bool(true)),
        ".f" | "false" => return Expr::Literal(Value::Bool(false)),
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
