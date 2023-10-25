use std::str::Chars;

#[derive(Debug)]
pub struct TokenTree {
    pub tokens: Vec<Token>,
}

#[derive(Debug)]
pub enum Token {
    Group(TokenTree),
    Text(String),
}

pub fn lex(file: String) -> TokenTree {
    let mut chars = file.chars();
    lex_part(&mut chars, 0)
}

fn lex_part(chars: &mut Chars, depth: usize) -> TokenTree {
    assert!(depth < 20, "max depth");

    let mut tokens = Vec::new();
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
                        tokens.push(Token::Text(current_text));
                        current_text = String::new();
                    }
                    tokens.push(Token::Group(lex_part(chars, depth + 1)));
                    continue;
                }
                ')' => {
                    assert!(depth > 0, "unexpected closing bracket");
                    if !current_text.is_empty() {
                        tokens.push(Token::Text(current_text));
                    }
                    return TokenTree { tokens };
                }
                ' ' | '\n' => {
                    if !current_text.is_empty() {
                        tokens.push(Token::Text(current_text));
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
        tokens.push(Token::Text(current_text));
    }
    TokenTree { tokens }
}
