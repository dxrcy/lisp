use rand::Rng;
use std::{
    collections::HashMap,
    fs,
    io::{stdin, stdout, Write},
    process,
};

use crate::{
    parse::{Expr, Method},
    RuntimeError, Value,
};

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

pub fn run(expr: Expr) -> Result<Value, RuntimeError> {
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
                "add" | "+" => arith2!(+),
                "sub" | "-" => arith2!(-),
                "mul" | "*" => arith2!(*),
                "div" | "/" => arith2!(/),
                "mod" | "%" => arith2!(%),
                "eq" | "==" => comp2!(==),
                "ne" | "!=" => comp2!(!=),
                "lt" | "<" => comp2!(<),
                "gt" | ">" => comp2!(>),
                "le" | "<=" => comp2!(<=),
                "ge" | ">=" => comp2!(>=),
                "and" | "&" => logic2!(&&),
                "or" | "|" => logic2!(||),
                "sqrt" => func1!(sqrt()),
                "^2" => func1!(powi(2)),
                "round" | "|-" => func1!(round()),
                "floor" | "|_" => func1!(floor()),
                "ceil" | "|^" => func1!(ceil()),
                "not" | "!" => {
                    let a = eval_arg!().bool()?;
                    no_more!();
                    Value::Bool(!a)
                }
                "exit" | "!!" => {
                    let code = match args.next() {
                        Some(arg) => eval!(arg).number()? as i32,
                        None => 0,
                    };
                    no_more!();
                    process::exit(code)
                }

                "put" | "->" => {
                    for arg in args {
                        print!("{}", eval!(arg));
                    }
                    Value::Null
                }
                "putl" | "=>" => {
                    for arg in args {
                        print!("{}", eval!(arg));
                    }
                    println!();
                    Value::Null
                }
                "inspect" | "?>" => {
                    for arg in args {
                        println!("{:?}", eval!(arg));
                    }
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
                "inc" | "+=" => {
                    let Expr::Variable(name) = arg!() else {
                        panic!("variable name must be string");
                    };
                    let rhs = eval_arg!();
                    no_more!();
                    let value = state.variables.get_mut(&name).expect("variable not set");
                    *value = (value.clone() + rhs)?;
                    Value::Null
                }
                "if" | "?" => {
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
                "do" | ":" => {
                    eval_all!(args)
                }
                "forever" | "@!" => {
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
                "while" | "@?" => {
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
                "for" | "@:" => {
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
                "break" | "!@" => {
                    state.do_break = true;
                    Value::Null
                }
                "read" | "<-" => {
                    no_more!();
                    Value::Text(read_input())
                }
                "num" | "%0" => {
                    let a = eval_arg!();
                    no_more!();
                    a.as_number()
                }
                "fopen" | "<<" => {
                    let Value::Text(filename) = eval_arg!() else {
                        panic!("filename argument must be string");
                    };
                    no_more!();
                    let file = fs::read_to_string(filename).expect("Failed to open file");
                    Value::Text(file)
                }
                "split" | "<>" => {
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
                "len" | ".#" => {
                    let a = eval_arg!();
                    no_more!();
                    match a.length() {
                        Some(len) => Value::Number(len as f32),
                        None => Value::Null,
                    }
                }
                "get" | ".?" => {
                    let index = eval_arg!().number()?;
                    let list = eval_arg!().list()?;
                    match list.get(index as usize) {
                        Some(item) => item.to_owned(),
                        None => Value::Null,
                    }
                }
                "random" | "!?" => {
                    let mut rng = rand::thread_rng();
                    Value::Number(rng.gen_range(0.0..=1.0))
                }
                "def" | ":=" => {
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
