use std::{env, fs};
use lisp::{run_file, Value};
 
fn main() {
    let mut args = env::args();
    args.next();
    let filename = args.next().unwrap_or("test".to_string());
    let file = fs::read_to_string(filename).expect("Cannot open that file");

    let result = run_file(file);
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
