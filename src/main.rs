use std::{env::args, error::Error, io::stdin};

use logic::{first_order, lk_calc::{tree, PrintDirect}, Formula};

fn main() -> Result<(), Box<dyn Error>> {
    let prop_mode = args().skip(1).any(|s| s == "-p" || s == "--propositional");
    if prop_mode {
        propositional_loop()
    } else {
        first_order_loop()
    }
}

fn propositional_loop() -> Result<(), Box<dyn Error>> {
    loop {
        let mut s = String::new();
        if stdin().read_line(&mut s)? == 0 {
            break;
        }
        s.pop();
        if s.is_empty() {
            continue;
        }

        let f: Formula = match s.parse() {
            Ok(f) => f,
            Err(e) => {
                eprintln!("{e}");
                continue;
            }
        };
        println!("{f}");
        tree(&mut PrintDirect::default(), &f);
    }
    Ok(())
}
fn first_order_loop() -> Result<(), Box<dyn Error>> {
    loop {
        let mut s = String::new();
        if stdin().read_line(&mut s)? == 0 {
            break;
        }
        s.pop();
        if s.is_empty() {
            continue;
        }

        let f: first_order::Formula = match s.parse() {
            Ok(f) => f,
            Err(e) => {
                eprintln!("{e}");
                continue;
            }
        };
        println!("{f}");
        first_order::lk_calc::tree(&mut first_order::lk_calc::PrintDirect::default(), &f);
    }
    Ok(())
}
