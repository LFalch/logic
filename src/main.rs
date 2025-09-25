use std::{env::args, error::Error, io::stdin};

use logic::{first_order, propositional::{self, norm::{cnf, nnf}}};

fn main() -> Result<(), Box<dyn Error>> {
    let prop_mode = args().skip(1).any(|s| s == "-p" || s == "--propositional");
    let disprove_mode = args().skip(1).any(|s| s == "-t" || s == "--tableaux");
    if disprove_mode {
        tableaux_loop()
    } else if prop_mode {
        propositional_loop()
    } else {
        first_order_loop()
    }
}

fn propositional_loop() -> Result<(), Box<dyn Error>> {
    line_loop(|s| {
        let f: propositional::Formula = match s.parse() {
            Ok(f) => f,
            Err(e) => {
                eprintln!("{e}");
                return;
            }
        };
        println!(" f: {f}");
        let nnf = nnf(&f);
        println!("nn: {nnf}");
        let mut cnf = cnf(nnf);
        println!("cn: {}", cnf);
        cnf.simplify();
        println!("cn: {}", cnf);
        drop(cnf);
        propositional::lk_calc::tree(&mut propositional::lk_calc::PrintDirect::default(), &f);
    })
}
fn first_order_loop() -> Result<(), Box<dyn Error>> {
    line_loop(|s| {
        let f: first_order::Formula = match s.parse() {
            Ok(f) => f,
            Err(e) => {
                eprintln!("{e}");
                return;
            }
        };
        println!("{f}");
        first_order::lk_calc::tree(&mut first_order::lk_calc::PrintDirect::default(), &f);
    })
}
fn line_loop(mut f: impl FnMut(&str)) -> Result<(), Box<dyn Error>> {
    loop {
        let mut s = String::new();
        if stdin().read_line(&mut s)? == 0 {
            break;
        }
        if s.is_empty() {
            continue;
        }

        f(&s)
    }
    Ok(())
}
fn tableaux_loop() -> Result<(), Box<dyn Error>> {
    line_loop(|s| {
        let f: propositional::Formula = match s.parse() {
            Ok(f) => f,
            Err(e) => {
                eprintln!("{e}");
                return;
            }
        };
        let nnf = nnf(&f);
        println!("f   : {f}");
        drop(f);
        println!("nnf : {nnf}");
        let satisfiable = !nnf.prove_tableaux();
        println!("sat?: {satisfiable}");
    })
}
