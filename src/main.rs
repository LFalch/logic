use std::{error::Error, io::stdin};

use logic::{lk_calc::{tree, PrintDirect}, Formula};


fn main() -> Result<(), Box<dyn Error>> {
    loop {
        let mut s = String::new();
        if stdin().read_line(&mut s)? == 0 {
            break;
        }
        s.pop();

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
