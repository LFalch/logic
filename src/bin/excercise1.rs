use logic::{lk_calc::{self, PrintDirect}, Formula::{self, *}};

use self::Atom as a;

fn main() {
    println!("1.2");
    let i = [('p', false), ('q', true), ('r', true)];
    println!("{}", Atom('p').implies(!Atom('q')).or(!Atom('r').and(Atom('q')))
        .evaluate(i.as_slice()).unwrap()
    );
    println!("{}", (!Atom('p') | !Atom('q')).implies(Atom('p') | !Atom('r'))
        .evaluate(i.as_slice()).unwrap()
    );
    println!("{}", (!((!Atom('p')).implies(!Atom('q'))) | Atom('r'))
        .evaluate(i.as_slice()).unwrap()
    );
    println!("{}", (!((!Atom('p')).implies(Atom('q') & !Atom('r'))))
        .evaluate(i.as_slice()).unwrap()
    );
    println!();
    println!("1.4");
    check_formula((!Atom('p') | Atom('q')) & (Atom('q').implies(!Atom('r') & !Atom('p'))) & (Atom('p') | Atom('r')));
    check_formula(((!Atom('p') | Atom('q')) >> Atom('q') & (Atom('q') >> Atom('r')) & !Atom('r')) >> Atom('p'));
    check_formula(!a('p') & (!a('q') | a('r')) & (!a('p') >> a('q') & !a('r')));

    println!("\n1.6");
    lk_calc::tree(&mut PrintDirect::default(), &( !(a('p') | a('q')) >> (!a('p') & !a('q')) ));
    println!();
    lk_calc::tree(&mut PrintDirect::default(), &( (a('p') | !a('p')) ));
    println!();
    lk_calc::tree(&mut PrintDirect::default(), &( (a('p') >> (a('q')) >> a('r')) >> ((a('p') & a('q')) >> a('r')) ));
    
    println!("\n1.7");
    lk_calc::tree(&mut PrintDirect::default(), &( (a('p') >> (a('q') >> a('r'))) >> ((a('p') | a('q')) >> a('r')) ));
    println!();
    lk_calc::tree(&mut PrintDirect::default(), &( !(!(a('p') | a('q')) >> (!a('p') & a('q'))) ));
    println!();
}

fn check_formula(formula: Formula) {
    println!("{formula}");
    println!("Satisfiable: {}", formula.satisfiable());
    println!("Valid      : {}", formula.valid());
    println!();
}
