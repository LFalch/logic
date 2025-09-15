use logic::first_order::{lk_calc::{self, PrintDirect}, Formula, Term};

fn exists(x: char, f: Formula) -> Formula {
    Formula::ThereExists(x, Box::new(f))
}
fn forall(x: char, f: Formula) -> Formula {
    Formula::ForAll(x, Box::new(f))
}
fn not(f: Formula) -> Formula {
    Formula::Not(Box::new(f))
}
fn implies(f: Formula, f1: Formula) -> Formula {
    Formula::Implication(Box::new(f), Box::new(f1))
}
fn predicate<const N: usize>(p: char, ts: [Term; N]) -> Formula {
    Formula::Predicate(p, Box::new(ts))
}

const X: Term = Term::Variable('x');
const Y: Term = Term::Variable('y');

const U: Term = Term::Variable('u');
const V: Term = Term::Variable('v');


fn main() {
    let f = implies(
        exists('x', forall('y', implies(not(predicate('S', [Y, Y])), predicate('S', [X, Y])))), 
        exists('x', predicate('S', [X, X]))
    );
    lk_calc::tree(&mut PrintDirect::default(), &f);
    println!();
    println!();

    // ∀x ∃y p(x, y) → ∀u ∃v p(u, v)
    let f = implies(forall('x', exists('y', predicate('p', [X, Y]))), forall('u', exists('v', predicate('p', [U, V]))));
    lk_calc::tree(&mut PrintDirect::default(), &f);
    
    println!();
    println!();

    // ∀x ∃y p(x, y) → ∃v ∀u p(u, v)
    let f = implies(forall('x', exists('y', predicate('p', [X, Y]))), exists('u', forall('v', predicate('p', [U, V]))));
    lk_calc::tree(&mut PrintDirect::default(), &f);
}
