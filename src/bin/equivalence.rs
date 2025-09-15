use logic::{lk_calc::{self, PrintDirect}, Formula::Atom as a};

fn main() {
    // (¬p ∨ q) → q ∧ (q → r) ∧ ¬r  === (q ∧ ¬r) ∧ (¬r → ¬q) ∨ (p ∧ ¬q)
    let l = (!a('p') | a('q')) >> (a('q') & (a('q') >> a('r')) & !a('r'));
    let r = (a('q') & !a('r')) & (!a('r') >> !a('q')) | (a('p') & !a('q'));
    lk_calc::tree(&mut PrintDirect::default(), &l.iff(r));
}

// Better proof:
// (¬p ∨ q) → q ∧ (q → r) ∧ ¬r  === (q ∧ ¬r) ∧ (¬r → ¬q) ∨ (p ∧ ¬q)
// (¬p ∨ q) → q ∧ (¬q ∨ r) ∧ ¬r  === (q ∧ ¬r) ∧ (¬r → ¬q) ∨ (p ∧ ¬q)
// (p ∧ ¬q) ∨ (q ∧ (¬q ∨ r) ∧ ¬r)  === q ∧ ¬r ∧ (r ∨ ¬q) ∨ (p ∧ ¬q)
// (q ∧ (¬q ∨ r) ∧ ¬r)  === q ∧ ¬r ∧ (r ∨ ¬q)
// (q ∧ q ∧ ¬r ∧ ¬r)  === q ∧ ¬r ∧ ¬r ∧ q
// q ∧ ¬r  === q ∧ ¬r
