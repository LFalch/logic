use std::collections::BTreeSet;

use super::Formula;

#[derive(Debug, Clone, PartialEq, Eq)]
// Negative normal form of formula
pub enum NnFormula {
    Atom(char, bool),
    Conjunction(Box<Self>, Box<Self>),
    Disjunction(Box<Self>, Box<Self>),
}
impl NnFormula {
    pub fn and(self, o: Self) -> Self {
        Self::Conjunction(Box::new(self), Box::new(o))
    }
    pub fn or(self, o: Self) -> Self {
        Self::Disjunction(Box::new(self), Box::new(o))
    }
    pub fn not(self) -> Self {
        match self {
            NnFormula::Atom(c, p) => NnFormula::Atom(c, !p),
            NnFormula::Conjunction(f, f1) => f.not().or(f1.not()),
            NnFormula::Disjunction(f, f1) => f.not().and(f1.not()),
        }
    }
}

#[inline]
pub fn nnf(formula: Formula) -> NnFormula {
    nnf_inner(formula, true)
}
fn nnf_inner(formula: Formula, positive: bool) -> NnFormula {
    match (formula, positive) {
        (Formula::Atom(c), p) => NnFormula::Atom(c, p),
        (Formula::Not(f), p) => nnf_inner(*f, !p),
        (Formula::Conjunction(f, f1), true) => NnFormula::Conjunction(
            Box::new(nnf_inner(*f, true)),
            Box::new(nnf_inner(*f1, true)),
        ),
        (Formula::Disjunction(f, f1), true) => NnFormula::Disjunction(
            Box::new(nnf_inner(*f, true)),
            Box::new(nnf_inner(*f1, true)),
        ),
        (Formula::Conjunction(f, f1), false) => NnFormula::Disjunction(
            Box::new(nnf_inner(*f, false)),
            Box::new(nnf_inner(*f1, false)),
        ),
        (Formula::Disjunction(f, f1), false) => NnFormula::Conjunction(
            Box::new(nnf_inner(*f, false)),
            Box::new(nnf_inner(*f1, false)),
        ),
        (Formula::Implication(f, f1), true) => NnFormula::Disjunction(
            Box::new(nnf_inner(*f, false)),
            Box::new(nnf_inner(*f1, true)),
        ),
        (Formula::Implication(f, f1), false) => NnFormula::Conjunction(
            Box::new(nnf_inner(*f, true)),
            Box::new(nnf_inner(*f1, false)),
        ),
        (Formula::Equivalance(f, f1), true) => NnFormula::Conjunction(
            Box::new(NnFormula::Disjunction(
                Box::new(nnf_inner((*f).clone(), false)),
                Box::new(nnf_inner((*f1).clone(), true)),
            )),
            Box::new(NnFormula::Disjunction(
                Box::new(nnf_inner(*f, true)),
                Box::new(nnf_inner(*f1, false)),
            )),
        ),
        (Formula::Equivalance(f, f1), false) => NnFormula::Disjunction(
            Box::new(NnFormula::Conjunction(
                Box::new(nnf_inner((*f).clone(), false)),
                Box::new(nnf_inner((*f1).clone(), true)),
            )),
            Box::new(NnFormula::Conjunction(
                Box::new(nnf_inner(*f, true)),
                Box::new(nnf_inner(*f1, false)),
            )),
        ),
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClausalForm {
    pub conjunction: BTreeSet<BTreeSet<(char, bool)>>,
}
impl ClausalForm {
    pub fn new(
        conjunction: impl IntoIterator<Item = impl IntoIterator<Item = (char, bool)>>,
    ) -> Self {
        Self {
            conjunction: conjunction
                .into_iter()
                .map(|i| i.into_iter().collect())
                .collect(),
        }
    }
    pub fn one(p: char, t: bool) -> Self {
        let mut conjunction = BTreeSet::new();
        let mut disjunction = BTreeSet::new();
        disjunction.insert((p, t));
        conjunction.insert(disjunction);
        Self { conjunction }
    }
    pub fn union(self, other: Self) -> Self {
        let (mut a, mut b) = (self, other);
        if a.conjunction.len() > b.conjunction.len() {
            a.conjunction.append(&mut b.conjunction);
            a
        } else {
            b.conjunction.append(&mut a.conjunction);
            b
        }
    }
    pub fn is_valid(&self) -> bool {
        self.conjunction
            .iter().all(|disjunction| {
                let mut last_false = None;
                for &(p, t) in disjunction {
                    if let Some(false_p) = last_false {
                        if p == false_p {
                            return true;
                        }
                    }
                    if !t {
                        last_false = Some(p);
                    }
                }
                false
            })
    }
    pub fn is_satisfiable(&self) -> bool {
        let mut true_set = BTreeSet::new();
        let mut false_set = BTreeSet::new();
        eprintln!();
        eprintln!("{:?}", self.conjunction);
        satis_helper(&mut true_set, &mut false_set, self.conjunction.iter())
    }
}
fn satis_helper<'a>(true_set: &mut BTreeSet<char>, false_set: &mut BTreeSet<char>, mut conjunction_rest: impl Iterator<Item=&'a BTreeSet<(char, bool)>> + Clone) -> bool {
    eprintln!("true: {true_set:?}, false: {false_set:?}");

    if let Some(assignments) = conjunction_rest.next() {
        eprintln!("  need to assign: {assignments:?}");
        let mut satisfiable = false;
        for &(p, b) in assignments {
            if b {
                if !false_set.contains(&p) {
                    // do not try to assign a predicate to true if it's already assigned false
                    let remove_after = true_set.insert(p);
                    if satis_helper(true_set, false_set, conjunction_rest.clone()) {
                        satisfiable = true;
                        break;
                    }
                    if remove_after {
                        true_set.remove(&p);
                    }
                }
            } else {
                if !true_set.contains(&p) {
                    let remove_after = false_set.insert(p);
                    if satis_helper(true_set, false_set, conjunction_rest.clone()) {
                        satisfiable = true;
                        break;
                    }
                    if remove_after {
                        false_set.remove(&p);
                    }
                }
            }
        }
        if !satisfiable {
            eprintln!("aww :(");
            return false;
        }
    }
    eprintln!("yay!");
    true
}

pub fn cnf(formula: NnFormula) -> ClausalForm {
    match formula {
        NnFormula::Atom(p, t) => ClausalForm::one(p, t),
        NnFormula::Conjunction(a, b) => cnf(*a).union(cnf(*b)),
        NnFormula::Disjunction(a, b) => {
            let mut a = cnf(*a).conjunction;
            let mut b = cnf(*b).conjunction;
            assert!(!(a.is_empty() || b.is_empty()));
            if a.len() + b.len() == 2 {
                let mut a = a.pop_first().unwrap();
                let mut b = b.pop_first().unwrap();
                a.append(&mut b);
                let mut conjunction = BTreeSet::new();
                conjunction.insert(a);
                return ClausalForm { conjunction };
            }

            let (smaller, larger) = if a.len() > b.len() { (a, b) } else { (b, a) };

            let mut conjunction = BTreeSet::new();

            for a in smaller {
                for b in larger.iter() {
                    conjunction.insert(a.iter().copied().chain(b.iter().copied()).collect());
                    // a or b1 and a or b2 and a or b3
                }
            }

            // A or ((B and C) and D) ->
            // A or (B and C) and A or D ->
            // A or B and A or C and A or D

            ClausalForm { conjunction }
        }
    }
}

#[cfg(test)]
mod tests {
    const P: Formula = Formula::Atom('p');
    const Q: Formula = Formula::Atom('q');
    const R: Formula = Formula::Atom('r');
    const S: Formula = Formula::Atom('s');

    const NP: NnFormula = NnFormula::Atom('p', true);
    const NQ: NnFormula = NnFormula::Atom('q', true);
    const NR: NnFormula = NnFormula::Atom('r', true);
    const NS: NnFormula = NnFormula::Atom('s', true);

    use super::{ClausalForm, Formula, NnFormula, cnf, nnf};
    #[test]
    fn nnf_basic() {
        assert_eq!(
            nnf(P.or(Q.not()).and(P.not().or(Q))),
            NP.or(NQ.not()).and(NP.not().or(NQ))
        );
        // (p → ¬q) ∨ ¬(r ∧ q)
        // ¬p ∨ ¬q ∨ ¬r ∨ ¬q
        assert_eq!(
            nnf((P.implies(!Q)).or(!(R.and(Q)))),
            NP.not().or(NQ.not()).or(NR.not().or(NQ.not())),
        );
        // ¬(¬p → ¬q) ∧ r
        // ¬p ∧ q ∧ r
        assert_eq!(
            nnf((P.not().implies(!Q)).not().and(R)),
            NP.not().and(NQ).and(NR),
        );
        // ¬(¬p → q ∧ ¬r)
        // (¬p ∧ ¬q) ∨ r
        assert_eq!(
            nnf(!((P.not().implies(Q)).and(!R))),
            NP.not().and(NQ.not()).or(NR),
        );
        assert_ne!(nnf(S), NS.not());
    }
    #[test]
    fn cnf_basic() {
        assert_eq!(
            cnf(nnf(P.or(Q.not()).and(P.not().or(Q)))),
            ClausalForm::new([[('p', false), ('q', true)], [('p', true), ('q', false)]]),
        );
        // (p → ¬q) ∨ ¬(r ∧ q)
        // ¬p ∨ ¬q ∨ ¬r ∨ ¬q
        assert_eq!(
            cnf(nnf((P.implies(!Q)).or(!(R.and(Q))))),
            ClausalForm::new([[('p', false), ('q', false), ('r', false)]],)
        );
        // ¬(¬p → ¬q) ∧ r
        // ¬p ∧ q ∧ r
        assert_eq!(
            cnf(nnf((P.not().implies(!Q)).not().and(R))),
            ClausalForm::new([[('q', true)], [('p', false)], [('r', true)]],)
        );
        // ¬(¬p → q ∧ ¬r)
        // (¬p ∧ ¬q) ∨ r
        // (¬p ∨ r) ∧ ¬q ∨ r
        assert_eq!(
            cnf(nnf(!((P.not().implies(Q)).and(!R)))),
            ClausalForm::new([[('q', false), ('r', true)], [('p', false), ('r', true)],])
        );
        assert_ne!(nnf(S), NS.not());
    }
    #[test]
    fn valid() {
        let f = cnf(nnf(P.or(Q.not()).and(P.not().or(Q))));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        // (p → ¬q) ∨ ¬(r ∧ q)
        // ¬p ∨ ¬q ∨ ¬r ∨ ¬q
        let f = cnf(nnf((P.implies(!Q)).or(!(R.and(Q)))));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        // ¬(¬p → ¬q) ∧ r
        // ¬p ∧ q ∧ r
        let f = cnf(nnf((P.not().implies(!Q)).not().and(R)));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        // ¬(¬p → q ∧ ¬r)
        // (¬p ∧ ¬q) ∨ r
        // (¬p ∨ r) ∧ ¬q ∨ r
        let f = cnf(nnf(!((P.not().implies(Q)).and(!R))));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        let f = cnf(nnf(P.implies(Q).implies(Q.not().implies(!P))));
        assert!(f.is_valid(), "{f:?}");
        assert!(f.is_satisfiable());
        let f = cnf(nnf(P.or(!P).implies(P.and(!P))));
        assert!(!f.is_valid());
        assert!(!f.is_satisfiable());

        let f = cnf(nnf( !(P | Q) >> (!P & !Q) ));
        assert!(f.is_valid());
        assert!(f.is_satisfiable());
        let f = cnf(nnf( ((P >> Q) >> R) >> ((P & Q) >> R) ));
        assert!(f.is_valid());
        assert!(f.is_satisfiable());
        let f = cnf(nnf( (P >> (Q >> R)) >> ((P | Q) >> R) ));
        assert!(!f.is_valid());
        println!("sat? {}", ((P >> (Q >> R)) >> ((P | Q) >> R)).satisfiable());
        assert!(f.is_satisfiable());
        let f = cnf(nnf( !(!(P | Q) >> (!P & Q)) ));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
    }
}
