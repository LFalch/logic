use std::{collections::{BTreeMap, BTreeSet}, fmt::{self, Display}, ops::Bound};

use super::Formula;

pub mod tableaux;

#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd)]
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
    pub fn not(&self) -> Self {
        match self {
            &NnFormula::Atom(c, p) => NnFormula::Atom(c, !p),
            NnFormula::Conjunction(f, f1) => f.not().or(f1.not()),
            NnFormula::Disjunction(f, f1) => f.not().and(f1.not()),
        }
    }
}

#[inline]
pub fn nnf(formula: &Formula) -> NnFormula {
    nnf_inner(formula, true)
}
fn nnf_inner(formula: &Formula, positive: bool) -> NnFormula {
    match (formula, positive) {
        (&Formula::Atom(c), p) => NnFormula::Atom(c, p),
        (Formula::Not(f), p) => nnf_inner(f, !p),
        (Formula::Conjunction(f, f1), true) => NnFormula::Conjunction(
            Box::new(nnf_inner(f, true)),
            Box::new(nnf_inner(f1, true)),
        ),
        (Formula::Disjunction(f, f1), true) => NnFormula::Disjunction(
            Box::new(nnf_inner(f, true)),
            Box::new(nnf_inner(f1, true)),
        ),
        (Formula::Conjunction(f, f1), false) => NnFormula::Disjunction(
            Box::new(nnf_inner(f, false)),
            Box::new(nnf_inner(f1, false)),
        ),
        (Formula::Disjunction(f, f1), false) => NnFormula::Conjunction(
            Box::new(nnf_inner(f, false)),
            Box::new(nnf_inner(f1, false)),
        ),
        (Formula::Implication(f, f1), true) => NnFormula::Disjunction(
            Box::new(nnf_inner(f, false)),
            Box::new(nnf_inner(f1, true)),
        ),
        (Formula::Implication(f, f1), false) => NnFormula::Conjunction(
            Box::new(nnf_inner(f, true)),
            Box::new(nnf_inner(f1, false)),
        ),
        (Formula::Equivalance(f, f1), true) => NnFormula::Conjunction(
            Box::new(NnFormula::Disjunction(
                Box::new(nnf_inner(f, false)),
                Box::new(nnf_inner(f1, true)),
            )),
            Box::new(NnFormula::Disjunction(
                Box::new(nnf_inner(f, true)),
                Box::new(nnf_inner(f1, false)),
            )),
        ),
        (Formula::Equivalance(f, f1), false) => NnFormula::Disjunction(
            Box::new(NnFormula::Conjunction(
                Box::new(nnf_inner(f, false)),
                Box::new(nnf_inner(f1, true)),
            )),
            Box::new(NnFormula::Conjunction(
                Box::new(nnf_inner(f, true)),
                Box::new(nnf_inner(f1, false)),
            )),
        ),
    }
}
fn is_subset(sub: &BTreeMap<char, bool>, sup: &BTreeMap<char, bool>) -> bool {
    let mut sup_iter = sup.iter();
    for sub in sub {
        loop {
            // Iterate through sup until we find the same predicate
            // If we don't find it, we return false "early"
            let Some(sup) = sup_iter.next() else {
                return false;
            };
            if sub == sup {
                break;
            }
        }
    }
    // If we kept finding the same element, then it is a subset (although not necessarily a strict subset)
    true
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClausalForm {
    pub conjunction: BTreeSet<BTreeMap<char, bool>>,
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
    pub const fn tautology() -> Self {
        Self {
            conjunction: BTreeSet::new(),
        }
    }
    pub fn one(p: char, t: bool) -> Self {
        let mut conjunction = BTreeSet::new();
        let mut disjunction = BTreeMap::new();
        disjunction.insert(p, t);
        conjunction.insert(disjunction);
        Self { conjunction }
    }
    pub fn and(self, other: Self) -> Self {
        let (mut a, mut b) = (self, other);
        if a.conjunction.len() > b.conjunction.len() {
            a.conjunction.append(&mut b.conjunction);
            a
        } else {
            b.conjunction.append(&mut a.conjunction);
            b
        }
    }
    pub fn or(self, other: Self) -> Self {
        let mut a = self.conjunction;
        let mut b = other.conjunction;
        if a.len() <= 1 && b.len() <= 1 {
            let a = a.pop_first().unwrap_or_default();
            let b = b.pop_first().unwrap_or_default();
            let mut union = BTreeMap::new();
            for (k, v) in a.into_iter().chain(b) {
                if let Some (v2) = union.insert(k, v) && v != v2 {
                    return ClausalForm::tautology();
                }
            }
            let mut conjunction = BTreeSet::new();
            conjunction.insert(union);
            return ClausalForm { conjunction };
        }

        let (smaller, larger) = if a.len() <= b.len() { (a, b) } else { (b, a) };

        let mut conjunction = BTreeSet::new();

        // each disjunction in each of the two conjunctions gets merged with each other, creating up to N*M new disjunctions
        for disj in larger {
            'disj: for other in smaller.iter() {
                let mut disj = disj.clone();
                for (&k, &v) in other.iter() {
                    if let Some(old) = disj.insert(k, v) {
                        if v != old {
                            // if we just overwrote a value with its opposite then this disjunction set
                            // is a tautology and thus we can skip it
                            continue 'disj;
                        }
                    }
                }
                conjunction.insert(disj);
            }
        }

        ClausalForm { conjunction }
    }
    pub fn is_valid(&self) -> bool {
        self.conjunction.is_empty()
    }
    pub fn is_satisfiable(&self) -> bool {
        let mut true_set = BTreeSet::new();
        let mut false_set = BTreeSet::new();
        satis_helper(&mut true_set, &mut false_set, self.conjunction.iter())
    }
    fn remove_supersets(&mut self) -> bool {
        let mut dead = Vec::new();
        for d1 in &self.conjunction {
            for d2 in self.conjunction.range((Bound::Excluded(d1), Bound::Unbounded)) {
                if is_subset(d1, d2) {
                    dead.push(d2.clone());
                } else if is_subset(d2, d1) {
                    dead.push(d1.clone());
                }
            } 
        }
        let any_dead = !dead.is_empty();
        for dead in dead {
            self.conjunction.remove(&dead);
        }
        any_dead
    }
    /// This attempts to reduce itself as much as possible while preserving its truthness for every interpretation
    pub fn simplify(&mut self) {
        if let Some(first) = self.conjunction.first() {
            if first.is_empty() {
                self.conjunction = [first.clone()].into_iter().collect();
            }
        } else {
            return;
        }

        // TODO: check for pairs of disjunctions who are different only by one predicate true in one and false in the other
        // and remove that predicate merging the two (p ∨ Γ) ∧ (¬p ∨ Γ) <=> Γ

        if self.remove_supersets() {
            self.simplify();
        }
    }
}
fn satis_helper<'a>(true_set: &mut BTreeSet<char>, false_set: &mut BTreeSet<char>, mut conjunction_rest: impl Iterator<Item=&'a BTreeMap<char, bool>> + Clone) -> bool {
    if let Some(assignments) = conjunction_rest.next() {
        let mut satisfiable = false;
        for (&p, &b) in assignments {
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
            return false;
        }
    }
    true
}

pub fn cnf(formula: NnFormula) -> ClausalForm {
    match formula {
        NnFormula::Atom(p, t) => ClausalForm::one(p, t),
        NnFormula::Conjunction(a, b) => cnf(*a).and(cnf(*b)),
        NnFormula::Disjunction(a, b) => cnf(*a).or(cnf(*b)),
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
            nnf(&P.or(Q.not()).and(P.not().or(Q))),
            NP.or(NQ.not()).and(NP.not().or(NQ))
        );
        // (p → ¬q) ∨ ¬(r ∧ q)
        // ¬p ∨ ¬q ∨ ¬r ∨ ¬q
        assert_eq!(
            nnf(&(P.implies(!Q)).or(!(R.and(Q)))),
            NP.not().or(NQ.not()).or(NR.not().or(NQ.not())),
        );
        // ¬(¬p → ¬q) ∧ r
        // ¬p ∧ q ∧ r
        assert_eq!(
            nnf(&(P.not().implies(!Q)).not().and(R)),
            NP.not().and(NQ).and(NR),
        );
        // ¬(¬p → q ∧ ¬r)
        // (¬p ∧ ¬q) ∨ r
        assert_eq!(
            nnf(&!((P.not().implies(Q)).and(!R))),
            NP.not().and(NQ.not()).or(NR),
        );
        assert_ne!(nnf(&S), NS.not());
    }
    #[test]
    fn cnf_basic() {
        assert_eq!(
            cnf(nnf(&P.or(Q.not()).and(P.not().or(Q)))),
            ClausalForm::new([[('p', false), ('q', true)], [('p', true), ('q', false)]]),
        );
        // (p → ¬q) ∨ ¬(r ∧ q)
        // ¬p ∨ ¬q ∨ ¬r ∨ ¬q
        assert_eq!(
            cnf(nnf(&(P.implies(!Q)).or(!(R.and(Q))))),
            ClausalForm::new([[('p', false), ('q', false), ('r', false)]],)
        );
        // ¬(¬p → ¬q) ∧ r
        // ¬p ∧ q ∧ r
        assert_eq!(
            cnf(nnf(&(P.not().implies(!Q)).not().and(R))),
            ClausalForm::new([[('q', true)], [('p', false)], [('r', true)]],)
        );
        // ¬(¬p → q ∧ ¬r)
        // (¬p ∧ ¬q) ∨ r
        // (¬p ∨ r) ∧ ¬q ∨ r
        assert_eq!(
            cnf(nnf(&!((P.not().implies(Q)).and(!R)))),
            ClausalForm::new([[('q', false), ('r', true)], [('p', false), ('r', true)],])
        );
        assert_ne!(nnf(&S), NS.not());
    }
    #[test]
    fn valid() {
        let f = cnf(nnf(&P.or(Q.not()).and(P.not().or(Q))));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        // (p → ¬q) ∨ ¬(r ∧ q)
        // ¬p ∨ ¬q ∨ ¬r ∨ ¬q
        let f = cnf(nnf(&(P.implies(!Q)).or(!(R.and(Q)))));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        // ¬(¬p → ¬q) ∧ r
        // ¬p ∧ q ∧ r
        let f = cnf(nnf(&(P.not().implies(!Q)).not().and(R)));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        // ¬(¬p → q ∧ ¬r)
        // (¬p ∧ ¬q) ∨ r
        // (¬p ∨ r) ∧ ¬q ∨ r
        let f = cnf(nnf(&!((P.not().implies(Q)).and(!R))));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
        let f = cnf(nnf(&P.implies(Q).implies(Q.not().implies(!P))));
        assert!(f.is_valid(), "{f:?}");
        assert!(f.is_satisfiable());
        let f = cnf(nnf(&P.or(!P).implies(P.and(!P))));
        assert!(!f.is_valid());
        assert!(!f.is_satisfiable());

        let f = cnf(nnf(&( !(P | Q) >> (!P & !Q) )));
        assert!(f.is_valid());
        assert!(f.is_satisfiable());
        let f = cnf(nnf(&( ((P >> Q) >> R) >> ((P & Q) >> R) )));
        assert!(f.is_valid());
        assert!(f.is_satisfiable());
        let f = cnf(nnf(&( (P >> (Q >> R)) >> ((P | Q) >> R) )));
        assert!(!f.is_valid());
        println!("sat? {}", ((P >> (Q >> R)) >> ((P | Q) >> R)).satisfiable());
        assert!(f.is_satisfiable());
        let f = cnf(nnf( &!(!(P | Q) >> (!P & Q)) ));
        assert!(!f.is_valid());
        assert!(f.is_satisfiable());
    }
    #[test]
    fn simple() {
        let f = !((!(P | Q)) >> (!P & Q));
        let mut cnf = cnf(nnf(&f));
        cnf.simplify();
        assert_eq!(cnf, ClausalForm::new([
            [('p', false)],
            [('q', false)],
        ]));

        let mut cnf = ClausalForm::new([
            vec![('p', false)],
            vec![('p', false), ('q', true), ('r', false)],
            vec![('p', false), ('q', true), ('r', false), ('s', false)],
        ]);
        cnf.simplify();
        let expected_simple = ClausalForm::new([
            vec![('p', false)],
        ]);
        assert_eq!(cnf, expected_simple, "{cnf} != {expected_simple}");
    }
}

impl Display for ClausalForm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        let mut comma = false;
        for disjunction in &self.conjunction {
            if comma {
                write!(f, ", ")?;
            }
            write!(f, "{{")?;
            comma = true;
            let mut comma = false;
            for (&c, &p) in disjunction {
                if comma {
                    write!(f, ", ")?;
                }
                comma = true;
                if !p {
                    write!(f, "¬")?;
                }
                write!(f, "{c}")?;
            }
            write!(f, "}}")?;
        }
        write!(f, "}}")
    }
}
impl Display for NnFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let upper_precedence = f.precision().unwrap_or(0);
        let prec = match self {
            Self::Atom(_, _) => 3,
            Self::Conjunction(_, _) => 2,
            Self::Disjunction(_, _) => 1,
        };

        let parentheses = upper_precedence > prec;
        if parentheses {
            write!(f, "(")?;
        }

        match self {
            &Self::Atom(c, p) => {
                if !p {
                    write!(f, "¬")?;
                }
                write!(f, "{c}")
            }
            Self::Disjunction(f1, f2) => write!(f, "{f1:.prec$} ∨ {f2:.prec$}"),
            Self::Conjunction(f1, f2) => write!(f, "{f1:.prec$} ∧ {f2:.prec$}"),
        }?;
        if parentheses {
            write!(f, ")")?;
        }
        Ok(())
    }
}
