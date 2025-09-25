use std::{collections::{BTreeMap, VecDeque}, fmt::Display, ops::Deref};

use crate::propositional::norm::NnFormula;

#[derive(Debug)]
pub enum TableauxResult {
    /// The formula is unsatisfiable
    Unsatisfiable,
    /// The formula is satisfiable and the attached map is a satisfying model
    Satisfiable(BTreeMap<char, bool>),
}
pub enum NegatedTableauxResult {
    /// The formula is valid (all interpretations satisfy the formula)
    Valid,
    /// The formula is falsifiable and the attached map is a counter-model
    Falsifiable(BTreeMap<char, bool>),
}

impl NnFormula {
    /// Uses the semantic tableaux to determine if the formula is satisfiable
    pub fn is_satisfiable(&self) -> TableauxResult {
        let mut branch = Branch::NEW;
        if tableaux(&mut branch, [self]) {
            TableauxResult::Unsatisfiable
        } else {
            TableauxResult::Satisfiable(branch.into_model())
        }
    }
    /// Runs `is_satifisable` on ~self
    #[inline]
    pub fn is_valid(&self) -> NegatedTableauxResult {
        match self.not().is_satisfiable() {
            TableauxResult::Unsatisfiable => NegatedTableauxResult::Valid,
            TableauxResult::Satisfiable(cm) => NegatedTableauxResult::Falsifiable(cm),
        }
    }

    /// Returns `true` if `self` is the negation of `other` (or equivalently vice versa)
    pub fn contradicts(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Atom(p1, c1), Self::Atom(p2, c2)) => p1 == p2 && c1 != c2,
            // ~(a | b) <=> ~a & ~b
            (Self::Disjunction(a1, b1), Self::Conjunction(a2, b2)) |
            // ~(a & b) <=> ~a | ~b
            (Self::Conjunction(a1, b1), Self::Disjunction(a2, b2)) => a1.contradicts(a2) && b1.contradicts(b2),
            _ => false,
        }
    }
}
#[derive(Debug, Clone)]
struct Branch<'a> {
    facts: VecDeque<&'a NnFormula>,
    predicates: BTreeMap<char, bool>,
}
impl<'a> Branch<'a> {
    const NEW: Self = Self{facts: VecDeque::new(), predicates: BTreeMap::new()};
    fn contradicts(&self, new_fact: &NnFormula) -> bool {
        for fact in &self.facts {
            if fact.contradicts(new_fact) {
                return true;
            }
        }
        false
    }
    #[inline]
    fn insert(&mut self, new_fact: &'a NnFormula) {
        if matches!(new_fact, NnFormula::Atom(_, _)) {
            // push atoms to the front because they are the most important facts
            self.facts.push_front(new_fact);
        } else {
            self.facts.push_back(new_fact);
        }
    }
    #[inline]
    fn unused_fact(&mut self) -> Option<&'a NnFormula> {
        self.facts.pop_front()
    }
    /// Returns true if the insertion was uncontradictory and we should continue, false if there was a contradiction and we should stop
    #[must_use]
    fn set_predicate(&mut self, pr: char, truth: bool) -> bool {
        self.predicates.insert(pr, truth)
            .map(|known_truth| truth == known_truth)
            .unwrap_or(true)
    }
    fn into_model(self) -> BTreeMap<char, bool> {
        debug_assert!(self.facts.is_empty(), "{self}");
        self.predicates
    }
}
#[inline]
fn tableaux<'a>(branch: &mut Branch<'a>, new_facts: impl IntoIterator<Item=&'a NnFormula>) -> bool {
    for new_fact in new_facts {
        if branch.contradicts(new_fact) {
            return true;
        }
        branch.insert(new_fact);
    }
    apply_rule(branch)
}
fn apply_rule(branch: &mut Branch) -> bool {
    let Some(unused_fact) = branch.unused_fact() else {
        // no new rules!! this means it _is_ satisfiable and we can end now
        return false;
    };
    match unused_fact {
        // set the predicate and loop back to apply a new rule if the new predicate was uncontradictory
        // if it is contradictory however, this branch will close here
        // notice that this is a logical implication!
        &NnFormula::Atom(p, t) => !branch.set_predicate(p, t) || apply_rule(branch),
        // add two new facts and check if they close the branch, (if they don't this function will be called again to try and apply a new rule)
        NnFormula::Conjunction(f, f1) => tableaux(branch, [f.deref(), f1.deref()]),
        // adds one the first fact to the branch and sees if that branch is closeable and if it is we do the same with the second
        // iff both sub-branches are closed, we 
        NnFormula::Disjunction(f, f1) => {
            // store the original branch in its own binding, so that if the first branch doesn't close, ITS branch bubbles up
            let orig_branch = branch.clone();
            tableaux(branch, [f.deref()]) &&
            tableaux({*branch = orig_branch; branch}, [f1.deref()])
        }
    }
}

impl Display for Branch<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut comma = false;
        for (p, t) in &self.predicates {
            if comma {
                write!(f, ", ")?;
            } else {
                comma = true;
            }
            if *t {
                write!(f, "¬")?;
            }
            write!(f, "{p}")?;
        }
        for fact in &self.facts {
            if comma {
                write!(f, ", ")?;
            } else {
                comma = true;
            }
            
            write!(f, "{fact}")?;
        }
        Ok(())
    }
}
