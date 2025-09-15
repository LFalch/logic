use std::{collections::HashSet, fmt::{self, Display}, hash::Hash};

pub mod lk_calc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Variable(char),
    Constant(char),
    Function(char, Box<[Term]>),
}

impl Term {
    pub fn get_symbols(&self) -> impl IntoIterator<Item=char> {
        match self {
            Term::Variable(v) => vec![*v],
            Term::Constant(c) => vec![*c],
            Term::Function(_, terms) => terms
                .into_iter()
                .flat_map(|t| t.get_symbols())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Predicate(char, Box<[Term]>),

    ForAll(char, Box<Formula>),
    ThereExists(char, Box<Formula>),

    Conjunction(Box<Formula>, Box<Formula>),
    Disjunction(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),

    Implication(Box<Formula>, Box<Formula>),
    Equivalance(Box<Formula>, Box<Formula>),
}

fn union<T: Eq + Hash>(a: HashSet<T>, b: HashSet<T>) -> HashSet<T> {
    let mut c = a;
    c.extend(b);
    c
}

impl Formula {
    pub fn get_all_symbols(&self) -> impl IntoIterator<Item=char> {
        match self {
            Formula::Predicate(_, terms) => terms
                .into_iter()
                .flat_map(|t| t.get_symbols())
                .collect::<Vec<_>>(),
            Formula::ForAll(_, formula) => formula.get_all_symbols(),
            Formula::ThereExists(_, formula) => formula.get_all_symbols(),
            Formula::Conjunction(formula, formula1) => formula.get_all_symbols().into_iter().chain(formula1.get_all_symbols()).collect(),
            Formula::Disjunction(formula, formula1) => formula.get_all_symbols().into_iter().chain(formula1.get_all_symbols()).collect(),
            Formula::Not(formula) => formula.get_all_symbols(),
            Formula::Implication(formula, formula1) => formula.get_all_symbols().into_iter().chain(formula1.get_all_symbols()).collect(),
            Formula::Equivalance(formula, formula1) => formula.get_all_symbols().into_iter().chain(formula1.get_all_symbols()).collect(),
        }
    }
    #[inline]
    pub fn get_free_symbols(&self) -> impl IntoIterator<Item=char> {
        self.inner_gfs()
    }
    fn inner_gfs(&self) -> HashSet<char> {
        match self {
            Formula::Predicate(_, terms) => terms
                .into_iter()
                .flat_map(|t| t.get_symbols())
                .collect(),
            Formula::ForAll(v, formula) => {
                let mut set = formula.inner_gfs();
                set.remove(v);
                set
            }
            Formula::ThereExists(v, formula) => {
                let mut set = formula.inner_gfs();
                set.remove(v);
                set
            },
            Formula::Conjunction(formula, formula1) => union(formula.inner_gfs(), formula1.inner_gfs()),
            Formula::Disjunction(formula, formula1) => union(formula.inner_gfs(), formula1.inner_gfs()),
            Formula::Not(formula) => formula.inner_gfs(),
            Formula::Implication(formula, formula1) => union(formula.inner_gfs(), formula1.inner_gfs()),
            Formula::Equivalance(formula, formula1) => union(formula.inner_gfs(), formula1.inner_gfs()),
        }
    }
}

impl Formula {
    pub fn try_to_propositional(&self) -> Option<super::Formula> {
        use super::Formula as Pf;
        Some(match self {
            Formula::Predicate(c, items) => {
                return items.is_empty().then_some(Pf::Atom(*c))
            }
            Formula::Conjunction(f, f2) => Pf::Conjunction(Box::new(f.try_to_propositional()?), Box::new(f2.try_to_propositional()?)),
            Formula::Disjunction(f, f2) => Pf::Disjunction(Box::new(f.try_to_propositional()?), Box::new(f2.try_to_propositional()?)),
            Formula::Not(f) => Pf::Not(Box::new(f.try_to_propositional()?)),
            Formula::Implication(f, f2) => Pf::Implication(Box::new(f.try_to_propositional()?), Box::new(f2.try_to_propositional()?)),
            Formula::Equivalance(f, f2) => Pf::Equivalance(Box::new(f.try_to_propositional()?), Box::new(f2.try_to_propositional()?)),
            Formula::ForAll(_, _) |
            Formula::ThereExists(_, _) => return None,
        })
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Variable(c) => write!(f, "{c}"),
            Term::Constant(c) => write!(f, "{c}"),
            Term::Function(c, terms) => {
                write!(f, "{c}(")?;
                let mut comma = false;
                for term in terms {
                    if comma {
                        write!(f, ", ")?;
                    }
                    write!(f, "{term}")?;
                    comma = true;
                }
                write!(f, ")")
            }
        }
    }
}
impl Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Formula::Predicate(c, terms) => {
                write!(f, "{c}(")?;
                let mut comma = false;
                for term in terms {
                    if comma {
                        write!(f, ", ")?;
                    }
                    write!(f, "{term}")?;
                    comma = true;
                }
                write!(f, ")")
            }
            Formula::ForAll(c, f1) => write!(f, "∀{c} {f1}"),
            Formula::ThereExists(c, f1) => write!(f, "∃{c} {f1}"),
            Formula::Conjunction(f1, f2) => write!(f, "({f1} ∧ {f2})"),
            Formula::Disjunction(f1, f2) => write!(f, "({f1} ∨ {f2})"),
            Formula::Not(f1) => write!(f, "(¬{f1})"),
            Formula::Implication(f1, f2) => write!(f, "({f1} → {f2})"),
            Formula::Equivalance(f1, f2) => write!(f, "({f1} ↔ {f2})"),
        }
    }
}
