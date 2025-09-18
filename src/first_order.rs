use std::{collections::HashSet, fmt::{self, Display}, hash::Hash};

use crate::propositional;

pub mod lk_calc;
pub mod parse;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Variable(char),
    Constant(char),
    Function(char, Box<[Term]>),
}

impl Term {
    pub fn func<const N: usize>(f: char, ts: [Term; N]) -> Self {
        Self::Function(f, Box::new(ts))
    }
    pub fn make_const(&mut self) {
        match *self {
            Term::Variable(c) => *self = Term::Constant(c),
            Term::Constant(_) => (),
            Term::Function(_, _) => unreachable!("only variables should be made const"),
        }
    }
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

fn union<T: Eq + Hash>(a: HashSet<T>, b: HashSet<T>) -> HashSet<T> {
    let mut c = a;
    c.extend(b);
    c
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

impl Formula {
    pub fn predicate<const N: usize>(p: char, ts: [Term; N]) -> Formula {
        Formula::Predicate(p, Box::new(ts))
    }
    pub fn forall(x: char, f: Formula) -> Formula {
        Formula::ForAll(x, Box::new(f))
    }
    pub fn exists(x: char, f: Formula) -> Formula {
        Formula::ThereExists(x, Box::new(f))
    }
    pub fn and(a: Formula, b: Formula) -> Self {
        Self::Conjunction(Box::new(a), Box::new(b))
    }
    pub fn or(a: Formula, b: Formula) -> Self {
        Self::Disjunction(Box::new(a), Box::new(b))
    }
    pub fn not(f: Formula) -> Formula {
        Formula::Not(Box::new(f))
    }
    pub fn implies(f: Formula, f1: Formula) -> Formula {
        Formula::Implication(Box::new(f), Box::new(f1))
    }
    pub fn iff(f: Formula, f1: Formula) -> Formula {
        Formula::Implication(Box::new(f), Box::new(f1))
    }
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
    const fn precedence(&self) -> u8 {
        match self {
            Formula::Predicate(_, _) => 255,
            Formula::ThereExists(_, _) => 20,
            Formula::ForAll(_, _) => 18,
            Formula::Not(_) => 16,
            Formula::Conjunction(_, _) => 14,
            Formula::Disjunction(_, _) => 12,
            Formula::Implication(_, _) => 6,
            Formula::Equivalance(_, _) => 4,
        }
    }
    pub fn try_to_propositional(&self) -> Option<propositional::Formula> {
        use propositional::Formula as Pf;
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
        let uprec = f.precision().unwrap_or(0);
        let prec = self.precedence() as usize;

        let parentheses = uprec >= prec;
        if parentheses {
            write!(f, "(")?;
        }
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
            Formula::ForAll(c, f1) => write!(f, "∀{c}. {f1:.prec$}"),
            Formula::ThereExists(c, f1) => write!(f, "∃{c}. {f1:.prec$}"),
            Formula::Conjunction(f1, f2) => write!(f, "{f1:.prec$} ∧ {f2:.prec$}"),
            Formula::Disjunction(f1, f2) => write!(f, "{f1:.prec$} ∨ {f2:.prec$}"),
            Formula::Not(f1) => write!(f, "¬{f1:.prec$}"),
            Formula::Implication(f1, f2) => write!(f, "{f1:.prec$} → {f2:.prec$}"),
            Formula::Equivalance(f1, f2) => write!(f, "{f1:.prec$} ↔ {f2:.prec$}"),
        }?;
        if parentheses {
            write!(f, ")")?;
        }
        Ok(())
    }
}
