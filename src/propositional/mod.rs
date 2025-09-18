use std::{collections::{HashMap, HashSet}, fmt::{self, Display}, ops::{BitAnd, BitOr, Not, Shl, Shr}};

use crate::symtab::Interpretation;

pub mod parse;
pub mod lk_calc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Atom(char),
    Conjunction(Box<Formula>, Box<Formula>),
    Disjunction(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),

    Implication(Box<Formula>, Box<Formula>),
    Equivalance(Box<Formula>, Box<Formula>),
}
impl Formula {
    const fn precedence(&self) -> u8 {
        match self {
            Formula::Atom(_) => 255,
            Formula::Not(_) => 16,
            Formula::Conjunction(_, _) => 14,
            Formula::Disjunction(_, _) => 12,
            Formula::Implication(_, _) => 10,
            Formula::Equivalance(_, _) => 8,
        }
    }
    #[inline]
    pub fn not(self) -> Self {
        Self::Not(Box::new(self))
    }
    #[inline]
    pub fn and(self, b: Self) -> Self {
        Self::Conjunction(Box::new(self), Box::new(b))
    }
    #[inline]
    pub fn or(self, b: Self) -> Self {
        Self::Disjunction(Box::new(self), Box::new(b))
    }
    #[inline]
    pub fn implies(self, other: Self) -> Self {
        Self::Implication(Box::new(self), Box::new(other))
    }
    #[inline]
    pub fn iff(self, other: Self) -> Self {
        Self::Equivalance(Box::new(self), Box::new(other))
    }
    pub fn evaluate(&self, i: &(impl ?Sized + Interpretation)) -> Option<bool> {
        Some(match self {
            &Formula::Atom(symbol) => i.get_symbol(symbol)?,
            Formula::Conjunction(f, f1) => f.evaluate(i)? && f1.evaluate(i)?,
            Formula::Disjunction(f, f1) => f.evaluate(i)? || f1.evaluate(i)?,
            Formula::Not(f) => !f.evaluate(i)?,
            Formula::Implication(f, f1) => !f.evaluate(i)? || f1.evaluate(i)?,
            Formula::Equivalance(f, f1) => f.evaluate(i)? == f1.evaluate(i)?,
        })
    }
    fn inner_collect_symbols(&self, set: &mut HashSet<char>) {
        match self {
            &Formula::Atom(symbol) => {
                set.insert(symbol);
            }
            Formula::Not(f) => f.inner_collect_symbols(set),
            Formula::Conjunction(f, f1) |
            Formula::Disjunction(f, f1) |
            Formula::Implication(f, f1) |
            Formula::Equivalance(f, f1) => {
                f.inner_collect_symbols(set);
                f1.inner_collect_symbols(set);
            },
        }
    }
    pub fn collect_symbols(&self) -> impl Iterator<Item = char> {
        let mut set = HashSet::new();
        self.inner_collect_symbols(&mut set);
        set.into_iter()
    }
    fn inner_valid(&self, i: &mut HashMap<char, bool>, mut iter: std::slice::Iter<char>) -> bool {
        if let Some(&c) = iter.next() {
            i.insert(c, false);
            return self.inner_valid(i, iter.clone()) && {
                i.insert(c, true);
                self.inner_valid(i, iter.clone())
            };
        }

        self.evaluate(i).unwrap()
    }
    /// Checks if the formula is valid i.e. a tautology.
    /// Every set of values for the contained atoms should make the formula evaluate to `true`.
    pub fn valid(&self) -> bool {
        let symbols: Vec<_> = self.collect_symbols().collect();

        self.inner_valid(&mut HashMap::new(), symbols.iter())
    }
    fn inner_satisfiable(&self, i: &mut HashMap<char, bool>, mut iter: std::slice::Iter<char>) -> bool {
        if let Some(&c) = iter.next() {
            i.insert(c, false);
            return self.inner_satisfiable(i, iter.clone()) || {
                i.insert(c, true);
                self.inner_satisfiable(i, iter.clone())
            };
        }

        self.evaluate(i).unwrap()
    }
    /// Checks if the formula is satifisable.
    /// Goes through sets of values for the contained atoms until
    /// one set makes it evaluate to `true`, if none return `false`.
    pub fn satisfiable(&self) -> bool {
        let symbols: Vec<_> = self.collect_symbols().collect();

        self.inner_satisfiable(&mut HashMap::new(), symbols.iter())
    }
}

impl Not for Formula {
    type Output = Self;
    fn not(self) -> Self::Output {
        Self::not(self)
    }
}
impl BitAnd for Formula {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}
impl BitOr for Formula {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let upper_precedence = f.precision().unwrap_or(0);
        let prec = self.precedence() as usize;

        let parentheses = upper_precedence >= prec;
        if parentheses {
            write!(f, "(")?;
        }

        match self {
            Formula::Atom(c) => write!(f, "{c}"),
            Formula::Not(f1) => write!(f, "¬{f1:.prec$}"),
            Formula::Disjunction(f1, f2) => write!(f, "{f1:.prec$} ∨ {f2:.prec$}"),
            Formula::Conjunction(f1, f2) => write!(f, "{f1:.prec$} ∧ {f2:.prec$}"),
            Formula::Implication(f1, f2) => write!(f, "{f1:.prec$} → {f2:.prec$}"),
            Formula::Equivalance(f1, f2) => write!(f, "{f1:.prec$} ↔ {f2:.prec$}"),
        }?;
        if parentheses {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl Shr for Formula {
    type Output = Self;
    fn shr(self, rhs: Self) -> Self::Output {
        self.implies(rhs)
    }
}
impl Shl for Formula {
    type Output = Self;
    fn shl(self, rhs: Self) -> Self::Output {
        rhs.implies(self)
    }
}
