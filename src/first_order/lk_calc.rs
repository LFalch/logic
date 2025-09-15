use rand::random;

use crate::first_order::Term;

use super::{Formula};
use std::{collections::HashSet, fmt::Debug, iter};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuleKind {
    Conjunction,
    Disjunction,
    Not,
    Implication,
    Equivalance,
    // TODO: add rules for if forall and exists that remove the quantifier if its variable is never referred to in its formula
    ForAll,
    ThereExists,
}
impl RuleKind {
    pub fn is_worse_left(self, other: Self) -> bool {
        match (self, other) {
            (Self::Not, _) => false,
            (_, Self::Not) => true,
            (Self::Conjunction, _) => false,
            (_, Self::Conjunction) => true,
            (Self::Disjunction, _) => false,
            (_, Self::Disjunction) => true,
            (Self::ThereExists, _) => false,
            (_, Self::ThereExists) => true,
            (Self::Implication, _) => false,
            (_, Self::Implication) => true,
            (Self::Equivalance, _) => false,
            (_, Self::Equivalance) => false,
            (Self::ForAll, Self::ForAll) => random(),
        }
    }
    pub fn is_worse_right(self, other: Self) -> bool {
        match (self, other) {
            (Self::Not, _) => false,
            (_, Self::Not) => true,
            (Self::Disjunction, _) => false,
            (_, Self::Disjunction) => true,
            (Self::Implication, _) => false,
            (_, Self::Implication) => true,
            (Self::ForAll, _) => false,
            (_, Self::ForAll) => true,
            (Self::Conjunction, _) => false,
            (_, Self::Conjunction) => true,
            (Self::Equivalance, _) => false,
            (_, Self::Equivalance) => true,
            (Self::ThereExists, Self::ThereExists) => random(),
        }
    }
    pub fn left_is_worse_right(self, other: Self) -> bool {
        match (self, other) {
            (Self::Not, _) => false,
            (_, Self::Not) => true,
            (Self::Conjunction, _) => false,
            (_, Self::Disjunction) => true,
            (_, Self::Implication) => true,
            (_, Self::Conjunction) => true,
            (_, Self::Equivalance) => false,
            (Self::Disjunction, _) => false,
            (Self::ThereExists, _) => false,
            (_, Self::ForAll) => true,
            (Self::ForAll, Self::ThereExists) => random(),
            (_, Self::ThereExists) => false,
        }
    }
}

pub fn is_valid(f: &Formula) -> bool {
    let mut valid = true;
    tree(&mut valid, f);
    valid
}
#[inline]
pub fn tree(wrt: &mut impl LkWriter, f: &Formula) {
    // we ignore this return value because all it means is if it's false, it returned early
    tree_inner(wrt, Vec::new(), vec![f]);
}

fn reduce_opt<T: Copy>(a: Option<T>, b: T, f: impl FnOnce(T, T) -> bool) -> Option<T> {
    a.and_then(|a| Some(if f(a, b) { b } else { a }))
        .or(Some(b))
}
fn is_worse_left_pair<T, U>((_, r1): (T, RuleKind), (_, r2): (U, RuleKind)) -> bool {
    r1.is_worse_left(r2)
}
fn is_worse_right_pair<T, U>((_, r1): (T, RuleKind), (_, r2): (U, RuleKind)) -> bool {
    r1.is_worse_right(r2)
}

fn new_constant<'a, I: Iterator<Item=&'a Formula>>(formulae: I) -> char {
    let mut symbols = Vec::new();
    for formula in formulae {
        symbols.extend(formula.get_all_symbols());
    }

    for v in 'a'..='z' {
        if !symbols.contains(&v) {
            return v;
        }
    }
    todo!("could not assign a letter from a-z, please fix this function now that it's a problem")
}

fn tree_inner<'a>(wrt: &mut impl LkWriter, mut antecedent: Vec<&'a Formula>, mut succedent: Vec<&'a Formula>) -> bool {
    loop {
        wrt.write_derivation(antecedent.iter().copied(), succedent.iter().copied());
        if antecedent.iter().any(|a| succedent.contains(a)) {
            wrt.axiom();
            break true;
        }

        let mut left_rule = None;
        for (i, a) in antecedent.iter().enumerate() {
            left_rule = match a {
                Formula::Predicate(_, _) => left_rule,
                Formula::ForAll(_, _) => if antecedent.iter().chain(&succedent)
                    .flat_map(|f| f.get_free_symbols())
                    .next()
                    .is_some()
                {
                    reduce_opt(left_rule, (i, RuleKind::ForAll), is_worse_left_pair)
                } else {
                    left_rule
                },
                Formula::ThereExists(_, _) => reduce_opt(left_rule, (i, RuleKind::ThereExists), is_worse_left_pair),
                Formula::Conjunction(_, _) => {
                    reduce_opt(left_rule, (i, RuleKind::Conjunction), is_worse_left_pair)
                }
                Formula::Disjunction(_, _) => {
                    reduce_opt(left_rule, (i, RuleKind::Disjunction), is_worse_left_pair)
                }
                Formula::Not(_) => reduce_opt(left_rule, (i, RuleKind::Not), is_worse_left_pair),
                Formula::Implication(_, _) => {
                    reduce_opt(left_rule, (i, RuleKind::Implication), is_worse_left_pair)
                }
                Formula::Equivalance(_, _) => {
                    reduce_opt(left_rule, (i, RuleKind::Equivalance), is_worse_left_pair)
                }
            };
        }
        let mut right_rule = None;
        for (i, s) in succedent.iter().enumerate() {
            right_rule = match s {
                Formula::Predicate(_, _) => right_rule,
                Formula::ThereExists(_, _) => if antecedent.iter().chain(&succedent)
                    .flat_map(|f| f.get_free_symbols())
                    .next()
                    .is_some()
                {
                    reduce_opt(right_rule, (i, RuleKind::ThereExists), is_worse_right_pair)
                } else {
                    right_rule
                },
                Formula::ForAll(_, _) => reduce_opt(right_rule, (i, RuleKind::ForAll), is_worse_right_pair),
                Formula::Conjunction(_, _) => {
                    reduce_opt(right_rule, (i, RuleKind::Conjunction), is_worse_right_pair)
                }
                Formula::Disjunction(_, _) => {
                    reduce_opt(right_rule, (i, RuleKind::Disjunction), is_worse_right_pair)
                }
                Formula::Not(_) => reduce_opt(right_rule, (i, RuleKind::Not), is_worse_right_pair),
                Formula::Implication(_, _) => {
                    reduce_opt(right_rule, (i, RuleKind::Implication), is_worse_right_pair)
                }
                Formula::Equivalance(_, _) => {
                    reduce_opt(right_rule, (i, RuleKind::Equivalance), is_worse_right_pair)
                }
            }
        }
        let (i, is_left_rule) = match (left_rule, right_rule) {
            (None, None) => break wrt.dead(),
            (Some((i, _)), None) => (i, true),
            (None, Some((i, _))) => (i, false),
            (Some((i, r1)), Some((j, r2))) => {
                if r1.left_is_worse_right(r2) {
                    (j, false)
                } else {
                    (i, true)
                }
            }
        };
        if is_left_rule {
            match antecedent.swap_remove(i) {
                Formula::Not(f) => succedent.push(f),
                Formula::Conjunction(f, f1) => antecedent.extend([&**f, f1]),
                Formula::Disjunction(f, f1) => {
                    wrt.start_branch();
                    if !tree_inner(wrt, add_one(&antecedent, f), succedent.clone()) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    antecedent.push(f1);
                }
                Formula::Implication(f, f1) => {
                    wrt.start_branch();
                    if !tree_inner(wrt, add_one(&antecedent, f1), succedent.clone()) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    succedent.push(f);
                }
                Formula::ThereExists(v, formula) => {
                    let s = new_constant(iter::once(&**formula)
                        .chain(antecedent.iter().copied())
                        .chain(succedent.iter().copied())
                    );
                    let substituted = substitue(*v, s, formula);
                    return tree_inner(wrt, add_one(&antecedent, &substituted), succedent);
                }
                f @ Formula::ForAll(v, formula) => {
                    // TODO: don't do this
                    let symbols: HashSet<_> = antecedent.iter().chain(&succedent)
                        .flat_map(|f| f.get_free_symbols())
                        .collect();
                    let (mut antecedent, succedent) = (antecedent, succedent);
                    let new: Vec<_> = symbols.into_iter().map(|s| substitue(*v, s, formula)).collect();
                    for f in &new {
                        antecedent.push(f);
                    }
                    antecedent.push(f);
                    return tree_inner(wrt, antecedent, succedent);
                }
                Formula::Equivalance(f, f1) => {
                    wrt.start_branch();
                    if !tree_inner(wrt, add_one(&antecedent, f1), succedent.clone()) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    wrt.start_branch();
                    if !tree_inner(wrt, add_one(&antecedent, f), succedent.clone()) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    wrt.start_branch(); 
                    if !tree_inner(wrt, antecedent.clone(), add_one(&antecedent, f)) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    succedent.push(f1);
                }
                Formula::Predicate(_, _) => unreachable!(),
            }
        } else {
            match succedent.swap_remove(i) {
                Formula::Not(f) => antecedent.push(f),
                Formula::Disjunction(f, f1) => succedent.extend([&**f, f1]),
                Formula::Implication(f, f1) => {
                                antecedent.push(f);
                                succedent.push(f1);
                            }
                Formula::Conjunction(f, f1) => {
                    wrt.start_branch();
                    if !tree_inner(wrt, antecedent.clone(), add_one(&succedent, f)) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    succedent.push(f1);
                }
                Formula::ForAll(v, formula) => {
                    let s = new_constant(iter::once(&**formula)
                        .chain(antecedent.iter().copied())
                        .chain(succedent.iter().copied())
                    );
                    let substituted = substitue(*v, s, formula);
                    return tree_inner(wrt, antecedent, add_one(&succedent, &substituted));
                }
                f @ Formula::ThereExists(v, formula) => {
                    // TODO: don't do this
                    let symbols: HashSet<_> = antecedent.iter().chain(&succedent)
                        .flat_map(|f| f.get_free_symbols())
                        .collect();
                    let (antecedent, mut succedent) = (antecedent, succedent);
                    let new: Vec<_> = symbols.into_iter().map(|s| substitue(*v, s, formula)).collect();
                    for f in &new {
                        succedent.push(f);
                    }
                    succedent.push(f);
                    return tree_inner(wrt, antecedent, succedent);
                }
                Formula::Equivalance(f, f1) => {
                    wrt.start_branch();
                    if !tree_inner(wrt, add_one(&antecedent, f1), add_one(&succedent, f)) {
                        wrt.end_branch();
                        break false;
                    }
                    wrt.end_branch();
                    succedent.push(f1);
                    antecedent.push(f);
                }
                Formula::Predicate(_, _) => unreachable!(),
            }
        }
    }
}

fn substitue_t(v: char, s: char, t: &Term) -> Term {
    match t {
        &Term::Variable(x) if x == v => Term::Variable(s),
        &Term::Variable(x) => Term::Variable(x),
        Term::Function(f, terms) => Term::Function(*f, terms
            .iter()
            .map(|t| substitue_t(v, s, t))
            .collect()
        ),
        &Term::Constant(c) => Term::Constant(c),
    }
}
fn substitue(v: char, s: char, formula: &Formula) -> Formula {
    match formula {
        Formula::Predicate(x, terms) if *x == v => Formula::Predicate(s, terms
            .iter()
            .map(|t| substitue_t(v, s, t))
            .collect()
        ),
        Formula::Predicate(x, terms) => Formula::Predicate(*x, terms
            .iter()
            .map(|t| substitue_t(v, s, t))
            .collect()
        ),
        Formula::ForAll(x, formula) if *x == v => Formula::ForAll(*x, formula.clone()),
        Formula::ThereExists(x, formula) if *x == v => Formula::ThereExists(*x, formula.clone()),
        Formula::ForAll(x, formula) => Formula::ForAll(*x, Box::new(substitue(v, s, formula))),
        Formula::ThereExists(x, formula) => Formula::ThereExists(*x, Box::new(substitue(v, s, formula))),
        Formula::Conjunction(f, f1) => Formula::Conjunction(Box::new(substitue(v, s, f)), Box::new(substitue(v, s, f1))),
        Formula::Disjunction(f, f1) => Formula::Disjunction(Box::new(substitue(v, s, f)), Box::new(substitue(v, s, f1))),
        Formula::Not(f) => Formula::Not(Box::new(substitue(v, s, f))),
        Formula::Implication(f, f1) => Formula::Implication(Box::new(substitue(v, s, f)), Box::new(substitue(v, s, f1))),
        Formula::Equivalance(f, f1) => Formula::Equivalance(Box::new(substitue(v, s, f)), Box::new(substitue(v, s, f1))),
    }
}

fn add_one<T: Clone>(vec: &Vec<T>, v: T) -> Vec<T> {
    let mut vec_out = Vec::with_capacity(vec.len() + 1);
    vec_out.extend(vec.iter().cloned());
    vec_out.push(v);
    vec_out
}

pub trait LkWriter {
    /// Branch of to two parents of current node
    fn start_branch(&mut self);
    /// Go to the next branch (the one started most recently)
    fn end_branch(&mut self);
    /// Current branch ended in an axiom
    fn axiom(&mut self);
    /// Current branch is a dead-end and cannot make any further derivations
    /// 
    /// Returns whether to continue (if false, it returns early)
    fn dead(&mut self) -> bool;
    /// Write a derivation on current branch; goes up a node
    fn write_derivation<'a, 'b>(&mut self, antecedent: impl Iterator<Item=&'a Formula>, succedent: impl Iterator<Item=&'b Formula>);
}

impl LkWriter for bool {
    fn start_branch(&mut self) {}
    fn end_branch(&mut self) {}
    fn axiom(&mut self) {}
    fn dead(&mut self) -> bool {
        *self = false;
        false
    }
    fn write_derivation<'a, 'b>(&mut self, _: impl Iterator<Item=&'a Formula>, _: impl Iterator<Item=&'b Formula>) {}
}
#[derive(Debug, Default)]
pub struct PrintDirect {
    indent: usize,
}
fn print_indent(indent: usize) {
    for _ in 0..indent {
        print!("  ");
    }
}
impl LkWriter for PrintDirect {
    fn start_branch(&mut self) {
        self.indent += 1;
    }
    fn end_branch(&mut self) {
        self.indent -= 1;
    }
    fn axiom(&mut self) {
        print_indent(self.indent);
        println!("=========");
    }
    fn dead(&mut self) -> bool {
        print_indent(self.indent);
        println!("- - - - -");
        true
    }
    fn write_derivation<'a, 'b>(&mut self, antecedent: impl Iterator<Item=&'a Formula>, succedent: impl Iterator<Item=&'b Formula>) {
        print_indent(self.indent);
        let mut comma = false;
        for a in antecedent {
            if comma {
                print!(", ");
            }
            print!("{a}");
            comma = true;
        }
        print!(" => ");
        comma = false;
        for s in succedent {
            if comma {
                print!(", ");
            }
            print!("{s}");
            comma = true;
        }
        println!();
    }
}
