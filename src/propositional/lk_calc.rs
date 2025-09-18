use super::Formula;
use std::fmt::Debug;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RuleKind {
    Conjunction,
    Disjunction,
    Not,
    Implication,
    Equivalance,
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
            (Self::Implication, _) => false,
            (_, Self::Implication) => true,
            (Self::Equivalance, Self::Equivalance) => false,
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
            (Self::Conjunction, _) => false,
            (_, Self::Conjunction) => true,
            (Self::Equivalance, Self::Equivalance) => false,
        }
    }
    pub fn left_is_worse_right(self, other: Self) -> bool {
        match (self, other) {
            (Self::Not, _) => false,
            (_, Self::Not) => true,
            (Self::Conjunction, _) => false,
            (_, Self::Disjunction) => true,
            (_, Self::Implication) => true,
            (_, RuleKind::Conjunction) => true,
            (_, RuleKind::Equivalance) => false,
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
                Formula::Atom(_) => left_rule,
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
                Formula::Atom(_) => right_rule,
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
                Formula::Atom(_) => unreachable!(),
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
                Formula::Atom(_) => unreachable!(),
            }
        }
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
