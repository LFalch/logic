use nom::{
    branch::alt, bytes::complete::tag, character::{
        anychar, complete::{char, multispace0, multispace1}
    }, combinator::{eof, opt}, error::ParseError, multi::{fold, separated_list0}, sequence::{delimited, pair, preceded, terminated}, AsChar, IResult, Input, Parser
};
use std::{collections::HashSet, str::FromStr};

use crate::{emit_once, first_order::{Formula, Term}};

impl FromStr for Formula {
    type Err = Box<dyn std::error::Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match formula(s) {
            Ok((_, mut f)) => {
                close(&mut f, []);
                Ok(f)
            }
            Err(e) => Err(Box::new(e.to_owned())),
        }
    }
}
pub fn with_open_variables(
    s: &str,
    open_variables: impl IntoIterator<Item = char>,
) -> IResult<&str, Formula> {
    biimplication(s).map(move |(s, mut f)| {
        close(&mut f, open_variables);
        (s, f)
    })
}

#[inline]
fn close(f: &mut Formula, leave_open: impl IntoIterator<Item = char>) {
    close_inner(f, &mut leave_open.into_iter().collect());
}
fn close_inner(f: &mut Formula, map: &mut HashSet<char>) {
    match f {
        Formula::Predicate(_, terms) => terms.iter_mut().for_each(|t| close_term(t, map)),
        Formula::ForAll(c, f) | Formula::ThereExists(c, f) => {
            map.insert(*c);
            close_inner(f, map);
            map.remove(c);
        }
        Formula::Not(f) => close_inner(f, map),
        Formula::Conjunction(f, f1)
        | Formula::Disjunction(f, f1)
        | Formula::Implication(f, f1)
        | Formula::Equivalance(f, f1) => {
            close_inner(f, map);
            close_inner(f1, map);
        }
    }
}
fn close_term(t: &mut Term, map: &HashSet<char>) {
    match t {
        Term::Variable(c) if !map.contains(c) => t.make_const(),
        Term::Function(_, terms) => terms.iter_mut().for_each(|t| close_term(t, map)),
        Term::Variable(_) | Term::Constant(_) => (),
    }
}

fn parens(i: &str) -> IResult<&str, Formula> {
    soft(delimited(tag("("), biimplication, tag(")"))).parse(i)
}

fn term(i: &str) -> IResult<&str, Term> {
    let (i, symbol) = anychar(i)?;

    let (i, p) = opt(delimited(
        char('('),
        separated_list0(soft(char(',')), term),
        char(')'),
    )).parse(i)?;

    Ok(if let Some(terms) = p {
        (i, Term::Function(symbol, terms.into_boxed_slice()))
    } else {
        (i, Term::Variable(symbol))
    })
}

fn predicate(i: &str) -> IResult<&str, Formula> {
    let (i, symbol) = anychar(i)?;

    let (i, p) = opt(delimited(
        char('('),
        separated_list0(soft(char(',')), term),
        char(')'),
    )).parse(i)?;

    Ok(if let Some(terms) = p {
        (i, Formula::Predicate(symbol, terms.into_boxed_slice()))
    } else {
        (i, Formula::predicate(symbol, []))
    })
}
fn last(i: &str) -> IResult<&str, Formula> {
    alt((parens, soft(predicate))).parse(i)
}
fn pref(i: &str) -> IResult<&str, Formula> {
    let (i, _) = multispace0(i)?;

    let meow = alt((
        preceded(alt((char('~'), char('!'), char('¬'))), pref).map(|f| Formula::not(f)),
        pair(
            delimited(alt((tag("∀"), tag("forall"))), anychar, opt(char('.'))),
            preceded(multispace1, pref),
        )
        .map(|(c, f)| Formula::forall(c, f)),
        pair(
            delimited(alt((tag("∃"), tag("exists"))), anychar, opt(char('.'))),
            preceded(multispace1, pref),
        )
        .map(|(c, f)| Formula::exists(c, f)),
        last,
    ))
    .parse(i)?;
    Ok(meow)
}

fn vee(i: &str) -> IResult<&str, Formula> {
    let (i, init) = pref(i)?;

    fold(
        0..,
        pair(alt((tag("||"), tag("|"), tag("∨"))), pref),
        emit_once(init),
        |acc, (_, val)| Formula::or(acc, val),
    )
    .parse(i)
}

fn wedge(i: &str) -> IResult<&str, Formula> {
    let (i, init) = vee(i)?;

    fold(
        0..,
        pair(alt((tag("&&"), tag("&"), tag("/\\"), tag("∧"))), vee),
        emit_once(init),
        |acc, (_, val)| Formula::and(acc, val),
    )
    .parse(i)
}

fn implication(i: &str) -> IResult<&str, Formula> {
    let (i, init) = wedge(i)?;

    fold(
        0..,
        pair(alt((tag("->"), tag("=>"), tag("→"), tag("⇒"))), wedge),
        emit_once(init),
        |acc, (_, val)| Formula::implies(acc, val),
    )
    .parse(i)
}

fn biimplication(i: &str) -> IResult<&str, Formula> {
    let (i, init) = implication(i)?;

    fold(
        0..,
        pair(alt((tag("<->"), tag("<=>"), tag("↔"), tag("⇔"))), implication),
        emit_once(init),
        |acc, (_, val)| Formula::iff(acc, val),
    )
    .parse(i)
}
#[inline]
fn formula(i: &str) -> IResult<&str, Formula> {
    terminated(biimplication, (multispace0, eof))
        .parse(i)
}

pub(crate) fn soft<I: Input, O, E: ParseError<I>>(p: impl Parser<I, Output = O, Error = E>) -> impl Parser<I, Output = O, Error = E>
where
    E: ParseError<I>,
    <I as Input>::Item: AsChar + Clone,
{
    delimited(multispace0, p, multispace0)
}
