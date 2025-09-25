use nom::{
    branch::alt, bytes::complete::tag, character::{
        anychar,
        complete::{char, multispace0},
    }, combinator::eof, multi::fold, sequence::{delimited, pair, terminated}, IResult, Parser
};
use std::str::FromStr;

use crate::{emit_once, first_order::parse::soft};

use super::Formula;

impl FromStr for Formula {
    type Err = Box<dyn std::error::Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match terminated(biimplication, (multispace0, eof)).parse(s) {
            Ok((_, e)) => Ok(e),
            Err(e) => Err(Box::new(e.to_owned())),
        }
    }
}

fn parens(i: &str) -> IResult<&str, Formula> {
    soft(delimited(tag("("), biimplication, tag(")"))).parse(i)
}

fn last(i: &str) -> IResult<&str, Formula> {
    alt((
        parens,
        soft(anychar).map(Formula::Atom),
    ))
    .parse(i)
}
fn pref(i: &str) -> IResult<&str, Formula> {
    let (i, _) = multispace0(i)?;

    alt((
        pair(alt((char('~'), char('!'), char('¬'))), pref)
            .map(|(_, f)| Formula::not(f)),
        last,
    ))
    .parse(i)
}

fn wedge(i: &str) -> IResult<&str, Formula> {
    let (i, init) = pref(i)?;
    
    fold(
        0..,
        pair(alt((tag("&&"), tag("&"), tag("/\\"), tag("∧"))), vee),
        emit_once(init),
        |acc, (_, val)| Formula::and(acc, val),
    )
    .parse(i)
}

fn vee(i: &str) -> IResult<&str, Formula> {
    let (i, init) = wedge(i)?;

    fold(
        0..,
        pair(alt((tag("||"), tag("|"), tag("∨"))), pref),
        emit_once(init),
        |acc, (_, val)| Formula::or(acc, val),
    )
    .parse(i)
}

fn implication(i: &str) -> IResult<&str, Formula> {
    let (i, init) = vee(i)?;

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
