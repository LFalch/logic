use nom::{
    branch::alt, bytes::complete::tag, character::{
        anychar,
        complete::{char, space0},
    }, error::{Error, ErrorKind::NonEmpty}, multi::fold, sequence::{delimited, pair}, IResult, Parser
};

impl FromStr for Formula {
    type Err = Box<dyn std::error::Error>;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match biimplication(s) {
            Ok((s, e)) if s.is_empty() => Ok(e),
            Ok((s, _)) => Err(Box::new(Error::new(s.to_owned(), NonEmpty))),
            Err(e) => Err(Box::new(e.to_owned())),
        }
    }
}

use std::str::FromStr;

use crate::Formula;

fn parens(i: &str) -> IResult<&str, Formula> {
    delimited(space0, delimited(tag("("), biimplication, tag(")")), space0).parse(i)
}

fn last(i: &str) -> IResult<&str, Formula> {
    alt((
        parens,
        delimited(space0, anychar, space0).map(Formula::Atom),
    ))
    .parse(i)
}
fn pref(i: &str) -> IResult<&str, Formula> {
    let (i, _) = space0(i)?;

    alt((
        pair(alt((char('~'), char('!'), char('¬'))), pref)
            .map(|(_, f)| Formula::Not(Box::new(f))),
        last,
    ))
    .parse(i)
}

fn vee(i: &str) -> IResult<&str, Formula> {
    let (i, init) = pref(i)?;

    fold(
        0..,
        pair(alt((tag("||"), tag("|"), tag("∨"))), pref),
        move || init.clone(),
        |acc, (_, val)| Formula::or(acc, val),
    )
    .parse(i)
}

fn wedge(i: &str) -> IResult<&str, Formula> {
    let (i, init) = vee(i)?;

    fold(
        0..,
        pair(alt((tag("&&"), tag("&"), tag("/\\"), tag("∧"))), vee),
        move || init.clone(),
        |acc, (_, val)| Formula::and(acc, val),
    )
    .parse(i)
}

fn implication(i: &str) -> IResult<&str, Formula> {
    let (i, init) = wedge(i)?;

    fold(
        0..,
        pair(alt((tag("->"), tag("=>"), tag("→"))), wedge),
        move || init.clone(),
        |acc, (_, val)| Formula::implies(acc, val),
    )
    .parse(i)
}

fn biimplication(i: &str) -> IResult<&str, Formula> {
    let (i, init) = implication(i)?;

    fold(
        0..,
        pair(alt((tag("<->"), tag("<=>"), tag("↔"))), implication),
        // wtf??
        move || init.clone(),
        |acc, (_, val)| Formula::iff(acc, val),
    )
    .parse(i)
}
