pub mod args;
pub mod constraint;
pub mod equivalence;
pub mod error_reporting;
pub mod freest;
pub mod fresh_var;
pub mod lexer;
pub mod parser;
pub mod pretty;
pub mod ren;
pub mod semantics;
pub mod syntax;
pub mod type_checker;
pub mod type_context;
pub mod util;

#[cfg(test)]
mod tests;

#[cfg(test)]
extern crate proptest;

use std::process::exit;

use clap::Parser;
use syntax::SExpr;

use crate::{
    args::Args,
    constraint::Constraints,
    equivalence::{EquivalenceResult, check_equivalence},
    error_reporting::{IErr, report_error},
    lexer::Token,
    semantics::eval,
    syntax::{Eff, Type},
    util::{
        lexer_offside::{self, Braced},
        pretty::pretty_def,
    },
};

fn main() {
    let args = Args::parse();
    let src_path = args.src_path.to_string_lossy();
    if let Err(e) = run(&args) {
        let src = std::fs::read_to_string(&*src_path).unwrap();
        report_error(&src_path, &src, e);
        exit(1)
    }
}

fn run(args: &Args) -> Result<(), IErr> {
    let src = std::fs::read_to_string(&args.src_path).unwrap();
    if args.verbose {
        println!("===== SRC =====");
        println!("{src}");
        println!();
    }
    let (_e, _t, cs, _p) = typecheck(&src, args.verbose)?;

    println!("===== CONSTRAINTS CHECKING =====");

    constraints_check(cs)?;

    // println!("===== EVALUATION =====");
    // println!("Program stdout:");
    // let v = eval(&e).map_err(IErr::Eval)?;
    // println!(
    //     "Program terminated successfully with value `{}`.",
    //     pretty_def(&v)
    // );
    Ok(())
}

pub fn typecheck(src: &str, verbose: bool) -> Result<(SExpr, Type, Constraints, Eff), IErr> {
    // println!("===== TOKENS =====");
    let toks = lexer::lex(&src).map_err(IErr::Lexer)?;
    // for (i, t) in toks.toks.iter().enumerate() {
    //     println!("{i}:\t{t:?}");
    // }
    // println!();

    let mut toks = lexer_offside::process_indent(toks, |_| false, |_| false);
    toks.toks = toks
        .toks
        .into_iter()
        .filter(|t| t.val != Braced::Token(Token::NewLine))
        .collect::<Vec<_>>();
    if verbose {
        println!("===== TOKENS =====");
        for (i, t) in toks.toks.iter().enumerate() {
            println!("{i}:\t{t:?}");
        }
        println!();
    }

    let e = parser::parse(&toks).map_err(IErr::Parser)?;
    if verbose {
        println!("===== AST =====");
        println!("{e:#?}");
        println!();
    }

    if verbose {
        println!("===== PRETTY =====");
        println!("{}", pretty_def(&e));
        println!();
    }

    println!("===== TYPECHECKER =====");
    let (t, cs, p) = type_checker::infer_type(&e).map_err(IErr::Typing)?;
    println!("Type:    {}", pretty_def(&t));
    println!("Effect:  {}", pretty_def(&p));
    println!();

    Ok((e, t.val, cs, p))
}

fn constraints_check(cs: Constraints) -> Result<(), IErr> {
    let cs = cs.solve();

    for (ty1, ty2) in cs.iter() {
        match check_equivalence(&ty1.val, &ty2.val) {
            EquivalenceResult::Success => (),
            EquivalenceResult::Error { reason } => Err(IErr::Constraint {
                ty1: ty1.clone(),
                ty2: ty2.clone(),
                reason,
            })?,
        }
    }
    Ok(())
}
