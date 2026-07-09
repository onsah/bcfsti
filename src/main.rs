pub mod args;
pub mod constraint;
pub mod equivalence;
pub mod error_reporting;
pub mod freest;
pub mod fresh_var;
pub mod lexer;
pub mod parser;
pub mod pretty;
pub mod syntax;
pub mod type_alias;
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
    syntax::{Eff, Type},
    type_alias::AliasEnv,
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
    let (_e, _t, aliases, cs, _p) = typecheck(&src, args.verbose)?;

    constraints_check(cs, &aliases, args.verbose)?;

    // println!("===== EVALUATION =====");
    // println!("Program stdout:");
    // let v = eval(&e).map_err(IErr::Eval)?;
    // println!(
    //     "Program terminated successfully with value `{}`.",
    //     pretty_def(&v)
    // );
    Ok(())
}

pub fn typecheck(
    src: &str,
    verbose: bool,
) -> Result<(SExpr, Type, AliasEnv, Constraints, Eff), IErr> {
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
    let (e, alias_env) = type_alias::get_alias_env(e);
    type_alias::check_shadowing(&e, &alias_env).map_err(IErr::Typing)?;
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

    let (t, cs, p) = type_checker::infer_type(&e, alias_env.clone()).map_err(IErr::Typing)?;
    if verbose {
        println!("===== TYPECHECKER =====");
        println!("Type:    {}", pretty_def(&t));
        println!("Effect:  {}", pretty_def(&p));
        println!();
    }

    Ok((e, t.val, alias_env, cs, p))
}

fn constraints_check(cs: Constraints, alias_env: &AliasEnv, verbose: bool) -> Result<(), IErr> {
    let cs = cs.solve().map_err(IErr::Constraint)?;

    if verbose {
        println!("===== CONSTRAINTS CHECKING =====");
        println!("Constraints:");
        for (ty1, ty2) in cs.iter() {
            println!("{} == {}", pretty_def(&ty1.val), pretty_def(&ty2.val));
        }
        println!();
    }

    for (ty1, ty2) in cs.iter() {
        match check_equivalence(&ty1.val, &ty2.val, alias_env) {
            EquivalenceResult::Success => (),
            EquivalenceResult::Error { reason } => Err(IErr::Equivalence {
                ty1: ty1.clone(),
                ty2: ty2.clone(),
                reason,
            })?,
        }
    }
    Ok(())
}
