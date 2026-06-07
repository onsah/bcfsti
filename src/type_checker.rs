use std::collections::{HashMap, HashSet};

use crate::{
    constraint::Constraints,
    ren::Ren,
    syntax::{
        Eff, Expr, Id, Label, Mult, Op1, Op2, Pattern, SEff, SExpr, SId, SLabel, SMult, SPattern,
        SSession, SType, Session, SessionOp, Type,
    },
    type_context::{ext, Ctx, CtxCtx, CtxS, JoinOrd},
    util::span::fake_span,
};

#[derive(Debug, Clone)]
pub enum TypeError {
    UndefinedVariable(SId),
    Mismatch(SExpr, Result<SType, String>, SType),
    MismatchMult(SExpr, SType, Result<SMult, String>, SMult),
    MismatchEff(SExpr, SEff, SEff),
    MismatchEffSub(SExpr, SEff, SEff),
    MismatchLabel(SExpr, Label, SType),
    Op2Mismatch(SExpr, Result<SType, String>, SType, SType),
    TypeAnnotationMissing(SExpr),
    //ClosedUnfinished(SExpr, SRegex),
    //InvalidWrite(SExpr, SRegex, SRegex),
    InvalidSplit(SExpr, SSession, SSession),
    //InvalidSplitArg(SRegex),
    //InvalidSplitRes(SExpr, SRegex, SRegex, SRegex),
    CtxSplitFailed(SExpr, Ctx, Ctx),
    CtxCtxSplitFailed(SExpr, Ctx, HashSet<Id>),
    Shadowing(SExpr, SId),
    CtxNotUnr(SExpr, Ctx),
    SeqDropsOrd(SExpr, SType),
    LeftOverVar(SExpr, SId, SSession, Option<Session>),
    LeftOverCtx(SExpr, Ctx),
    MultipleClauses(SExpr),
    NotEnoughPatterns(SExpr),
    PatternMismatch(SPattern, SType),
    ClauseWithWrongId(SExpr, SId, SId),
    ClauseWithZeroPatterns(SExpr),
    CaseMissingLabel(SExpr, SType, Label),
    CaseExtraLabel(SExpr, SType, Label),
    CaseDuplicateLabel(SExpr, SType, Label),
    CaseClauseTypeMismatch(SExpr, SType, SType),
    CaseLeftOverMismatch(SExpr, Id, Session, Option<Session>),
    VariantEmpty(SExpr),
    VariantDuplicateLabel(SExpr, SType, Label),
    RecursiveNonFunctionBinding(SExpr, SId),
    WfNonContractive(SSession, SId),
    WfEmptyChoice(SSession),
    WfEmptyVariant(SType),
    MainReturnsOrd(SExpr, SType),
    WfSessionNotClosed(SSession, SId),
    WfSessionShadowing(SSession, SId),
    NewWithBorrowedType(SExpr, SSession),
}

pub fn rename_vars(r: &Ren, xs: &HashSet<Id>) -> HashSet<Id> {
    let mut out = HashSet::new();
    for x in xs {
        if let Some(y) = r.map.get(x) {
            out.insert(y.clone());
        } else {
            out.insert(x.clone());
        }
    }
    out
}

pub fn intersection<T: std::hash::Hash + Eq + Clone>(
    xss: impl IntoIterator<Item = HashSet<T>>,
) -> HashSet<T> {
    let xss: Vec<_> = xss.into_iter().collect();
    if xss.len() == 0 {
        return HashSet::new();
    }
    let mut it = xss.into_iter();
    let mut out = it.next().unwrap().clone();
    for xs in it {
        out = out.intersection(&xs).cloned().collect();
    }
    out
}

pub fn union<T: std::hash::Hash + Eq + Clone>(
    xss: impl IntoIterator<Item = HashSet<T>>,
) -> HashSet<T> {
    let mut out = HashSet::new();
    for xs in xss {
        out = out.union(&xs).cloned().collect();
    }
    out
}

pub fn check_variant_label_eq(
    e: &SExpr,
    t: &SType,
    actual: &[&Label],
    expected: &[&Label],
) -> Result<(), TypeError> {
    if actual.len() == 0 {
        return Err(TypeError::VariantEmpty(e.clone()));
    }
    for l in actual {
        if !expected.contains(l) {
            return Err(TypeError::CaseExtraLabel(
                e.clone(),
                t.clone(),
                (*l).clone(),
            ));
        }
    }
    for l in expected {
        if !actual.contains(l) {
            return Err(TypeError::CaseMissingLabel(
                e.clone(),
                t.clone(),
                (*l).clone(),
            ));
        }
    }
    for (i, l) in actual.iter().enumerate() {
        if i != actual.len() {
            if (&actual[i + 1..]).contains(l) {
                return Err(TypeError::CaseDuplicateLabel(
                    e.clone(),
                    t.clone(),
                    (*l).clone(),
                ));
            }
        }
    }
    for (i, l) in expected.iter().enumerate() {
        if i != expected.len() {
            if (&expected[i + 1..]).contains(l) {
                return Err(TypeError::VariantDuplicateLabel(
                    e.clone(),
                    t.clone(),
                    (*l).clone(),
                ));
            }
        }
    }
    Ok(())
}

fn check_wf_session_(s: &SSession, at_mu: bool, vars: &HashSet<Id>) -> Result<(), TypeError> {
    match &s.val {
        Session::Var(x) => {
            if at_mu {
                Err(TypeError::WfNonContractive(s.clone(), x.clone()))
            } else if !vars.contains(&x.val) {
                Err(TypeError::WfSessionNotClosed(s.clone(), x.clone()))
            } else {
                Ok(())
            }
        }
        Session::Mu(x, s1) => {
            if vars.contains(&x.val) {
                return Err(TypeError::WfSessionShadowing(s.clone(), x.clone()));
            }
            let mut vars = vars.clone();
            vars.insert(x.val.clone());
            check_wf_session_(s1, true, &vars)
        }
        Session::Op(_op, t1) => todo!(),
        Session::Choice(_op, cs) => {
            if cs.len() == 0 {
                Err(TypeError::WfEmptyChoice(s.clone()))
            } else {
                for (_l, s1) in cs {
                    check_wf_session_(s1, at_mu, vars)?;
                }
                Ok(())
            }
        }
        Session::End(_op) => Ok(()),
        Session::BorrowEnd(_op) => Ok(()),
        Session::Skip => todo!(),
        Session::Semi { first, second } => todo!(),
    }
}

pub fn check_wf_session(s: &SSession) -> Result<(), TypeError> {
    check_wf_session_(s, false, &HashSet::new())
}

pub fn check_wf_type(t: &SType) -> Result<(), TypeError> {
    match &t.val {
        Type::Chan(s) => check_wf_session(todo!()),
        Type::Arr {
            param: t1, ret: t2, ..
        } => {
            check_wf_type(t1)?;
            check_wf_type(t2)?;
            Ok(())
        }
        Type::Prod {
            first: t1,
            second: t2,
            ..
        } => {
            check_wf_type(t1)?;
            check_wf_type(t2)?;
            Ok(())
        }
        Type::Variant(cs) => {
            if cs.len() == 0 {
                return Err(TypeError::WfEmptyVariant(t.clone()));
            }
            for (_l, t) in cs {
                check_wf_type(t)?;
            }
            Ok(())
        }
        Type::Unit => Ok(()),
        Type::Int => Ok(()),
        Type::Bool => Ok(()),
        Type::String => Ok(()),
    }
}

pub fn check(ctx: &Ctx, e: &SExpr, t: &SType) -> Result<(Constraints, Eff), TypeError> {
    todo!()
}

pub fn infer_recv_arg(ctx: &Ctx, e: &SExpr) -> Result<(SType, Constraints, Eff), TypeError> {
    infer(ctx, e)
}

pub fn infer_select_arg(
    ctx: &Ctx,
    e: &SExpr,
    l: &SLabel,
) -> Result<(SType, Constraints, Eff), TypeError> {
    infer(ctx, e)
}

pub fn indented(n: usize, s: impl AsRef<str>) -> String {
    let mut out = String::new();
    for l in s.as_ref().lines() {
        for _ in 0..n {
            out += " ";
        }
        out += l;
    }
    out
}

pub fn infer(ctx: &Ctx, e: &SExpr) -> Result<(SType, Constraints, Eff), TypeError> {
    // println!("\nExpression: {}", pretty_def(&e));
    // println!("Ctx: {}", pretty_context_notype(&ctx.simplify()));
    match &e.val {
        Expr::Var(x) => match ctx.lookup_ord_pure(x) {
            Some((ctx, t)) => {
                assert_unr_ctx(e, &ctx)?;
                Ok((t.clone(), Constraints::empty(), Eff::No))
            }
            None => Err(TypeError::UndefinedVariable(x.clone())),
        },
        _ => todo!(),
    }
}

pub fn check_pattern(pat: &SPattern, t: &SType) -> Result<Ctx, TypeError> {
    match (&pat.val, &t.val) {
        (Pattern::Var(x), _) => Ok(Ctx::Bind(x.clone(), t.clone())),
        (
            Pattern::Pair(pat1, pat2),
            Type::Prod {
                mult: m,
                first: t1,
                second: t2,
            },
        ) => {
            let c1 = check_pattern(pat1, t1)?;
            let c2 = check_pattern(pat2, t2)?;
            Ok(ext(m.val, c1, c2))
        }
        (Pattern::Pair(_pat1, _pat2), _) => Err(TypeError::PatternMismatch(pat.clone(), t.clone())),
    }
}

pub fn split_arrow_type(mut t: &SType) -> (Vec<(SType, SMult)>, SType, Option<SEff>) {
    let mut args = vec![];
    let mut eff = None;
    loop {
        match &t.val {
            Type::Arr {
                mult: m,
                eff: e,
                param: t1,
                ret: t2,
            } => {
                t = t2;
                eff = Some(e.clone());
                args.push((t1.as_ref().clone(), m.clone()));
            }
            _ => return (args, t.clone(), eff),
        }
    }
}

pub fn infer_type(e: &SExpr) -> Result<(SType, Eff), TypeError> {
    let (t, _u, eff) = infer(&Ctx::Empty, e)?;
    if t.is_ord() {
        return Err(TypeError::MainReturnsOrd(e.clone(), t.clone()));
    }
    Ok((t, eff))
}

pub fn assert_unr_ctx(e: &SExpr, ctx: &Ctx) -> Result<(), TypeError> {
    if ctx.is_unr() {
        Ok(())
    } else {
        Err(TypeError::LeftOverCtx(e.clone(), ctx.clone()))
    }
}
