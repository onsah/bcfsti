use std::collections::{HashMap, HashSet};

use crate::syntax::{Clause, Expr, Id, SClause, SExpr, SId, SSession, SType, Session, Type};
use crate::util::span::Spanned;

type AliasEnv = HashMap<Id, SType>;

#[derive(Debug, Clone)]
pub enum AliasError {
    NonSessionAliasUsedAsSession(SSession, SType),
    CyclicAlias(Id),
}

pub fn expand_aliases(e: &SExpr) -> Result<SExpr, AliasError> {
    expand_expr(e, &HashMap::new(), &HashSet::new())
}

fn expand_expr(e: &SExpr, env: &AliasEnv, visiting: &HashSet<Id>) -> Result<SExpr, AliasError> {
    let span = e.span.clone();
    let e2 = match &e.val {
        Expr::TypeDef(name, t, body, is_rec) => {
            let env_def = if *is_rec {
                env.iter()
                    .filter(|(k, _)| **k != name.val)
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect()
            } else {
                env.clone()
            };
            let t_expanded = expand_type(t, &env_def, visiting)?;
            let t_final = if *is_rec {
                wrap_mu(name, t_expanded)
            } else {
                t_expanded
            };
            let mut env2 = env.clone();
            env2.insert(name.val.clone(), t_final);
            return expand_expr(body, &env2, visiting);
        }
        Expr::Ann(inner, t) => Expr::Ann(
            Box::new(expand_expr(inner, env, visiting)?),
            expand_type(t, env, visiting)?,
        ),
        Expr::LetDecl(id, t, clause, body) => Expr::LetDecl(
            id.clone(),
            expand_type(t, env, visiting)?,
            Box::new(expand_clause(clause, env, visiting)?),
            Box::new(expand_expr(body, env, visiting)?),
        ),
        Expr::Send(ty, e1, e2) => Expr::Send(
            expand_type(ty, env, visiting)?,
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::Recv(ty, e) => Expr::Recv(
            expand_type(ty, env, visiting)?,
            Box::new(expand_expr(e, env, visiting)?),
        ),
        Expr::New(s) => Expr::New(expand_session(s, env, visiting)?),
        Expr::LSplit(s, e) => Expr::LSplit(
            expand_session(s, env, visiting)?,
            Box::new(expand_expr(e, env, visiting)?),
        ),
        Expr::RSplit(s, e) => Expr::RSplit(
            expand_session(s, env, visiting)?,
            Box::new(expand_expr(e, env, visiting)?),
        ),
        Expr::Const(c) => Expr::Const(c.clone()),
        Expr::Var(x) => Expr::Var(x.clone()),
        Expr::Abs(x, body) => Expr::Abs(x.clone(), Box::new(expand_expr(body, env, visiting)?)),
        Expr::App(e1, e2) => Expr::App(
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::Seq(e1, e2) => Expr::Seq(
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::Pair(e1, e2) => Expr::Pair(
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::Let(x, e1, e2) => Expr::Let(
            x.clone(),
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::LetPair(x, y, e1, e2) => Expr::LetPair(
            x.clone(),
            y.clone(),
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::Inj(l, e) => Expr::Inj(l.clone(), Box::new(expand_expr(e, env, visiting)?)),
        Expr::CaseSum(e, cs) => {
            let cs = cs
                .iter()
                .map(|(l, x, ce)| {
                    Ok::<_, AliasError>((l.clone(), x.clone(), expand_expr(ce, env, visiting)?))
                })
                .collect::<Result<Vec<_>, _>>()?;
            Expr::CaseSum(Box::new(expand_expr(e, env, visiting)?), cs)
        }
        Expr::Select(l, e) => Expr::Select(l.clone(), Box::new(expand_expr(e, env, visiting)?)),
        Expr::Branch(e) => Expr::Branch(Box::new(expand_expr(e, env, visiting)?)),
        Expr::Op1(op, e) => Expr::Op1(*op, Box::new(expand_expr(e, env, visiting)?)),
        Expr::Op2(op, e1, e2) => Expr::Op2(
            *op,
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
        ),
        Expr::If(e1, e2, e3) => Expr::If(
            Box::new(expand_expr(e1, env, visiting)?),
            Box::new(expand_expr(e2, env, visiting)?),
            Box::new(expand_expr(e3, env, visiting)?),
        ),
        Expr::Fork(e) => Expr::Fork(Box::new(expand_expr(e, env, visiting)?)),
        Expr::End(op, e) => Expr::End(*op, Box::new(expand_expr(e, env, visiting)?)),
        Expr::BorrowEnd(op, e) => Expr::BorrowEnd(*op, Box::new(expand_expr(e, env, visiting)?)),
        Expr::Discard(e) => Expr::Discard(Box::new(expand_expr(e, env, visiting)?)),
    };
    Ok(Spanned::new(e2, span))
}

fn expand_clause(
    c: &SClause,
    env: &AliasEnv,
    visiting: &HashSet<Id>,
) -> Result<SClause, AliasError> {
    Ok(Spanned::new(
        Clause {
            id: c.id.clone(),
            var_id: c.var_id.clone(),
            body: expand_expr(&c.body, env, visiting)?,
        },
        c.span.clone(),
    ))
}

fn expand_type(t: &SType, env: &AliasEnv, visiting: &HashSet<Id>) -> Result<SType, AliasError> {
    let span = t.span.clone();
    let t2 = match &t.val {
        // Alias used as a full channel type: `Chan(Var(x))` where `x` is an alias.
        // Replace the whole type with the alias's expanded definition.
        Type::Chan(Session::Var(x)) if env.contains_key(&x.val) => {
            if visiting.contains(&x.val) {
                return Err(AliasError::CyclicAlias(x.val.clone()));
            }
            let mut visiting2 = visiting.clone();
            visiting2.insert(x.val.clone());
            return expand_type(&env[&x.val], env, &visiting2);
        }
        Type::Chan(s) => {
            let s_expanded = expand_session(&Spanned::new(s.clone(), span.clone()), env, visiting)?;
            Type::Chan(s_expanded.val)
        }
        Type::Arr {
            mob,
            mult,
            eff,
            param,
            ret,
        } => Type::Arr {
            mob: mob.clone(),
            mult: mult.clone(),
            eff: eff.clone(),
            param: Box::new(expand_type(param, env, visiting)?),
            ret: Box::new(expand_type(ret, env, visiting)?),
        },
        Type::Prod {
            mult,
            first,
            second,
        } => Type::Prod {
            mult: mult.clone(),
            first: Box::new(expand_type(first, env, visiting)?),
            second: Box::new(expand_type(second, env, visiting)?),
        },
        Type::Variant(cs) => Type::Variant(
            cs.iter()
                .map(|(l, t)| Ok((l.clone(), expand_type(t, env, visiting)?)))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Type::Unit | Type::Int | Type::Bool | Type::String => t.val.clone(),
    };
    Ok(Spanned::new(t2, span))
}

fn expand_session(
    s: &SSession,
    env: &AliasEnv,
    visiting: &HashSet<Id>,
) -> Result<SSession, AliasError> {
    let span = s.span.clone();
    let s2 = match &s.val {
        // A session variable that refers to a type alias. The alias must expand
        // to a channel type; we splice its inner session in place.
        Session::Var(x) => {
            if let Some(alias_ty) = env.get(&x.val) {
                if visiting.contains(&x.val) {
                    return Err(AliasError::CyclicAlias(x.val.clone()));
                }
                let mut visiting2 = visiting.clone();
                visiting2.insert(x.val.clone());
                let expanded = expand_type(alias_ty, env, &visiting2)?;
                match expanded.val {
                    Type::Chan(inner_s) => {
                        return expand_session(
                            &Spanned::new(inner_s, expanded.span),
                            env,
                            &visiting2,
                        );
                    }
                    _ => {
                        return Err(AliasError::NonSessionAliasUsedAsSession(
                            s.clone(),
                            expanded,
                        ));
                    }
                }
            } else {
                // A real recursion variable bound by `mu`.
                Session::Var(x.clone())
            }
        }
        Session::Semi { first, second } => Session::Semi {
            first: Box::new(expand_session(first, env, visiting)?),
            second: Box::new(expand_session(second, env, visiting)?),
        },
        Session::Mu(x, body) => {
            // Shadow the alias environment for the bound variable while
            // expanding the body, so that a `mu`-bound variable is never
            // mistaken for a type alias.
            let env2: AliasEnv = env
                .iter()
                .filter(|(k, _)| **k != x.val)
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect();
            Session::Mu(x.clone(), Box::new(expand_session(body, &env2, visiting)?))
        }
        Session::Op(op, t) => Session::Op(*op, Box::new(expand_type(t, env, visiting)?)),
        Session::Choice(op, cs) => Session::Choice(
            *op,
            cs.iter()
                .map(|(l, s)| Ok((l.clone(), expand_session(s, env, visiting)?)))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        Session::End(op) => Session::End(*op),
        Session::BorrowEnd(op) => Session::BorrowEnd(*op),
        Session::Skip => Session::Skip,
        Session::UVar(id) => Session::UVar(*id),
    };
    Ok(Spanned::new(s2, span))
}

fn wrap_mu(name: &SId, t: SType) -> SType {
    let span = t.span.clone();
    let t2 = match t.val {
        Type::Chan(s) => Type::Chan(Session::Mu(
            name.clone(),
            Box::new(Spanned::new(s, t.span.clone())),
        )),
        other => other,
    };
    Spanned::new(t2, span)
}
