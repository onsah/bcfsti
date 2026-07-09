use std::collections::{HashMap, HashSet};

use crate::syntax::{Expr, Id, SExpr, SSession, SType, Session, Type};
use crate::type_checker::TypeError;
use crate::util::span::Spanned;

pub type AliasEnv = HashMap<Id, SSession>;

pub fn get_alias_env(e: SExpr) -> (SExpr, AliasEnv) {
    let mut env = HashMap::new();
    let mut current_expr = e;
    loop {
        match current_expr.val {
            Expr::TypeDef(name, t, body, _) => {
                env.insert(
                    name.val.clone(),
                    Spanned::new(
                        Session::Mu(name.clone(), Box::new(t.clone())),
                        current_expr.span.clone(),
                    ),
                );
                current_expr = *body;
            }
            _ => break (current_expr, env),
        }
    }
}

pub fn expand_stype(ty: &SType, env: &AliasEnv) -> Result<SType, TypeError> {
    let bound = HashSet::new();
    Ok(Spanned::new(expand_type(ty, env, &bound)?, ty.span.clone()))
}

pub fn expand_type(ty: &Type, env: &AliasEnv, bound: &HashSet<Id>) -> Result<Type, TypeError> {
    match ty {
        Type::Chan(session) => expand_session(&session, env, bound).map(Type::Chan),
        Type::Arr {
            mob,
            mult,
            eff,
            param,
            ret,
        } => Ok(Type::Arr {
            mob: mob.clone(),
            mult: mult.clone(),
            eff: eff.clone(),
            param: Box::new(Spanned::new(
                expand_type(param, env, bound)?,
                param.span.clone(),
            )),
            ret: Box::new(Spanned::new(
                expand_type(ret, env, bound)?,
                ret.span.clone(),
            )),
        }),
        Type::Prod {
            mult,
            first,
            second,
        } => Ok(Type::Prod {
            mult: mult.clone(),
            first: Box::new(Spanned::new(
                expand_type(first, env, bound)?,
                first.span.clone(),
            )),
            second: Box::new(Spanned::new(
                expand_type(second, env, bound)?,
                second.span.clone(),
            )),
        }),
        Type::Variant(items) => Ok(Type::Variant(
            items
                .iter()
                .map(|(label, ty)| {
                    Ok((
                        label.clone(),
                        Spanned::new(expand_type(ty, env, bound)?, ty.span.clone()),
                    ))
                })
                .collect::<Result<_, _>>()?,
        )),
        Type::Unit => Ok(Type::Unit),
        Type::Int => Ok(Type::Int),
        Type::Bool => Ok(Type::Bool),
        Type::String => Ok(Type::String),
    }
}

pub fn expand_session(
    session: &Session,
    env: &AliasEnv,
    bound: &HashSet<Id>,
) -> Result<Session, TypeError> {
    match &session {
        Session::Var(id) => {
            if bound.contains(&id.val) {
                Ok(Session::Var(id.clone()))
            } else if let Some(session) = env.get(&id.val) {
                expand_session(&session, env, bound)
            } else {
                Err(TypeError::UndefinedAlias(id.clone()))
            }
        }
        Session::Mu(id, body) => {
            let mut new_bound = bound.clone();
            new_bound.insert(id.val.clone());
            let expanded_body = expand_session(&body.val, env, &new_bound)?;
            Ok(Session::Mu(
                id.clone(),
                Box::new(Spanned::new(expanded_body, body.span.clone())),
            ))
        }
        Session::Semi { first, second } => Ok(Session::Semi {
            first: Box::new(Spanned::new(
                expand_session(&first.val, env, bound)?,
                first.span.clone(),
            )),
            second: Box::new(Spanned::new(
                expand_session(&second.val, env, bound)?,
                second.span.clone(),
            )),
        }),
        Session::Op(op, ty) => Ok(Session::Op(
            *op,
            Box::new(Spanned::new(
                expand_type(&ty.val, env, bound)?,
                ty.span.clone(),
            )),
        )),
        Session::Choice(op, items) => {
            let mut new_items = Vec::new();
            for (name, session) in items {
                new_items.push((
                    name.clone(),
                    Spanned::new(expand_session(session, env, bound)?, session.span.clone()),
                ));
            }
            Ok(Session::Choice(*op, new_items))
        }
        Session::End(op) => Ok(Session::End(*op)),
        Session::BorrowEnd(op) => Ok(Session::BorrowEnd(*op)),
        Session::Skip => Ok(Session::Skip),
        Session::UVar(id) => Ok(Session::UVar(id.clone())),
    }
}
