use std::collections::HashMap;

use crate::syntax::{Expr, Id, SExpr, SSession, SType, Session, Type};
use crate::type_checker::TypeError;
use crate::util::span::{Spanned, fake_span};

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

/// Since type variable shadowing is forbidden,
pub fn check_shadowing(e: &SExpr, alias_env: &AliasEnv) -> Result<(), TypeError> {
    match &e.val {
        Expr::Const(_) => Ok(()),
        Expr::New(session) => check_session_shadowing(session, alias_env),
        Expr::Fork(spanned) => check_shadowing(spanned, alias_env),
        Expr::End(_, spanned) => check_shadowing(spanned, alias_env),
        Expr::Send(spanned, spanned1, spanned2) => {
            check_type_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)?;
            check_shadowing(spanned2, alias_env)
        }
        Expr::Recv(spanned, spanned1) => {
            check_type_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::LSplit(spanned, spanned1) => {
            check_session_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::RSplit(spanned, spanned1) => {
            check_session_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::BorrowEnd(_, spanned) => check_shadowing(spanned, alias_env),
        Expr::Discard(spanned) => check_shadowing(spanned, alias_env),
        Expr::Var(_) => Ok(()),
        Expr::Abs(_, spanned1) => check_shadowing(spanned1, alias_env),
        Expr::App(spanned, spanned1) => {
            check_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::Seq(spanned, spanned1) => {
            check_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::Pair(spanned, spanned1) => {
            check_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::Let(_, spanned1, spanned2, _) => {
            check_shadowing(spanned1, alias_env)?;
            check_shadowing(spanned2, alias_env)
        }
        Expr::LetDecl(_, spanned1, _, spanned2, spanned3) => {
            check_type_shadowing(spanned1, alias_env)?;
            check_shadowing(&spanned2.val.body, alias_env)?;
            check_shadowing(spanned3, alias_env)
        }
        Expr::LetPair(_, _, spanned2, spanned3) => {
            check_shadowing(spanned2, alias_env)?;
            check_shadowing(spanned3, alias_env)
        }
        Expr::TypeDef(_, spanned1, spanned2, _) => {
            check_session_shadowing(spanned1, alias_env)?;
            check_shadowing(spanned2, alias_env)
        }
        Expr::Inj(_, spanned1) => check_shadowing(spanned1, alias_env),
        Expr::CaseSum(spanned, items) => {
            check_shadowing(spanned, alias_env)?;
            for (_, _, expr) in items {
                check_shadowing(expr, alias_env)?;
            }
            Ok(())
        }
        Expr::Select(_, spanned1) => check_shadowing(spanned1, alias_env),
        Expr::Branch(spanned) => check_shadowing(spanned, alias_env),
        Expr::Ann(spanned, spanned1) => {
            check_shadowing(spanned, alias_env)?;
            check_type_shadowing(spanned1, alias_env)
        }
        Expr::Op1(_, spanned) => check_shadowing(spanned, alias_env),
        Expr::Op2(_, spanned, spanned1) => {
            check_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)
        }
        Expr::If(spanned, spanned1, spanned2) => {
            check_shadowing(spanned, alias_env)?;
            check_shadowing(spanned1, alias_env)?;
            check_shadowing(spanned2, alias_env)
        }
        Expr::TyApp(e, ty) => {
            check_shadowing(e, alias_env)?;
            check_type_shadowing(ty, alias_env)
        }
        Expr::TyAbs { expr, .. } => check_shadowing(expr, alias_env),
    }
}

fn check_session_shadowing(session: &SSession, alias_env: &AliasEnv) -> Result<(), TypeError> {
    match &session.val {
        Session::Skip => Ok(()),
        Session::Semi { first, second } => {
            check_session_shadowing(first, alias_env)?;
            check_session_shadowing(second, alias_env)
        }
        Session::End(_) => Ok(()),
        Session::BorrowEnd(_) => Ok(()),
        Session::Op(_, ty) => check_type_shadowing(ty, alias_env),
        Session::Choice(_, items) => {
            for (_, session) in items {
                check_session_shadowing(session, alias_env)?;
            }
            Ok(())
        }
        Session::Mu(id, body) => {
            if alias_env.contains_key(&id.val) {
                Err(TypeError::WfSessionShadowing(session.clone(), id.clone()))
            } else {
                check_session_shadowing(body, alias_env)
            }
        }
        Session::Var(_) => Ok(()),
        Session::UVar(_) => Ok(()),
        Session::PVar { .. } => Ok(()),
    }
}

fn check_type_shadowing(ty: &SType, alias_env: &AliasEnv) -> Result<(), TypeError> {
    match &ty.val {
        Type::Chan(session) => check_session_shadowing(&fake_span(session.clone()), alias_env),
        Type::Arr { param, ret, .. } => {
            check_type_shadowing(param, alias_env)?;
            check_type_shadowing(ret, alias_env)
        }
        Type::Prod { first, second, .. } => {
            check_type_shadowing(first, alias_env)?;
            check_type_shadowing(second, alias_env)
        }
        Type::Variant(items) => {
            for (_, ty) in items {
                check_type_shadowing(ty, alias_env)?;
            }
            Ok(())
        }
        Type::Unit | Type::Int | Type::Bool | Type::String => Ok(()),
        Type::Abstraction { ty, .. } => check_type_shadowing(ty, alias_env),
        Type::PVar { .. } => Ok(()),
    }
}
