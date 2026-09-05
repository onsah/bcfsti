use std::collections::HashMap;

use crate::syntax::{Expr, Id, SExpr, SType, Type};
use crate::type_checker::TypeError;
use crate::util::span::Spanned;

pub type AliasEnv = HashMap<Id, SType>;

pub fn get_alias_env(e: SExpr) -> (SExpr, AliasEnv) {
    let mut env = HashMap::new();
    let mut current_expr = e;
    loop {
        match current_expr.val {
            Expr::TypeDef(name, t, body, _) => {
                env.insert(
                    name.val.clone(),
                    Spanned::new(
                        Type::Mu(name.clone(), Box::new(t.clone())),
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
        Expr::New(sess_type) => check_type_shadowing(sess_type, alias_env),
        Expr::Fork(func) => check_shadowing(func, alias_env),
        Expr::End(_, chan) => check_shadowing(chan, alias_env),
        Expr::Send(ty, val, chan) => {
            check_type_shadowing(ty, alias_env)?;
            check_shadowing(val, alias_env)?;
            check_shadowing(chan, alias_env)
        }
        Expr::Recv(ty, chan) => {
            check_type_shadowing(ty, alias_env)?;
            check_shadowing(chan, alias_env)
        }
        Expr::LSplit(prefix_session, chan) => {
            check_type_shadowing(prefix_session, alias_env)?;
            check_shadowing(chan, alias_env)
        }
        Expr::RSplit(prefix_session, chan) => {
            check_type_shadowing(prefix_session, alias_env)?;
            check_shadowing(chan, alias_env)
        }
        Expr::BorrowEnd(_, chan) => check_shadowing(chan, alias_env),
        Expr::Discard(chan) => check_shadowing(chan, alias_env),
        Expr::Var(_) => Ok(()),
        Expr::Abs(_, body) => check_shadowing(body, alias_env),
        Expr::App(abs, arg) => {
            check_shadowing(abs, alias_env)?;
            check_shadowing(arg, alias_env)
        }
        Expr::Seq(e1, e2) => {
            check_shadowing(e1, alias_env)?;
            check_shadowing(e2, alias_env)
        }
        Expr::Pair(first, second) => {
            check_shadowing(first, alias_env)?;
            check_shadowing(second, alias_env)
        }
        Expr::Let(_, var_expr, body_expr, _) => {
            check_shadowing(var_expr, alias_env)?;
            check_shadowing(body_expr, alias_env)
        }
        Expr::LetDecl(_, ty, _, clause, body, _) => {
            check_type_shadowing(ty, alias_env)?;
            check_shadowing(&clause.val.body, alias_env)?;
            check_shadowing(body, alias_env)
        }
        Expr::LetPair(_, _, expr, body) => {
            check_shadowing(expr, alias_env)?;
            check_shadowing(body, alias_env)
        }
        Expr::TypeDef(_, ty, body, _) => {
            check_type_shadowing(ty, alias_env)?;
            check_shadowing(body, alias_env)
        }
        Expr::Inj(_, expr) => check_shadowing(expr, alias_env),
        Expr::CaseSum(expr, items) => {
            check_shadowing(expr, alias_env)?;
            for (_, _, case_expr) in items {
                check_shadowing(case_expr, alias_env)?;
            }
            Ok(())
        }
        Expr::Select(_, chan_expr) => check_shadowing(chan_expr, alias_env),
        Expr::Branch(chan_expr) => check_shadowing(chan_expr, alias_env),
        Expr::Ann(expr, ty) => {
            check_shadowing(expr, alias_env)?;
            check_type_shadowing(ty, alias_env)
        }
        Expr::Op1(_, expr) => check_shadowing(expr, alias_env),
        Expr::Op2(_, expr1, expr2) => {
            check_shadowing(expr1, alias_env)?;
            check_shadowing(expr2, alias_env)
        }
        Expr::If(cond_expr, then_expr, else_expr) => {
            check_shadowing(cond_expr, alias_env)?;
            check_shadowing(then_expr, alias_env)?;
            check_shadowing(else_expr, alias_env)
        }
        Expr::TyApp(expr, tys) => {
            check_shadowing(expr, alias_env)?;
            for ty in tys {
                check_type_shadowing(ty, alias_env)?;
            }
            Ok(())
        }
        Expr::TyAbs { expr, .. } => check_shadowing(expr, alias_env),
    }
}

fn check_type_shadowing(ty: &SType, alias_env: &AliasEnv) -> Result<(), TypeError> {
    match &ty.val {
        Type::Skip => Ok(()),
        Type::Semi { first, second } => {
            check_type_shadowing(first, alias_env)?;
            check_type_shadowing(second, alias_env)
        }
        Type::End(_) => Ok(()),
        Type::BorrowEnd(_) => Ok(()),
        Type::Op(_, payload_ty) => check_type_shadowing(payload_ty, alias_env),
        Type::Choice(_, items) => {
            for (_, branch) in items {
                check_type_shadowing(branch, alias_env)?;
            }
            Ok(())
        }
        Type::Mu(id, body) => {
            if alias_env.contains_key(&id.val) {
                Err(TypeError::WfSessionShadowing(ty.clone(), id.clone()))
            } else {
                check_type_shadowing(body, alias_env)
            }
        }
        Type::Var(_) => Ok(()),
        Type::UVar(_) => Ok(()),
        Type::PVar { .. } => Ok(()),
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
    }
}
