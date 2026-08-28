use std::collections::{HashMap, HashSet};

use crate::{
    constraint::Constraints,
    context::{Ctx, JoinOrd, ext},
    kinding,
    normalization::{normalise, normalise_session},
    session_type,
    syntax::{
        Eff, Expr, Id, Kind, Label, Mob, Mult, Op1, Op2, PVarId, Quantification,
        QuantificationType, SEff, SExpr, SId, SMult, SPattern, SQualification, SQuantification,
        SSession, SType, Session, SessionOp, Type, UVarId,
    },
    type_alias::AliasEnv,
    type_context::TypeCtx,
    util::{
        boxed::Boxed,
        pretty::pretty_def,
        span::{Spanned, fake_span},
    },
};

#[derive(Debug, Clone, PartialEq)]
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
    AbsNotMobile(SExpr, SType),
    UnrArrMustBeMobile(SType, Mob),
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
    RecursiveFunctionMustBeUnrestricted(SType, SId),
    WfNonContractive(SSession, SId),
    WfEmptyChoice(SSession),
    WfEmptyVariant(SType),
    MainReturnsOrd(SExpr, SType),
    WfSessionNotClosed(SSession, SId),
    WfSessionShadowing(SSession, SId),
    TypeNotValidForNew(SSession),
    SessionTypeOnlySkips(SSession),
    SessionTypeNotMobileInContext(SExpr, Ctx, SId),
    UndefinedAlias(SId),
    QualificationNotWellFormed(TypeCtx, SQuantification),
    KindMismatch(SType, Kind, TypeCtx),
    QualificationNotSatisfied(TypeCtx, SQualification),
    UndefinedPVar(SType, PVarId),
    VariablesUnsolvable { vars: HashSet<UVarId> },
    AssignmentNotMobile { expr: SExpr, id: SId, ctx: Ctx },
}

pub fn infer_type(e: &SExpr, alias_env: AliasEnv) -> Result<(SType, Constraints, Eff), TypeError> {
    let mut checker = TypeChecker {
        uvar_counter: 0,
        alias_env,
    };
    let (t, cs, eff) = checker.infer(&Ctx::Empty, &TypeCtx::empty(), e)?;
    if !TypeCtx::empty().unr(&t) {
        return Err(TypeError::MainReturnsOrd(e.clone(), t.clone()));
    }
    Ok((t, cs, eff))
}

struct TypeChecker {
    uvar_counter: usize,
    alias_env: AliasEnv,
}

impl TypeChecker {
    fn infer(
        &mut self,
        ctx: &Ctx,
        ty_ctx: &TypeCtx,
        e: &SExpr,
    ) -> Result<(SType, Constraints, Eff), TypeError> {
        // println!("Infer: {}", pretty_def(&e));
        // println!("Ctx: {}", pretty_context_notype(&ctx.simplify()));
        let ty = match &e.val {
            Expr::Const(c) => {
                assert_unr_ctx(e, ctx, ty_ctx)?;
                let ty = match c {
                    crate::syntax::Const::Unit => Type::Unit,
                    crate::syntax::Const::Int(_) => Type::Int,
                    crate::syntax::Const::Bool(_) => Type::Bool,
                    crate::syntax::Const::String(_) => Type::String,
                };

                Ok((fake_span(ty), Constraints::empty(), Eff::No))
            }
            Expr::Var(x) => match ctx.lookup_ord_pure(ty_ctx, x) {
                Some((ctx, ty)) => {
                    assert_unr_ctx(e, &ctx, ty_ctx)?;
                    let ty = normalise(ty_ctx, &self.alias_env, &ty)?;
                    Ok((ty, Constraints::empty(), Eff::No))
                }
                None => Err(TypeError::UndefinedVariable(x.clone())),
            },
            Expr::New(sess_type) => {
                if !ctx.is_unr(ty_ctx) {
                    return Err(TypeError::LeftOverCtx(e.clone(), ctx.clone()));
                }
                let sess_type = normalise_session(ty_ctx, &self.alias_env, sess_type)?;
                kinding::check_session(ty_ctx, &self.alias_env, &sess_type)?;

                if !ty_ctx.new(&sess_type.val) {
                    return Err(TypeError::TypeNotValidForNew(sess_type.clone()));
                }
                let typ = fake_span(Type::Prod {
                    mult: fake_span(Mult::Lin),
                    first: Box::new(Spanned::new(
                        Type::Chan(session_type! { Acq; (sess_type.clone(); Close) }.val),
                        sess_type.span.clone(),
                    )),
                    second: Box::new(Spanned::new(
                        Type::Chan(session_type! { Acq; (fake_span(sess_type.dual()); Wait) }.val),
                        sess_type.span.clone(),
                    )),
                });
                Ok((typ, Constraints::empty(), Eff::No))
            }
            Expr::LetPair(id1, id2, expr, body) => {
                if ctx.vars().contains(&id1.val) {
                    return Err(TypeError::Shadowing(e.clone(), id1.clone()));
                }
                if ctx.vars().contains(&id2.val) {
                    return Err(TypeError::Shadowing(e.clone(), id2.clone()));
                }

                let expr_ctx = ctx.restrict(&expr.free_vars());
                let body_ctx = ctx.restrict(&body.free_vars());

                {
                    let res_ctx = ctx_join(e, ty_ctx, &expr_ctx, &body_ctx, JoinOrd::Ordered)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            res_ctx.clone(),
                            ctx.clone(),
                        ));
                    }
                }

                let (expr_ty, expr_constraints, expr_eff) = self.infer(&expr_ctx, ty_ctx, expr)?;

                let Type::Prod {
                    mult,
                    first,
                    second,
                } = &expr_ty.val
                else {
                    return Err(TypeError::Mismatch(
                        *expr.clone(),
                        Err("Product".into()),
                        expr_ty.clone(),
                    ));
                };

                let (body_ty, body_constraints, body_eff) = {
                    let var_ctx = ext(
                        mult.val,
                        Ctx::Bind(id1.clone(), *first.clone()),
                        Ctx::Bind(id2.clone(), *second.clone()),
                    );
                    let ord = if expr_eff == Eff::Yes {
                        JoinOrd::Ordered
                    } else {
                        JoinOrd::Unordered
                    };
                    let body_ctx = ctx_join(e, ty_ctx, &var_ctx, &body_ctx, ord)?;
                    self.infer(&body_ctx, ty_ctx, body)
                }?;

                Ok((
                    body_ty,
                    expr_constraints.join(body_constraints),
                    Eff::lub(expr_eff, body_eff),
                ))
            }
            Expr::Seq(e1, e2) => {
                let e1_ctx = ctx.restrict(&e1.free_vars());
                let e2_ctx = ctx.restrict(&e2.free_vars());

                {
                    let res_ctx = ctx_join(e, ty_ctx, &e1_ctx, &e2_ctx, JoinOrd::Ordered)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                let (e1_constraints, e1_eff) =
                    self.check(&e1_ctx, ty_ctx, e1, &fake_span(Type::Unit))?;
                let (e2_ty, e2_constraints, e2_eff) = self.infer(&e2_ctx, ty_ctx, e2)?;

                Ok((
                    e2_ty,
                    e1_constraints.join(e2_constraints),
                    Eff::lub(e1_eff, e2_eff),
                ))
            }
            Expr::Send(ty, val, chan) => {
                if !ty_ctx.mobile(&ty.val) {
                    return Err(TypeError::AbsNotMobile(e.clone(), ty.clone()));
                }

                let val_ctx = ctx.restrict(&val.free_vars());
                let (val_cs, _) = self.check(&val_ctx, ty_ctx, val, ty)?;

                let chan_ctx = ctx.restrict(&chan.free_vars());
                let expected_chan_ty = fake_span(Type::Chan(Session::Op(
                    SessionOp::Send,
                    Box::new(ty.clone()),
                )));
                let (chan_cs, _) = self.check(&chan_ctx, ty_ctx, chan, &expected_chan_ty)?;

                // ctx must be a subcontext of unordered join of val_ctx and chan_ctx must
                {
                    let res_ctx = ctx_join(e, ty_ctx, &val_ctx, &chan_ctx, JoinOrd::Unordered)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                Ok((fake_span(Type::Unit), val_cs.join(chan_cs), Eff::Yes))
            }
            Expr::Recv(ty, chan) => {
                if !ty_ctx.mobile(&ty.val) {
                    return Err(TypeError::AbsNotMobile(e.clone(), ty.clone()));
                }

                let chan_ctx = ctx.restrict(&chan.free_vars());
                let expected_chan_ty = fake_span(Type::Chan(Session::Op(
                    SessionOp::Recv,
                    Box::new(ty.clone()),
                )));
                let (chan_cs, _) = self.check(&chan_ctx, ty_ctx, chan, &expected_chan_ty)?;

                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                Ok((ty.clone(), chan_cs, Eff::Yes))
            }
            Expr::Fork(func) => {
                let body_ctx = ctx.restrict(&func.free_vars());

                if !ctx.is_subctx_of(&ty_ctx, &body_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        body_ctx.clone(),
                    ));
                }

                let expected_body_ty = fake_span(Type::Arr {
                    mob: fake_span(Mob::Mobile),
                    mult: fake_span(Mult::Lin),
                    eff: fake_span(Eff::Yes),
                    param: Box::new(fake_span(Type::Unit)),
                    ret: Box::new(fake_span(Type::Unit)),
                });
                let (body_cs, body_eff) = self.check(&body_ctx, ty_ctx, func, &expected_body_ty)?;

                Ok((fake_span(Type::Unit), body_cs, body_eff))
            }
            Expr::Discard(chan) => {
                let chan_ctx = ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let (chan_cs, chan_eff) = self.check(
                    &chan_ctx,
                    ty_ctx,
                    chan,
                    &fake_span(Type::Chan(Session::Skip)),
                )?;

                Ok((fake_span(Type::Unit), chan_cs, chan_eff))
            }
            Expr::BorrowEnd(op, chan) => {
                let chan_ctx = ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let expected_ty = fake_span(Type::Chan(Session::BorrowEnd(*op)));
                let (chan_cs, chan_eff) = self.check(&chan_ctx, ty_ctx, chan, &expected_ty)?;

                Ok((fake_span(Type::Unit), chan_cs, chan_eff))
            }
            Expr::End(op, chan) => {
                let chan_ctx = ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let expected_ty = fake_span(Type::Chan(Session::End(*op)));
                let (chan_cs, chan_eff) = self.check(&chan_ctx, ty_ctx, chan, &expected_ty)?;

                Ok((fake_span(Type::Unit), chan_cs, chan_eff))
            }
            Expr::LSplit(prefix_session, chan) => {
                let chan_ctx = &ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let uvar = self.new_uvar();
                let expected_chan_ty = fake_span(Type::Chan(
                    session_type! { prefix_session.clone(); uvar.clone() }.val,
                ));
                let (chan_cs, chan_eff) = self.check(chan_ctx, ty_ctx, chan, &expected_chan_ty)?;

                let ret_ty = Type::Prod {
                    mult: fake_span(Mult::OrdL),
                    first: Box::new(fake_span(Type::Chan(prefix_session.val.clone()))),
                    second: Box::new(fake_span(Type::Chan(uvar.val))),
                };

                Ok((fake_span(ret_ty), chan_cs, chan_eff))
            }
            Expr::RSplit(prefix_session, chan) => {
                let chan_ctx = &ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let uvar = self.new_uvar();
                let expected_chan_ty = fake_span(Type::Chan(
                    session_type! { prefix_session.clone(); uvar.clone() }.val,
                ));
                let (chan_cs, chan_eff) = self.check(chan_ctx, ty_ctx, chan, &expected_chan_ty)?;

                let ret_ty = Type::Prod {
                    mult: fake_span(Mult::Lin),
                    first: Box::new(fake_span(Type::Chan(
                        session_type! { prefix_session.clone(); Ret }.val,
                    ))),
                    second: Box::new(fake_span(Type::Chan(
                        session_type! { Acq; uvar.clone() }.val,
                    ))),
                };

                Ok((fake_span(ret_ty), chan_cs, chan_eff))
            }
            Expr::App(abs, arg) => {
                let abs_ctx = ctx.restrict(&abs.free_vars());
                let arg_ctx = ctx.restrict(&arg.free_vars());

                let (abs_ty, abs_cs, abs_eff) = self.infer(&abs_ctx, ty_ctx, abs)?;

                let Type::Arr {
                    mult,
                    eff,
                    param,
                    ret,
                    ..
                } = abs_ty.val
                else {
                    return Err(TypeError::Mismatch(
                        *abs.clone(),
                        Err("Function".into()),
                        abs_ty.clone(),
                    ));
                };

                {
                    let (c1, c2, o) = match mult.val {
                        Mult::OrdR => (&arg_ctx, &abs_ctx, JoinOrd::Ordered),
                        Mult::OrdL => (&abs_ctx, &arg_ctx, JoinOrd::Ordered),
                        Mult::Unr | Mult::Lin => (&abs_ctx, &arg_ctx, JoinOrd::Unordered),
                    };
                    let res_ctx = ctx_join(e, ty_ctx, c1, c2, o)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                if mult.val == Mult::OrdL && abs_eff == Eff::Yes {
                    return Err(TypeError::MismatchEff(
                        e.clone(),
                        fake_span(abs_eff),
                        fake_span(Eff::No),
                    ));
                }

                let (arg_cs, arg_eff) = self.check(&arg_ctx, ty_ctx, arg, &param)?;

                if mult.val == Mult::OrdR && arg_eff == Eff::Yes {
                    return Err(TypeError::MismatchEff(
                        e.clone(),
                        fake_span(arg_eff),
                        fake_span(Eff::No),
                    ));
                }

                let ret = normalise(ty_ctx, &self.alias_env, &ret)?;
                Ok((
                    ret,
                    abs_cs.join(arg_cs),
                    Eff::lub(*eff, Eff::lub(abs_eff, arg_eff)),
                ))
            }
            Expr::Let(var_id, var_expr, body_expr, _) => {
                let var_ctx = ctx.restrict(&var_expr.free_vars());
                let (var_ty, var_cs, var_eff) = self.infer(&var_ctx, ty_ctx, var_expr)?;

                let (body_ty, body_cs, body_eff) = self.infer_let_body(
                    ctx, ty_ctx, e, var_id, &var_ctx, &var_ty, var_eff, body_expr,
                )?;

                Ok((body_ty, var_cs.join(body_cs), Eff::lub(var_eff, body_eff)))
            }
            Expr::LetDecl(id, var_ty, quant, clause, body) => {
                let (var_ty, var_body) = {
                    // Desugar clause to an abstraction
                    let var_body = Spanned::new(
                        Expr::Abs(clause.var_id.clone(), Box::new(clause.body.clone())),
                        clause.span.clone(),
                    );
                    Self::desugar_quantification(quant.clone(), var_ty.clone(), var_body)
                };

                if let Type::Arr { mult, .. } = &var_ty.val
                    && mult.val != Mult::Unr
                {
                    return Err(TypeError::RecursiveFunctionMustBeUnrestricted(
                        var_ty.clone(),
                        id.clone(),
                    ));
                }

                // Add the function to the context
                let clause_ctx = ctx.restrict(&clause.body.free_vars());
                let (var_cs, var_eff) = {
                    let clause_ctx = ext(
                        Mult::Unr,
                        clause_ctx.clone(),
                        Ctx::Bind(id.clone(), var_ty.clone()),
                    );
                    self.check(&clause_ctx, ty_ctx, &var_body, &var_ty)?
                };

                let (ty, let_cs, let_eff) =
                    self.infer_let_body(ctx, ty_ctx, e, id, &clause_ctx, &var_ty, var_eff, body)?;
                Ok((ty, var_cs.join(let_cs), Eff::lub(var_eff, let_eff)))
            }
            Expr::CaseSum(expr, cases) => {
                let expr_ctx = ctx.restrict(&expr.free_vars());
                let (expr_ty, expr_cs, expr_eff) = self.infer(&expr_ctx, ty_ctx, expr)?;

                let Type::Variant(variants) = &expr_ty.val else {
                    return Err(TypeError::Mismatch(
                        *expr.clone(),
                        Err("Variant".into()),
                        expr_ty.clone(),
                    ));
                };

                // Ensure variants and cases labels are equivalent
                {
                    let case_labels: Vec<_> =
                        cases.iter().map(|(label, _, _)| &label.val).collect();
                    let variant_labels: Vec<_> =
                        variants.iter().map(|(label, _)| &label.val).collect();
                    Self::check_variant_label_eq(e, &expr_ty, &case_labels, &variant_labels)?
                };

                let case_inferences: Vec<(String, (Spanned<Type>, Constraints, Eff))> = cases
                    .iter()
                    .map(|(label, var_name, case_expr)| {
                        let case_ctx = ctx.restrict(&case_expr.free_vars());

                        let res_ctx =
                            ctx_join(e, ty_ctx, &expr_ctx, &case_ctx, JoinOrd::Ordered)?;
                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                            return Err(TypeError::CtxSplitFailed(
                                e.clone(),
                                ctx.clone(),
                                res_ctx.clone(),
                            ));
                        }

                        if expr_ctx.vars().contains(&var_name.val) {
                            return Err(TypeError::Shadowing(e.clone(), var_name.clone()));
                        }

                        let case_ty = variants.iter().find_map(|(var_label, var_ty)| if var_label.val == label.val {
                            Some(var_ty.clone())
                        } else {
                            None
                        }).expect("Bug: set of labels in the variant type must be equal to the set of labels in cases");

                        let case_ctx = ctx_join(
                            e,
                            ty_ctx,
                            &Ctx::Bind(var_name.clone(), case_ty),
                            &case_ctx,
                            JoinOrd::Ordered,
                        )?;
                        let infer_res = self.infer(&case_ctx, ty_ctx, case_expr)?;
                        Ok((label.val.clone(), infer_res))
                    })
                    .collect::<Result<_, _>>()?;

                let expr_ty = case_inferences.first().unwrap().1.0.clone();
                let expr_cs = case_inferences
                    .iter()
                    .map(|(_, infer_res)| infer_res)
                    .fold(expr_cs, |acc, (_, cs, _)| acc.join(cs.clone()));
                let expr_eff = case_inferences
                    .iter()
                    .map(|(_, infer_res)| infer_res)
                    .fold(expr_eff, |acc, (_, _, eff)| Eff::lub(acc, *eff));

                let mut cs = expr_cs;
                for (i, (_, (ty1, _, _))) in case_inferences.iter().enumerate() {
                    for (_, (ty2, _, _)) in case_inferences[i + 1..].iter() {
                        cs.add(ty1.clone(), ty2.clone());
                    }
                }
                Ok((expr_ty, cs, expr_eff))
            }
            Expr::Select(label, chan_expr) => {
                let chan_ctx = ctx.restrict(&chan_expr.free_vars());

                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let (chan_ty, chan_cs, _chan_eff) = self.infer(&chan_ctx, ty_ctx, chan_expr)?;

                if let Type::Chan(Session::UVar(_)) = &chan_ty.val {
                    return Err(TypeError::TypeAnnotationMissing(*chan_expr.clone()));
                }

                let Type::Chan(s) = &chan_ty.val else {
                    return Err(TypeError::Mismatch(
                        *chan_expr.clone(),
                        Err("Chan".into()),
                        chan_ty.clone(),
                    ));
                };

                let Session::Choice(SessionOp::Send, branches) = s else {
                    return Err(TypeError::Mismatch(
                        *chan_expr.clone(),
                        Err("Choice<Send>".into()),
                        fake_span(Type::Chan(s.clone())),
                    ));
                };

                let label_ty = branches
                    .iter()
                    .find_map(|(branch_label, branch_ty)| {
                        if branch_label.val == label.val {
                            Some(branch_ty.clone())
                        } else {
                            None
                        }
                    })
                    .ok_or(TypeError::MismatchLabel(
                        e.clone(),
                        label.val.clone(),
                        chan_ty.clone(),
                    ))?;

                Ok((fake_span(Type::Chan(label_ty.val)), chan_cs, Eff::Yes))
            }
            Expr::Branch(chan_expr) => {
                let chan_ctx = ctx.restrict(&chan_expr.free_vars());

                if !ctx.is_subctx_of(&ty_ctx, &chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let (chan_ty, chan_cs, _chan_eff) = self.infer(&chan_ctx, ty_ctx, chan_expr)?;

                if let Type::Chan(Session::UVar(_)) = &chan_ty.val {
                    return Err(TypeError::TypeAnnotationMissing(*chan_expr.clone()));
                }

                let Type::Chan(Session::Choice(SessionOp::Recv, branches)) = chan_ty.val else {
                    return Err(TypeError::Mismatch(
                        *chan_expr.clone(),
                        Err("Chan<Choice<Recv>>".into()),
                        chan_ty.clone(),
                    ));
                };

                let ty = Type::Variant(
                    branches
                        .into_iter()
                        .map(|(label, Spanned { val, span })| {
                            (label, Spanned::new(Type::Chan(val), span))
                        })
                        .collect(),
                );
                Ok((fake_span(ty), chan_cs, Eff::Yes))
            }
            Expr::Ann(expr, ty) => {
                let ty = normalise(ty_ctx, &self.alias_env, ty)?;
                let (expr_cs, expr_eff) =
                    self.check(&ctx.restrict(&expr.free_vars()), ty_ctx, expr, &ty)?;

                Ok((ty, expr_cs, expr_eff))
            }
            Expr::Op1(op1, expr) => {
                let (expr_ty, expr_cs, expr_eff) = self.infer(ctx, ty_ctx, expr)?;
                let ty = match (op1, &expr_ty.val) {
                    (Op1::Neg, Type::Int) => Type::Int,
                    (Op1::Neg, _) => {
                        return Err(TypeError::Mismatch(
                            e.clone(),
                            Err(format!("Int")),
                            expr_ty.clone(),
                        ));
                    }
                    (Op1::Not, Type::Bool) => Type::Bool,
                    (Op1::Not, _) => {
                        return Err(TypeError::Mismatch(
                            e.clone(),
                            Err(format!("Bool")),
                            expr_ty.clone(),
                        ));
                    }
                    (Op1::ToStr, _) => Type::String,
                    (Op1::Print, _) => Type::Unit,
                };
                Ok((fake_span(ty), expr_cs, expr_eff))
            }
            Expr::Op2(op2, expr1, expr2) => {
                let expr1_ctx = ctx.restrict(&expr1.free_vars());
                let (expr1_ty, expr1_cs, expr1_eff) = self.infer(&expr1_ctx, ty_ctx, expr1)?;

                let expr2_ctx = ctx.restrict(&expr2.free_vars());
                let (expr2_ty, expr2_cs, expr2_eff) = self.infer(&expr2_ctx, ty_ctx, expr2)?;

                {
                    let res_ctx = ctx_join(e, ty_ctx, &expr1_ctx, &expr2_ctx, JoinOrd::Unordered)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                let ty = match (op2, &expr1_ty.val, &expr2_ty.val) {
                    (Op2::Add, Type::Int, Type::Int) => Type::Int,
                    (Op2::Add, Type::String, Type::String) => Type::String,
                    (Op2::Add, _, _) => {
                        return Err(TypeError::Op2Mismatch(
                            e.clone(),
                            Err(format!("String or Int")),
                            expr1_ty.clone(),
                            expr2_ty.clone(),
                        ));
                    }
                    (Op2::Sub | Op2::Mul | Op2::Div, Type::Int, Type::Int) => Type::Int,
                    (Op2::Sub | Op2::Mul | Op2::Div, _, _) => {
                        return Err(TypeError::Op2Mismatch(
                            e.clone(),
                            Err(format!("Int")),
                            expr1_ty.clone(),
                            expr2_ty.clone(),
                        ));
                    }
                    (
                        Op2::Eq | Op2::Neq | Op2::Lt | Op2::Le | Op2::Gt | Op2::Ge,
                        t1 @ (Type::Int | Type::Bool | Type::String | Type::Unit),
                        t2,
                    ) if ty_ctx.equivalent(t1, t2) => Type::Bool,
                    (Op2::Eq | Op2::Neq | Op2::Lt | Op2::Le | Op2::Gt | Op2::Ge, _, _) => {
                        return Err(TypeError::Op2Mismatch(
                            e.clone(),
                            Err(format!("Int or Bool or String or Unit")),
                            expr1_ty.clone(),
                            expr2_ty.clone(),
                        ));
                    }
                    (Op2::And | Op2::Or, Type::Bool, Type::Bool) => Type::Bool,
                    (Op2::And | Op2::Or, _, _) => {
                        return Err(TypeError::Op2Mismatch(
                            e.clone(),
                            Err(format!("Bool")),
                            expr1_ty.clone(),
                            expr2_ty.clone(),
                        ));
                    }
                };

                Ok((
                    fake_span(ty),
                    expr1_cs.join(expr2_cs),
                    Eff::lub(expr1_eff, expr2_eff),
                ))
            }
            Expr::If(cond_expr, then_expr, else_expr) => {
                let cond_ctx = ctx.restrict(&cond_expr.free_vars());
                let (cond_cs, cond_eff) =
                    self.check(&cond_ctx, ty_ctx, cond_expr, &fake_span(Type::Bool))?;

                let then_ctx = ctx.restrict(&then_expr.free_vars());
                let else_ctx = ctx.restrict(&else_expr.free_vars());

                {
                    let res_ctx = ctx_join(e, ty_ctx, &cond_ctx, &then_ctx, JoinOrd::Unordered)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                {
                    let res_ctx = ctx_join(e, ty_ctx, &cond_ctx, &else_ctx, JoinOrd::Unordered)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                let (then_ty, then_cs, then_eff) = self.infer(&then_ctx, ty_ctx, then_expr)?;
                let (else_ty, else_cs, else_eff) = self.infer(&else_ctx, ty_ctx, else_expr)?;

                let mut cs = cond_cs.join(then_cs).join(else_cs);
                cs.add(then_ty.clone(), else_ty.clone());

                Ok((
                    then_ty,
                    cs,
                    Eff::lub(cond_eff, Eff::lub(then_eff, else_eff)),
                ))
            }
            Expr::Inj(_, _) => Err(TypeError::TypeAnnotationMissing(e.clone())),
            Expr::Pair(_, _) => Err(TypeError::TypeAnnotationMissing(e.clone())),
            Expr::Abs(_, _) => Err(TypeError::TypeAnnotationMissing(e.clone())),
            Expr::TypeDef(_, _, _, _) => {
                unreachable!("type abbreviations are expanded before type checking")
            }
            Expr::TyApp(expr, tys) => {
                let (expr_ty, expr_cs, expr_eff) = self.infer(ctx, ty_ctx, expr)?;

                let Type::Abstraction {
                    typ: QuantificationType::Universal,
                    quantification,
                    ty: abs_ty,
                } = &expr_ty.val
                else {
                    return Err(TypeError::Mismatch(
                        *expr.clone(),
                        Err("Universal type abstraction".to_owned()),
                        expr_ty,
                    ));
                };

                for (ty, expected_kind) in tys
                    .iter()
                    .zip(quantification.bindings.iter().map(|(_, kind)| kind))
                {
                    kinding::check(ty_ctx, &self.alias_env, ty, expected_kind.val)?;
                }

                let bindings: HashMap<PVarId, SType> = quantification
                    .bindings
                    .iter()
                    .map(|(id, _)| id.val.clone())
                    .zip(tys.iter().cloned())
                    .collect();
                let substituted_qualifications: Vec<SQualification> = quantification
                    .qualifications
                    .iter()
                    .map(|q| Spanned::new(q.val.subst_poly(&bindings), q.span.clone()))
                    .collect();
                Self::check_qualifications(ty_ctx, substituted_qualifications.iter())?;

                let app_ty = fake_span(abs_ty.subst_poly(&bindings));
                Ok((app_ty, expr_cs, expr_eff))
            }
            Expr::TyAbs { .. } => Err(TypeError::TypeAnnotationMissing(e.clone())),
        }?;
        // println!("Inferred: {}", pretty_def(&ty.0));
        Ok(ty)
    }

    fn check_qualifications<'a>(
        ty_ctx: &TypeCtx,
        qualifications: impl Iterator<Item = &'a SQualification>,
    ) -> Result<(), TypeError> {
        for qualification in qualifications {
            if !ty_ctx.entails(qualification) {
                return Err(TypeError::QualificationNotSatisfied(
                    ty_ctx.clone(),
                    qualification.clone(),
                ));
            }
        }
        Ok(())
    }

    fn desugar_quantification(
        quantification: Option<SQuantification>,
        ty: SType,
        expr: SExpr,
    ) -> (SType, SExpr) {
        match quantification {
            Some(quantification) => {
                let var_ty = Spanned::new(
                    Type::Abstraction {
                        typ: QuantificationType::Universal,
                        quantification: quantification.clone(),
                        ty: Box::new(ty.clone()),
                    },
                    quantification.span.clone(),
                );

                let var_body = Spanned::new(
                    Expr::TyAbs {
                        quantification: quantification.clone(),
                        expr: Box::new(expr),
                    },
                    quantification.span.clone(),
                );

                (var_ty, var_body)
            }
            None => (ty, expr),
        }
    }

    /// Given an already type-checked variable, check the body
    fn infer_let_body(
        &mut self,
        ctx: &Ctx,
        ty_ctx: &TypeCtx,
        expr: &SExpr,
        var_id: &SId,
        var_ctx: &Ctx,
        var_ty: &SType,
        var_eff: Eff,
        body_expr: &SExpr,
    ) -> Result<(SType, Constraints, Eff), TypeError> {
        if ctx.vars().contains(&var_id.val) {
            return Err(TypeError::Shadowing(expr.clone(), var_id.clone()));
        }

        let body_ctx = ctx.restrict(&body_expr.free_vars());

        {
            let res_ctx = ctx_join(expr, ty_ctx, var_ctx, &body_ctx, JoinOrd::Ordered)?;

            if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                return Err(TypeError::CtxSplitFailed(
                    expr.clone(),
                    ctx.clone(),
                    res_ctx.clone(),
                ));
            }
        }

        let body_ctx = {
            let binding = Ctx::Bind(var_id.clone(), var_ty.clone());
            let ord = if var_eff == Eff::Yes {
                JoinOrd::Ordered
            } else {
                JoinOrd::Unordered
            };
            ctx_join(expr, ty_ctx, &binding, &body_ctx, ord)?
        };
        let (body_ty, body_cs, body_eff) = self.infer(&body_ctx, ty_ctx, body_expr)?;

        Ok((body_ty, body_cs, body_eff))
    }

    fn check(
        &mut self,
        ctx: &Ctx,
        ty_ctx: &TypeCtx,
        e: &SExpr,
        expected_ty: &SType,
    ) -> Result<(Constraints, Eff), TypeError> {
        // println!(
        //     "Check: {} against {}",
        //     pretty_def(&e),
        //     pretty_def(&expected_ty)
        // );
        match &e.val {
            Expr::Abs(id, body) => {
                let Type::Arr {
                    mob,
                    mult,
                    eff,
                    param,
                    ret,
                } = &expected_ty.val
                else {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!("function type")),
                        expected_ty.clone(),
                    ));
                };

                let mut ctx_cs = Constraints::empty();
                if mob.val == Mob::Mobile {
                    self.check_mobility(e, ctx, ty_ctx, &mut ctx_cs)?;
                }

                if mult.val == Mult::Unr {
                    if !ctx.is_unr(ty_ctx) {
                        return Err(TypeError::CtxNotUnr(e.clone(), ctx.clone()));
                    }
                    if mob.val != Mob::Mobile {
                        return Err(TypeError::UnrArrMustBeMobile(expected_ty.clone(), mob.val));
                    }
                }

                // Assert that `x` is not] in the context.
                if ctx.vars().contains(&id.val) {
                    Err(TypeError::Shadowing(e.clone(), id.clone()))?
                }

                let ctx = ext(**mult, Ctx::Bind(id.clone(), *param.clone()), ctx.clone());
                let (body_cs, body_eff) = self.check(&ctx, ty_ctx, body, ret)?;

                if body_eff > eff.val {
                    return Err(TypeError::MismatchEffSub(
                        *body.clone(),
                        fake_span(body_eff),
                        eff.clone(),
                    ));
                }

                Ok((ctx_cs.join(body_cs), Eff::No))
            }
            Expr::Pair(first, second) => {
                let first_ctx = ctx.restrict(&first.free_vars());
                let second_ctx = ctx.restrict(&second.free_vars());

                let Type::Prod {
                    mult,
                    first: expected_first,
                    second: expected_second,
                } = &expected_ty.val
                else {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!("product type")),
                        expected_ty.clone(),
                    ));
                };

                let (first_cs, first_eff) =
                    self.check(&first_ctx, ty_ctx, first, &expected_first)?;
                let (second_cs, second_eff) =
                    self.check(&second_ctx, ty_ctx, second, &expected_second)?;

                if mult.val == Mult::OrdL && second_eff == Eff::Yes {
                    return Err(TypeError::MismatchEff(
                        *second.clone(),
                        fake_span(second_eff),
                        fake_span(Eff::No),
                    ));
                }
                if mult.val == Mult::OrdR && first_eff == Eff::Yes {
                    return Err(TypeError::MismatchEff(
                        *first.clone(),
                        fake_span(first_eff),
                        fake_span(Eff::No),
                    ));
                }

                {
                    let (c1, c2, o) = match mult.val {
                        Mult::OrdR => (&second_ctx, &first_ctx, JoinOrd::Ordered),
                        Mult::OrdL => (&first_ctx, &second_ctx, JoinOrd::Ordered),
                        Mult::Unr | Mult::Lin => (&first_ctx, &second_ctx, JoinOrd::Unordered),
                    };
                    let res_ctx = ctx_join(e, ty_ctx, c1, c2, o)?;

                    if !ctx.is_subctx_of(&ty_ctx, &res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                Ok((first_cs.join(second_cs), Eff::lub(first_eff, second_eff)))
            }
            Expr::Inj(label, expr) => {
                let Type::Variant(variants) = &expected_ty.val else {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!("variant type")),
                        expected_ty.clone(),
                    ));
                };

                let Some((_, actual_ty)) = variants.iter().find(|(l2, _)| label.val == l2.val)
                else {
                    return Err(TypeError::MismatchLabel(
                        e.clone(),
                        label.val.clone(),
                        expected_ty.clone(),
                    ));
                };

                let (expr_cs, expr_eff) =
                    self.check(&ctx.restrict(&expr.free_vars()), ty_ctx, expr, actual_ty)?;

                Ok((expr_cs, expr_eff))
            }
            Expr::TyAbs {
                quantification,
                expr,
            } => {
                // TODO: Ensure expr is value
                let Quantification {
                    bindings,
                    qualifications,
                } = quantification.val.clone();
                let ty_ctx = ty_ctx.extend_bindings(Quantification::bindings(bindings.into_iter()));
                if kinding::check_qualifications_well_formed(
                    &ty_ctx,
                    &self.alias_env,
                    qualifications.iter(),
                )
                .is_err()
                {
                    return Err(TypeError::QualificationNotWellFormed(
                        ty_ctx,
                        quantification.clone(),
                    ));
                }

                if let Some(id) = quantification
                    .val
                    .bindings
                    .iter()
                    .map(|(id, _)| id)
                    .find(|id| ctx.vars().contains(&id.val))
                {
                    return Err(TypeError::Shadowing(e.clone(), id.clone()));
                }

                let Type::Abstraction {
                    typ: QuantificationType::Universal,
                    quantification: expected_quantification,
                    ty: expr_ty,
                } = &expected_ty.val
                else {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!("forall type")),
                        expected_ty.clone(),
                    ));
                };

                if quantification.val.bindings != expected_quantification.bindings
                    || &qualifications != &expected_quantification.qualifications
                {
                    return Err(TypeError::Mismatch(
                        e.clone(),
                        Err(format!(
                            "Forall with quantification {}",
                            pretty_def(Quantification {
                                bindings: quantification.bindings.clone(),
                                qualifications
                            })
                        )),
                        expected_ty.clone(),
                    ));
                }

                let ty_ctx =
                    ty_ctx.extend_qualifications(qualifications.into_iter().map(|q| q.val));
                self.check(&ctx, &ty_ctx, expr, expr_ty)
            }
            _ => {
                let (inferred_ty, mut cs, eff) = self.infer(ctx, ty_ctx, e)?;
                // let inferred_ty = self.expand_type(ty_ctx, &inferred_ty)?;
                // let expected_ty = self.expand_type(ty_ctx, expected_ty)?;

                if !ty_ctx.equivalent(&inferred_ty, &expected_ty) {
                    cs.add(inferred_ty, expected_ty.clone());
                }

                Ok((cs, eff))
            }
        }
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

    fn new_uvar(&mut self) -> SSession {
        let id = self.uvar_counter;
        self.uvar_counter += 1;
        fake_span(Session::UVar(id))
    }

    fn check_mobility(
        &self,
        expr: &SExpr,
        ctx: &Ctx,
        ty_ctx: &TypeCtx,
        cs: &mut Constraints,
    ) -> Result<(), TypeError> {
        // If we can't ensure that the type is mobile
        // we add a constraint that the type must be mobile
        // to later check that the solution satisfies mobility requirements.
        let mut non_mobile_ids = HashSet::new();
        for (id, ty) in ctx.binds_spanned() {
            if !ty_ctx.mobile(&normalise(ty_ctx, &self.alias_env, &ty)?.val) {
                if !ty.is_closed() {
                    non_mobile_ids.insert(id.clone());
                } else {
                    return Err(TypeError::SessionTypeNotMobileInContext(
                        expr.clone(),
                        ctx.clone(),
                        id,
                    ));
                }
            }
        }
        if !non_mobile_ids.is_empty() {
            cs.check_mobility(expr.clone(), non_mobile_ids, ctx.clone());
        }
        Ok(())
    }
}

fn assert_unr_ctx(e: &SExpr, ctx: &Ctx, ty_ctx: &TypeCtx) -> Result<(), TypeError> {
    if ctx.is_unr(ty_ctx) {
        Ok(())
    } else {
        Err(TypeError::LeftOverCtx(e.clone(), ctx.clone()))
    }
}

fn ctx_join(e: &SExpr, ty_ctx: &TypeCtx, c1: &Ctx, c2: &Ctx, o: JoinOrd) -> Result<Ctx, TypeError> {
    let binds2 = c2.binds();
    let mut xs = HashSet::new();
    for (x, t1) in c1.binds() {
        if let Some(t2) = binds2.get(&x)
            && (!ty_ctx.unr(&t1) || !ty_ctx.unr(t2))
        {
            xs.insert(x);
        }
    }
    if !xs.is_empty() {
        return Err(TypeError::CtxCtxSplitFailed(
            e.clone(),
            Ctx::Join(c1.boxed(), c2.boxed(), o),
            xs,
        ));
    }
    Ok(Ctx::Join(c1.boxed(), c2.boxed(), o))
}
