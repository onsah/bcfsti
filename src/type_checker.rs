use std::{
    collections::{HashMap, HashSet},
    ops::Mul,
    task::Context,
};

use crate::{
    constraint::Constraints,
    ren::Ren,
    semantics::Chan,
    session_type,
    syntax::{
        Eff, Expr, Id, Label, Mob, Mult, Op1, Op2, Pattern, SEff, SExpr, SId, SLabel, SMult,
        SPattern, SSession, SType, Session, SessionOp, Type, UVarId,
    },
    type_context::{ext, Ctx, CtxCtx, CtxS, JoinOrd},
    util::{
        pretty::pretty_def,
        span::{fake_span, Spanned},
    },
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
    AbsNotMobile(SExpr, SType),
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
    TypeNotValidForNew(SSession),
    SessionTypeOnlySkips(SSession),
}

pub fn infer_type(e: &SExpr) -> Result<(SType, Constraints, Eff), TypeError> {
    let mut checker = TypeChecker { uvar_counter: 0 };
    let (t, cs, eff) = checker.infer(&Ctx::Empty, e)?;
    for (ty1, ty2) in cs.iter() {
        println!("Constraint: {} == {}", pretty_def(ty1), pretty_def(ty2));
    }
    if t.is_ord() {
        return Err(TypeError::MainReturnsOrd(e.clone(), t.clone()));
    }
    Ok((t, cs, eff))
}

struct TypeChecker {
    uvar_counter: usize,
}

impl TypeChecker {
    fn infer(&mut self, ctx: &Ctx, e: &SExpr) -> Result<(SType, Constraints, Eff), TypeError> {
        // println!("Expression: {}, {:?}", pretty_def(&e), e);
        // println!("Ctx: {}", pretty_context_notype(&ctx.simplify()));
        match &e.val {
            Expr::Const(c) => {
                let ty = match c {
                    crate::syntax::Const::Unit => Type::Unit,
                    crate::syntax::Const::Int(_) => Type::Int,
                    crate::syntax::Const::Bool(_) => Type::Bool,
                    crate::syntax::Const::String(_) => Type::String,
                };

                Ok((fake_span(ty), Constraints::empty(), Eff::No))
            }
            Expr::Var(x) => match ctx.lookup_ord_pure(x) {
                Some((ctx, t)) => {
                    assert_unr_ctx(e, &ctx)?;
                    Ok((t.clone(), Constraints::empty(), Eff::No))
                }
                None => Err(TypeError::UndefinedVariable(x.clone())),
            },
            Expr::New(sess_type) => match ctx.is_unr() {
                false => Err(TypeError::LeftOverCtx(e.clone(), ctx.clone())),
                true => {
                    if !is_valid_for_new(&sess_type.val) {
                        return Err(TypeError::TypeNotValidForNew(sess_type.clone()));
                    }
                    let typ = fake_span(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(Spanned::new(
                            Type::Chan(session_type! { Acq; (sess_type.clone(); Wait) }.val),
                            sess_type.span.clone(),
                        )),
                        second: Box::new(Spanned::new(
                            Type::Chan(session_type! { Acq; (sess_type.clone(); Close) }.val),
                            sess_type.span.clone(),
                        )),
                    });
                    Ok((typ, Constraints::empty(), Eff::No))
                }
            },
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
                    let res_ctx = Ctx::Join(
                        Box::new(expr_ctx.clone()),
                        Box::new(body_ctx.clone()),
                        JoinOrd::Ordered,
                    );

                    if !ctx.is_subctx_of(&res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            res_ctx.clone(),
                            ctx.clone(),
                        ));
                    }
                }

                let (expr_ty, expr_constraints, expr_eff) = self.infer(&expr_ctx, expr)?;

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
                    let body_ctx =
                        Ctx::Join(Box::new(var_ctx), Box::new(body_ctx), JoinOrd::Ordered);
                    self.infer(&body_ctx, body)
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
                    let res_ctx = Ctx::Join(
                        Box::new(e1_ctx.clone()),
                        Box::new(e2_ctx.clone()),
                        JoinOrd::Ordered,
                    );

                    // dbg!(&res_ctx);
                    // dbg!(&ctx);
                    if !ctx.is_subctx_of(&res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            res_ctx.clone(),
                            ctx.clone(),
                        ));
                    }
                }

                let (e1_constraints, e1_eff) = self.check(&e1_ctx, e1, &fake_span(Type::Unit))?;
                let (e2_ty, e2_constraints, e2_eff) = self.infer(&e2_ctx, e2)?;

                Ok((
                    e2_ty,
                    e1_constraints.join(e2_constraints),
                    Eff::lub(e1_eff, e2_eff),
                ))
            }
            Expr::Send(ty, val, chan) => {
                // TODO: check if ty is mobile

                let val_ctx = ctx.restrict(&val.free_vars());
                let (val_cs, _) = self.check(&val_ctx, val, ty)?;

                let chan_ctx = ctx.restrict(&chan.free_vars());
                let expected_chan_ty = fake_span(Type::Chan(Session::Op(
                    SessionOp::Send,
                    Box::new(ty.clone()),
                )));
                let (chan_cs, _) = self.check(&chan_ctx, chan, &expected_chan_ty)?;

                // ctx must be a subcontext of unordered join of val_ctx and chan_ctx must
                {
                    let res_ctx = Ctx::Join(
                        Box::new(val_ctx.clone()),
                        Box::new(chan_ctx.clone()),
                        JoinOrd::Unordered,
                    );
                    // dbg!(&res_ctx);
                    // dbg!(&ctx);
                    if !ctx.is_subctx_of(&res_ctx) {
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
                // TODO: Check if ty is mobile

                let chan_ctx = ctx.restrict(&chan.free_vars());
                let expected_chan_ty = fake_span(Type::Chan(Session::Op(
                    SessionOp::Recv,
                    Box::new(ty.clone()),
                )));
                let (chan_cs, _) = self.check(&chan_ctx, chan, &expected_chan_ty)?;

                if !ctx.is_subctx_of(&chan_ctx) {
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

                if !ctx.is_subctx_of(&body_ctx) {
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
                let (body_cs, body_eff) = self.check(&body_ctx, func, &expected_body_ty)?;

                Ok((fake_span(Type::Unit), body_cs, body_eff))
            }
            Expr::BorrowEnd(op, chan) => {
                let chan_ctx = ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let expected_ty = fake_span(Type::Chan(Session::BorrowEnd(*op)));
                let (chan_cs, chan_eff) = self.check(&chan_ctx, chan, &expected_ty)?;

                // TODO: double check whether acquire constant is pure
                Ok((fake_span(Type::Unit), chan_cs, chan_eff))
            }
            Expr::End(op, chan) => {
                let chan_ctx = ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let expected_ty = fake_span(Type::Chan(Session::End(*op)));
                let (chan_cs, chan_eff) = self.check(&chan_ctx, chan, &expected_ty)?;

                // TODO: double check whether acquire constant is pure
                Ok((fake_span(Type::Unit), chan_cs, chan_eff))
            }
            Expr::LSplit(prefix_session, chan) => {
                if prefix_session.is_only_skips() {
                    return Err(TypeError::SessionTypeOnlySkips(prefix_session.clone()));
                }

                let chan_ctx = &ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&chan_ctx) {
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
                let (chan_cs, chan_eff) = self.check(chan_ctx, chan, &expected_chan_ty)?;

                let ret_ty = Type::Prod {
                    mult: fake_span(Mult::Lin),
                    first: Box::new(fake_span(Type::Chan(prefix_session.val.clone()))),
                    second: Box::new(fake_span(Type::Chan(uvar.val))),
                };

                Ok((fake_span(ret_ty), chan_cs, chan_eff))
            }
            Expr::RSplit(prefix_session, chan) => {
                let chan_ctx = &ctx.restrict(&chan.free_vars());
                if !ctx.is_subctx_of(&chan_ctx) {
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
                let (chan_cs, chan_eff) = self.check(chan_ctx, chan, &expected_chan_ty)?;

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

                let (abs_ty, abs_cs, abs_eff) = self.infer(&abs_ctx, abs)?;

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
                    let res_ctx = ext(mult.val, abs_ctx.clone(), arg_ctx.clone());

                    if !ctx.is_subctx_of(&res_ctx) {
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

                let (arg_cs, arg_eff) = self.check(&arg_ctx, arg, &param)?;

                if mult.val == Mult::OrdR && arg_eff == Eff::Yes {
                    return Err(TypeError::MismatchEff(
                        e.clone(),
                        fake_span(arg_eff),
                        fake_span(Eff::No),
                    ));
                }

                Ok((
                    *ret,
                    abs_cs.join(arg_cs),
                    Eff::lub(*eff, Eff::lub(abs_eff, arg_eff)),
                ))
            }
            Expr::Let(var_id, var_expr, body_expr) => {
                if ctx.vars().contains(&var_id.val) {
                    return Err(TypeError::Shadowing(e.clone(), var_id.clone()));
                }

                let var_ctx = ctx.restrict(&var_expr.free_vars());
                let body_ctx = ctx.restrict(&body_expr.free_vars());

                {
                    let res_ctx = Ctx::Join(
                        Box::new(var_ctx.clone()),
                        Box::new(body_ctx.clone()),
                        JoinOrd::Ordered,
                    );

                    if !ctx.is_subctx_of(&res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                let (var_ty, var_cs, var_eff) = self.infer(&var_ctx, var_expr)?;

                let body_ctx = {
                    let binding = Ctx::Bind(var_id.clone(), var_ty);
                    Ctx::Join(Box::new(binding), Box::new(body_ctx), JoinOrd::Ordered)
                };
                let (body_ty, body_cs, body_eff) = self.infer(&body_ctx, body_expr)?;

                Ok((body_ty, var_cs.join(body_cs), Eff::lub(var_eff, body_eff)))
            }
            Expr::LetDecl(id, expected_ty, clause, body) => {
                let decl_ctx = ctx.restrict(&clause.free_vars());
                let body_ctx = ctx.restrict(&body.free_vars());

                {
                    let res_ctx = Ctx::Join(
                        Box::new(decl_ctx.clone()),
                        Box::new(body_ctx.clone()),
                        JoinOrd::Ordered,
                    );

                    if !ctx.is_subctx_of(&res_ctx) {
                        return Err(TypeError::CtxSplitFailed(
                            e.clone(),
                            ctx.clone(),
                            res_ctx.clone(),
                        ));
                    }
                }

                let (clause_cs, clause_eff) = {
                    let clause_expr = fake_span(Expr::Abs(
                        clause.var_id.clone(),
                        Box::new(clause.body.clone()),
                    ));
                    self.check(&decl_ctx, &clause_expr, expected_ty)?
                };

                let (body_ty, body_cs, body_eff) = {
                    let var_ctx = Ctx::Bind(id.clone(), expected_ty.clone());
                    let body_ctx =
                        Ctx::Join(Box::new(var_ctx), Box::new(body_ctx), JoinOrd::Ordered);
                    self.infer(&body_ctx, body)?
                };

                Ok((
                    body_ty,
                    clause_cs.join(body_cs),
                    Eff::lub(clause_eff, body_eff),
                ))
            }
            Expr::CaseSum(expr, cases) => {
                let expr_ctx = ctx.restrict(&expr.free_vars());
                let (expr_ty, expr_cs, expr_eff) = self.infer(&expr_ctx, expr)?;

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

                let case_inferences: Vec<(Spanned<Type>, Constraints, Eff)> = cases
                    .iter()
                    .map(|(label, var_name, case_expr)| {
                        let case_ctx = ctx.restrict(&case_expr.free_vars());

                        let res_ctx = Ctx::Join(
                            Box::new(expr_ctx.clone()),
                            Box::new(case_ctx.clone()),
                            JoinOrd::Ordered,
                        );
                        if !ctx.is_subctx_of(&res_ctx) {
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

                        let case_ctx = Ctx::Join(Box::new(Ctx::Bind(var_name.clone(), case_ty)), Box::new(case_ctx), JoinOrd::Ordered);
                        self.infer(&case_ctx, case_expr)
                    })
                    .collect::<Result<_, _>>()?;

                let expr_ty = case_inferences.first().unwrap().0.clone();
                let expr_cs = case_inferences
                    .iter()
                    .fold(expr_cs, |acc, (_, cs, _)| acc.join(cs.clone()));
                let expr_eff = case_inferences
                    .iter()
                    .fold(expr_eff, |acc, (_, _, eff)| Eff::lub(acc, *eff));

                Ok((expr_ty, expr_cs, expr_eff))
            }
            Expr::Select(label, chan_expr) => {
                let chan_ctx = ctx.restrict(&chan_expr.free_vars());

                if !ctx.is_subctx_of(&chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let (chan_ty, chan_cs, _chan_eff) = self.infer(&chan_ctx, chan_expr)?;

                if let Type::Chan(Session::UVar(_)) = &chan_ty.val {
                    return Err(TypeError::TypeAnnotationMissing(*chan_expr.clone()));
                }

                let Type::Chan(Session::Choice(SessionOp::Send, branches)) = &chan_ty.val else {
                    return Err(TypeError::Mismatch(
                        *chan_expr.clone(),
                        Err("Chan<Choice<Send>>".into()),
                        chan_ty.clone(),
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

                if !ctx.is_subctx_of(&chan_ctx) {
                    return Err(TypeError::CtxSplitFailed(
                        e.clone(),
                        ctx.clone(),
                        chan_ctx.clone(),
                    ));
                }

                let (chan_ty, chan_cs, _chan_eff) = self.infer(&chan_ctx, chan_expr)?;

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
                let (expr_cs, expr_eff) = self.check(&ctx.restrict(&expr.free_vars()), expr, ty)?;

                Ok((ty.clone(), expr_cs, expr_eff))
            }
            Expr::Op1(op1, expr) => {
                let (expr_ty, expr_cs, expr_eff) = self.infer(ctx, expr)?;
                let ty = match (op1, &expr_ty.val) {
                    (Op1::Neg, Type::Int) => Type::Int,
                    (Op1::Neg, _) => {
                        return Err(TypeError::Mismatch(
                            e.clone(),
                            Err(format!("Int")),
                            expr_ty.clone(),
                        ))
                    }
                    (Op1::Not, Type::Bool) => Type::Bool,
                    (Op1::Not, _) => {
                        return Err(TypeError::Mismatch(
                            e.clone(),
                            Err(format!("Bool")),
                            expr_ty.clone(),
                        ))
                    }
                    (Op1::ToStr, _) => Type::String,
                    (Op1::Print, _) => Type::Unit,
                };
                Ok((fake_span(ty), expr_cs, expr_eff))
            }
            Expr::Op2(op2, spanned, spanned1) => todo!(),
            Expr::If(spanned, spanned1, spanned2) => todo!(),
            Expr::Inj(_, _) => Err(TypeError::TypeAnnotationMissing(e.clone())),
            Expr::Pair(_, _) => Err(TypeError::TypeAnnotationMissing(e.clone())),
            Expr::Abs(_, _) => Err(TypeError::TypeAnnotationMissing(e.clone())),
        }
    }

    fn check(
        &mut self,
        ctx: &Ctx,
        e: &SExpr,
        expected_ty: &SType,
    ) -> Result<(Constraints, Eff), TypeError> {
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
                // TODO: Check context mobility

                // For unrestricted lambdas: ensure that context is unrestricted.
                if mult.val == Mult::Unr {
                    if !ctx.is_unr() {
                        return Err(TypeError::CtxNotUnr(e.clone(), ctx.clone()));
                    }
                    if mob.val != Mob::Mobile {
                        return Err(TypeError::AbsNotMobile(e.clone(), expected_ty.clone()));
                    }
                }

                // Assert that `x` is not] in the context.
                if ctx.vars().contains(&id.val) {
                    Err(TypeError::Shadowing(e.clone(), id.clone()))?
                }

                let ctx = ext(**mult, Ctx::Bind(id.clone(), *param.clone()), ctx.clone());
                let (body_cs, body_eff) = self.check(&ctx, body, ret)?;

                if body_eff > eff.val {
                    return Err(TypeError::MismatchEffSub(
                        *body.clone(),
                        fake_span(body_eff),
                        eff.clone(),
                    ));
                }

                Ok((body_cs, Eff::No))
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

                let (first_cs, first_eff) = self.check(&first_ctx, first, &expected_first)?;
                let (second_cs, second_eff) = self.check(&second_ctx, second, &expected_second)?;

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
                    let res_ctx = ext(mult.val, first_ctx, second_ctx);

                    if !ctx.is_subctx_of(&res_ctx) {
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
                    self.check(&ctx.restrict(&expr.free_vars()), expr, actual_ty)?;

                Ok((expr_cs, expr_eff))
            }
            _ => {
                let (inferred_ty, mut cs, eff) = self.infer(ctx, e)?;
                dbg!(pretty_def(e));
                dbg!(pretty_def(&inferred_ty));
                dbg!(pretty_def(expected_ty));

                if !inferred_ty.sem_eq(expected_ty) {
                    println!("adding constraint");
                    cs.add(inferred_ty.val, expected_ty.val.clone());
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

    fn infer_recv_arg(
        &mut self,
        ctx: &Ctx,
        e: &SExpr,
    ) -> Result<(SType, Constraints, Eff), TypeError> {
        self.infer(ctx, e)
    }

    fn infer_select_arg(
        &mut self,
        ctx: &Ctx,
        e: &SExpr,
        l: &SLabel,
    ) -> Result<(SType, Constraints, Eff), TypeError> {
        self.infer(ctx, e)
    }

    fn new_uvar(&mut self) -> SSession {
        let id = self.uvar_counter;
        self.uvar_counter += 1;
        fake_span(Session::UVar(id))
    }
}

fn is_valid_for_new(s: &Session) -> bool {
    match s {
        Session::Skip => true,
        Session::Semi { first, second } => {
            is_valid_for_new(&first.val) && is_valid_for_new(&second.val)
        }
        Session::Op(_, _) => true,
        Session::Choice(_, items) => items.iter().all(|(_, s)| is_valid_for_new(s)),
        Session::Mu(_, body) => is_valid_for_new(body),
        Session::Var(_) => true,
        Session::UVar(_) => false,
        Session::End(_) | Session::BorrowEnd(_) => false,
    }
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
        Session::UVar(_) => todo!(),
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

fn union<T: std::hash::Hash + Eq + Clone>(xss: impl IntoIterator<Item = HashSet<T>>) -> HashSet<T> {
    let mut out = HashSet::new();
    for xs in xss {
        out = out.union(&xs).cloned().collect();
    }
    out
}

fn intersection<T: std::hash::Hash + Eq + Clone>(
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

fn rename_vars(r: &Ren, xs: &HashSet<Id>) -> HashSet<Id> {
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

fn indented(n: usize, s: impl AsRef<str>) -> String {
    let mut out = String::new();
    for l in s.as_ref().lines() {
        for _ in 0..n {
            out += " ";
        }
        out += l;
    }
    out
}

fn split_arrow_type(mut t: &SType) -> (Vec<(SType, SMult)>, SType, Option<SEff>) {
    let mut args = vec![];
    let mut eff = None;
    loop {
        match &t.val {
            Type::Arr {
                mob,
                mult: m,
                eff: e,
                param: t1,
                ret: t2,
            } => {
                todo!();
                t = t2;
                eff = Some(e.clone());
                args.push((t1.as_ref().clone(), m.clone()));
            }
            _ => return (args, t.clone(), eff),
        }
    }
}

fn assert_unr_ctx(e: &SExpr, ctx: &Ctx) -> Result<(), TypeError> {
    if ctx.is_unr() {
        Ok(())
    } else {
        Err(TypeError::LeftOverCtx(e.clone(), ctx.clone()))
    }
}
