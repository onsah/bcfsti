use std::collections::HashSet;

use crate::{
    syntax::{
        Id, Kind, Qualification, Quantification, SId, SQualification, SSession, SType, Session,
        Type,
    },
    type_alias::AliasEnv,
    type_checker::TypeError,
    type_context::TypeCtx,
};

pub(crate) fn infer(ty_ctx: &TypeCtx, alias_env: &AliasEnv, ty: &SType) -> Result<Kind, TypeError> {
    let state = KindCheckState::from(ty_ctx.clone(), alias_env);
    state.infer(ty)
}

pub(crate) fn check(
    ty_ctx: &TypeCtx,
    alias_env: &AliasEnv,
    ty: &SType,
    expected: Kind,
) -> Result<(), TypeError> {
    let state = KindCheckState::from(ty_ctx.clone(), alias_env);
    state.check(ty, expected)
}

pub(crate) fn check_session(
    ty_ctx: &TypeCtx,
    alias_env: &AliasEnv,
    session: &SSession,
) -> Result<(), TypeError> {
    let state = KindCheckState::from(ty_ctx.clone(), alias_env);
    state.check_session_well_formed(session)
}

pub(crate) fn check_qualifications_well_formed<'a>(
    ty_ctx: &TypeCtx,
    alias_env: &AliasEnv,
    qualifications: impl Iterator<Item = &'a SQualification>,
) -> Result<(), TypeError> {
    let state = KindCheckState::from(ty_ctx.clone(), alias_env);
    state.check_qualifications_well_formed(qualifications)
}

#[derive(Clone)]
struct KindCheckState<'a> {
    ty_ctx: TypeCtx,
    alias_env: &'a AliasEnv,
    rvars: HashSet<Id>,
}

impl KindCheckState<'_> {
    fn from<'a>(ty_ctx: TypeCtx, alias_env: &'a AliasEnv) -> KindCheckState<'a> {
        KindCheckState {
            ty_ctx,
            alias_env,
            rvars: HashSet::new(),
        }
    }

    fn infer(&self, ty: &SType) -> Result<Kind, TypeError> {
        match &ty.val {
            Type::Unit | Type::Int | Type::Bool | Type::String => Ok(Kind::Type),
            Type::Skip
            | Type::Semi { .. }
            | Type::End(_)
            | Type::BorrowEnd(_)
            | Type::Op(_, _)
            | Type::Choice(_, _)
            | Type::Mu(_, _)
            | Type::Var(_)
            | Type::UVar(_) => {
                self.check_session_well_formed(ty)?;
                Ok(Kind::Session)
            }
            Type::Variant(variants) => {
                for (_, ty) in variants {
                    self.infer(ty)?;
                }
                Ok(Kind::Type)
            }
            Type::Prod { first, second, .. } => {
                self.infer(first)?;
                self.infer(second)?;
                Ok(Kind::Type)
            }
            Type::Arr { param, ret, .. } => {
                self.infer(param)?;
                self.infer(ret)?;
                Ok(Kind::Type)
            }
            Type::Abstraction {
                quantification, ty, ..
            } => {
                let new_ctx = self.clone().add_quantification(quantification.val.clone());
                new_ctx.check_qualifications_well_formed(quantification.qualifications.iter())?;
                new_ctx.check(ty, Kind::Type)?;
                Ok(Kind::Type)
            }
            Type::PVar { id, .. } => match self.ty_ctx.vars.get(id) {
                Some(kind) => Ok(kind.clone()),
                None => Err(TypeError::UndefinedPVar(ty.clone(), id.clone())),
            },
        }
    }

    fn check(&self, ty: &SType, expected: Kind) -> Result<(), TypeError> {
        let actual = self.infer(ty)?;
        if actual.is_subkind_of(&expected) {
            Ok(())
        } else {
            Err(TypeError::KindMismatch(
                ty.clone(),
                expected,
                self.ty_ctx.clone(),
            ))
        }
    }

    // TODO: Return the kind immediately, instead of check form, work like inference
    fn check_session_well_formed(&self, session: &SSession) -> Result<(), TypeError> {
        match &session.val {
            Session::Skip | Session::End(_) | Session::BorrowEnd(_) => Ok(()),
            Session::Op(_, ty) => self.check(&ty, Kind::Type),
            Session::Choice(_, branches) => {
                for (_, branch) in branches {
                    self.check_session_well_formed(branch)?;
                }
                Ok(())
            }
            Session::Semi { first, second } => {
                self.check_session_well_formed(first)?;
                self.check_session_well_formed(second)
            }
            Session::Mu(var, body) => {
                self.check_contractive(body, var)?;
                // TODO: Optimize by using functional data structures
                let new_ctx: KindCheckState = self.clone().add_rvar(var.val.clone());
                new_ctx.check_session_well_formed(body)
            }
            Session::PVar { id, .. } => match self.ty_ctx.vars.get(id) {
                Some(kind) => {
                    if kind == &Kind::Session {
                        Ok(())
                    } else {
                        Err(TypeError::KindMismatch(
                            session.clone(),
                            Kind::Session,
                            self.ty_ctx.clone(),
                        ))
                    }
                }
                None => Err(TypeError::UndefinedPVar(session.clone(), id.clone())),
            },
            Session::Var(id) => {
                if !self.rvars.contains(&id.val) && !self.alias_env.contains_key(&id.val) {
                    Err(TypeError::WfSessionNotClosed(session.clone(), id.clone()))
                } else {
                    Ok(())
                }
            }
            // We assume unifications variables are well formed
            // therefore we must check well formedness after unification
            // variables are solved.
            Session::UVar(_) => Ok(()),
            _ => unreachable!("Regular type in session well-formed check"),
        }
    }

    fn check_contractive(&self, session: &SSession, on: &SId) -> Result<(), TypeError> {
        match &session.val {
            Session::Skip
            | Session::Op(_, _)
            | Session::Choice(_, _)
            | Session::End(_)
            | Session::BorrowEnd(_) => Ok(()),
            Session::Semi { first, second } => {
                if !first.is_only_skips() {
                    self.check_contractive(first, on)
                } else {
                    self.check_contractive(second, on)
                }
            }
            Session::Mu(_, body) => self.check_contractive(body, on),
            Session::Var(id) => {
                if &on.val == &id.val {
                    Err(TypeError::WfNonContractive(session.clone(), on.clone()))
                } else {
                    Ok(())
                }
            }
            Session::PVar { .. } => Err(TypeError::WfNonContractive(session.clone(), on.clone())),
            Session::UVar(_) => unreachable!("Should be called after unification!"),
            _ => unreachable!("Regular type in contractivity check"),
        }
    }

    fn check_qualifications_well_formed<'a>(
        &self,
        qualifications: impl Iterator<Item = &'a SQualification>,
    ) -> Result<(), TypeError> {
        for qualification in qualifications {
            match &qualification.val {
                // QF-Unr, QF-Mobile: T : KVal
                Qualification::Unr(ty) | Qualification::Mobile(ty) => self.check(ty, Kind::Type)?,
                // QF-Bounded, QF-New, QF-Dualable, QF-NonSkip: S : KSess
                Qualification::Bounded(s)
                | Qualification::New(s)
                | Qualification::Dualable(s)
                | Qualification::NonSkip(s) => self.check(&s.0, Kind::Session)?,
            }
        }
        Ok(())
    }

    fn add_quantification(
        self,
        Quantification {
            bindings,
            qualifications,
        }: Quantification,
    ) -> Self {
        Self {
            // TODO: Implement extend that reuses the existing context instead of cloning everything
            ty_ctx: self.ty_ctx.extend(
                Quantification::bindings(bindings.into_iter()),
                qualifications.into_iter().map(|q| q.val),
            ),
            alias_env: self.alias_env,
            rvars: self.rvars,
        }
    }

    fn add_rvar(mut self, new_id: Id) -> Self {
        self.rvars.insert(new_id);
        self
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        session_type,
        syntax::{PVarId, QuantificationType, SSemType, SessionOp, Type},
        util::span::{Spanned, fake_span},
    };

    use super::*;

    fn ctx(vars: &[(PVarId, Kind)]) -> TypeCtx {
        TypeCtx {
            vars: vars.iter().cloned().collect(),
            qualifications: vec![],
        }
    }

    fn pvar_chan(id: PVarId) -> Type {
        Type::PVar { id, dual: false }
    }

    fn variant(case: &str, ty: Type) -> Type {
        Type::Variant(vec![(fake_span(case.to_string()), fake_span(ty))])
    }

    #[test]
    fn empty_is_well_formed() {
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new())
                .check_qualifications_well_formed([].iter()),
            Ok(())
        );
    }

    #[test]
    fn unr_and_mobile_of_value_type() {
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(Type::Unit.into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(Type::Int.into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Mobile(Type::Bool.into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(Type::Skip.into()))].iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn session_qualifications_of_closed_session() {
        let s = Session::End(SessionOp::Send);
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Bounded(s.clone().into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::New(s.clone().into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Dualable(s.clone().into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::NonSkip(s.into()))].iter()
            ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Bounded(Session::Skip.into()))].iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn conjunction_of_well_formed() {
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [
                    fake_span(Qualification::Unr(Type::Unit.into())),
                    fake_span(Qualification::Mobile(Type::Int.into())),
                    fake_span(Qualification::Bounded(Session::Skip.into())),
                ]
                .iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn conjunction_with_one_ill_formed_is_not_well_formed() {
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [
                    fake_span(Qualification::Unr(Type::Unit.into())),
                    fake_span(Qualification::Bounded(Session::PVar {
                        id: "a".to_string(),
                        dual: false
                    }.into())),
                ]
                .iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "a"
        ));
    }

    #[test]
    fn free_pvar_in_value_type_not_well_formed() {
        let q = fake_span(Qualification::Unr(pvar_chan("a".to_string()).into()));
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed([q].iter()),
            Err(TypeError::UndefinedPVar(_, id)) if id == "a"
        ));
    }

    #[test]
    fn free_pvar_in_session_not_well_formed() {
        let q = fake_span(Qualification::Bounded(
            Session::PVar {
                id: "a".to_string(),
                dual: false,
            }
            .into(),
        ));
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed([q].iter()),
            Err(TypeError::UndefinedPVar(_, id)) if id == "a"
        ));
    }

    #[test]
    fn in_scope_session_pvar_is_well_formed() {
        assert_eq!(
            KindCheckState::from(ctx(&[("a".to_string(), Kind::Session)]), &HashMap::new())
                .check_qualifications_well_formed(
                    [fake_span(Qualification::Bounded(
                        Session::PVar {
                            id: "a".to_string(),
                            dual: false
                        }
                        .into()
                    ))]
                    .iter()
                ),
            Ok(())
        );
        assert_eq!(
            KindCheckState::from(ctx(&[("a".to_string(), Kind::Session)]), &HashMap::new())
                .check_qualifications_well_formed(
                    [fake_span(Qualification::Unr(
                        pvar_chan("a".to_string()).into()
                    ))]
                    .iter()
                ),
            Ok(())
        );
    }

    #[test]
    fn pvar_of_wrong_kind_not_well_formed() {
        let result = KindCheckState::from(ctx(&[("a".to_string(), Kind::Type)]), &HashMap::new())
            .check_qualifications_well_formed(
                [fake_span(Qualification::Bounded(
                    Session::PVar {
                        id: "a".to_string(),
                        dual: false,
                    }
                    .into(),
                ))]
                .iter(),
            );
        assert!(matches!(
            result,
            Err(TypeError::KindMismatch(Spanned { val: Type::PVar { id, .. }, .. }, Kind::Session, _)) if id == "a"
        ));
    }

    #[test]
    fn nested_ill_kinded_session_not_well_formed() {
        let s = Session::Semi {
            first: Box::new(fake_span(Session::Skip)),
            second: Box::new(fake_span(Session::PVar {
                id: "a".to_string(),
                dual: false,
            })),
        };
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Bounded(s.into()))].iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "a"
        ));
    }

    #[test]
    fn nested_ill_kinded_value_type_not_well_formed() {
        let ty = variant("a", pvar_chan("b".to_string()));
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(ty.into()))].iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "b"
        ));
    }

    #[test]
    fn recursive_session_is_well_formed() {
        let s = Session::Mu(
            fake_span("X".to_string()),
            Box::new(session_type! { !String; X }),
        );
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Bounded(s.into()))].iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn mobile_with_free_pvar_not_well_formed() {
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Mobile(pvar_chan(
                    "5".to_string()
                ).into()))]
                .iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "5"
        ));
    }

    #[test]
    fn new_dualable_nonskip_with_free_pvar_not_well_formed() {
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::New(Session::PVar {
                    id: "4".to_string(),
                    dual: false
                }.into()))]
                .iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "4"
        ));
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Dualable(Session::PVar {
                    id: "4".to_string(),
                    dual: false
                }.into()))]
                .iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "4"
        ));
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::NonSkip(Session::PVar {
                    id: "4".to_string(),
                    dual: false
                }.into()))]
                .iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "4"
        ));
    }

    #[test]
    fn dualable_op_with_ill_kinded_payload_not_well_formed() {
        let s = Session::Op(
            SessionOp::Send,
            Box::new(fake_span(pvar_chan("9".to_string()))),
        );
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Dualable(s.into()))].iter()
            ),
            Err(TypeError::UndefinedPVar(_, id)) if id == "9"
        ));
    }

    #[test]
    fn non_contrative_mu_not_well_formed() {
        let s = Session::Mu(
            fake_span("X".to_string()),
            Box::new(fake_span(Session::Var(fake_span("X".to_string())))),
        );
        let result = KindCheckState::from(ctx(&[]), &HashMap::new())
            .check_qualifications_well_formed([fake_span(Qualification::Bounded(s.into()))].iter());
        assert!(matches!(
            result,
            Err(TypeError::WfNonContractive(_, Spanned { val, .. })) if val == "X"
        ));
    }

    #[test]
    fn bounded_mu_with_free_pvar_not_well_formed() {
        let s = Session::Mu(
            fake_span("X".to_string()),
            Box::new(fake_span(Session::Semi {
                first: Box::new(fake_span(Session::Skip)),
                second: Box::new(fake_span(Session::PVar {
                    id: "9".to_string(),
                    dual: false,
                })),
            })),
        );
        let result = KindCheckState::from(ctx(&[]), &HashMap::new())
            .check_qualifications_well_formed([fake_span(Qualification::Bounded(s.into()))].iter());
        assert!(matches!(result, Err(TypeError::WfNonContractive(_, _))));
    }

    #[test]
    fn forall_with_well_formed_body() {
        let ty = Type::Abstraction {
            typ: QuantificationType::Universal,
            quantification: fake_span(Quantification {
                bindings: vec![(fake_span("a".to_string()), fake_span(Kind::Session))],
                qualifications: vec![],
            }),
            ty: Box::new(fake_span(Type::Unit)),
        };
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(ty.into()))].iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn forall_with_free_pvar_in_body_not_well_formed() {
        let ty = Type::Abstraction {
            typ: QuantificationType::Universal,
            quantification: fake_span(Quantification {
                bindings: vec![(fake_span("a".to_string()), fake_span(Kind::Session))],
                qualifications: vec![],
            }),
            ty: Box::new(fake_span(pvar_chan("b".to_string()))),
        };
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(ty.into()))].iter()
            ),
            Err(TypeError::UndefinedPVar(_, _))
        ));
    }

    #[test]
    fn forall_using_bound_pvar_in_body_is_well_formed() {
        let ty = Type::Abstraction {
            typ: QuantificationType::Universal,
            quantification: fake_span(Quantification {
                bindings: vec![(fake_span("a".to_string()), fake_span(Kind::Session))],
                qualifications: vec![],
            }),
            ty: Box::new(fake_span(pvar_chan("a".to_string()))),
        };
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Unr(ty.into()))].iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn choice_with_well_formed_branches_is_well_formed() {
        let s = session_type! { +{ a: !Int, b: !Bool } };
        assert_eq!(
            KindCheckState::from(ctx(&[]), &HashMap::new()).check_qualifications_well_formed(
                [fake_span(Qualification::Bounded(SSemType(s)))].iter()
            ),
            Ok(())
        );
    }

    #[test]
    fn choice_with_free_pvar_in_payload_not_well_formed() {
        let s =
            session_type! { &{ a: fake_span(Session::PVar { id: "b".to_string(), dual: false }) } };
        assert!(matches!(
            KindCheckState::from(ctx(&[]), &HashMap::new())
                .check_qualifications_well_formed([fake_span(Qualification::Bounded(SSemType(s)))].iter()),
            Err(TypeError::UndefinedPVar(_, id)) if id == "b"
        ));
    }

    #[test]
    fn session_kind_pvar_well_formed() {
        let session = Session::PVar {
            id: "a".to_string(),
            dual: false,
        };
        assert_eq!(
            KindCheckState::from(ctx(&[("a".to_string(), Kind::Session)]), &HashMap::new())
                .check_qualifications_well_formed(
                    [fake_span(Qualification::Dualable(session.into()))].iter()
                ),
            Ok(())
        );
    }

    #[test]
    fn type_kind_pvar_not_well_formed() {
        let session = Session::PVar {
            id: "a".to_string(),
            dual: false,
        };
        let result = KindCheckState::from(ctx(&[("a".to_string(), Kind::Type)]), &HashMap::new())
            .check_qualifications_well_formed(
                [fake_span(Qualification::Dualable(session.into()))].iter(),
            );
        assert!(matches!(
            result,
                Err(TypeError::KindMismatch(
                    Spanned {
                        val: Type::PVar { id, .. },
                        ..
                    },
                    Kind::Session,
                    _
                )) if id == "a"
        ));
    }
}
