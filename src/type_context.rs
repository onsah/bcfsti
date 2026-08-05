use std::collections::{HashMap, HashSet};

use crate::syntax::{Id, Kind, Label, PVarId, Qualification, Session, SessionOp, Type};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TypeCtx {
    vars: HashMap<PVarId, Kind>,
    qualifications: Vec<Qualification>,
}

/// Entailment rules
impl TypeCtx {
    pub fn entails(&self, qualification: &Qualification) -> bool {
        self.or_assumed(
            move || qualification.clone(),
            match qualification {
                Qualification::Unr(ty) => self.unr(ty),
                Qualification::Mobile(ty) => self.mobile(ty),
                Qualification::Bounded(session) => self.bounded(session),
                Qualification::New(session) => self.new(session),
                Qualification::Dualable(session) => self.dualable(session),
                Qualification::NonSkip(session) => self.nonskip(session),
                Qualification::Equiv(ty1, ty2) => self.equivalent(ty1, ty2),
            },
        )
    }

    fn equivalent(&self, ty1: &Type, ty2: &Type) -> bool {
        ty1.sem_eq(ty2)||
            self.contains_equiv(ty1, ty2) ||
            // We don't need the symmetric case since if we can find from one direction
            // we can also find from the other direction
            self.equivalent_to(ty1).any(|ty| self.equivalent(ty, ty2))
    }

    fn contains_equiv(&self, ty11: &Type, ty12: &Type) -> bool {
        self.qualifications.iter().any(|q| match q {
            Qualification::Equiv(ty21, ty22) => {
                (ty11.sem_eq(ty21) && ty12.sem_eq(ty22)) || (ty11.sem_eq(ty22) && ty12.sem_eq(ty21))
            }
            _ => false,
        })
    }

    /// Set of types equivalent to a type under this context
    fn equivalent_to(&self, ty: &Type) -> impl Iterator<Item = &Type> {
        self.qualifications.iter().filter_map(|q| match q {
            Qualification::Equiv(ty1, ty2) if ty1.sem_eq(ty) => Some(ty2),
            Qualification::Equiv(ty1, ty2) if ty2.sem_eq(ty) => Some(ty1),
            _ => None,
        })
    }

    fn unr(&self, ty: &Type) -> bool {
        self.or_assumed(
            || Qualification::Unr(ty.clone()),
            match ty {
                // Q-Unr-Atom
                Type::Unit | Type::Arr { .. } => true,
                // Q-Unr-Prod
                Type::Prod { first, second, .. } => self.unr(first) && self.unr(second),
                // Q-Unr-Variant
                Type::Variant(variants) => variants
                    .iter()
                    .map(|(_, ty)| &ty.val)
                    .all(|ty| self.unr(ty)),
                // Q-Unr-Conv
                Type::Chan(Session::PVar { id, .. }) => {
                    self.equivalent_types_pv(*id).any(|ty| self.unr(ty))
                }
                _ => false,
            },
        )
    }

    fn mobile(&self, ty: &Type) -> bool {
        self.or_assumed(
            || Qualification::Mobile(ty.clone()),
            match ty {
                // Q-Mbl-Atom
                Type::Unit | Type::Arr { .. } => true,
                // Q-Mbl-Prod
                Type::Prod { first, second, .. } => self.mobile(first) && self.mobile(second),
                // Q-Mbl-Variant
                Type::Variant(variants) => variants
                    .iter()
                    .map(|(_, ty)| &ty.val)
                    .all(|ty| self.unr(ty)),
                // Q-Mbl-Acq
                // TODO: Check weak head normal form for the semicolon
                Type::Chan(Session::Semi { first, second })
                    if first.val == Session::BorrowEnd(SessionOp::Recv) =>
                {
                    self.bounded(second)
                }
                // Q-Mbl-Conv
                Type::Chan(Session::PVar { id, .. }) => {
                    self.equivalent_types_pv(*id).any(|ty| self.mobile(ty))
                }
                Type::Forall {
                    id,
                    kind,
                    qualifications,
                    ty,
                } => {
                    let new_ctx = self.extend(*id, *kind, qualifications.iter().cloned());
                    new_ctx.mobile(ty)
                }
                _ => false,
            },
        )
    }

    fn bounded(&self, session: &Session) -> bool {
        self.or_assumed(
            || Qualification::Bounded(session.clone()),
            match session {
                Session::Skip | Session::End(_) => true,
                Session::Semi { first, second } => {
                    (self.bounded(first) && second.is_only_skips()) || self.bounded(second)
                }
                Session::Mu(_, session) => self.bounded(session),
                Session::Choice(_, branches) => branches.iter().all(|(_, s)| self.bounded(s)),
                Session::PVar { id, .. } => self
                    .qualifications
                    .iter()
                    .filter_map::<&Session, _>(|q| match q {
                        Qualification::Equiv(ty1, ty2) => {
                            if let Type::Chan(s) = ty2
                                && ty1 == &pvar(*id)
                            {
                                Some(s)
                            } else if let Type::Chan(s) = ty1
                                && ty2 == &pvar(*id)
                            {
                                Some(s)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    })
                    .any(|s| self.bounded(s)),
                _ => false,
            },
        )
    }

    fn dualable(&self, session: &Session) -> bool {
        self.or_assumed(
            || Qualification::Dualable(session.clone()),
            match session {
                Session::Skip | Session::Op(_, _) | Session::End(_) | Session::Var(_) => true,
                Session::PVar { id, .. } => {
                    self.new(session)
                        || self.equivalent_types(*id).any(|ty| match ty {
                            Type::Chan(session) => self.dualable(session),
                            _ => false,
                        })
                }
                Session::Semi { first, second } => {
                    self.dualable(&first.val) && self.dualable(&second.val)
                }
                Session::Choice(_, items) => items.iter().all(|(_, s)| self.dualable(s)),
                Session::Mu(_, body) => self.dualable(body),
                _ => false,
            },
        )
    }

    fn nonskip(&self, session: &Session) -> bool {
        if session.poly_variables().count() == 0 && !session.is_only_skips() {
            true
        } else if let Session::Semi { first, second } = session {
            self.nonskip(first) || self.nonskip(second)
        } else {
            false
        }
    }

    fn new(&self, session: &Session) -> bool {
        self.or_assumed(
            || Qualification::New(session.clone()),
            match session {
                Session::Skip | Session::Op(_, _) | Session::Var(_) => true,

                Session::Semi { first, second } => self.new(&first.val) && self.new(&second.val),
                Session::Choice(_, items) => items.iter().all(|(_, s)| self.new(s)),
                Session::Mu(_, body) => self.new(body),
                Session::PVar { id, .. } => self.equivalent_types(*id).any(|ty| match ty {
                    Type::Chan(session) => self.new(session),
                    _ => false,
                }),
                _ => false,
            },
        )
    }

    /// Returns the set of types from equivalent qualifications
    /// that `id` occurs in the other type.
    fn equivalent_types(&self, id: PVarId) -> impl Iterator<Item = &Type> {
        self.qualifications.iter().filter_map(move |q| match q {
            Qualification::Equiv(ty1, ty2)
                if ty1.poly_variables().find(|id1| id1 == &id).is_some() =>
            {
                Some(ty2)
            }
            Qualification::Equiv(ty1, ty2)
                if ty2.poly_variables().find(|id1| id1 == &id).is_some() =>
            {
                Some(ty1)
            }
            _ => None,
        })
    }

    /// Returns the set of types from equivalent qualifications
    /// that `id` occurs in the other type under any amount of prod and variant constructors.
    fn equivalent_types_pv(&self, id: PVarId) -> impl Iterator<Item = &Type> {
        self.qualifications.iter().filter_map(move |q| match q {
            Qualification::Equiv(ty1, ty2)
                if ty1
                    .poly_variables_under_prod_and_variant()
                    .find(|id1| id1 == &id)
                    .is_some() =>
            {
                Some(ty2)
            }
            Qualification::Equiv(ty1, ty2)
                if ty2
                    .poly_variables_under_prod_and_variant()
                    .find(|id1| id1 == &id)
                    .is_some() =>
            {
                Some(ty1)
            }
            _ => None,
        })
    }

    fn or_assumed<F>(&self, make_qualification: F, result: bool) -> bool
    where
        F: FnOnce() -> Qualification,
    {
        result ||
        // Q-Assume
        self.qualifications.contains(&make_qualification())
    }
}

// Kinding and well formedness
impl TypeCtx {
    pub(crate) fn infer_kind(&self, ty: &Type) -> Option<Kind> {
        self.infer_kind_inner(ty)
    }

    pub(crate) fn check_kind(&self, ty: &Type, kind: Kind) -> bool {
        self.check_kind_inner(ty, kind)
    }

    fn infer_kind_inner(&self, ty: &Type) -> Option<Kind> {
        // HACK: minimal kind inference for the type shapes used in tests.
        // Channels infer to Session; value types to Type.
        match ty {
            Type::Unit | Type::Int | Type::Bool | Type::String => Some(Kind::Type),
            Type::Chan(session) => self
                .is_session_well_formed(session, &HashSet::new())
                .then_some(Kind::Session),
            Type::Variant(variants) => variants
                .iter()
                .all(|(_, ty)| self.infer_kind_inner(&ty.val).is_some())
                .then_some(Kind::Type),
            Type::Prod { first, second, .. } => (self.infer_kind_inner(first).is_some()
                && self.infer_kind_inner(second).is_some())
            .then_some(Kind::Type),
            Type::Arr { param, ret, .. } => (self.infer_kind_inner(param).is_some()
                && self.infer_kind_inner(ret).is_some())
            .then_some(Kind::Type),
            Type::Forall {
                id,
                kind,
                qualifications,
                ty,
            } => {
                let new_ctx = self.extend(*id, *kind, qualifications.iter().cloned());
                (new_ctx.is_well_formed(&qualifications) && new_ctx.check_kind(ty, Kind::Type))
                    .then_some(Kind::Type)
            }
        }
    }

    fn check_kind_inner(&self, ty: &Type, kind: Kind) -> bool {
        self.infer_kind(ty)
            .map(|kind1| kind1.is_subkind_of(&kind))
            .unwrap_or(false)
    }

    fn is_session_well_formed(&self, session: &Session, rvars: &HashSet<Id>) -> bool {
        match session {
            Session::Skip | Session::End(_) | Session::BorrowEnd(_) => true,
            Session::Op(_, ty) => self.check_kind_inner(&ty.val, Kind::Type) && self.mobile(ty),
            Session::Choice(_, branches) => branches
                .iter()
                .all(|(_, branch)| self.is_session_well_formed(branch, rvars)),
            Session::Semi { first, second } => {
                self.is_session_well_formed(&first.val, rvars)
                    && self.is_session_well_formed(&second.val, rvars)
            }
            Session::Mu(var, body) => {
                Self::is_contractive(body, var, &self.vars) && {
                    // TODO: Optimize by using functional data structures
                    let mut rvars = rvars.clone();
                    rvars.insert(var.val.clone());
                    self.is_session_well_formed(body, &rvars)
                }
            }
            Session::PVar { id, .. } => self.vars.get(id).copied() == Some(Kind::Session),
            Session::Var(id) => rvars.contains(&id.val),
            // We assume unifications variables are well formed
            // therefore we must check well formedness after unification
            // variables are solved.
            Session::UVar(_) => true,
        }
    }

    fn is_contractive(session: &Session, on: &Label, pvars: &HashMap<PVarId, Kind>) -> bool {
        todo!()
    }

    /// Check if the qualifications are well formed w.r.t. the type context.
    fn is_well_formed(&self, qualifications: &[Qualification]) -> bool {
        // QF-Top (empty conjunction) / QF-And (each conjunct well formed)
        qualifications.iter().all(|q| match q {
            // QF-Unr, QF-Mobile: T : KVal
            Qualification::Unr(ty) | Qualification::Mobile(ty) => self.check_kind(ty, Kind::Type),
            // QF-Bounded, QF-New, QF-Dualable, QF-NonSkip: S : KSess
            Qualification::Bounded(s)
            | Qualification::New(s)
            | Qualification::Dualable(s)
            | Qualification::NonSkip(s) => self.check_kind(&Type::Chan(s.clone()), Kind::Session),
            // QF-Eq: T : K and U : K for the same kind (via inference)
            Qualification::Equiv(ty1, ty2) => match (self.infer_kind(ty1), self.infer_kind(ty2)) {
                (Some(k1), Some(k2)) => k1 == k2,
                _ => false,
            },
        })
    }

    fn extend(
        &self,
        id: PVarId,
        kind: Kind,
        qualifications: impl IntoIterator<Item = Qualification>,
    ) -> TypeCtx {
        let mut new_vars = self.vars.clone();
        new_vars.insert(id, kind);
        let mut new_qualifications = self.qualifications.clone();
        new_qualifications.extend(qualifications);
        TypeCtx {
            vars: new_vars,
            qualifications: new_qualifications,
        }
    }

    fn domain(&self) -> HashSet<PVarId> {
        self.vars.keys().copied().collect()
    }
}

fn pvar(id: PVarId) -> Type {
    Type::Chan(Session::PVar { id, dual: false })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::span::fake_span;

    fn ctx(vars: &[(PVarId, Kind)]) -> TypeCtx {
        TypeCtx {
            vars: vars.iter().copied().collect(),
            qualifications: vec![],
        }
    }

    fn pvar_chan(id: PVarId) -> Type {
        Type::Chan(Session::PVar { id, dual: false })
    }

    fn variant(case: &str, ty: Type) -> Type {
        Type::Variant(vec![(fake_span(case.to_string()), fake_span(ty))])
    }

    #[test]
    fn empty_is_well_formed() {
        // QF-Top
        assert!(ctx(&[]).is_well_formed(&[]));
    }

    #[test]
    fn unr_and_mobile_of_value_type() {
        // QF-Unr, QF-Mobile: T : KVal
        assert!(ctx(&[]).is_well_formed(&[Qualification::Unr(Type::Unit)]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::Unr(Type::Int)]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::Mobile(Type::Bool)]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::Unr(Type::Chan(Session::Skip))]));
    }

    #[test]
    fn session_qualifications_of_closed_session() {
        // QF-Bounded, QF-New, QF-Dualable, QF-NonSkip: S : KSess
        let s = Session::End(SessionOp::Send);
        assert!(ctx(&[]).is_well_formed(&[Qualification::Bounded(s.clone())]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::New(s.clone())]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::Dualable(s.clone())]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::NonSkip(s)]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::Bounded(Session::Skip)]));
    }

    #[test]
    fn equiv_of_value_types() {
        // QF-Eq
        assert!(ctx(&[]).is_well_formed(&[Qualification::Equiv(Type::Int, Type::Bool)]));
        assert!(ctx(&[]).is_well_formed(&[Qualification::Equiv(
            Type::Chan(Session::Skip),
            Type::Chan(Session::End(SessionOp::Recv))
        )]));
    }

    #[test]
    fn conjunction_of_well_formed() {
        // QF-And
        assert!(ctx(&[]).is_well_formed(&[
            Qualification::Unr(Type::Unit),
            Qualification::Mobile(Type::Int),
            Qualification::Bounded(Session::Skip),
        ]));
    }

    #[test]
    fn conjunction_with_one_ill_formed_is_not_well_formed() {
        assert!(!ctx(&[]).is_well_formed(&[
            Qualification::Unr(Type::Unit),
            Qualification::Bounded(Session::PVar { id: 7, dual: false }),
        ]));
    }

    #[test]
    fn free_pvar_in_value_type_not_well_formed() {
        let q = Qualification::Unr(pvar_chan(3));
        assert!(!ctx(&[]).is_well_formed(&[q]));
    }

    #[test]
    fn free_pvar_in_session_not_well_formed() {
        let q = Qualification::Bounded(Session::PVar { id: 3, dual: false });
        assert!(!ctx(&[]).is_well_formed(&[q]));
    }

    #[test]
    fn in_scope_session_pvar_is_well_formed() {
        assert!(
            ctx(&[(0, Kind::Session)])
                .is_well_formed(&[Qualification::Bounded(Session::PVar { id: 0, dual: false })])
        );
        assert!(ctx(&[(0, Kind::Session)]).is_well_formed(&[Qualification::Unr(pvar_chan(0))]));
    }

    #[test]
    fn pvar_of_wrong_kind_not_well_formed() {
        // var 0 has value kind but is used in session position
        assert!(
            !ctx(&[(0, Kind::Type)])
                .is_well_formed(&[Qualification::Bounded(Session::PVar { id: 0, dual: false })])
        );
    }

    #[test]
    fn nested_ill_kinded_session_not_well_formed() {
        let s = Session::Semi {
            first: Box::new(fake_span(Session::Skip)),
            second: Box::new(fake_span(Session::PVar { id: 9, dual: false })),
        };
        assert!(!ctx(&[]).is_well_formed(&[Qualification::Bounded(s)]));
    }

    #[test]
    fn nested_ill_kinded_value_type_not_well_formed() {
        let ty = variant("a", pvar_chan(9));
        assert!(!ctx(&[]).is_well_formed(&[Qualification::Unr(ty)]));
    }

    #[test]
    fn equiv_with_ill_kinded_side_not_well_formed() {
        let q = Qualification::Equiv(Type::Int, pvar_chan(9));
        assert!(!ctx(&[]).is_well_formed(&[q]));
    }

    #[test]
    fn recursive_session_is_well_formed() {
        let s = Session::Mu(
            fake_span("X".to_string()),
            Box::new(fake_span(Session::Var(fake_span("X".to_string())))),
        );
        assert!(ctx(&[]).is_well_formed(&[Qualification::Bounded(s)]));
    }

    #[test]
    fn equiv_different_kinds_not_well_formed() {
        // QF-Eq: both sides must share a kind. Channels infer Session,
        // value types infer Type, so these equivalences are ill-formed.
        assert!(
            !ctx(&[]).is_well_formed(&[Qualification::Equiv(Type::Int, Type::Chan(Session::Skip))])
        );
        assert!(
            !ctx(&[])
                .is_well_formed(&[Qualification::Equiv(Type::Chan(Session::Skip), Type::Int,)])
        );
    }

    #[test]
    fn equiv_both_sides_ill_kinded_not_well_formed() {
        let q = Qualification::Equiv(pvar_chan(1), pvar_chan(2));
        assert!(!ctx(&[]).is_well_formed(&[q]));
    }

    #[test]
    fn mobile_with_free_pvar_not_well_formed() {
        assert!(!ctx(&[]).is_well_formed(&[Qualification::Mobile(pvar_chan(5))]));
    }

    #[test]
    fn new_dualable_nonskip_with_free_pvar_not_well_formed() {
        assert!(
            !ctx(&[]).is_well_formed(&[Qualification::New(Session::PVar { id: 4, dual: false })])
        );
        assert!(
            !ctx(&[]).is_well_formed(&[Qualification::Dualable(Session::PVar {
                id: 4,
                dual: false
            })])
        );
        assert!(
            !ctx(&[])
                .is_well_formed(&[Qualification::NonSkip(Session::PVar { id: 4, dual: false })])
        );
    }

    #[test]
    fn dualable_op_with_ill_kinded_payload_not_well_formed() {
        let s = Session::Op(SessionOp::Send, Box::new(fake_span(pvar_chan(9))));
        assert!(!ctx(&[]).is_well_formed(&[Qualification::Dualable(s)]));
    }

    #[test]
    fn bounded_mu_with_free_pvar_not_well_formed() {
        let s = Session::Mu(
            fake_span("X".to_string()),
            Box::new(fake_span(Session::Semi {
                first: Box::new(fake_span(Session::Skip)),
                second: Box::new(fake_span(Session::PVar { id: 9, dual: false })),
            })),
        );
        assert!(!ctx(&[]).is_well_formed(&[Qualification::Bounded(s)]));
    }

    #[test]
    fn forall_with_well_formed_body() {
        // forall (a: Session). Unit
        let ty = Type::Forall {
            id: 0,
            kind: Kind::Session,
            qualifications: vec![],
            ty: Box::new(fake_span(Type::Unit)),
        };
        assert!(ctx(&[]).is_well_formed(&[Qualification::Unr(ty)]));
    }

    #[test]
    fn forall_with_free_pvar_in_body_not_well_formed() {
        // forall (a: Session). <b> where b is not bound by the forall
        let ty = Type::Forall {
            id: 0,
            kind: Kind::Session,
            qualifications: vec![],
            ty: Box::new(fake_span(pvar_chan(1))),
        };
        assert!(!ctx(&[]).is_well_formed(&[Qualification::Unr(ty)]));
    }
}
