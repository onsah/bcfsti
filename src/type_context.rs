use std::collections::HashMap;

use crate::{
    freest::Kind,
    syntax::{Label, PVarId, Qualification, Session, SessionOp, Type},
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TypeCtx {
    vars: HashMap<Label, Kind>,
    qualifications: Vec<Qualification>,
}

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
                Type::Chan(Session::PVar(id)) => {
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
                Type::Chan(Session::PVar(id)) => {
                    self.equivalent_types_pv(*id).any(|ty| self.mobile(ty))
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
                Session::PVar(id) => self
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
                Session::PVar(id) => {
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
                Session::PVar(id) => self.equivalent_types(*id).any(|ty| match ty {
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

    pub(crate) fn has_kind(&self, var: &Label, kind: Kind) -> bool {
        match self.vars.get(var) {
            Some(k) if k == &kind => true,
            _ => false,
        }
    }

    pub fn is_well_formed(&self, qualifications: &[Qualification]) -> bool {
        todo!()
    }
}

fn pvar(id: PVarId) -> Type {
    Type::Chan(Session::PVar(id))
}
