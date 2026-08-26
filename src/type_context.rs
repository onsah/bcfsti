use std::collections::{HashMap, HashSet};

use crate::context::Ctx;
use crate::syntax::{
    Kind, Mult, PVarId, Qualification, Quantification, SLabel, Session, SessionOp, Type,
};
use crate::util::pretty::{Pretty, PrettyEnv};
use crate::util::span::fake_span;

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct TypeCtx {
    pub(crate) vars: HashMap<PVarId, Kind>,
    pub(crate) qualifications: Vec<Qualification>,
}

impl TypeCtx {
    pub fn empty() -> Self {
        TypeCtx {
            vars: HashMap::new(),
            qualifications: vec![],
        }
    }
}
impl TypeCtx {
    pub fn unr_ctx(&self, ctx: &Ctx) -> bool {
        ctx.binds()
            .into_iter()
            .map(|(_, ty)| ty)
            .all(|ty| self.entails(&Qualification::Unr(fake_span(ty))))
    }

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

    pub fn unr(&self, ty: &Type) -> bool {
        let (ty_ctx, ty) = Self::non_qualified_type(ty);
        self.clone().join(ty_ctx).or_assumed(
            || Qualification::Unr(fake_span(ty.clone())),
            match ty {
                // Q-Unr-Atom
                Type::Unit | Type::Int | Type::Bool | Type::String => true,
                Type::Arr { mult, .. } => mult.val == Mult::Unr,
                // Q-Unr-Prod
                Type::Prod { first, second, .. } => self.unr(first) && self.unr(second),
                // Q-Unr-Variant
                Type::Variant(variants) => variants
                    .iter()
                    .map(|(_, ty)| &ty.val)
                    .all(|ty| self.unr(ty)),
                // Q-Unr-Conv
                Type::Chan(Session::PVar { id, .. }) => {
                    self.equivalent_types_pv(id.clone()).any(|ty| self.unr(ty))
                }
                _ => false,
            },
        )
    }

    pub fn mobile(&self, ty: &Type) -> bool {
        let (ty_ctx, ty) = Self::non_qualified_type(ty);
        self.clone().join(ty_ctx).or_assumed(
            || Qualification::Mobile(fake_span(ty.clone())),
            match ty {
                // Q-Mbl-Atom
                Type::Unit | Type::String | Type::Int | Type::Bool | Type::Arr { .. } => true,
                // Q-Mbl-Prod
                Type::Prod { first, second, .. } => self.mobile(first) && self.mobile(second),
                // Q-Mbl-Variant
                Type::Variant(variants) => variants
                    .iter()
                    .map(|(_, ty)| &ty.val)
                    .all(|ty| self.unr(ty)),
                // Q-Mbl-Acq
                Type::Chan(session @ Session::Semi { .. }) => {
                    let Session::Semi { first, second } = session else {
                        unreachable!()
                    };
                    first.val == Session::BorrowEnd(SessionOp::Recv) && self.bounded(&second)
                }
                // Q-Mbl-Conv
                Type::Chan(Session::PVar { id, .. }) => self
                    .equivalent_types_pv(id.clone())
                    .any(|ty| self.mobile(ty)),
                Type::Abstraction {
                    quantification, ty, ..
                } => {
                    let new_ctx = self.extend(
                        Quantification::bindings(quantification.bindings.iter().cloned()),
                        quantification.qualifications.iter().map(|q| q.val.clone()),
                    );
                    new_ctx.mobile(ty)
                }
                _ => false,
            },
        )
    }

    fn non_qualified_type(ty: &Type) -> (TypeCtx, &Type) {
        match ty {
            Type::Abstraction {
                quantification, ty, ..
            } => {
                let new_ctx = TypeCtx::empty().extend(
                    Quantification::bindings(quantification.bindings.iter().cloned()),
                    quantification.qualifications.iter().map(|q| q.val.clone()),
                );
                let (inner_ctx, inner_ty) = Self::non_qualified_type(ty);
                (new_ctx.join(inner_ctx), inner_ty)
            }
            _ => (TypeCtx::empty(), ty),
        }
    }

    fn bounded(&self, session: &Session) -> bool {
        self.or_assumed(
            || Qualification::Bounded(fake_span(session.clone())),
            match session {
                Session::End(_) | Session::BorrowEnd(SessionOp::Send) => true,
                Session::Semi { first, second } => {
                    (self.bounded(first) && second.is_only_skips()) || self.bounded(second)
                }
                Session::Mu(_, session) => self.bounded(session),
                Session::Var(_) => true,
                Session::Choice(_, branches) => branches.iter().all(|(_, s)| self.bounded(s)),
                Session::PVar { id, .. } => self
                    .qualifications
                    .iter()
                    .filter_map::<&Session, _>(|q| match q {
                        Qualification::Equiv(ty1, ty2) => {
                            if let Type::Chan(s) = &ty2.val
                                && ty1.val == pvar(id.clone())
                            {
                                Some(s)
                            } else if let Type::Chan(s) = &ty1.val
                                && ty2.val == pvar(id.clone())
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
            || Qualification::Dualable(fake_span(session.clone())),
            match session {
                Session::Skip | Session::Op(_, _) | Session::End(_) | Session::Var(_) => true,
                Session::PVar { id, .. } => {
                    self.new(session)
                        || self.equivalent_types(id.clone()).any(|ty| match ty {
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

    pub fn new(&self, session: &Session) -> bool {
        self.or_assumed(
            || Qualification::New(fake_span(session.clone())),
            match session {
                Session::Skip | Session::Op(_, _) | Session::Var(_) => true,

                Session::Semi { first, second } => self.new(&first.val) && self.new(&second.val),
                Session::Choice(_, items) => items.iter().all(|(_, s)| self.new(s)),
                Session::Mu(_, body) => self.new(body),
                Session::PVar { id, .. } => self.equivalent_types(id.clone()).any(|ty| match ty {
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
                if ty1.val.poly_variables().find(|id1| id1 == &id).is_some() =>
            {
                Some(&ty2.val)
            }
            Qualification::Equiv(ty1, ty2)
                if ty2.val.poly_variables().find(|id1| id1 == &id).is_some() =>
            {
                Some(&ty1.val)
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
                    .val
                    .poly_variables_under_prod_and_variant()
                    .find(|id1| id1 == &id)
                    .is_some() =>
            {
                Some(&ty2.val)
            }
            Qualification::Equiv(ty1, ty2)
                if ty2
                    .val
                    .poly_variables_under_prod_and_variant()
                    .find(|id1| id1 == &id)
                    .is_some() =>
            {
                Some(&ty1.val)
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

impl TypeCtx {
    pub fn join(self, other: TypeCtx) -> TypeCtx {
        let mut new_vars = self.vars;
        new_vars.extend(other.vars);
        let mut new_qualifications = self.qualifications;
        new_qualifications.extend(other.qualifications);
        TypeCtx {
            vars: new_vars,
            qualifications: new_qualifications,
        }
    }

    pub fn extend_bindings(&self, bindings: impl Iterator<Item = (PVarId, Kind)>) -> TypeCtx {
        let mut new_vars = self.vars.clone();
        new_vars.extend(bindings);
        TypeCtx {
            vars: new_vars,
            qualifications: self.qualifications.clone(),
        }
    }

    pub fn extend_qualifications(
        &self,
        qualifications: impl IntoIterator<Item = Qualification>,
    ) -> TypeCtx {
        let mut new_ctx = self.clone();
        new_ctx.qualifications.extend(qualifications);
        new_ctx
    }

    pub fn extend(
        &self,
        bindings: impl Iterator<Item = (PVarId, Kind)>,
        qualifications: impl IntoIterator<Item = Qualification>,
    ) -> TypeCtx {
        self.extend_bindings(bindings)
            .extend_qualifications(qualifications)
    }
}

// Equality
impl TypeCtx {
    pub fn equivalent(&self, ty1: &Type, ty2: &Type) -> bool {
        self.type_sem_eq(ty1, ty2)
                ||
                // We don't need the symmetric case since if we can find from one direction
                // we can also find from the other direction
                self.equivalent_to(ty1).any(|ty| self.equivalent(ty, ty2))
    }

    /// Set of types equivalent to a type under this context
    fn equivalent_to(&self, ty: &Type) -> impl Iterator<Item = &Type> {
        self.qualifications.iter().filter_map(|q| match q {
            Qualification::Equiv(ty1, ty2) if self.type_sem_eq(&ty1.val, ty) => Some(&ty2.val),
            Qualification::Equiv(ty1, ty2) if self.type_sem_eq(&ty2.val, ty) => Some(&ty1.val),
            _ => None,
        })
    }

    fn type_sem_eq(&self, t1: &Type, t2: &Type) -> bool {
        match (t1, t2) {
            (Type::Chan(s1), Type::Chan(s2)) => self.session_sem_eq(s1, s2),
            (
                Type::Arr {
                    mob: mob1,
                    mult: m1,
                    eff: p1,
                    param: t11,
                    ret: t12,
                },
                Type::Arr {
                    mob: mob2,
                    mult: m2,
                    eff: p2,
                    param: t21,
                    ret: t22,
                },
            ) => {
                mob1 == mob2
                    && m1 == m2
                    && p1 == p2
                    && self.type_sem_eq(t11, t21)
                    && self.type_sem_eq(t12, t22)
            }
            (
                Type::Prod {
                    mult: m1,
                    first: t11,
                    second: t12,
                },
                Type::Prod {
                    mult: m2,
                    first: t21,
                    second: t22,
                },
            ) => m1 == m2 && self.type_sem_eq(t11, t21) && self.type_sem_eq(t12, t22),
            (Type::Variant(cs1), Type::Variant(cs2)) => {
                if let Some(cs) = Self::merge_clauses(cs1, cs2, false) {
                    cs.iter().all(|(_, t1, t2)| self.type_sem_eq(t1, t2))
                } else {
                    false
                }
            }
            (Type::Unit, Type::Unit) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (
                Type::PVar {
                    id: id1,
                    dual: dual1,
                },
                Type::PVar {
                    id: id2,
                    dual: dual2,
                },
            )
            | (
                Type::PVar {
                    id: id1,
                    dual: dual1,
                },
                Type::Chan(Session::PVar {
                    id: id2,
                    dual: dual2,
                }),
            )
            | (
                Type::Chan(Session::PVar {
                    id: id1,
                    dual: dual1,
                }),
                Type::PVar {
                    id: id2,
                    dual: dual2,
                },
            ) => id1 == id2 && dual1 == dual2,
            (
                Type::Abstraction {
                    typ: typ1,
                    quantification: q1,
                    ty: ty1,
                },
                Type::Abstraction {
                    typ: typ2,
                    quantification: q2,
                    ty: ty2,
                },
            ) => typ1 == typ2 && q1 == q2 && self.type_sem_eq(ty1, ty2),
            _ => false,
        }
    }

    fn session_sem_eq(&self, s1: &Session, s2: &Session) -> bool {
        self.session_sem_eq_(s1, s2, &HashSet::new())
    }

    fn session_sem_eq_(
        &self,
        s1: &Session,
        s2: &Session,
        seen: &HashSet<(Session, Session)>,
    ) -> bool {
        let mut seen = seen.clone();
        if !seen.insert((s1.clone(), s2.clone())) {
            return true;
        } else {
            match (s1, s2) {
                (Session::Op(op1, t1), Session::Op(op2, t2)) => {
                    op1 == op2 && self.type_sem_eq(t1, t2)
                }
                (Session::End(op1), Session::End(op2)) => op1 == op2,
                (Session::BorrowEnd(end1), Session::BorrowEnd(end2)) => end1 == end2,
                (Session::Choice(op1, cs1), Session::Choice(op2, cs2)) if op1 == op2 => {
                    if let Some(cs) = Self::merge_clauses(cs1, cs2, false) {
                        cs.iter()
                            .all(|(_, s1, s2)| self.session_sem_eq_(s1, s2, &seen))
                    } else {
                        false
                    }
                }
                (Session::Mu(x1, s1), Session::Mu(x2, s2)) => {
                    x1.val == x2.val && self.session_sem_eq_(s1, s2, &seen)
                }
                (Session::Var(x1), Session::Var(x2)) => x1.val == x2.val,
                (
                    Session::Semi {
                        first: first1,
                        second: second1,
                    },
                    Session::Semi {
                        first: first2,
                        second: second2,
                    },
                ) => {
                    self.session_sem_eq_(first1, first2, &seen)
                        && self.session_sem_eq_(second1, second2, &seen)
                }
                (Session::UVar(x1), Session::UVar(x2)) => x1 == x2,
                (
                    Session::PVar {
                        id: id1,
                        dual: dual1,
                    },
                    Session::PVar {
                        id: id2,
                        dual: dual2,
                    },
                ) => id1 == id2 && dual1 == dual2,
                (Session::Skip, Session::Skip) => true,
                _ => false,
            }
        }
    }

    fn merge_clauses<T: Clone>(
        cs1: &[(SLabel, T)],
        cs2: &[(SLabel, T)],
        sub: bool,
    ) -> Option<Vec<(SLabel, T, T)>> {
        let mut out = vec![];
        for (l2, s2) in cs2 {
            if let Some((_, s1)) = cs1.iter().find(|(l1, _)| l2 == l1) {
                out.push((l2.clone(), s1.clone(), s2.clone()))
            } else {
                return None;
            }
        }
        if !sub {
            for (l1, _) in cs1 {
                if let None = cs2.iter().find(|(l2, _)| l1 == l2) {
                    return None;
                }
            }
        }
        Some(out)
    }
}

impl Pretty<()> for (&String, &Kind) {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        p.pp(self.0);
        p.pp(": ");
        p.pp(self.1);
    }
}

impl Pretty<()> for TypeCtx {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        p.pp_sep(",", self.vars.iter());
        if !self.qualifications.is_empty() {
            p.pp(" | ");
            p.pp_sep(",", self.qualifications.iter());
        }
    }
}

fn pvar(id: PVarId) -> Type {
    Type::Chan(Session::PVar { id, dual: false })
}
