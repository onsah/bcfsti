use std::collections::HashMap;

use crate::context::Ctx;
use crate::syntax::{Kind, Mult, PVarId, Qualification, Quantification, Session, SessionOp, Type};
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
                _ => false,
            },
        )
    }

    fn dualable(&self, session: &Session) -> bool {
        self.or_assumed(
            || Qualification::Dualable(fake_span(session.clone())),
            match session {
                Session::Skip | Session::Op(_, _) | Session::End(_) | Session::Var(_) => true,
                Session::PVar { .. } => self.new(session),
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
                _ => false,
            },
        )
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
