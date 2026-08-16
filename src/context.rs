use std::collections::{HashMap, HashSet};
use std::hash::Hash;

use crate::syntax::{Id, Mult, SId, SType, Type, TypeSemEq};
use crate::type_context::TypeCtx;
use crate::util::boxed::Boxed;
use crate::util::graph::Graph;
use crate::util::pretty::{Pretty, PrettyEnv};

use CtxCtxS::*;
use CtxS::*;
use JoinOrd::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinOrd {
    Ordered,
    Unordered,
}

impl Mult {
    pub fn to_join_ord(&self) -> JoinOrd {
        match self {
            Mult::Unr => JoinOrd::Ordered,
            Mult::Lin => JoinOrd::Unordered,
            Mult::OrdR => JoinOrd::Ordered,
            Mult::OrdL => JoinOrd::Ordered,
        }
    }
    pub fn choose_ctxs<'a>(&self, c1: &'a Ctx, c2: &'a Ctx) -> (&'a Ctx, &'a Ctx) {
        match self {
            Mult::OrdL => (c2, c1),
            _ => (c1, c2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ctx {
    Empty,
    Bind(SId, SType),
    Join(Box<Ctx>, Box<Ctx>, JoinOrd),
}

#[allow(non_snake_case)]
pub mod CtxS {
    use super::*;

    #[allow(non_upper_case_globals)]
    pub const Empty: Ctx = Ctx::Empty;

    pub fn Bind(x: SId, t: SType) -> Ctx {
        Ctx::Bind(x, t)
    }

    pub fn Join(c1: impl Boxed<Ctx>, c2: impl Boxed<Ctx>, o: JoinOrd) -> Ctx {
        Ctx::Join(c1.boxed(), c2.boxed(), o)
    }
}

pub fn ext(m: Mult, c1: Ctx, c2: Ctx) -> Ctx {
    match m {
        Mult::Unr => CtxS::Join(c1, c2, JoinOrd::Unordered),
        Mult::Lin => CtxS::Join(c1, c2, JoinOrd::Unordered),
        Mult::OrdR => CtxS::Join(c2, c1, JoinOrd::Ordered),
        Mult::OrdL => CtxS::Join(c1, c2, JoinOrd::Ordered),
    }
}

impl Ctx {
    pub fn map_binds(&self, f: &mut impl FnMut(&Id, &Type)) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => f(x, t),
            Ctx::Join(c1, c2, _o) => {
                c1.map_binds(f);
                c2.map_binds(f);
            }
        }
    }
    pub fn map_binds_spanned(&self, f: &mut impl FnMut(&SId, &Type)) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => f(x, t),
            Ctx::Join(c1, c2, _o) => {
                c1.map_binds_spanned(f);
                c2.map_binds_spanned(f);
            }
        }
    }
    pub fn map_binds_mut(&mut self, f: &mut impl FnMut(&mut Id, &mut Type)) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => f(x, t),
            Ctx::Join(c1, c2, _o) => {
                c1.map_binds_mut(f);
                c2.map_binds_mut(f);
            }
        }
    }
    pub fn flatmap_binds_mut(&mut self, f: &mut impl FnMut(Id, Type) -> Ctx) {
        match self {
            Ctx::Empty => (),
            Ctx::Bind(x, t) => *self = f(x.val.clone(), t.val.clone()),
            Ctx::Join(c1, c2, _o) => {
                c1.flatmap_binds_mut(f);
                c2.flatmap_binds_mut(f);
            }
        }
    }
    pub fn flatmap_binds(&self, f: &mut impl FnMut(Id, Type) -> Ctx) -> Ctx {
        let mut ctx = self.clone();
        ctx.flatmap_binds_mut(f);
        ctx
    }
    pub fn is_unr(&self, ty_ctx: &TypeCtx) -> bool {
        let mut unr = true;
        self.map_binds(&mut |_x, t| unr = unr && ty_ctx.unr(t));
        unr
    }
    /// ```
    /// let (leftover_ctx, ty) = ctx.lookup_ord_pure(x)
    /// ```
    pub fn lookup_ord_pure(&self, ty_ctx: &TypeCtx, x: &Id) -> Option<(Ctx, SType)> {
        let mut c = self.clone();
        c.lookup_ord(ty_ctx, x).map(|t| (c, t))
    }
    pub fn lookup_ord(&mut self, ty_ctx: &TypeCtx, x: &Id) -> Option<SType> {
        match self {
            Ctx::Empty => None,
            Ctx::Bind(y, t) if x == &y.val => {
                if t.is_ord() {
                    let t = t.clone();
                    *self = Ctx::Empty;
                    Some(t)
                } else {
                    Some(t.clone())
                }
            }
            Ctx::Bind(_y, _t) => None,
            Ctx::Join(c1, c2, o) => c1.lookup_ord(ty_ctx, x).or_else(|| {
                if c1.is_unr(ty_ctx) || *o == JoinOrd::Unordered {
                    c2.lookup_ord(ty_ctx, x)
                } else {
                    None
                }
            }),
        }
    }

    pub fn restrict(&self, xs: &HashSet<Id>) -> Self {
        match self {
            Ctx::Empty => Ctx::Empty,
            Ctx::Bind(x, t) if xs.contains(&x.val) => Ctx::Bind(x.clone(), t.clone()),
            Ctx::Bind(_, _) => Ctx::Empty,
            Ctx::Join(c1, c2, o) => CtxS::Join(c1.restrict(xs), c2.restrict(xs), *o),
        }
    }

    pub fn vars(&self) -> HashSet<Id> {
        let mut res = HashSet::new();
        self.map_binds(&mut |x, _t| {
            res.insert(x.clone());
        });
        res
    }
    pub fn lin_vars(&self, ty_ctx: &TypeCtx) -> HashSet<Id> {
        let mut res = HashSet::new();
        self.map_binds(&mut |x, t| {
            if !ty_ctx.unr(t) {
                res.insert(x.clone());
            }
        });
        res
    }
    pub fn binds(&self) -> HashMap<Id, Type> {
        let mut res = HashMap::new();
        self.map_binds(&mut |x, t| {
            res.insert(x.clone(), t.clone());
        });
        res
    }
    pub fn binds_spanned(&self) -> HashMap<SId, Type> {
        let mut res = HashMap::new();
        self.map_binds_spanned(&mut |x, t| {
            res.insert(x.clone(), t.clone());
        });
        res
    }
    pub fn to_sem(&self, ty_ctx: &TypeCtx) -> SemCtx {
        match self {
            Ctx::Empty => SemCtx::empty(),
            Ctx::Bind(x, t) => SemCtx::bind(x.val.clone(), t.val.clone(), ty_ctx),
            Ctx::Join(c1, c2, o) => c1.to_sem(ty_ctx).join(&c2.to_sem(ty_ctx), *o),
        }
    }
    pub fn is_splittable(&self, ty_ctx: &TypeCtx, xs: &HashSet<Id>) -> bool {
        let sem = self.to_sem(ty_ctx);
        let (binds_xs, binds_not_xs) = self
            .binds()
            .into_iter()
            .filter(|(_, t)| !ty_ctx.unr(t))
            .map(|(x, t)| (x, TypeSemEq(t)))
            .partition::<HashSet<_>, _>(|(x, _)| xs.contains(x));
        for b1 in &binds_xs {
            for b2 in &binds_not_xs {
                if sem.ord.is_reachable(b1, b2) {
                    for b3 in &binds_xs {
                        if sem.ord.is_reachable(b2, b3) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
    pub fn split(&self, ty_ctx: &TypeCtx, xs: &HashSet<Id>) -> Option<(CtxCtx, Ctx)> {
        if xs.len() == 0 {
            return Some((
                CtxCtx::JoinR(
                    Box::new(self.clone()),
                    Box::new(CtxCtx::Hole),
                    JoinOrd::Unordered,
                ),
                Ctx::Empty,
            ));
        }
        match self {
            Ctx::Empty => Some((CtxCtxS::Hole, Ctx::Empty)),
            Ctx::Bind(x, t) => {
                if !xs.contains(&x.val) {
                    Some((
                        CtxCtxS::JoinL(CtxCtxS::Hole, Ctx::Bind(x.clone(), t.clone()), Unordered),
                        Ctx::Empty,
                    ))
                } else if t.is_ord() {
                    Some((CtxCtxS::Hole, Ctx::Bind(x.clone(), t.clone())))
                } else {
                    Some((
                        CtxCtxS::JoinL(CtxCtxS::Hole, Ctx::Bind(x.clone(), t.clone()), Unordered),
                        Ctx::Bind(x.clone(), t.clone()),
                    ))
                }
            }
            Ctx::Join(c1, c2, o) => {
                if xs.is_disjoint(&c1.vars()) {
                    let (cc, c) = c2.split(ty_ctx, xs)?;
                    return Some((CtxCtxS::JoinR(c1.clone(), cc, *o), c));
                } else if xs.is_disjoint(&c2.vars()) {
                    let (cc, c) = c1.split(ty_ctx, xs)?;
                    return Some((CtxCtxS::JoinL(cc, c2.clone(), *o), c));
                }
                let (cc1, c1) = c1.split(ty_ctx, xs)?;
                let (cc2, c2) = c2.split(ty_ctx, xs)?;
                match o {
                    Ordered if !c1.is_unr(ty_ctx) && !c2.is_unr(ty_ctx) => {
                        if let (Some(c1x), Some(c2x)) =
                            (cc1.pull_right(ty_ctx), cc2.pull_left(ty_ctx))
                        {
                            Some((
                                JoinR(c1x, JoinL(Hole, c2x, Ordered), Ordered),
                                Join(c1, c2, Ordered),
                            ))
                        } else {
                            None
                        }
                    }
                    _ => {
                        if let (Some(c1x), Some(c2x)) = (cc1.pull_par(ty_ctx), cc2.pull_par(ty_ctx))
                        {
                            Some((
                                JoinR(c1x, JoinL(CtxCtxS::Hole, c2x, Unordered), Unordered),
                                Join(c1, c2, Unordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) =
                            (cc1.pull_right(ty_ctx), cc2.pull_right(ty_ctx))
                        {
                            Some((
                                JoinR(Join(c1x, c2x, Unordered), CtxCtxS::Hole, Ordered),
                                Join(c1, c2, Unordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) =
                            (cc1.pull_left(ty_ctx), cc2.pull_left(ty_ctx))
                        {
                            Some((
                                JoinL(CtxCtxS::Hole, Join(c1x, c2x, Unordered), Ordered),
                                Join(c1, c2, Unordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) =
                            (cc1.pull_left(ty_ctx), cc2.pull_right(ty_ctx))
                        {
                            Some((
                                JoinR(c2x, JoinL(CtxCtxS::Hole, c1x, Ordered), Ordered),
                                Join(c1, c2, Ordered),
                            ))
                        } else if let (Some(c1x), Some(c2x)) =
                            (cc1.pull_right(ty_ctx), cc2.pull_left(ty_ctx))
                        {
                            Some((
                                JoinR(c1x, JoinL(CtxCtxS::Hole, c2x, Ordered), Ordered),
                                Join(c2, c1, Ordered),
                            ))
                        } else {
                            let ((c11, c12), (c21, c22)) = (cc1.pull_closed(), cc2.pull_closed());
                            Some((
                                JoinR(
                                    Join(c11, c21, Unordered),
                                    JoinL(Hole, Join(c12, c22, Unordered), Ordered),
                                    Ordered,
                                ),
                                Join(c1, c2, Unordered),
                            ))
                        }
                    }
                }
            }
        }
    }
    pub fn simplify(&self) -> Self {
        match self {
            Ctx::Empty => Ctx::Empty,
            Ctx::Bind(x, t) => Ctx::Bind(x.clone(), t.clone()),
            Ctx::Join(c1, c2, o) => match (c1.simplify(), c2.simplify()) {
                (c1, Ctx::Empty) => c1,
                (Ctx::Empty, c2) => c2,
                (c1, c2) => CtxS::Join(c1, c2, *o),
            },
        }
    }
    pub fn is_subctx_of(&self, ty_ctx: &TypeCtx, other: &Self) -> bool {
        self.to_sem(ty_ctx).is_subctx_of(&other.to_sem(ty_ctx))
    }

    /// Returns Ok(()) if the context is mobile, otherwise returns Err(x) where x is a variable that is not mobile.
    pub fn is_mobile(&self, ty_ctx: &TypeCtx) -> Result<(), SId> {
        match self {
            Ctx::Empty => Ok(()),
            Ctx::Bind(var, ty) => {
                if ty_ctx.mobile(&ty.val) {
                    Ok(())
                } else {
                    Err(var.clone())
                }
            }
            Ctx::Join(ctx1, ctx2, _) => {
                ctx1.is_mobile(ty_ctx)?;
                ctx2.is_mobile(ty_ctx)
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum CtxCtx {
    Hole,
    JoinL(Box<CtxCtx>, Box<Ctx>, JoinOrd),
    JoinR(Box<Ctx>, Box<CtxCtx>, JoinOrd),
}

#[allow(non_snake_case)]
pub mod CtxCtxS {
    use super::*;

    #[allow(non_upper_case_globals)]
    pub const Hole: CtxCtx = CtxCtx::Hole;

    pub fn JoinL(cc: impl Boxed<CtxCtx>, c: impl Boxed<Ctx>, o: JoinOrd) -> CtxCtx {
        CtxCtx::JoinL(cc.boxed(), c.boxed(), o)
    }

    pub fn JoinR(c: impl Boxed<Ctx>, cc: impl Boxed<CtxCtx>, o: JoinOrd) -> CtxCtx {
        CtxCtx::JoinR(c.boxed(), cc.boxed(), o)
    }
}

impl CtxCtx {
    pub fn flatmap_binds_mut(&mut self, f: &mut impl FnMut(Id, Type) -> Ctx) {
        match self {
            CtxCtx::Hole => (),
            CtxCtx::JoinL(cc1, c2, _o) => {
                cc1.flatmap_binds_mut(f);
                c2.flatmap_binds_mut(f);
            }
            CtxCtx::JoinR(c1, cc2, _o) => {
                c1.flatmap_binds_mut(f);
                cc2.flatmap_binds_mut(f);
            }
        }
    }
    pub fn flatmap_binds(&self, f: &mut impl FnMut(Id, Type) -> Ctx) -> Self {
        let mut cc = self.clone();
        cc.flatmap_binds_mut(f);
        cc
    }
    pub fn fill(&self, c: Ctx) -> Ctx {
        match self {
            CtxCtx::Hole => c,
            CtxCtx::JoinL(cc1, c2, o) => Ctx::Join(Box::new(cc1.fill(c)), c2.clone(), o.clone()),
            CtxCtx::JoinR(c1, cc2, o) => Ctx::Join(c1.clone(), Box::new(cc2.fill(c)), o.clone()),
        }
    }
    pub fn is_left(&self, ty_ctx: &TypeCtx) -> bool {
        match self {
            CtxCtx::Hole => true,
            CtxCtx::JoinL(cc1, _c2, _o) => cc1.is_left(ty_ctx),
            CtxCtx::JoinR(c1, cc2, o) => {
                cc2.is_left(ty_ctx) && (*o == JoinOrd::Unordered || c1.is_unr(ty_ctx))
            }
        }
    }

    pub fn is_right(&self, ty_ctx: &TypeCtx) -> bool {
        match self {
            CtxCtx::Hole => true,
            CtxCtx::JoinL(cc1, c2, o) => {
                cc1.is_right(ty_ctx) && (*o == JoinOrd::Unordered || c2.is_unr(ty_ctx))
            }
            CtxCtx::JoinR(_c1, cc2, _o) => cc2.is_right(ty_ctx),
        }
    }

    fn pull_left_(&self, ty_ctx: &TypeCtx) -> Option<Ctx> {
        match self {
            CtxCtx::Hole => Some(Ctx::Empty),
            CtxCtx::JoinL(cc, c, o) => {
                let c2 = cc.pull_left(ty_ctx)?;
                Some(CtxS::Join(c2, c, *o))
            }
            CtxCtx::JoinR(c, cc, o) => {
                let c2 = cc.pull_left(ty_ctx)?;
                Some(CtxS::Join(c2, c, *o))
            }
        }
    }

    pub fn pull_left(&self, ty_ctx: &TypeCtx) -> Option<Ctx> {
        if self.is_left(ty_ctx) {
            self.pull_left_(ty_ctx)
        } else {
            None
        }
    }

    fn pull_right_(&self, ty_ctx: &TypeCtx) -> Option<Ctx> {
        match self {
            CtxCtx::Hole => Some(Ctx::Empty),
            CtxCtx::JoinL(cc, c, o) => {
                let c2 = cc.pull_right(ty_ctx)?;
                Some(CtxS::Join(c, c2, *o))
            }
            CtxCtx::JoinR(c, cc, o) => {
                let c2 = cc.pull_right(ty_ctx)?;
                Some(CtxS::Join(c, c2, *o))
            }
        }
    }

    pub fn pull_right(&self, ty_ctx: &TypeCtx) -> Option<Ctx> {
        if self.is_right(ty_ctx) {
            self.pull_right_(ty_ctx)
        } else {
            None
        }
    }

    fn pull_par_(&self, ty_ctx: &TypeCtx) -> Option<Ctx> {
        match self {
            CtxCtx::Hole => Some(Ctx::Empty),
            CtxCtx::JoinL(cc, c, _o) => {
                let c2 = cc.pull_par(ty_ctx)?;
                Some(CtxS::Join(c, c2, JoinOrd::Unordered))
            }
            CtxCtx::JoinR(c, cc, _o) => {
                let c2 = cc.pull_par(ty_ctx)?;
                Some(CtxS::Join(c, c2, JoinOrd::Unordered))
            }
        }
    }

    pub fn pull_par(&self, ty_ctx: &TypeCtx) -> Option<Ctx> {
        if self.is_left(ty_ctx) && self.is_right(ty_ctx) {
            self.pull_par_(ty_ctx)
        } else {
            None
        }
    }

    pub fn pull_closed(&self) -> (Ctx, Ctx) {
        match self {
            CtxCtx::Hole => (Ctx::Empty, Ctx::Empty),
            CtxCtx::JoinL(cc, c, o) => {
                let (c1, c2) = cc.pull_closed();
                (c1, CtxS::Join(c2, c, *o))
            }
            CtxCtx::JoinR(c, cc, o) => {
                let (c1, c2) = cc.pull_closed();
                (CtxS::Join(c, c1, *o), c2)
            }
        }
    }

    pub fn simplify(&self) -> Self {
        match self {
            CtxCtx::Hole => CtxCtx::Hole,
            CtxCtx::JoinL(c1, c2, o) => match (c1.simplify(), c2.simplify()) {
                (c1, Ctx::Empty) => c1,
                (c1, c2) => CtxCtxS::JoinL(c1, c2, *o),
            },
            CtxCtx::JoinR(c1, c2, o) => match (c1.simplify(), c2.simplify()) {
                (Ctx::Empty, c2) => c2,
                (c1, c2) => CtxCtxS::JoinR(c1, c2, *o),
            },
        }
    }

    pub fn vars(&self) -> HashSet<Id> {
        self.fill(Ctx::Empty).vars()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemCtx {
    pub ord: Graph<(Id, TypeSemEq)>,
    pub unr: HashSet<(Id, TypeSemEq)>,
}

impl SemCtx {
    pub fn empty() -> Self {
        Self {
            ord: Graph::empty(),
            unr: HashSet::new(),
        }
    }
    pub fn bind(x: Id, t: Type, ty_ctx: &TypeCtx) -> Self {
        let mut c = Self::empty();
        if ty_ctx.unr(&t) {
            c.unr.insert((x, TypeSemEq(t)));
        } else {
            c.ord = Graph::singleton((x, TypeSemEq(t)));
        }
        c
    }
    pub fn join(&self, other: &Self, o: JoinOrd) -> Self {
        match o {
            JoinOrd::Ordered => self.plus(other),
            JoinOrd::Unordered => self.union(other),
        }
    }
    pub fn union(&self, other: &Self) -> Self {
        Self {
            ord: self.ord.union(&other.ord),
            unr: self.unr.union(&other.unr).cloned().collect(),
        }
    }
    pub fn plus(&self, other: &Self) -> Self {
        Self {
            ord: self.ord.plus(&other.ord),
            unr: self.unr.union(&other.unr).cloned().collect(),
        }
    }
    pub fn is_subctx_of(&self, other: &Self) -> bool {
        self.ord.is_subgraph_of(&other.ord) && other.unr.is_subset(&self.unr)
    }
}

impl Pretty<()> for Ctx {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        match self {
            Ctx::Empty => p.pp("·"),
            Ctx::Bind(x, t) => {
                p.pp(x);
                p.pp(" : ");
                p.pp(t);
            }
            Ctx::Join(c1, c2, o) => {
                p.pp("(");
                p.pp(c1);
                match o {
                    Ordered => p.pp(" , "),
                    Unordered => p.pp(" ∥ "),
                }
                p.pp(c2);
                p.pp(")")
            }
        }
    }
}

pub fn pretty_context_notype(c: &Ctx) -> String {
    match c {
        Ctx::Empty => format!("·"),
        Ctx::Bind(x, _) => format!("{}", x.val),
        Ctx::Join(c1, c2, o) => {
            format!(
                "({} {} {})",
                pretty_context_notype(c1),
                match o {
                    Ordered => ",",
                    Unordered => "∥",
                },
                pretty_context_notype(c2),
            )
        }
    }
}

impl Pretty<()> for CtxCtx {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        match self {
            CtxCtx::Hole => p.pp("■"),
            CtxCtx::JoinL(c1, c2, o) => {
                p.pp("(");
                p.pp(c1);
                match o {
                    Ordered => p.pp(" , "),
                    Unordered => p.pp(" ∥ "),
                }
                p.pp(c2);
                p.pp(")")
            }
            CtxCtx::JoinR(c1, c2, o) => {
                p.pp("(");
                p.pp(c1);
                match o {
                    Ordered => p.pp(" , "),
                    Unordered => p.pp(" ∥ "),
                }
                p.pp(c2);
                p.pp(")")
            }
        }
    }
}

impl Pretty<()> for SemCtx {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        p.pp("Unrestricted:\n");
        let mut unr = self.unr.iter().collect::<Vec<_>>();
        unr.sort_by_key(|(x, _t)| x);
        for (x, t) in unr {
            p.pp("  ");
            p.pp(x);
            p.pp(" : ");
            p.pp(&t.0);
            p.pp("\n");
        }
        p.pp("\nGraph:\n");
        let mut ord = self.ord.edges.iter().collect::<Vec<_>>();
        ord.sort_by_key(|((x, _t), _ys)| x);
        for ((x, t), ys) in ord {
            p.pp("  ");
            p.pp(x);
            p.pp(" : ");
            p.pp(&t.0);
            p.pp("\n");
            for (x, t) in ys {
                p.pp("    ");
                p.pp(x);
                p.pp(" : ");
                p.pp(&t.0);
                p.pp("\n");
            }
        }
    }
}

impl<T: Ord + Eq + Hash + Pretty<()>> Pretty<()> for HashSet<T> {
    fn pp(&self, p: &mut PrettyEnv<()>) {
        let mut xs: Vec<_> = self.iter().collect();
        xs.sort();
        p.pp("{");
        for (i, x) in xs.into_iter().enumerate() {
            if i != 0 {
                p.pp(", ");
            }
            p.pp(x);
        }
        p.pp("}");
    }
}

pub struct CtxEnum {
    pub vars: Vec<Id>,
    pub catalanian: Vec<usize>,
    pub cur: usize,
}

pub fn catalanians_up_to(n: usize) -> Vec<usize> {
    let mut catalanian = vec![0, 1];
    for i in 2..=n {
        let mut c = 0;
        for j in 1..i {
            c += catalanian[j] * catalanian[i - j] * 2;
        }
        catalanian.push(c)
    }

    catalanian
}
