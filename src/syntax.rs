use crate::util::span::{Spanned, fake_span};
use std::{collections::HashSet, hash::Hash};

pub type Id = String;
pub type SId = Spanned<Id>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mob {
    Mobile,
    Static,
}
pub type SMob = Spanned<Mob>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mult {
    Unr,
    Lin,
    OrdR,
    OrdL,
}
pub type SMult = Spanned<Mult>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Eff {
    Yes,
    No,
}
pub type SEff = Spanned<Eff>;

impl PartialOrd for Eff {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Eff {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Eff::No, Eff::No) => std::cmp::Ordering::Equal,
            (Eff::No, Eff::Yes) => std::cmp::Ordering::Less,
            (Eff::Yes, Eff::No) => std::cmp::Ordering::Greater,
            (Eff::Yes, Eff::Yes) => std::cmp::Ordering::Equal,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SessionOp {
    Send,
    Recv,
}
pub type SSessionOp = Spanned<SessionOp>;

pub type UVarId = usize;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Session {
    Skip,
    Semi {
        first: Box<SSession>,
        second: Box<SSession>,
    },
    End(SessionOp),
    BorrowEnd(SessionOp),
    Op(SessionOp, Box<SType>),
    Choice(SessionOp, Vec<(SLabel, SSession)>),
    Mu(SId, Box<SSession>),
    Var(SId),
    // Unification variable introduced from splits
    UVar(UVarId),
}
pub type SSession = Spanned<Session>;

impl Session {
    const ACQ: Session = Session::BorrowEnd(SessionOp::Recv);

    pub fn is_only_skips(&self) -> bool {
        match self {
            Session::Skip => true,
            Session::Semi { first, second } => first.is_only_skips() && second.is_only_skips(),
            Session::Mu(_, body) => body.is_only_skips(),
            _ => false,
        }
    }

    /// Closed session means it has no unification variables.
    pub fn is_closed(&self) -> bool {
        match self {
            Session::Skip => true,
            Session::Semi { first, second } => first.is_closed() && second.is_closed(),
            Session::End(_) => true,
            Session::BorrowEnd(_) => true,
            Session::Op(_, t) => t.is_closed(),
            Session::Choice(_, cs) => cs.iter().all(|(_, s)| s.is_closed()),
            Session::Mu(_, body) => body.is_closed(),
            Session::Var(_) => true,
            Session::UVar(_) => false,
        }
    }

    pub fn unification_variables(&self) -> HashSet<UVarId> {
        match self {
            Session::Skip => HashSet::new(),
            Session::Semi { first, second } => union(
                first.unification_variables(),
                second.unification_variables(),
            ),
            Session::End(_) => HashSet::new(),
            Session::BorrowEnd(_) => HashSet::new(),
            Session::Op(_, t) => t.unification_variables(),
            Session::Choice(_, cs) => cs
                .iter()
                .flat_map(|(_, s)| s.unification_variables())
                .collect(),
            Session::Mu(_, body) => body.unification_variables(),
            Session::Var(_) => HashSet::new(),
            Session::UVar(x) => HashSet::from([*x]),
        }
    }

    fn is_mobile(&self) -> bool {
        let this = &self;
        if let Session::Semi { first, second } = this.normalise() {
            matches!(first.val, Session::ACQ) && second.is_bounded()
        } else {
            false
        }
    }

    fn is_bounded(&self) -> bool {
        match self {
            Session::Semi { first, second } => {
                second.is_bounded() || (first.is_bounded() && second.is_only_skips())
            }
            Session::BorrowEnd(session_op) => session_op == &SessionOp::Send,
            Session::Choice(_, branches) => branches.iter().all(|(_, branch)| branch.is_bounded()),
            Session::Mu(_, body) => body.is_bounded(),
            Session::End(_) => true,
            Session::Var(_) => true,
            Session::Op(_, _) => false,
            // Unification variables are not bounded, as they can be instantiated to any session type.
            Session::UVar(_) => false,
            Session::Skip => false,
        }
    }

    pub fn is_contractive_on(&self, var: &SId) -> bool {
        match self {
            Session::Skip => true,
            Session::Semi { first, second } => match first.is_only_skips() {
                true => second.is_contractive_on(var),
                false => first.is_contractive_on(var),
            },
            Session::End(_) => true,
            Session::BorrowEnd(_) => true,
            Session::Op(_, _) => true,
            Session::Choice(_, _) => true,
            Session::Mu(_, body) => body.is_contractive_on(var),
            Session::Var(id) => id != var,
            Session::UVar(_) => true,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Chan(Session),
    Arr {
        mob: SMob,
        mult: SMult,
        eff: SEff,
        param: Box<SType>,
        ret: Box<SType>,
    },
    Prod {
        mult: SMult,
        first: Box<SType>,
        second: Box<SType>,
    },
    Variant(Vec<(SLabel, SType)>),
    Unit,
    Int,
    Bool,
    String,
}
pub type SType = Spanned<Type>;

impl Type {
    /// Closed type means it has no unification variables.
    pub fn is_closed(&self) -> bool {
        match self {
            Type::Chan(s) => s.is_closed(),
            Type::Arr { param, ret, .. } => param.is_closed() && ret.is_closed(),
            Type::Prod { first, second, .. } => first.is_closed() && second.is_closed(),
            Type::Variant(cs) => cs.iter().all(|(_, t)| t.is_closed()),
            Type::Unit | Type::Int | Type::Bool | Type::String => true,
        }
    }

    /// Unification variables appear inside the type
    pub fn unification_variables(&self) -> HashSet<UVarId> {
        match self {
            Type::Chan(s) => s.unification_variables(),
            Type::Arr { param, ret, .. } => {
                union(param.unification_variables(), ret.unification_variables())
            }
            Type::Prod { first, second, .. } => union(
                first.unification_variables(),
                second.unification_variables(),
            ),
            Type::Variant(cs) => cs
                .iter()
                .flat_map(|(_, t)| t.unification_variables())
                .collect(),
            Type::Unit | Type::Int | Type::Bool | Type::String => HashSet::new(),
        }
    }

    pub fn normalise(&self) -> Type {
        match self {
            Type::Chan(session) => Type::Chan(session.normalise()),
            _ => self.clone(),
        }
    }

    pub fn is_mobile(&self) -> bool {
        match self {
            Type::Chan(session) => session.is_mobile(),
            Type::Arr { mob, .. } => mob.val == Mob::Mobile,
            Type::Prod { first, second, .. } => first.is_mobile() && second.is_mobile(),
            Type::Variant(cases) => cases.iter().all(|(_, ty)| ty.is_mobile()),
            Type::Unit | Type::Int | Type::Bool | Type::String => true,
        }
    }
}

pub type Label = String;
pub type SLabel = Spanned<Label>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Pattern {
    Var(SId),
    Pair(Box<SPattern>, Box<SPattern>),
    //Inj(Label, Box<SPattern>),
}
pub type SPattern = Spanned<Pattern>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Clause {
    pub id: SId,
    pub var_id: SId,
    // pub pats: Vec<SPattern>,
    pub body: SExpr,
}
pub type SClause = Spanned<Clause>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Const {
    Unit,
    Int(i64),
    Bool(bool),
    String(String),
}

impl Const {
    pub fn type_(&self) -> Type {
        match self {
            Const::Unit => Type::Unit,
            Const::Int(_) => Type::Int,
            Const::Bool(_) => Type::Bool,
            Const::String(_) => Type::String,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op1 {
    Neg,
    Not,
    ToStr,
    Print,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Op2 {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expr {
    Const(Const),

    New(SSession),
    Fork(Box<SExpr>),

    End(SessionOp, Box<SExpr>),

    Send(SType, Box<SExpr>, Box<SExpr>),
    Recv(SType, Box<SExpr>),

    LSplit(SSession, Box<SExpr>),
    RSplit(SSession, Box<SExpr>),
    BorrowEnd(SessionOp, Box<SExpr>),
    Discard(Box<SExpr>),

    Var(SId),
    Abs(SId, Box<SExpr>),
    App(Box<SExpr>, Box<SExpr>),

    Seq(Box<SExpr>, Box<SExpr>),
    Pair(Box<SExpr>, Box<SExpr>),

    Let(SId, Box<SExpr>, Box<SExpr>),
    LetDecl(SId, SType, Box<SClause>, Box<SExpr>),
    LetPair(SId, SId, Box<SExpr>, Box<SExpr>),

    TypeDef(SId, SSession, Box<SExpr>, bool),

    Inj(SLabel, Box<SExpr>),
    CaseSum(Box<SExpr>, Vec<(SLabel, SId, SExpr)>),

    Select(SLabel, Box<SExpr>),
    Branch(Box<SExpr>),

    Ann(Box<SExpr>, SType),

    Op1(Op1, Box<SExpr>),
    Op2(Op2, Box<SExpr>, Box<SExpr>),

    If(Box<SExpr>, Box<SExpr>, Box<SExpr>),
}
pub type SExpr = Spanned<Expr>;

pub fn without<T: Hash + Eq>(mut xs: HashSet<T>, x: &T) -> HashSet<T> {
    xs.remove(x);
    xs
}

pub fn union<T: Hash + Eq>(mut xs: HashSet<T>, ys: HashSet<T>) -> HashSet<T> {
    for y in ys {
        xs.insert(y);
    }
    xs
}

impl SessionOp {
    pub fn dual(self) -> Self {
        match self {
            SessionOp::Send => SessionOp::Recv,
            SessionOp::Recv => SessionOp::Send,
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

impl Session {
    pub fn subst(&self, x: &Id, s_new: &Self) -> Self {
        match self {
            Session::Var(y) if *x == **y => s_new.clone(),
            Session::Var(y) => Session::Var(y.clone()),
            Session::Mu(y, e) => {
                if x != &y.val {
                    Session::Mu(y.clone(), Box::new(fake_span(e.subst(x, s_new))))
                } else {
                    self.clone()
                }
            }
            Session::Op(op, t) => Session::Op(op.clone(), t.clone()),
            Session::Choice(op, cs) => {
                let cs2 = cs
                    .iter()
                    .map(|(l, s)| (l.clone(), fake_span(s.subst(x, s_new))))
                    .collect();
                Session::Choice(op.clone(), cs2)
            }
            Session::End(op) => Session::End(op.clone()),
            Session::BorrowEnd(_) => self.clone(),
            Session::Skip => Session::Skip,
            Session::Semi { first, second } => Self::Semi {
                first: Box::new(fake_span(first.subst(x, s_new))),
                second: Box::new(fake_span(second.subst(x, s_new))),
            },
            Session::UVar(var) => Session::UVar(*var),
        }
    }
    fn unfold(&self, x: &SId) -> Self {
        self.subst(
            x,
            &Session::Mu(x.clone(), Box::new(fake_span(self.clone()))),
        )
    }
    pub fn unfold_if_mu(&self) -> Self {
        match self {
            Session::Mu(x, s) => s.unfold(x).unfold_if_mu(),
            _ => self.clone(),
        }
    }
    fn sem_eq_(&self, other: &Self, seen: &HashSet<(Session, Session)>) -> bool {
        let mut seen = seen.clone();
        if !seen.insert((self.clone(), other.clone())) {
            return true;
        } else {
            match (self, other) {
                (Session::Op(op1, t1), Session::Op(op2, t2)) => op1 == op2 && t1.sem_eq(t2),
                (Session::End(op1), Session::End(op2)) => op1 == op2,
                (Session::BorrowEnd(end1), Session::BorrowEnd(end2)) => end1 == end2,
                (Session::Choice(op1, cs1), Session::Choice(op2, cs2)) if op1 == op2 => {
                    if let Some(cs) = merge_clauses(&cs1, &cs2, false) {
                        cs.iter().all(|(_, s1, s2)| s1.sem_eq_(s2, &seen))
                    } else {
                        false
                    }
                }
                (Session::Mu(x1, s1), Session::Mu(x2, s2)) => {
                    x1.val == x2.val && s1.sem_eq_(s2, &seen)
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
                ) => first1.sem_eq_(first2, &seen) && second1.sem_eq_(second2, &seen),
                (Session::UVar(x1), Session::UVar(x2)) => x1 == x2,
                (Session::Skip, Session::Skip) => true,
                _ => false,
            }
        }
    }
    pub fn sem_eq(&self, other: &Self) -> bool {
        self.sem_eq_(other, &HashSet::new())
    }
    pub fn dual(&self) -> Self {
        match self {
            Session::Op(op, t) => Session::Op(op.dual(), t.clone()),
            Session::Choice(op, cs) => {
                let cs2: Vec<(SLabel, SSession)> = cs
                    .iter()
                    .map(|(l, s)| (l.clone(), fake_span(s.dual())))
                    .collect();
                Session::Choice(op.dual(), cs2)
            }
            Session::End(op) => Session::End(op.dual()),
            Session::BorrowEnd(op) => Session::BorrowEnd(op.dual()),
            Session::Mu(x, s) => Session::Mu(x.clone(), Box::new(fake_span(s.dual()))),
            Session::Var(x) => Session::Var(x.clone()),
            Session::Skip => Session::Skip,
            Session::Semi { first, second } => Session::Semi {
                first: Box::new(fake_span(first.dual())),
                second: Box::new(fake_span(second.dual())),
            },
            Session::UVar(_) => unreachable!(),
        }
    }

    fn concatenate(&self, other: &Session) -> Session {
        match (self, other) {
            (_, Session::Skip) => self.clone(),
            (Session::Semi { first, second }, other) => Session::Semi {
                first: first.clone(),
                second: Box::new(fake_span(second.val.concatenate(other))),
            },
            (s1, s2) => Session::Semi {
                first: Box::new(fake_span(s1.clone())),
                second: Box::new(fake_span(s2.clone())),
            },
        }
    }

    pub fn normalise(&self) -> Session {
        match self {
            Session::Semi { first, second } => {
                if first.is_only_skips() {
                    second.val.normalise()
                } else {
                    let normalised_first = first.val.normalise();
                    match normalised_first {
                        Session::Choice(op, branches) => Session::Choice(
                            op.clone(),
                            branches
                                .iter()
                                .map(|(label, branch)| {
                                    (
                                        label.clone(),
                                        fake_span(Session::Semi {
                                            first: Box::new(branch.clone()),
                                            second: second.clone(),
                                        }),
                                    )
                                })
                                .collect(),
                        ),
                        _ => normalised_first.concatenate(&second.val),
                    }
                }
            }
            Session::Mu(var, body) => {
                let normalised_body = body.val.normalise();
                let recursive_type =
                    Session::Mu(var.clone(), Box::new(fake_span(normalised_body.clone())));
                normalised_body.subst(&var.val, &recursive_type)
            }
            _ => self.clone(),
        }
    }
}

#[derive(Debug, Clone, Hash, Eq)]
pub struct TypeSemEq(pub Type);

impl PartialEq for TypeSemEq {
    fn eq(&self, other: &Self) -> bool {
        self.0.sem_eq(&other.0)
    }
}

// impl Eq for TypeSemEq {}

// Safe, but not performant
// impl Hash for TypeSemEq {
//     fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
// }

impl Expr {
    pub fn free_vars(&self) -> HashSet<Id> {
        match self {
            Expr::Const(_) => HashSet::new(),
            Expr::New(_r) => HashSet::new(),
            Expr::BorrowEnd(_, e) => e.free_vars(),
            Expr::Var(x) => HashSet::from([x.val.clone()]),
            Expr::Abs(x, e) => without(e.free_vars(), &x.val),
            Expr::App(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::Pair(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::LetPair(x, y, e1, e2) => {
                union(e1.free_vars(), without(without(e2.free_vars(), y), x))
            }
            Expr::Ann(e, _t) => e.free_vars(),
            Expr::Let(x, e1, e2) => union(e1.free_vars(), without(e2.free_vars(), x)),
            Expr::Seq(e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::Inj(_l, e) => e.free_vars(),
            Expr::CaseSum(e, cs) => {
                let mut xs = e.free_vars();
                for (_l, x, e) in cs {
                    xs = union(xs, without(e.free_vars(), &x.val));
                }
                xs
            }
            Expr::Fork(e) => e.free_vars(),
            Expr::Send(_, e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::Recv(_, e) => e.free_vars(),
            Expr::End(_l, e) => e.free_vars(),
            Expr::Op1(_op1, e) => e.free_vars(),
            Expr::Op2(_op2, e1, e2) => union(e1.free_vars(), e2.free_vars()),
            Expr::If(e, e1, e2) => union(e.free_vars(), union(e1.free_vars(), e2.free_vars())),
            Expr::Select(_l, e) => e.free_vars(),
            Expr::Branch(e) => e.free_vars(),
            Expr::LSplit(_, e) => e.free_vars(),
            Expr::RSplit(_, e) => e.free_vars(),
            Expr::LetDecl(id, _, clause, body) => {
                union(clause.body.free_vars(), without(body.free_vars(), &id.val))
            }
            Expr::TypeDef(_, _, body, _) => body.free_vars(),
            Expr::Discard(e) => e.free_vars(),
        }
    }
}

impl Clause {
    pub fn free_vars(&self) -> HashSet<Id> {
        let mut vars = self.body.free_vars();
        vars.remove(self.var_id.as_str());
        // for p in &self.pats {
        //     vars = vars.difference(&p.bound_vars()).cloned().collect();
        // }
        vars
    }
}

impl Pattern {
    pub fn bound_vars(&self) -> HashSet<Id> {
        match self {
            Pattern::Var(x) => HashSet::from([x.val.clone()]),
            Pattern::Pair(p1, p2) => union(p1.bound_vars(), p2.bound_vars()),
            //Pattern::Inj(_l, p) => p.bound_vars(),
        }
    }
}

impl Type {
    pub fn sem_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Type::Chan(s1), Type::Chan(s2)) => s1.sem_eq(s2),
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
            ) => mob1 == mob2 && m1 == m2 && p1 == p2 && t11.sem_eq(t21) && t12.sem_eq(t22),
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
            ) => m1 == m2 && t11.sem_eq(t21) && t12.sem_eq(t22),
            (Type::Variant(cs1), Type::Variant(cs2)) => {
                if let Some(cs) = merge_clauses(&cs1, &cs2, false) {
                    cs.iter().all(|(_, t1, t2)| t1.sem_eq(t2))
                } else {
                    false
                }
            }
            (Type::Unit, Type::Unit) => true,
            (Type::Int, Type::Int) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            _ => false,
        }
    }
    pub fn is_unr(&self) -> bool {
        match self {
            Type::Chan(_) => false,
            Type::Arr { mult: m, .. } => m.val == Mult::Unr,
            Type::Prod {
                first: t1,
                second: t2,
                ..
            } => t1.is_unr() && t2.is_unr(),
            Type::Variant(cs) => cs.iter().all(|(_, t)| t.is_unr()),
            Type::Unit => true,
            Type::Int => true,
            Type::Bool => true,
            Type::String => true,
        }
    }

    pub fn is_ord(&self) -> bool {
        !self.is_unr()
    }
}

impl Eff {
    pub fn lub(p1: Eff, p2: Eff) -> Eff {
        match p1 {
            Eff::Yes => Eff::Yes,
            Eff::No => p2,
        }
    }

    pub fn leq(e1: Eff, e2: Eff) -> bool {
        match (e1, e2) {
            (Eff::Yes, Eff::Yes) => true,
            (Eff::Yes, Eff::No) => false,
            (Eff::No, _) => true,
        }
    }
}

/////////////////////////// Macros ////////////////////////////

/// let s = session_type! { ... };
#[macro_export]
macro_rules! session_type {
    (@seq [$($items:expr),*] [$($curr:tt)*] ; $($rest:tt)*) => {
        session_type!(@seq [$($items,)* session_type!(@atom $($curr)+)] [] $($rest)*)
    };
    (@seq [$($items:expr),*] [] mu $var:ident . $($body:tt)+) => {
        session_type!(@fold [$($items,)* session_type!(@atom mu $var . $($body)+)])
    };
    (@seq [$($items:expr),*] [$($curr:tt)*] $tok:tt $($rest:tt)*) => {
        session_type!(@seq [$($items),*] [$($curr)* $tok] $($rest)*)
    };
    (@seq [$($items:expr),*] [$($curr:tt)*]) => {
        session_type!(@fold [$($items,)* session_type!(@atom $($curr)+)])
    };

    (@fold [$single:expr]) => {
        $single
    };
    (@fold [$first:expr, $($rest:expr),+]) => {
        session_type!(@semi $first, session_type!(@fold [$($rest),+]))
    };

    (@atom ! Int) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type Int))
    };
    (@atom ! Bool) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type Bool))
    };
    (@atom ! String) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type String))
    };
    (@atom ! Unit) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type Unit))
    };
    (@atom ! Chan ( $($sess:tt)+ )) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type Chan ( $($sess)+ )))
    };
    (@atom ! ($t:expr)) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type ($t)))
    };
    (@atom ! $t:path) => {
        session_type!(@op $crate::syntax::SessionOp::Send, session_type!(@type $t))
    };

    (@atom ? Int) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type Int))
    };
    (@atom ? Bool) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type Bool))
    };
    (@atom ? String) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type String))
    };
    (@atom ? Unit) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type Unit))
    };
    (@atom ? Chan ( $($sess:tt)+ )) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type Chan ( $($sess)+ )))
    };
    (@atom ? ($t:expr)) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type ($t)))
    };
    (@atom ? $t:path) => {
        session_type!(@op $crate::syntax::SessionOp::Recv, session_type!(@type $t))
    };

    (@atom + { $($branches:tt)* }) => {
        session_type!(@choice $crate::syntax::SessionOp::Send, session_type!(@branches [] $($branches)*))
    };
    (@atom & { $($branches:tt)* }) => {
        session_type!(@choice $crate::syntax::SessionOp::Recv, session_type!(@branches [] $($branches)*))
    };
    (@atom Close) => {
        session_type!(@end $crate::syntax::SessionOp::Send)
    };
    (@atom Wait) => {
        session_type!(@end $crate::syntax::SessionOp::Recv)
    };
    (@atom Ret) => {
        session_type!(@borrow_end $crate::syntax::SessionOp::Send)
    };
    (@atom Acq) => {
        session_type!(@borrow_end $crate::syntax::SessionOp::Recv)
    };
    (@atom Skip) => {
        session_type!(@spanned $crate::syntax::Session::Skip)
    };
    (@atom mu $var:ident . $($body:tt)+) => {
        session_type!(@mu $var, session_type!($($body)+))
    };
    (@atom $var:ident) => {
        session_type!(@spanned $crate::syntax::Session::Var(session_type!(@sid $var)))
    };
    (@atom ( $($inner:tt)+ )) => {
        session_type!($($inner)+)
    };
    (@atom $e:expr) => {
        $e
    };

    (@branches [$($acc:expr),*]) => {
        vec![$($acc),*]
    };
    (@branches [$($acc:expr),*] ,) => {
        vec![$($acc),*]
    };
    (@branches [$($acc:expr),*] $label:ident : $($rest:tt)+) => {
        session_type!(@branch_value [$($acc),*] $label [] $($rest)+)
    };
    (@branch_value [$($acc:expr),*] $label:ident [$($sess:tt)*] , $($rest:tt)*) => {
        session_type!(@branches [$($acc,)* session_type!(@branch $label [$($sess)*]) ] $($rest)*)
    };
    (@branch_value [$($acc:expr),*] $label:ident [$($sess:tt)*]) => {
        session_type!(@branches_done [$($acc,)* session_type!(@branch $label [$($sess)*]) ])
    };
    (@branch_value [$($acc:expr),*] $label:ident [$($sess:tt)*] $tok:tt $($rest:tt)*) => {
        session_type!(@branch_value [$($acc),*] $label [$($sess)* $tok] $($rest)*)
    };
    (@branches_done [$($acc:expr),*]) => {
        vec![$($acc),*]
    };
    (@branch $label:ident [$($sess:tt)+]) => {
        (session_type!(@label $label), session_type!($($sess)+))
    };
    (@label $label:ident) => {
        $crate::util::span::Spanned::new(stringify!($label).to_string(), 0..0)
    };

    (@type Int) => {
        $crate::util::span::Spanned::new($crate::syntax::Type::Int, 0..0)
    };
    (@type Bool) => {
        $crate::util::span::Spanned::new($crate::syntax::Type::Bool, 0..0)
    };
    (@type String) => {
        $crate::util::span::Spanned::new($crate::syntax::Type::String, 0..0)
    };
    (@type Unit) => {
        $crate::util::span::Spanned::new($crate::syntax::Type::Unit, 0..0)
    };
    (@type Chan ( $($sess:tt)+ )) => {
        $crate::util::span::Spanned::new(
            $crate::syntax::Type::Chan(session_type!($($sess)+).val),
            0..0,
        )
    };
    (@type ($t:expr)) => {
        $crate::util::span::Spanned::new($t, 0..0)
    };
    (@type $t:path) => {
        $crate::util::span::Spanned::new($t, 0..0)
    };

    (@spanned $val:expr) => {
        $crate::util::span::Spanned::new($val, 0..0)
    };
    (@semi $first:expr, $second:expr) => {
        session_type!(@spanned $crate::syntax::Session::Semi {
            first: Box::new($first),
            second: Box::new($second),
        })
    };
    (@op $op:expr, $ty:expr) => {
        session_type!(@spanned $crate::syntax::Session::Op($op, Box::new($ty)))
    };
    (@choice $op:expr, $branches:expr) => {
        session_type!(@spanned $crate::syntax::Session::Choice($op, $branches))
    };
    (@end $op:expr) => {
        session_type!(@spanned $crate::syntax::Session::End($op))
    };
    (@borrow_end $op:expr) => {
        session_type!(@spanned $crate::syntax::Session::BorrowEnd($op))
    };
    (@mu $var:ident, $body:expr) => {
        session_type!(@spanned $crate::syntax::Session::Mu(
            session_type!(@sid $var),
            Box::new($body),
        ))
    };
    (@sid $var:ident) => {
        $crate::util::span::Spanned::new(stringify!($var).to_string(), 0..0)
    };

    ($($tokens:tt)+) => {
        session_type!(@seq [] [] $($tokens)+)
    };
}

#[cfg(test)]
mod session_type_tests {
    use super::{SSession, Session, SessionOp, Type};
    use crate::util::span::Spanned;

    fn spanned_session(session: Session) -> SSession {
        Spanned::new(session, 0..0)
    }

    fn session_op(session_op: SessionOp, typ: Type) -> Session {
        Session::Op(session_op, Box::new(Spanned::new(typ, 0..0)))
    }

    #[test]
    fn session_type_send_recv_semi() {
        let got = session_type!(!Int; ?Bool; Close);
        let expected = spanned_session(Session::Semi {
            first: Box::new(spanned_session(Session::Op(
                SessionOp::Send,
                Box::new(Spanned::new(Type::Int, 0..0)),
            ))),
            second: Box::new(spanned_session(Session::Semi {
                first: Box::new(spanned_session(Session::Op(
                    SessionOp::Recv,
                    Box::new(Spanned::new(Type::Bool, 0..0)),
                ))),
                second: Box::new(spanned_session(Session::End(SessionOp::Send))),
            })),
        });

        assert_eq!(got, expected);
    }

    #[test]
    fn session_type_semi_parentheses() {
        let got = session_type!(!Int; (?Bool; !String));
        let expected = spanned_session(Session::Semi {
            first: Box::new(spanned_session(session_op(SessionOp::Send, Type::Int))),
            second: Box::new(spanned_session(Session::Semi {
                first: Box::new(spanned_session(session_op(SessionOp::Recv, Type::Bool))),
                second: Box::new(spanned_session(session_op(SessionOp::Send, Type::String))),
            })),
        });

        assert_eq!(got, expected);
    }

    #[test]
    fn session_type_choice_offer_select() {
        let got = session_type!(+{ left: !Int, right: ?String });
        let expected = spanned_session(Session::Choice(
            SessionOp::Send,
            vec![
                (
                    Spanned::new("left".to_string(), 0..0),
                    spanned_session(Session::Op(
                        SessionOp::Send,
                        Box::new(Spanned::new(Type::Int, 0..0)),
                    )),
                ),
                (
                    Spanned::new("right".to_string(), 0..0),
                    spanned_session(Session::Op(
                        SessionOp::Recv,
                        Box::new(Spanned::new(Type::String, 0..0)),
                    )),
                ),
            ],
        ));

        assert_eq!(got, expected);
    }

    #[test]
    fn session_type_recursive_and_vars() {
        let got = session_type!(mu X. ?Int; X);
        let expected = spanned_session(Session::Mu(
            Spanned::new("X".to_string(), 0..0),
            Box::new(spanned_session(Session::Semi {
                first: Box::new(spanned_session(Session::Op(
                    SessionOp::Recv,
                    Box::new(Spanned::new(Type::Int, 0..0)),
                ))),
                second: Box::new(spanned_session(Session::Var(Spanned::new(
                    "X".to_string(),
                    0..0,
                )))),
            })),
        ));

        assert_eq!(got, expected);
    }

    #[test]
    fn session_type_borrow_and_skip() {
        let got = session_type!(Ret; Skip; Acq; Wait);
        let expected = spanned_session(Session::Semi {
            first: Box::new(spanned_session(Session::BorrowEnd(SessionOp::Send))),
            second: Box::new(spanned_session(Session::Semi {
                first: Box::new(spanned_session(Session::Skip)),
                second: Box::new(spanned_session(Session::Semi {
                    first: Box::new(spanned_session(Session::BorrowEnd(SessionOp::Recv))),
                    second: Box::new(spanned_session(Session::End(SessionOp::Recv))),
                })),
            })),
        });

        assert_eq!(got, expected);
    }

    #[test]
    fn session_type_verbatim_unknown_tokens() {
        let sess_type = spanned_session(Session::Op(
            SessionOp::Send,
            Box::new(Spanned::new(Type::Int, 0..0)),
        ));

        let got = session_type! { Acq; (sess_type.clone(); Wait) };
        let expected = spanned_session(Session::Semi {
            first: Box::new(spanned_session(Session::BorrowEnd(SessionOp::Recv))),
            second: Box::new(spanned_session(Session::Semi {
                first: Box::new(sess_type.clone()),
                second: Box::new(spanned_session(Session::End(SessionOp::Recv))),
            })),
        });

        assert_eq!(got, expected);
    }
}
