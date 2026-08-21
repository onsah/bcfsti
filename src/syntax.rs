use crate::{
    type_alias::AliasEnv,
    util::span::{Spanned, fake_span},
};
use std::{collections::HashSet, hash::Hash, iter};

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
pub type PVarId = Label;
pub type SPVarId = Spanned<PVarId>;

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
    PVar {
        id: PVarId,
        dual: bool,
    },
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
            Session::PVar { .. } => todo!(),
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
            Session::PVar { .. } => HashSet::new(),
        }
    }

    pub fn poly_variables<'a>(&'a self) -> Box<dyn Iterator<Item = PVarId> + 'a> {
        match self {
            Session::Skip => Box::new(iter::empty()),
            Session::Semi { first, second } => {
                Box::new(first.poly_variables().chain(second.poly_variables()))
            }
            Session::End(_) => Box::new(iter::empty()),
            Session::BorrowEnd(_) => Box::new(iter::empty()),
            Session::Op(_, t) => t.poly_variables_under_prod_and_variant(),
            Session::Choice(_, cs) => Box::new(cs.iter().flat_map(|(_, s)| s.poly_variables())),
            Session::Mu(_, body) => body.poly_variables(),
            Session::Var(_) => Box::new(iter::empty()),
            Session::UVar(_) => Box::new(iter::empty()),
            Session::PVar { id, .. } => Box::new(iter::once(id.clone())),
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
            Session::PVar { .. } => todo!(),
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
            Session::PVar { .. } => todo!(),
        }
    }
}

impl SSession {
    pub fn to_type(self) -> SType {
        Spanned::new(Type::Chan(self.val), self.span)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuantificationType {
    Universal,
    Existential,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    // Quantifiers
    Abstraction {
        typ: QuantificationType,
        quantification: SQuantification,
        ty: Box<SType>,
    },
    PVar {
        id: PVarId,
        dual: bool,
    },
    // Session Types
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Quantification {
    pub id: SPVarId,
    pub kind: SKind,
    pub qualifications: Vec<SQualification>,
}
pub type SQuantification = Spanned<Quantification>;

impl Type {
    /// Closed type means it has no unification variables.
    pub fn is_closed(&self) -> bool {
        match self {
            Type::Chan(s) => s.is_closed(),
            Type::Arr { param, ret, .. } => param.is_closed() && ret.is_closed(),
            Type::Prod { first, second, .. } => first.is_closed() && second.is_closed(),
            Type::Variant(cs) => cs.iter().all(|(_, t)| t.is_closed()),
            Type::Unit | Type::Int | Type::Bool | Type::String => true,
            Type::Abstraction { ty, .. } => ty.is_closed(),
            Type::PVar { .. } => true,
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
            Type::Abstraction { ty, .. } => ty.unification_variables(),
            Type::PVar { .. } => HashSet::new(),
        }
    }

    pub fn poly_variables<'a>(&'a self) -> Box<dyn Iterator<Item = PVarId> + 'a> {
        match self {
            Type::Chan(session) => session.poly_variables(),
            Type::Arr { param, ret, .. } => {
                Box::new(param.poly_variables().chain(ret.poly_variables()))
            }
            Type::Prod { first, second, .. } => {
                Box::new(first.poly_variables().chain(second.poly_variables()))
            }
            Type::Variant(cs) => Box::new(cs.iter().flat_map(|(_, t)| t.poly_variables())),
            Type::Unit | Type::Int | Type::Bool | Type::String => Box::new(iter::empty()),
            Type::Abstraction {
                quantification, ty, ..
            } => Box::new(
                ty.poly_variables()
                    .filter(move |id1| quantification.id.as_str() != id1.as_str()),
            ),
            Type::PVar { id, .. } => Box::new(iter::once(id.clone())),
        }
    }

    pub fn poly_variables_under_prod_and_variant<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = PVarId> + 'a> {
        match self {
            Type::Chan(Session::PVar { id, .. }) => Box::new(iter::once(id.clone())),
            Type::Prod { first, second, .. } => Box::new(
                first
                    .poly_variables_under_prod_and_variant()
                    .chain(second.poly_variables_under_prod_and_variant()),
            ),
            Type::Variant(cs) => Box::new(
                cs.iter()
                    .flat_map(|(_, t)| t.poly_variables_under_prod_and_variant()),
            ),
            Type::Unit
            | Type::Int
            | Type::Bool
            | Type::String
            | Type::Arr { .. }
            | Type::Chan(_) => Box::new(iter::empty()),
            Type::Abstraction {
                quantification, ty, ..
            } => Box::new(
                ty.poly_variables_under_prod_and_variant()
                    .filter(move |id1| quantification.id.as_str() != id1.as_str()),
            ),
            Type::PVar { id, .. } => Box::new(iter::once(id.clone())),
        }
    }

    pub fn normalise(&self, alias_env: &AliasEnv) -> Type {
        match self {
            Type::Chan(session) => Type::Chan(session.normalise(alias_env)),
            _ => self.clone(),
        }
    }

    pub fn subst_poly(&self, var_id: &PVarId, ty: &SType) -> Type {
        match self {
            Type::PVar { id, dual } => {
                if id == var_id {
                    let ty = ty.val.clone();
                    if *dual { ty.dual() } else { ty }
                } else {
                    self.clone()
                }
            }
            Type::Abstraction {
                typ,
                quantification,
                ty,
            } => {
                if &quantification.id.val != var_id {
                    Type::Abstraction {
                        typ: *typ,
                        quantification: quantification.clone(),
                        ty: Box::new(fake_span(ty.val.subst_poly(var_id, ty))),
                    }
                } else {
                    panic!("Polymorphic variable shadowing is not allowed.")
                }
            }
            Type::Chan(session) => Type::Chan(session.subst_poly(var_id, ty)),
            Type::Arr {
                mob,
                mult,
                eff,
                param,
                ret,
            } => Type::Arr {
                mob: mob.clone(),
                mult: mult.clone(),
                eff: eff.clone(),
                param: Box::new(fake_span(param.val.subst_poly(var_id, ty))),
                ret: Box::new(fake_span(ret.val.subst_poly(var_id, ty))),
            },
            Type::Prod {
                mult,
                first,
                second,
            } => Type::Prod {
                mult: mult.clone(),
                first: Box::new(fake_span(first.val.subst_poly(var_id, ty))),
                second: Box::new(fake_span(second.val.subst_poly(var_id, ty))),
            },
            Type::Variant(items) => Type::Variant(
                items
                    .iter()
                    .map(|(label, ty)| (label.clone(), fake_span(ty.val.subst_poly(var_id, ty))))
                    .collect(),
            ),
            Type::Unit | Type::Int | Type::Bool | Type::String => self.clone(),
        }
    }

    fn dual(&self) -> Self {
        todo!()
    }
}

impl SType {
    pub fn from_session(session: SSession) -> Self {
        Spanned::new(Type::Chan(session.val), session.span)
    }
}

impl Qualification {
    pub fn subst_poly(&self, var_id: &PVarId, ty: &SType) -> Qualification {
        match self {
            Qualification::Unr(t) => Qualification::Unr(fake_span(t.val.subst_poly(var_id, ty))),
            Qualification::Mobile(t) => {
                Qualification::Mobile(fake_span(t.val.subst_poly(var_id, ty)))
            }
            Qualification::Bounded(s) => {
                Qualification::Bounded(fake_span(s.val.subst_poly(var_id, ty)))
            }
            Qualification::New(s) => Qualification::New(fake_span(s.val.subst_poly(var_id, ty))),
            Qualification::Dualable(s) => {
                Qualification::Dualable(fake_span(s.val.subst_poly(var_id, ty)))
            }
            Qualification::NonSkip(s) => {
                Qualification::NonSkip(fake_span(s.val.subst_poly(var_id, ty)))
            }
            Qualification::Equiv(t1, t2) => Qualification::Equiv(
                fake_span(t1.val.subst_poly(var_id, ty)),
                fake_span(t2.val.subst_poly(var_id, ty)),
            ),
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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub enum Kind {
    Type,
    Session,
}
pub type SKind = Spanned<Kind>;

impl Kind {
    pub fn is_subkind_of(&self, other: &Kind) -> bool {
        match (self, other) {
            (Kind::Type, Kind::Type) => true,
            (Kind::Session, Kind::Type) => true,
            (Kind::Session, Kind::Session) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Qualification {
    Unr(SType),
    Mobile(SType),
    Bounded(SSession),
    New(SSession),
    Dualable(SSession),
    NonSkip(SSession),
    Equiv(SType, SType),
}
pub type SQualification = Spanned<Qualification>;

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

    Let(SId, Box<SExpr>, Box<SExpr>, Option<SType>),
    LetDecl(
        SId,
        SType,
        Option<SQuantification>,
        Box<SClause>,
        Box<SExpr>,
    ),
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

    TyApp(Box<SExpr>, SType),
    TyAbs {
        quantification: SQuantification,
        expr: Box<SExpr>,
    },
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
            Session::Semi { first, second } => Self::Semi {
                first: Box::new(fake_span(first.subst(x, s_new))),
                second: Box::new(fake_span(second.subst(x, s_new))),
            },
            Session::End(_)
            | Session::BorrowEnd(_)
            | Session::Skip
            | Session::UVar(_)
            | Session::PVar { .. } => self.clone(),
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
            Session::PVar { id, dual } => Session::PVar {
                id: id.clone(),
                dual: !dual,
            },
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

    pub fn normalise(&self, alias_env: &AliasEnv) -> Session {
        match self {
            Session::Semi { first, second } => {
                if first.is_only_skips() {
                    second.val.normalise(alias_env)
                } else {
                    let normalised_first = first.val.normalise(alias_env);
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
                let normalised_body = body.val.normalise(alias_env);
                let recursive_type =
                    Session::Mu(var.clone(), Box::new(fake_span(normalised_body.clone())));
                normalised_body.subst(&var.val, &recursive_type)
            }
            Session::Var(id) => {
                let session = alias_env.get(&id.val).expect(
                    "Bug: well formed types must have their free recursion variables defined in the alias environment",
                );
                session.val.normalise(alias_env)
            }
            _ => self.clone(),
        }
    }
}

impl Session {
    pub fn subst_poly(&self, var_id: &PVarId, ty: &SType) -> Session {
        match self {
            Session::PVar { id, dual } => {
                if id == var_id {
                    let ty = ty.val.clone();
                    let Type::Chan(session) = ty else {
                        panic!("Polymorphic variable substitution must be a session type.");
                    };
                    if *dual { session.dual() } else { session }
                } else {
                    self.clone()
                }
            }
            Session::Semi { first, second } => Session::Semi {
                first: Box::new(fake_span(first.val.subst_poly(var_id, ty))),
                second: Box::new(fake_span(second.val.subst_poly(var_id, ty))),
            },
            Session::Op(session_op, payload) => Session::Op(
                session_op.clone(),
                Box::new(fake_span(payload.val.subst_poly(var_id, ty))),
            ),
            Session::Choice(session_op, items) => Session::Choice(
                session_op.clone(),
                items
                    .iter()
                    .map(|(label, s)| (label.clone(), fake_span(s.val.subst_poly(var_id, ty))))
                    .collect(),
            ),
            // Recursion variables are separate than polymorphic variables, so we don't substitute them.
            Session::Mu(id, body) => Session::Mu(
                id.clone(),
                Box::new(fake_span(body.val.subst_poly(var_id, ty))),
            ),
            Session::Skip
            | Session::End(_)
            | Session::BorrowEnd(_)
            | Session::Var(_)
            | Session::UVar(_) => self.clone(),
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
            Expr::Let(x, e1, e2, _) => union(e1.free_vars(), without(e2.free_vars(), x)),
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
            Expr::LetDecl(id, _, _, clause, body) => {
                union(clause.body.free_vars(), without(body.free_vars(), &id.val))
            }
            Expr::TypeDef(_, _, body, _) => body.free_vars(),
            Expr::Discard(e) => e.free_vars(),
            Expr::TyApp(e, _) => e.free_vars(),
            Expr::TyAbs {
                quantification, // TODO: qualification free vars
                expr,
                ..
            } => expr.free_vars(),
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
            (
                Type::PVar {
                    id: id1,
                    dual: dual1,
                },
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
            ) => typ1 == typ2 && q1 == q2 && ty1.sem_eq(ty2),
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
            Type::Abstraction { .. } => todo!("Delete this function"),
            Type::PVar { .. } => todo!("Delete this function"),
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
