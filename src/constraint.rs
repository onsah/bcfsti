use std::collections::{HashMap, HashSet};

use crate::{
    syntax::{SExpr, SId, SType, Session, Type, UVarId},
    type_context::Ctx,
    util::span::{Spanned, fake_span},
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraints {
    equivalences: Equivalences,
    mobilities: Mobilities,
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Equivalences(HashSet<(SType, SType)>);

#[derive(Debug, PartialEq, Eq, Clone)]
struct Mobilities(Vec<(SExpr, HashSet<SId>, Ctx)>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConstraintSolutionError {
    AssignmentNotMobile { expr: SExpr, id: SId, ctx: Ctx },
}

type Assignments = HashMap<UVarId, Session>;

impl Constraints {
    pub fn empty() -> Constraints {
        Constraints {
            equivalences: Equivalences::new(),
            mobilities: Mobilities::new(),
        }
    }

    pub fn from_equivalences(equivalences: HashSet<(SType, SType)>) -> Constraints {
        Constraints {
            equivalences: Equivalences::from(equivalences),
            mobilities: Mobilities::new(),
        }
    }

    pub fn join(self, other: Constraints) -> Constraints {
        Constraints {
            equivalences: self.equivalences.join(other.equivalences),
            mobilities: self.mobilities.join(other.mobilities),
        }
    }

    pub fn add(&mut self, ty1: SType, ty2: SType) {
        self.equivalences.add((ty1, ty2));
    }

    pub fn check_mobility(&mut self, expr: SExpr, ids: HashSet<SId>, ctx: Ctx) {
        self.mobilities.add(expr, ids, ctx);
    }

    pub fn iter(&self) -> impl Iterator<Item = &(SType, SType)> {
        self.equivalences.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = (SType, SType)> {
        self.equivalences.into_iter()
    }

    /// Solve the constraints by propagating assignments to unification variables until a fixed point is reached.
    /// If there is still no solution for some unification variables, `Skip` is substituted instead.
    pub fn solve(self) -> Result<Constraints, ConstraintSolutionError> {
        let (assignments, remaining_equivalences) = self.equivalences.infer_assignments();
        let equivalences = remaining_equivalences.subst(&assignments);

        if !equivalences.is_closed() {
            return Constraints {
                equivalences,
                mobilities: self.mobilities,
            }
            .solve();
        }

        self.mobilities.check(&assignments)?;
        Ok(Constraints {
            equivalences,
            mobilities: Mobilities::new(),
        })
    }

    fn subst(ty: SType, assignments: &Assignments) -> SType {
        let span = ty.span.clone();
        let val = match ty.val {
            Type::Chan(session) => Type::Chan(Self::subst_session(session, assignments)),
            Type::Bool | Type::Int | Type::String => ty.val,
            Type::Prod {
                mult,
                first,
                second,
            } => Type::Prod {
                mult,
                first: Box::new(Self::subst(*first, assignments)),
                second: Box::new(Self::subst(*second, assignments)),
            },
            Type::Arr {
                mob,
                mult,
                eff,
                param,
                ret,
            } => Type::Arr {
                mob,
                mult,
                eff,
                param: Box::new(Self::subst(*param, assignments)),
                ret: Box::new(Self::subst(*ret, assignments)),
            },
            Type::Variant(items) => Type::Variant(
                items
                    .into_iter()
                    .map(|(label, ty)| (label, Self::subst(ty, assignments)))
                    .collect(),
            ),
            Type::Unit => Type::Unit,
        };
        Spanned::new(val, span)
    }

    fn subst_session(ty: Session, assignments: &Assignments) -> Session {
        match ty {
            Session::UVar(var) => {
                if let Some(ty) = assignments.get(&var) {
                    ty.clone()
                } else {
                    Session::UVar(var)
                }
            }
            Session::Skip => Session::Skip,
            Session::Semi { first, second } => Session::Semi {
                first: Box::new(fake_span(Self::subst_session(first.val, assignments))),
                second: Box::new(fake_span(Self::subst_session(second.val, assignments))),
            },
            Session::End(session_op) => Session::End(session_op),
            Session::BorrowEnd(session_op) => Session::BorrowEnd(session_op),
            Session::Op(session_op, ty) => {
                Session::Op(session_op, Box::new(Self::subst(*ty, assignments)))
            }
            Session::Choice(session_op, items) => Session::Choice(
                session_op,
                items
                    .into_iter()
                    .map(|(label, s)| (label, fake_span(Self::subst_session(s.val, assignments))))
                    .collect(),
            ),
            Session::Mu(id, body) => Session::Mu(
                id,
                Box::new(fake_span(Self::subst_session(body.val, assignments))),
            ),
            Session::Var(id) => Session::Var(id),
        }
    }

    fn subst_ctx(ctx: &mut Ctx, assignments: &Assignments) {
        ctx.map_binds_mut(&mut |_, ty| {
            *ty = Constraints::subst(fake_span(ty.clone()), assignments).val;
        })
    }
}

impl Equivalences {
    pub fn new() -> Equivalences {
        Equivalences(HashSet::new())
    }

    fn join(self, other: Equivalences) -> Equivalences {
        let mut equivalences = self.0;
        for constraint in other.0 {
            equivalences.insert(constraint);
        }
        Equivalences(equivalences)
    }

    fn add(&mut self, constraint: (SType, SType)) {
        self.0.insert(constraint);
    }

    fn iter(&self) -> impl Iterator<Item = &(SType, SType)> {
        self.0.iter()
    }

    fn into_iter(self) -> impl Iterator<Item = (SType, SType)> {
        self.0.into_iter()
    }

    /// Infer assignments for unification variables from the equivalences.
    /// Returns a tuple of the assignments and the remaining equivalences that didn't yield an assignment.
    fn infer_assignments(self) -> (Assignments, Self) {
        let mut assignments: Assignments = HashMap::new();
        let mut other = Self::new();
        for (ty1, ty2) in self.into_iter() {
            match Self::extract_bare_assignment(&ty1.val, &ty2.val)
                .or(Self::extract_bare_assignment(&ty2.val, &ty1.val))
            {
                Some((uvar_id, session)) => {
                    if !assignments.contains_key(&uvar_id) {
                        assignments.insert(uvar_id, session);
                    } else {
                        other.add((ty1, ty2));
                    }
                }
                None => {
                    match Self::extract_nested_assignments(&ty1.val, &ty2.val)
                        .or(Self::extract_nested_assignments(&ty2.val, &ty1.val))
                    {
                        Some(extracted) => {
                            for (var, session) in extracted {
                                assignments.entry(var).or_insert(session);
                            }
                        }
                        None => {
                            other.add((ty1, ty2));
                        }
                    }
                }
            }
        }

        // If there are still unsolved variables with no more assignments,
        // substitute Skip for them
        let assignments = if assignments.is_empty() {
            other
                .unsolved_variables()
                .into_iter()
                .map(|var| (var, Session::Skip))
                .collect()
        } else {
            assignments
        };

        (assignments, other)
    }

    /// If `lhs` is a channel carrying a bare unification variable and `rhs` is a channel
    /// carrying a closed session, return the variable and the type pair
    fn extract_bare_assignment(lhs: &Type, rhs: &Type) -> Option<(UVarId, Session)> {
        if let Type::Chan(Session::UVar(var)) = lhs
            && let Type::Chan(session) = rhs
            && session.is_closed()
        {
            Some((*var, session.clone()))
        } else {
            None
        }
    }

    /// Attempt to structurally match `ty_uvars` (which contains unification variables) against
    /// `ty_closed` (which is closed). When the structures match, every unification variable in
    /// `ty_uvars` is assigned the corresponding sub-part of `ty_closed`. Returns `None` if the
    /// structures do not match.
    fn extract_nested_assignments(ty_uvars: &Type, ty_closed: &Type) -> Option<Assignments> {
        if !(ty_closed.is_closed() && !ty_uvars.is_closed()) {
            return None;
        }

        let mut assignments = Assignments::new();
        if Self::match_types(ty_uvars, ty_closed, &mut assignments) {
            Some(assignments)
        } else {
            None
        }
    }

    fn match_types(ty_uvars: &Type, ty_closed: &Type, assignments: &mut Assignments) -> bool {
        match (ty_uvars, ty_closed) {
            (Type::Chan(s1), Type::Chan(s2)) => Self::match_sessions(s1, s2, assignments),
            (
                Type::Prod {
                    mult: m1,
                    first: f1,
                    second: s1,
                },
                Type::Prod {
                    mult: m2,
                    first: f2,
                    second: s2,
                },
            ) => {
                m1 == m2
                    && Self::match_types(&f1.val, &f2.val, assignments)
                    && Self::match_types(&s1.val, &s2.val, assignments)
            }
            (
                Type::Arr {
                    mob: mob1,
                    mult: mult1,
                    eff: eff1,
                    param: p1,
                    ret: r1,
                },
                Type::Arr {
                    mob: mob2,
                    mult: mult2,
                    eff: eff2,
                    param: p2,
                    ret: r2,
                },
            ) => {
                mob1 == mob2
                    && mult1 == mult2
                    && eff1 == eff2
                    && Self::match_types(&p1.val, &p2.val, assignments)
                    && Self::match_types(&r1.val, &r2.val, assignments)
            }
            (Type::Variant(cs1), Type::Variant(cs2)) => {
                cs1.len() == cs2.len()
                    && cs1.iter().zip(cs2.iter()).all(|((l1, t1), (l2, t2))| {
                        l1 == l2 && Self::match_types(&t1.val, &t2.val, assignments)
                    })
            }
            (Type::Int, Type::Int)
            | (Type::Bool, Type::Bool)
            | (Type::String, Type::String)
            | (Type::Unit, Type::Unit) => true,
            _ => false,
        }
    }

    fn match_sessions(
        s_uvars: &Session,
        s_closed: &Session,
        assignments: &mut Assignments,
    ) -> bool {
        match (s_uvars, s_closed) {
            (Session::UVar(var), s) => match assignments.get(var) {
                Some(existing) => existing == s,
                None => {
                    assignments.insert(*var, s.clone());
                    true
                }
            },
            (Session::Skip, Session::Skip) => true,
            (
                Session::Semi {
                    first: f1,
                    second: s1,
                },
                Session::Semi {
                    first: f2,
                    second: s2,
                },
            ) => {
                Self::match_sessions(&f1.val, &f2.val, assignments)
                    && Self::match_sessions(&s1.val, &s2.val, assignments)
            }
            (Session::End(a), Session::End(b)) => a == b,
            (Session::BorrowEnd(a), Session::BorrowEnd(b)) => a == b,
            (Session::Op(op1, t1), Session::Op(op2, t2)) => {
                op1 == op2 && Self::match_types(&t1.val, &t2.val, assignments)
            }
            (Session::Choice(op1, cs1), Session::Choice(op2, cs2)) => {
                op1 == op2
                    && cs1.len() == cs2.len()
                    && cs1.iter().zip(cs2.iter()).all(|((l1, c1), (l2, c2))| {
                        l1 == l2 && Self::match_sessions(&c1.val, &c2.val, assignments)
                    })
            }
            (Session::Mu(id1, b1), Session::Mu(id2, b2)) => {
                id1 == id2 && Self::match_sessions(&b1.val, &b2.val, assignments)
            }
            (Session::Var(id1), Session::Var(id2)) => id1 == id2,
            _ => false,
        }
    }

    fn is_closed(&self) -> bool {
        self.iter()
            .all(|(ty1, ty2)| ty1.val.is_closed() && ty2.val.is_closed())
    }

    fn unsolved_variables(&self) -> HashSet<UVarId> {
        let mut result = HashSet::new();
        for (ty1, ty2) in self.iter() {
            result.extend(ty1.val.unification_variables());
            result.extend(ty2.val.unification_variables());
        }
        result
    }

    /// Substitute the assignments into the equivalences, and return new ones
    fn subst(&self, assignments: &Assignments) -> Self {
        let mut new_equivalences = HashSet::new();
        for (ty1, ty2) in self.0.iter() {
            let ty1 = Constraints::subst(ty1.clone(), assignments);
            let ty2 = Constraints::subst(ty2.clone(), assignments);
            new_equivalences.insert((ty1, ty2));
        }
        Equivalences(new_equivalences)
    }
}

impl From<HashSet<(SType, SType)>> for Equivalences {
    fn from(equivalences: HashSet<(SType, SType)>) -> Self {
        Equivalences(equivalences)
    }
}

impl Mobilities {
    fn new() -> Mobilities {
        Mobilities(Vec::new())
    }

    fn join(mut self, mut other: Mobilities) -> Mobilities {
        self.0.append(&mut other.0);
        self
    }

    fn add(&mut self, expr: SExpr, ids: HashSet<SId>, ctx: Ctx) {
        self.0.push((expr, ids, ctx));
    }

    fn check(mut self, assignments: &Assignments) -> Result<(), ConstraintSolutionError> {
        for (expr, ids, ctx) in self.0.iter_mut() {
            Constraints::subst_ctx(ctx, &assignments);
            let binds = ctx.binds();
            for id in ids.iter() {
                if !binds.get(&id.val).unwrap().is_mobile() {
                    return Err(ConstraintSolutionError::AssignmentNotMobile {
                        expr: expr.clone(),
                        id: id.clone(),
                        ctx: ctx.clone(),
                    });
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{
        constraint::Constraints,
        session_type,
        syntax::{Eff, Mob, Mult, Session, Type},
        util::span::fake_span,
    };

    #[test]
    fn test_simple_cs() {
        let uvar1 = fake_span(Type::Chan(Session::UVar(1)));
        let uvar2 = fake_span(Type::Chan(Session::UVar(2)));

        let session1 = fake_span(Type::Chan(session_type! { !Int }.val));
        let session2 = fake_span(Type::Chan(session_type! { ?Int }.val));

        let mut constraints = Constraints::empty();
        constraints.add(uvar1.clone(), uvar2.clone());
        constraints.add(uvar1.clone(), session1.clone());
        constraints.add(uvar2.clone(), session2.clone());

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(
                vec![(session1.clone(), session2.clone())]
                    .into_iter()
                    .collect()
            ))
        );
    }

    #[test]
    fn test_two_iterations() {
        let uvar1 = fake_span(Type::Chan(Session::UVar(1)));
        let uvar2 = fake_span(Type::Chan(Session::UVar(2)));
        let uvar3 = fake_span(Type::Chan(Session::UVar(3)));

        let session1 = fake_span(Type::Chan(session_type! { !Int }.val));
        let session2 = fake_span(Type::Chan(session_type! { ?Int }.val));

        let mut constraints = Constraints::empty();
        constraints.add(uvar1.clone(), uvar2.clone());
        constraints.add(uvar2.clone(), uvar3.clone());
        constraints.add(uvar3.clone(), session1.clone());
        constraints.add(uvar1.clone(), session2.clone());

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(
                vec![(session2, session1)].into_iter().collect()
            ))
        );
    }

    #[test]
    fn test_unsolvable_constraints() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(uvar1.clone())),
            fake_span(Type::Chan(uvar2.clone())),
        );

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(session_type! { Skip }.val)),
                fake_span(Type::Chan(session_type! { Skip }.val))
            )])))
        );
    }

    #[test]
    fn test_prod() {
        let uvar1 = fake_span(Type::Chan(Session::UVar(1)));
        let uvar2 = fake_span(Type::Chan(Session::UVar(2)));

        let mut constraints = Constraints::empty();
        constraints.add(
            uvar1.clone(),
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Int)),
                        second: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            )),
        );
        constraints.add(
            uvar2.clone(),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::from_equivalences(HashSet::new())));

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(uvar1.clone().val)),
                        second: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    })
                }
                .val,
            )),
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        second: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            )),
        );
        constraints.add(
            uvar1.clone(),
            fake_span(Type::Chan(session_type! { !Int }.val)),
        );
        constraints.add(
            uvar2.clone(),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(
                    session_type! { !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        second: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                )),
                fake_span(Type::Chan(
                    session_type! { !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        second: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                )),
            ),])))
        );
    }

    #[test]
    fn test_arr() {
        let uvar1 = fake_span(Type::Chan(Session::UVar(1)));
        let uvar2 = fake_span(Type::Chan(Session::UVar(2)));

        let mut constraints = Constraints::empty();
        constraints.add(
            uvar1.clone(),
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Int)),
                        ret: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            )),
        );
        constraints.add(
            uvar2.clone(),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::from_equivalences(HashSet::new())));

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(uvar1.clone().val)),
                        ret: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    })
                }
                .val,
            )),
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        ret: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            )),
        );
        constraints.add(
            uvar1.clone(),
            fake_span(Type::Chan(session_type! { !Int }.val)),
        );
        constraints.add(
            uvar2.clone(),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(
                    session_type! { !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        ret: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                )),
                fake_span(Type::Chan(
                    session_type! { !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        ret: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                )),
            ),])))
        );
    }

    #[test]
    fn test_variant() {
        let uvar1 = fake_span(Type::Chan(Session::UVar(1)));
        let uvar2 = fake_span(Type::Chan(Session::UVar(2)));

        let mut constraints = Constraints::empty();
        constraints.add(
            uvar1.clone(),
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Int)),
                        (fake_span("Right".to_string()), fake_span(uvar2.clone().val))
                    ]))
                }
                .val,
            )),
        );
        constraints.add(
            uvar2.clone(),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::from_equivalences(HashSet::new())));

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(uvar1.clone().val)),
                        (fake_span("Right".to_string()), fake_span(Type::Chan(session_type! { ?String }.val)))
                    ]))
                }
                .val,
            )),
            fake_span(Type::Chan(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Chan(session_type! { !Int }.val))),
                        (fake_span("Right".to_string()), fake_span(uvar2.clone().val))
                    ]))
                }
                .val,
            )),
        );
        constraints.add(
            uvar1.clone(),
            fake_span(Type::Chan(session_type! { !Int }.val)),
        );
        constraints.add(
            uvar2.clone(),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(
                    session_type! { !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Chan(session_type! { !Int }.val))),
                        (fake_span("Right".to_string()), fake_span(Type::Chan(session_type! { ?String }.val)))
                    ])) }
                    .val
                )),
                fake_span(Type::Chan(
                    session_type! { !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Chan(session_type! { !Int }.val))),
                        (fake_span("Right".to_string()), fake_span(Type::Chan(session_type! { ?String }.val)))
                    ])) }
                    .val
                )),
            ),])))
        );
    }

    #[test]
    fn test_semicolon() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! { fake_span(Session::UVar(1)); !Int }.val,
            )),
            fake_span(Type::Chan(
                session_type! { ?String; fake_span(Session::UVar(2)) }.val,
            )),
        );
        constraints.add(
            fake_span(Type::Chan(uvar1.clone())),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );
        constraints.add(
            fake_span(Type::Chan(uvar2.clone())),
            fake_span(Type::Chan(session_type! { !Int }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(session_type! { ?String; !Int }.val)),
                fake_span(Type::Chan(session_type! { ?String; !Int }.val)),
            )])))
        );
    }

    #[test]
    fn test_choice() {
        let uvar1 = Session::UVar(1);

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! { +{ left: !Int, right: fake_span(uvar1.clone()) } }.val,
            )),
            fake_span(Type::Chan(
                session_type! { +{ left: !Int, right: ?String } }.val,
            )),
        );

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_recursion() {
        let uvar1 = Session::UVar(1);

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! { mu X. !Int; fake_span(uvar1.clone()) }.val,
            )),
            fake_span(Type::Chan(session_type! { mu X. !Int; X }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_complex_composite() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        // mu X. +{ a: !Int; X, b: !Bool; fake_span(uvar1) }
        constraints.add(
            fake_span(Type::Chan(
                session_type! { mu X. +{ a: !Int; X, b: !Bool; fake_span(uvar1.clone()) } }.val,
            )),
            fake_span(Type::Chan(
                session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; fake_span(uvar2.clone()) } }
                    .val,
            )),
        );
        constraints.add(
            fake_span(Type::Chan(uvar1.clone())),
            fake_span(Type::Chan(session_type! { ?String; Wait }.val)),
        );
        constraints.add(
            fake_span(Type::Chan(uvar2.clone())),
            fake_span(Type::Chan(session_type! { Wait }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(
                    session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; Wait } }.val
                )),
                fake_span(Type::Chan(
                    session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; Wait } }.val
                )),
            )])))
        );
    }

    #[test]
    fn test_uvar_inside() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.add(
            fake_span(Type::Chan(
                session_type! { !Int; fake_span(uvar1.clone()) }.val,
            )),
            fake_span(Type::Chan(session_type! { !Int; ?String }.val)),
        );
        constraints.add(
            fake_span(Type::Chan(
                session_type! { !Int; fake_span(uvar2.clone()) }.val,
            )),
            fake_span(Type::Chan(
                session_type! { !Int; fake_span(uvar1.clone()) }.val,
            )),
        );
        constraints.add(
            fake_span(Type::Chan(uvar2.clone())),
            fake_span(Type::Chan(session_type! { ?String }.val)),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Ok(Constraints::from_equivalences(HashSet::from([(
                fake_span(Type::Chan(session_type! { !Int; ?String }.val,)),
                fake_span(Type::Chan(session_type! { !Int; ?String }.val,)),
            )])))
        );
    }
}
