use std::collections::{HashMap, HashSet};

use crate::{
    context::Ctx,
    syntax::{SExpr, SId, SType, Session, Type, UVarId},
    type_context::TypeCtx,
    util::span::{Spanned, fake_span},
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraints {
    equivalences: Equivalences,
    mobilities: Mobilities,
}

#[derive(Debug, Clone)]
struct Equivalences(HashSet<(SType, SType)>);

impl PartialEq for Equivalences {
    fn eq(&self, other: &Self) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        for (ty1, ty2) in self.0.iter() {
            if !(other.0.contains(&(ty1.clone(), ty2.clone()))
                || other.0.contains(&(ty2.clone(), ty1.clone())))
            {
                return false;
            }
        }
        true
    }
}

impl Eq for Equivalences {}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Mobilities(Vec<(SExpr, HashSet<SId>, Ctx)>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConstraintSolutionError {
    VariablesUnsolvable { vars: HashSet<UVarId> },
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
        self.solve_with_type_ctx(&TypeCtx::empty())
    }

    /// Solve the constraints with a type context for checking mobility.
    pub fn solve_with_type_ctx(
        self,
        ty_ctx: &TypeCtx,
    ) -> Result<Constraints, ConstraintSolutionError> {
        let (assignments, equivalences) = self.equivalences.solve();

        let unsolved_vars = equivalences.unsolved_variables();
        if !unsolved_vars.is_empty() {
            return Err(ConstraintSolutionError::VariablesUnsolvable {
                vars: unsolved_vars,
            });
        }

        self.mobilities.check(ty_ctx, &assignments)?;
        Ok(Constraints {
            equivalences,
            mobilities: Mobilities::new(),
        })
    }
}

enum SolveError {
    SubEqs(Vec<(SType, SType)>),
    Check,
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

    pub fn solve(self) -> (Assignments, Equivalences) {
        let mut assignments = Assignments::new();
        let mut equivelances: HashSet<(SType, SType)> = HashSet::new();

        for (ty1, ty2) in self.0.into_iter() {
            equivelances.insert((ty1, ty2));
        }

        loop {
            let Some((result, (ty1, ty2))) = equivelances
                .iter()
                .map(|(ty1, ty2)| (Self::unify_type(ty1, ty2), (ty1.clone(), ty2.clone())))
                .find(|(result, _)| !matches!(result, Err(SolveError::Check)))
            else {
                break;
            };

            equivelances.remove(&(ty1, ty2));

            match result {
                Ok(assignments_) => {
                    // Substitute assignments to the remaining constraints
                    equivelances = equivelances
                        .into_iter()
                        .map(|(ty1, ty2)| {
                            (
                                subst_type(ty1, &assignments_),
                                subst_type(ty2, &assignments_),
                            )
                        })
                        .collect();
                    assignments.extend(assignments_);
                }
                Err(SolveError::SubEqs(more_eqs)) => equivelances.extend(more_eqs),
                Err(SolveError::Check) => unreachable!(),
            }
        }

        (assignments, Equivalences(equivelances))
    }

    /// Unifies two regular types. When structures match, further subconstraints are generated.
    /// When a unification variable on one side is found, it's converted to an assignment.
    fn unify_type(ty1: &Type, ty2: &Type) -> Result<Assignments, SolveError> {
        if ty1.sem_eq(ty2) {
            Ok(HashMap::new())
        } else {
            match (ty1, ty2) {
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
                ) if mob1 == mob2 && mult1 == mult2 && eff1 == eff2 => {
                    Err(SolveError::SubEqs(vec![
                        (*p1.clone(), *p2.clone()),
                        (*r1.clone(), *r2.clone()),
                    ]))
                }
                (
                    Type::Prod {
                        mult: mult1,
                        first: first1,
                        second: second1,
                    },
                    Type::Prod {
                        mult: mult2,
                        first: first2,
                        second: second2,
                    },
                ) if mult1 == mult2 => Err(SolveError::SubEqs(vec![
                    (*first1.clone(), *first2.clone()),
                    (*second1.clone(), *second2.clone()),
                ])),
                (Type::Variant(items1), Type::Variant(items2))
                    if items1
                        .iter()
                        .map(|(label, _)| label.val.clone())
                        .collect::<HashSet<_>>()
                        == items2
                            .iter()
                            .map(|(label, _)| label.val.clone())
                            .collect::<HashSet<_>>() =>
                {
                    Err(SolveError::SubEqs(
                        items1
                            .iter()
                            .zip(items2.iter())
                            .map(|((_, ty1), (_, ty2))| (ty1.clone(), ty2.clone()))
                            .collect::<Vec<(SType, SType)>>(),
                    ))
                }
                (Type::Chan(session1), Type::Chan(session2)) => {
                    Self::unify_session(session1, session2)
                }
                _ => Err(SolveError::Check),
            }
        }
    }

    /// Unifies two session types. Unlike regular types we can't further generate subconstraints
    /// due to associativity of sequencing operators. So either two types fully match modulo unification variables
    /// or the equivalence constraint should be checked by FreeST.
    ///
    /// 1. When one part is a unification variable and the other side is not, generates an assignment
    /// 2. When both side structurally match, further substructures are unified.
    ///    - If all substructures generate assignment, the result is the union of those assignments
    ///    - Otherwise, equivalence constraint can't be unified
    fn unify_session(session1: &Session, session2: &Session) -> Result<Assignments, SolveError> {
        match (session1, session2) {
            (Session::UVar(id), session) | (session, Session::UVar(id))
                if !matches!(session, Session::UVar(_)) =>
            {
                Ok(HashMap::from([(*id, session.clone())]))
            }
            (Session::Skip, Session::Skip) => Ok(HashMap::new()),
            (Session::End(op1), Session::End(op2)) if op1 == op2 => Ok(HashMap::new()),
            (Session::BorrowEnd(op1), Session::BorrowEnd(op2)) if op1 == op2 => Ok(HashMap::new()),
            (Session::Var(id1), Session::Var(id2)) if id1 == id2 => Ok(HashMap::new()),
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
                let mut assignments = Self::unify_session(first1, first2)?;
                assignments.extend(Self::unify_session(second1, second2)?);
                Ok(assignments)
            }
            (Session::Op(op1, session1), Session::Op(op2, session2)) if op1 == op2 => {
                Self::unify_type(&session1.val, &session2.val).map_err(|_| SolveError::Check)
            }
            (Session::Choice(op1, branches1), Session::Choice(op2, branches2)) if op1 == op2 => {
                if branches1.len() != branches2.len() {
                    return Err(SolveError::Check);
                }

                let mut assignments = HashMap::new();
                for (label, branch1) in branches1.iter() {
                    let Some(branch2) = branches2.iter().find_map(|(label_, branch)| {
                        if &label_.val == &label.val {
                            Some(branch)
                        } else {
                            None
                        }
                    }) else {
                        return Err(SolveError::Check);
                    };

                    assignments.extend(Self::unify_session(branch1, branch2)?);
                }

                Ok(assignments)
            }
            (Session::Mu(id1, session1), Session::Mu(id2, session2)) if id1 == id2 => {
                Self::unify_session(session1, session2).map_err(|_| SolveError::Check)
            }
            _ => Err(SolveError::Check),
        }
    }

    fn unsolved_variables(&self) -> HashSet<UVarId> {
        let mut result = HashSet::new();
        for (ty1, ty2) in self.iter() {
            result.extend(ty1.val.unification_variables());
            result.extend(ty2.val.unification_variables());
        }
        result
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

    fn check(
        mut self,
        ty_ctx: &TypeCtx,
        assignments: &Assignments,
    ) -> Result<(), ConstraintSolutionError> {
        for (expr, ids, ctx) in self.0.iter_mut() {
            subst_ctx(ctx, &assignments);
            let binds = ctx.binds();
            for id in ids.iter() {
                if !ty_ctx.mobile(binds.get(&id.val).unwrap()) {
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

fn subst_type(ty: SType, assignments: &Assignments) -> SType {
    let span = ty.span.clone();
    let val = match ty.val {
        Type::Forall {
            id,
            kind,
            qualifications,
            ty,
        } => Type::Forall {
            id,
            kind,
            qualifications,
            ty: Box::new(subst_type(*ty, assignments)),
        },
        Type::Exists {
            id,
            kind,
            qualifications,
            ty,
        } => Type::Exists {
            id,
            kind,
            qualifications,
            ty: Box::new(subst_type(*ty, assignments)),
        },
        Type::Chan(session) => Type::Chan(subst_session(session, assignments)),
        Type::Bool | Type::Int | Type::String => ty.val,
        Type::Prod {
            mult,
            first,
            second,
        } => Type::Prod {
            mult,
            first: Box::new(subst_type(*first, assignments)),
            second: Box::new(subst_type(*second, assignments)),
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
            param: Box::new(subst_type(*param, assignments)),
            ret: Box::new(subst_type(*ret, assignments)),
        },
        Type::Variant(items) => Type::Variant(
            items
                .into_iter()
                .map(|(label, ty)| (label, subst_type(ty, assignments)))
                .collect(),
        ),
        Type::Unit => Type::Unit,
        Type::PVar { id, dual } => Type::PVar { id, dual },
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
        Session::PVar { .. } => todo!(),
        Session::Skip => Session::Skip,
        Session::Semi { first, second } => Session::Semi {
            first: Box::new(fake_span(subst_session(first.val, assignments))),
            second: Box::new(fake_span(subst_session(second.val, assignments))),
        },
        Session::End(session_op) => Session::End(session_op),
        Session::BorrowEnd(session_op) => Session::BorrowEnd(session_op),
        Session::Op(session_op, ty) => {
            Session::Op(session_op, Box::new(subst_type(*ty, assignments)))
        }
        Session::Choice(session_op, items) => Session::Choice(
            session_op,
            items
                .into_iter()
                .map(|(label, s)| (label, fake_span(subst_session(s.val, assignments))))
                .collect(),
        ),
        Session::Mu(id, body) => Session::Mu(
            id,
            Box::new(fake_span(subst_session(body.val, assignments))),
        ),
        Session::Var(id) => Session::Var(id),
    }
}

fn subst_ctx(ctx: &mut Ctx, assignments: &Assignments) {
    ctx.map_binds_mut(&mut |_, ty| {
        *ty = subst_type(fake_span(ty.clone()), assignments).val;
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{
        constraint::{ConstraintSolutionError, Constraints},
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
            Err(ConstraintSolutionError::VariablesUnsolvable {
                vars: HashSet::from([1, 2])
            })
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
        assert_eq!(solved, Ok(Constraints::empty()));
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
        assert_eq!(solved, Ok(Constraints::empty()));
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
        assert_eq!(solved, Ok(Constraints::empty()));
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
        assert_eq!(solved, Ok(Constraints::empty()));
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
        assert_eq!(solved, Ok(Constraints::empty()));
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
        assert_eq!(solved, Ok(Constraints::empty()));
    }
}
