use std::collections::{HashMap, HashSet};

use crate::{
    context::Ctx,
    syntax::{PVarId, SExpr, SId, SType, Type, UVarId},
    type_checker::TypeError,
    type_context::TypeCtx,
    util::span::{fake_span, Spanned},
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraints {
    pub equivalences: Equivalences,
    pub mobilities: Mobilities,
}

#[derive(Debug, Clone)]
pub struct Equivalences(HashSet<(SType, SType)>);

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
pub struct Mobilities(Vec<(SExpr, HashSet<SId>, Ctx)>);

type Assignments = HashMap<UVarId, Type>;

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

    /// Solve the constraints by propagating assignments to unification variables until a fixed point is reached.
    /// If there is still no solution for some unification variables, `Skip` is substituted instead.
    pub fn solve(self) -> Result<Constraints, TypeError> {
        self.solve_with_type_ctx(&TypeCtx::empty())
    }

    /// Solve the constraints with a type context for checking mobility.
    fn solve_with_type_ctx(self, ty_ctx: &TypeCtx) -> Result<Constraints, TypeError> {
        let (assignments, equivalences) = self.equivalences.solve(ty_ctx);

        let unsolved_vars = equivalences.unsolved_variables();
        if !unsolved_vars.is_empty() {
            return Err(TypeError::VariablesUnsolvable {
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

    pub fn from(eqs: HashSet<(SType, SType)>) -> Self {
        Equivalences(eqs)
    }

    pub fn join(self, other: Equivalences) -> Equivalences {
        let mut equivalences = self.0;
        for constraint in other.0 {
            equivalences.insert(constraint);
        }
        Equivalences(equivalences)
    }

    pub fn add(&mut self, constraint: (SType, SType)) {
        self.0.insert(constraint);
    }

    pub fn iter(&self) -> impl Iterator<Item = &(SType, SType)> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = (SType, SType)> {
        self.0.into_iter()
    }

    /// Partition equivalences into ones that contains polymorphic variable from
    /// `pvars` vs ones that don't
    pub fn partition(self, pvars: &HashSet<PVarId>) -> (Equivalences, Equivalences) {
        let (with_pvars, without_pvars) = self.into_iter().partition(|(ty1, ty2)| {
            ty1.val
                .poly_variables()
                .collect::<HashSet<_>>()
                .is_subset(&pvars)
                || ty2
                    .poly_variables()
                    .collect::<HashSet<_>>()
                    .is_subset(&pvars)
        });

        (
            Equivalences::from(with_pvars),
            Equivalences::from(without_pvars),
        )
    }

    fn solve(self, ty_ctx: &TypeCtx) -> (Assignments, Equivalences) {
        let mut assignments = Assignments::new();
        let mut equivelances: HashSet<(SType, SType)> = HashSet::new();

        for (ty1, ty2) in self.0.into_iter() {
            equivelances.insert((ty1, ty2));
        }

        loop {
            let Some((result, (ty1, ty2))) = equivelances
                .iter()
                .map(|(ty1, ty2)| (Self::unify(ty_ctx, ty1, ty2), (ty1.clone(), ty2.clone())))
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
                        .map(|(ty1, ty2)| (subst(ty1, &assignments_), subst(ty2, &assignments_)))
                        .collect();
                    assignments.extend(assignments_);
                }
                Err(SolveError::SubEqs(more_eqs)) => equivelances.extend(more_eqs),
                Err(SolveError::Check) => unreachable!(),
            }
        }

        (assignments, Equivalences(equivelances))
    }

    /// Unifies two types. When structures match, further subconstraints are generated.
    /// When a unification variable on one side is found, it's converted to an assignment.
    fn unify(ty_ctx: &TypeCtx, ty1: &Type, ty2: &Type) -> Result<Assignments, SolveError> {
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
                (Type::UVar(uvar_id), Type::PVar { id, dual })
                | (Type::PVar { id, dual }, Type::UVar(uvar_id)) => Ok(HashMap::from([(
                    *uvar_id,
                    Type::PVar {
                        id: id.clone(),
                        dual: *dual,
                    },
                )])),
                (Type::Skip, Type::Skip) => Ok(HashMap::new()),
                (Type::End(op1), Type::End(op2)) if op1 == op2 => Ok(HashMap::new()),
                (Type::BorrowEnd(op1), Type::BorrowEnd(op2)) if op1 == op2 => Ok(HashMap::new()),
                (Type::Var(id1), Type::Var(id2)) if id1 == id2 => Ok(HashMap::new()),
                (
                    Type::Semi {
                        first: first1,
                        second: second1,
                    },
                    Type::Semi {
                        first: first2,
                        second: second2,
                    },
                ) => {
                    let mut assignments = Self::unify(ty_ctx, &first1.val, &first2.val)?;
                    assignments.extend(Self::unify(ty_ctx, &second1.val, &second2.val)?);
                    Ok(assignments)
                }
                (Type::Op(op1, t1), Type::Op(op2, t2)) if op1 == op2 => {
                    Self::unify(ty_ctx, &t1.val, &t2.val).map_err(|_| SolveError::Check)
                }
                (Type::Choice(op1, branches1), Type::Choice(op2, branches2)) if op1 == op2 => {
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

                        assignments.extend(Self::unify(ty_ctx, &branch1.val, &branch2.val)?);
                    }

                    Ok(assignments)
                }
                (Type::Mu(id1, body1), Type::Mu(id2, body2)) if id1 == id2 => {
                    Self::unify(ty_ctx, &body1.val, &body2.val).map_err(|_| SolveError::Check)
                }
                (Type::UVar(id), other) | (other, Type::UVar(id))
                    if Self::is_assignable_session_structure(other) =>
                {
                    Ok(HashMap::from([(*id, other.clone())]))
                }
                _ => Err(SolveError::Check),
            }
        }
    }

    fn is_assignable_session_structure(ty: &Type) -> bool {
        matches!(
            ty,
            Type::Skip
                | Type::Semi { .. }
                | Type::End(_)
                | Type::BorrowEnd(_)
                | Type::Op(_, _)
                | Type::Choice(_, _)
                | Type::Mu(_, _)
                | Type::Var(_)
                | Type::PVar { .. }
        )
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
    pub fn new() -> Mobilities {
        Mobilities(Vec::new())
    }

    fn join(mut self, mut other: Mobilities) -> Mobilities {
        self.0.append(&mut other.0);
        self
    }

    pub fn add(&mut self, expr: SExpr, ids: HashSet<SId>, ctx: Ctx) {
        self.0.push((expr, ids, ctx));
    }

    fn check(mut self, ty_ctx: &TypeCtx, assignments: &Assignments) -> Result<(), TypeError> {
        for (expr, ids, ctx) in self.0.iter_mut() {
            subst_ctx(ctx, &assignments);
            let binds = ctx.binds();
            for id in ids.iter() {
                if !ty_ctx.mobile(binds.get(&id.val).unwrap()) {
                    return Err(TypeError::AssignmentNotMobile {
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

fn subst(ty: SType, assignments: &Assignments) -> SType {
    let span = ty.span.clone();
    let val = match ty.val {
        Type::UVar(var) => assignments.get(&var).cloned().unwrap_or(Type::UVar(var)),
        Type::Abstraction {
            typ,
            quantification,
            ty,
        } => Type::Abstraction {
            typ,
            quantification,
            ty: Box::new(subst(*ty, assignments)),
        },
        Type::PVar { id, dual } => Type::PVar { id, dual },
        Type::Skip => Type::Skip,
        Type::Semi { first, second } => Type::Semi {
            first: Box::new(subst(*first, assignments)),
            second: Box::new(subst(*second, assignments)),
        },
        Type::End(op) => Type::End(op),
        Type::BorrowEnd(op) => Type::BorrowEnd(op),
        Type::Op(op, ty) => Type::Op(op, Box::new(subst(*ty, assignments))),
        Type::Choice(op, items) => Type::Choice(
            op,
            items
                .into_iter()
                .map(|(label, ty)| (label, subst(ty, assignments)))
                .collect(),
        ),
        Type::Mu(id, body) => Type::Mu(id, Box::new(subst(*body, assignments))),
        Type::Var(id) => Type::Var(id),
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
            param: Box::new(subst(*param, assignments)),
            ret: Box::new(subst(*ret, assignments)),
        },
        Type::Prod {
            mult,
            first,
            second,
        } => Type::Prod {
            mult,
            first: Box::new(subst(*first, assignments)),
            second: Box::new(subst(*second, assignments)),
        },
        Type::Variant(items) => Type::Variant(
            items
                .into_iter()
                .map(|(label, ty)| (label, subst(ty, assignments)))
                .collect(),
        ),
        Type::Unit => Type::Unit,
        Type::Int => Type::Int,
        Type::Bool => Type::Bool,
        Type::String => Type::String,
    };
    Spanned::new(val, span)
}

fn subst_ctx(ctx: &mut Ctx, assignments: &Assignments) {
    ctx.map_binds_mut(&mut |_, ty| {
        *ty = subst(fake_span(ty.clone()), assignments).val;
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{
        constraint::Constraints,
        session_type,
        syntax::{Eff, Mob, Mult, Session, Type},
        type_checker::TypeError,
        util::span::fake_span,
    };

    #[test]
    fn test_simple_cs() {
        let uvar1 = fake_span(Session::UVar(1));
        let uvar2 = fake_span(Session::UVar(2));

        let session1 = fake_span(session_type! { !Int }.val);
        let session2 = fake_span(session_type! { ?Int }.val);

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((uvar1.clone(), uvar2.clone()));
        constraints
            .equivalences
            .add((uvar1.clone(), session1.clone()));
        constraints
            .equivalences
            .add((uvar2.clone(), session2.clone()));

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
        let uvar1 = fake_span(Session::UVar(1));
        let uvar2 = fake_span(Session::UVar(2));
        let uvar3 = fake_span(Session::UVar(3));

        let session1 = fake_span(session_type! { !Int }.val);
        let session2 = fake_span(session_type! { ?Int }.val);

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((uvar1.clone(), uvar2.clone()));
        constraints.equivalences.add((uvar2.clone(), uvar3.clone()));
        constraints
            .equivalences
            .add((uvar3.clone(), session1.clone()));
        constraints
            .equivalences
            .add((uvar1.clone(), session2.clone()));

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
        constraints
            .equivalences
            .add((fake_span(uvar1.clone()), fake_span(uvar2.clone())));

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Err(TypeError::VariablesUnsolvable {
                vars: HashSet::from([1, 2])
            })
        );
    }

    #[test]
    fn test_prod() {
        let uvar1 = fake_span(Session::UVar(1));
        let uvar2 = fake_span(Session::UVar(2));

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            uvar1.clone(),
            fake_span(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Int)),
                        second: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            ),
        ));
        constraints
            .equivalences
            .add((uvar2.clone(), fake_span(session_type! { ?String }.val)));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::from_equivalences(HashSet::new())));

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(uvar1.clone().val)),
                        second: Box::new(fake_span(session_type! { ?String }.val))
                    })
                }
                .val,
            ),
            fake_span(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(session_type! { !Int }.val)),
                        second: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            ),
        ));
        constraints
            .equivalences
            .add((uvar1.clone(), fake_span(session_type! { !Int }.val)));
        constraints
            .equivalences
            .add((uvar2.clone(), fake_span(session_type! { ?String }.val)));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_arr() {
        let uvar1 = fake_span(Session::UVar(1));
        let uvar2 = fake_span(Session::UVar(2));

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            uvar1.clone(),
            fake_span(
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
            ),
        ));
        constraints
            .equivalences
            .add((uvar2.clone(), fake_span(session_type! { ?String }.val)));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::from_equivalences(HashSet::new())));

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(uvar1.clone().val)),
                        ret: Box::new(fake_span(session_type! { ?String }.val))
                    })
                }
                .val,
            ),
            fake_span(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(session_type! { !Int }.val)),
                        ret: Box::new(fake_span(uvar2.clone().val))
                    })
                }
                .val,
            ),
        ));
        constraints
            .equivalences
            .add((uvar1.clone(), fake_span(session_type! { !Int }.val)));
        constraints
            .equivalences
            .add((uvar2.clone(), fake_span(session_type! { ?String }.val)));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_variant() {
        let uvar1 = fake_span(Session::UVar(1));
        let uvar2 = fake_span(Session::UVar(2));

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            uvar1.clone(),
            fake_span(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Int)),
                        (fake_span("Right".to_string()), fake_span(uvar2.clone().val))
                    ]))
                }
                .val,
            ),
        ));
        constraints
            .equivalences
            .add((uvar2.clone(), fake_span(session_type! { ?String }.val)));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::from_equivalences(HashSet::new())));

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(uvar1.clone().val)),
                        (fake_span("Right".to_string()), fake_span(session_type! { ?String }.val))
                    ]))
                }
                .val,
            ),
            fake_span(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(session_type! { !Int }.val)),
                        (fake_span("Right".to_string()), fake_span(uvar2.clone().val))
                    ]))
                }
                .val,
            ),
        ));
        constraints
            .equivalences
            .add((uvar1.clone(), fake_span(session_type! { !Int }.val)));
        constraints
            .equivalences
            .add((uvar2.clone(), fake_span(session_type! { ?String }.val)));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_semicolon() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(session_type! { fake_span(Session::UVar(1)); !Int }.val),
            fake_span(session_type! { ?String; fake_span(Session::UVar(2)) }.val),
        ));
        constraints.equivalences.add((
            fake_span(uvar1.clone()),
            fake_span(session_type! { ?String }.val),
        ));
        constraints.equivalences.add((
            fake_span(uvar2.clone()),
            fake_span(session_type! { !Int }.val),
        ));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_choice() {
        let uvar1 = Session::UVar(1);

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(session_type! { +{ left: !Int, right: fake_span(uvar1.clone()) } }.val),
            fake_span(session_type! { +{ left: !Int, right: ?String } }.val),
        ));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_recursion() {
        let uvar1 = Session::UVar(1);

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(session_type! { mu X. !Int; fake_span(uvar1.clone()) }.val),
            fake_span(session_type! { mu X. !Int; X }.val),
        ));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_complex_composite() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        // mu X. +{ a: !Int; X, b: !Bool; fake_span(uvar1) }
        constraints.equivalences.add((fake_span(
            session_type! { mu X. +{ a: !Int; X, b: !Bool; fake_span(uvar1.clone()) } }.val,
        ), fake_span(
            session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; fake_span(uvar2.clone()) } }
                .val,
        )));
        constraints.equivalences.add((
            fake_span(uvar1.clone()),
            fake_span(session_type! { ?String; Wait }.val),
        ));
        constraints.equivalences.add((
            fake_span(uvar2.clone()),
            fake_span(session_type! { Wait }.val),
        ));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }

    #[test]
    fn test_uvar_inside() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.equivalences.add((
            fake_span(session_type! { !Int; fake_span(uvar1.clone()) }.val),
            fake_span(session_type! { !Int; ?String }.val),
        ));
        constraints.equivalences.add((
            fake_span(session_type! { !Int; fake_span(uvar2.clone()) }.val),
            fake_span(session_type! { !Int; fake_span(uvar1.clone()) }.val),
        ));
        constraints.equivalences.add((
            fake_span(uvar2.clone()),
            fake_span(session_type! { ?String }.val),
        ));

        let solved = constraints.solve();
        assert_eq!(solved, Ok(Constraints::empty()));
    }
}
