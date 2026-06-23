use std::collections::{HashMap, HashSet};

use crate::{
    syntax::{Session, Type, UVarId},
    util::span::fake_span,
};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Constraints(HashSet<(Type, Type)>);

type Assignments = HashMap<UVarId, Session>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ConstraintSolutionError {
    MissingAssignments(HashSet<UVarId>),
}

impl Constraints {
    pub fn empty() -> Constraints {
        Constraints(HashSet::new())
    }

    pub fn join(self, other: Constraints) -> Constraints {
        let mut constraints = self.0;
        for constraint in other.0 {
            constraints.insert(constraint);
        }
        Constraints(constraints)
    }

    pub fn add(&mut self, ty1: Type, ty2: Type) {
        self.0.insert((ty1, ty2));
    }

    pub fn iter(&self) -> impl Iterator<Item = &(Type, Type)> {
        self.0.iter()
    }

    pub fn into_iter(self) -> impl Iterator<Item = (Type, Type)> {
        self.0.into_iter()
    }

    /// Solve the constraints by propagating assignments to unification variables until a fixed point is reached.
    /// If there is still no solution for some unification variables, `Skip` is substituted instead.
    pub fn solve(self) -> Constraints {
        let (assignments, remaining_constraints) = self.infer_assignments();

        println!("assignments: {:?}", assignments);
        println!("remaining_constraints: {:?}", remaining_constraints);
        //

        let assignments = if assignments.is_empty() {
            remaining_constraints
                .unsolved_variables()
                .into_iter()
                .map(|var| (var, Session::Skip))
                .collect()
        } else {
            assignments
        };

        let mut result = Constraints::empty();
        for (ty1, ty2) in remaining_constraints.into_iter() {
            let ty1 = Constraints::subst(ty1.clone(), &assignments);
            let ty2 = Constraints::subst(ty2.clone(), &assignments);
            result.add(ty1, ty2);
        }

        println!("result: {:?}", result);

        if result.is_closed() {
            result
        } else {
            result.solve()
        }
    }

    fn infer_assignments(self) -> (Assignments, Constraints) {
        let mut assignments: Assignments = HashMap::new();
        let mut other_cs = Constraints::empty();
        for (ty1, ty2) in self.into_iter() {
            if let Type::Chan(Session::UVar(var)) = ty1 {
                if let Type::Chan(session) = &ty2
                    && session.is_closed()
                    && !assignments.contains_key(&var)
                {
                    assignments.insert(var, session.clone());
                } else {
                    other_cs.add(ty1, ty2)
                }
            } else if let Type::Chan(Session::UVar(var)) = ty2 {
                if let Type::Chan(session) = &ty1
                    && session.is_closed()
                    && !assignments.contains_key(&var)
                {
                    assignments.insert(var, session.clone());
                } else {
                    other_cs.add(ty1, ty2)
                }
            } else {
                other_cs.add(ty1, ty2)
            }
        }

        (assignments, other_cs)
    }

    fn subst(ty: Type, assignments: &Assignments) -> Type {
        match ty {
            Type::Chan(session) => Type::Chan(Self::subst_session(session, assignments)),
            Type::Bool | Type::Int | Type::String => ty,
            Type::Prod {
                mult,
                first,
                second,
            } => Type::Prod {
                mult,
                first: Box::new(fake_span(Self::subst(first.val, assignments))),
                second: Box::new(fake_span(Self::subst(second.val, assignments))),
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
                param: Box::new(fake_span(Self::subst(param.val, assignments))),
                ret: Box::new(fake_span(Self::subst(ret.val, assignments))),
            },
            Type::Variant(items) => Type::Variant(
                items
                    .into_iter()
                    .map(|(label, ty)| (label, fake_span(Self::subst(ty.val, assignments))))
                    .collect(),
            ),
            Type::Unit => Type::Unit,
        }
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
            Session::Op(session_op, ty) => Session::Op(
                session_op,
                Box::new(fake_span(Self::subst(ty.val, assignments))),
            ),
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

    fn is_closed(&self) -> bool {
        self.iter()
            .all(|(ty1, ty2)| ty1.is_closed() && ty2.is_closed())
    }

    fn unsolved_variables(&self) -> HashSet<UVarId> {
        let mut result = HashSet::new();
        for (ty1, ty2) in self.iter() {
            result.extend(ty1.unification_variables());
            result.extend(ty2.unification_variables());
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::{
        constraint::{self, ConstraintSolutionError, Constraints},
        session_type,
        syntax::{Eff, Mob, Mult, Session, Type},
        util::span::fake_span,
    };

    #[test]
    fn test_simple_cs() {
        let uvar1 = Type::Chan(Session::UVar(1));
        let uvar2 = Type::Chan(Session::UVar(2));

        let session1 = Type::Chan(session_type! { !Int }.val);
        let session2 = Type::Chan(session_type! { ?Int }.val);

        let mut constraints = Constraints::empty();
        constraints.add(uvar1.clone(), uvar2.clone());
        constraints.add(uvar1.clone(), session1.clone());
        constraints.add(uvar2.clone(), session2.clone());

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Constraints(
                vec![(session1.clone(), session2.clone())]
                    .into_iter()
                    .collect()
            )
        );
    }

    #[test]
    fn test_two_iterations() {
        let uvar1 = Type::Chan(Session::UVar(1));
        let uvar2 = Type::Chan(Session::UVar(2));
        let uvar3 = Type::Chan(Session::UVar(3));

        let session1 = Type::Chan(session_type! { !Int }.val);
        let session2 = Type::Chan(session_type! { ?Int }.val);

        let mut constraints = Constraints::empty();
        constraints.add(uvar1.clone(), uvar2.clone());
        constraints.add(uvar2.clone(), uvar3.clone());
        constraints.add(uvar3.clone(), session1.clone());
        constraints.add(uvar1.clone(), session2.clone());

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Constraints(vec![(session2, session1)].into_iter().collect())
        );
    }

    #[test]
    fn test_unsolvable_constraints() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(session_type! { !Int; fake_span(uvar1.clone()) }.val),
            Type::Chan(session_type! { !Int; ?String }.val),
        );
        constraints.add(
            Type::Chan(session_type! { !Int; fake_span(uvar2.clone()) }.val),
            Type::Chan(session_type! { !Int; ?Bool }.val),
        );

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Constraints(HashSet::from([
                (
                    Type::Chan(session_type! { !Int; Skip }.val),
                    Type::Chan(session_type! { !Int; ?String }.val)
                ),
                (
                    Type::Chan(session_type! { !Int; Skip }.val),
                    Type::Chan(session_type! { !Int; ?Bool }.val)
                )
            ]))
        );

        let mut constraints = Constraints::empty();
        constraints.add(Type::Chan(uvar1.clone()), Type::Chan(uvar2.clone()));

        let solved = constraints.solve();

        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(session_type! { Skip }.val),
                Type::Chan(session_type! { Skip }.val)
            )]))
        );
    }

    #[test]
    fn test_prod() {
        let uvar1 = Type::Chan(Session::UVar(1));
        let uvar2 = Type::Chan(Session::UVar(2));

        let mut constraints = Constraints::empty();
        constraints.add(
            uvar1.clone(),
            Type::Chan(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Int)),
                        second: Box::new(fake_span(uvar2.clone()))
                    })
                }
                .val,
            ),
        );
        constraints.add(uvar2.clone(), Type::Chan(session_type! { ?String }.val));

        let solved = constraints.solve();
        assert_eq!(solved, Constraints(HashSet::new()));

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(uvar1.clone())),
                        second: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    })
                }
                .val,
            ),
            Type::Chan(
                session_type! {
                    !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        second: Box::new(fake_span(uvar2.clone()))
                    })
                }
                .val,
            ),
        );
        constraints.add(uvar1.clone(), Type::Chan(session_type! { !Int }.val));
        constraints.add(uvar2.clone(), Type::Chan(session_type! { ?String }.val));

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(
                    session_type! { !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        second: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                ),
                Type::Chan(
                    session_type! { !(Type::Prod {
                        mult: fake_span(Mult::Lin),
                        first: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        second: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                ),
            ),]))
        );
    }

    #[test]
    fn test_arr() {
        let uvar1 = Type::Chan(Session::UVar(1));
        let uvar2 = Type::Chan(Session::UVar(2));

        let mut constraints = Constraints::empty();
        constraints.add(
            uvar1.clone(),
            Type::Chan(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Int)),
                        ret: Box::new(fake_span(uvar2.clone()))
                    })
                }
                .val,
            ),
        );
        constraints.add(uvar2.clone(), Type::Chan(session_type! { ?String }.val));

        let solved = constraints.solve();
        assert_eq!(solved, Constraints(HashSet::new()));

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(uvar1.clone())),
                        ret: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    })
                }
                .val,
            ),
            Type::Chan(
                session_type! {
                    !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        ret: Box::new(fake_span(uvar2.clone()))
                    })
                }
                .val,
            ),
        );
        constraints.add(uvar1.clone(), Type::Chan(session_type! { !Int }.val));
        constraints.add(uvar2.clone(), Type::Chan(session_type! { ?String }.val));

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(
                    session_type! { !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        ret: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                ),
                Type::Chan(
                    session_type! { !(Type::Arr {
                        mob: fake_span(Mob::Mobile),
                        mult: fake_span(Mult::Lin),
                        eff: fake_span(Eff::No),
                        param: Box::new(fake_span(Type::Chan(session_type! { !Int }.val))),
                        ret: Box::new(fake_span(Type::Chan(session_type! { ?String }.val)))
                    }) }
                    .val
                ),
            ),]))
        );
    }

    #[test]
    fn test_variant() {
        let uvar1 = Type::Chan(Session::UVar(1));
        let uvar2 = Type::Chan(Session::UVar(2));

        let mut constraints = Constraints::empty();
        constraints.add(
            uvar1.clone(),
            Type::Chan(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Int)),
                        (fake_span("Right".to_string()), fake_span(uvar2.clone()))
                    ]))
                }
                .val,
            ),
        );
        constraints.add(uvar2.clone(), Type::Chan(session_type! { ?String }.val));

        let solved = constraints.solve();
        assert_eq!(solved, Constraints(HashSet::new()));

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(uvar1.clone())),
                        (fake_span("Right".to_string()), fake_span(Type::Chan(session_type! { ?String }.val)))
                    ]))
                }
                .val,
            ),
            Type::Chan(
                session_type! {
                    !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Chan(session_type! { !Int }.val))),
                        (fake_span("Right".to_string()), fake_span(uvar2.clone()))
                    ]))
                }
                .val,
            ),
        );
        constraints.add(uvar1.clone(), Type::Chan(session_type! { !Int }.val));
        constraints.add(uvar2.clone(), Type::Chan(session_type! { ?String }.val));

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(
                    session_type! { !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Chan(session_type! { !Int }.val))),
                        (fake_span("Right".to_string()), fake_span(Type::Chan(session_type! { ?String }.val)))
                    ])) }
                    .val
                ),
                Type::Chan(
                    session_type! { !(Type::Variant(vec![
                        (fake_span("Left".to_string()), fake_span(Type::Chan(session_type! { !Int }.val))),
                        (fake_span("Right".to_string()), fake_span(Type::Chan(session_type! { ?String }.val)))
                    ])) }
                    .val
                ),
            ),]))
        );
    }

    #[test]
    fn test_semicolon() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(session_type! { fake_span(Session::UVar(1)); !Int }.val),
            Type::Chan(session_type! { ?String; fake_span(Session::UVar(2)) }.val),
        );
        constraints.add(
            Type::Chan(uvar1.clone()),
            Type::Chan(session_type! { ?String }.val),
        );
        constraints.add(
            Type::Chan(uvar2.clone()),
            Type::Chan(session_type! { !Int }.val),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(session_type! { ?String; !Int }.val),
                Type::Chan(session_type! { ?String; !Int }.val),
            )]))
        );
    }

    #[test]
    fn test_choice() {
        let uvar1 = Session::UVar(1);

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(session_type! { +{ left: !Int, right: fake_span(uvar1.clone()) } }.val),
            Type::Chan(session_type! { +{ left: !Int, right: ?String } }.val),
        );
        constraints.add(
            Type::Chan(uvar1.clone()),
            Type::Chan(session_type! { ?String }.val),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(session_type! { +{ left: !Int, right: ?String } }.val),
                Type::Chan(session_type! { +{ left: !Int, right: ?String } }.val),
            )]))
        );
    }

    #[test]
    fn test_recursion() {
        let uvar1 = Session::UVar(1);

        let mut constraints = Constraints::empty();
        constraints.add(
            Type::Chan(session_type! { mu X. !Int; fake_span(uvar1.clone()) }.val),
            Type::Chan(session_type! { mu X. !Int; X }.val),
        );
        constraints.add(
            Type::Chan(uvar1.clone()),
            Type::Chan(session_type! { X }.val), // Note: X is a Var("X") here
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(session_type! { mu X. !Int; X }.val),
                Type::Chan(session_type! { mu X. !Int; X }.val),
            )]))
        );
    }

    #[test]
    fn test_complex_composite() {
        let uvar1 = Session::UVar(1);
        let uvar2 = Session::UVar(2);

        let mut constraints = Constraints::empty();
        // mu X. +{ a: !Int; X, b: !Bool; fake_span(uvar1) }
        constraints.add(
            Type::Chan(
                session_type! { mu X. +{ a: !Int; X, b: !Bool; fake_span(uvar1.clone()) } }.val,
            ),
            Type::Chan(
                session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; fake_span(uvar2.clone()) } }
                    .val,
            ),
        );
        constraints.add(
            Type::Chan(uvar1.clone()),
            Type::Chan(session_type! { ?String; Wait }.val),
        );
        constraints.add(
            Type::Chan(uvar2.clone()),
            Type::Chan(session_type! { Wait }.val),
        );

        let solved = constraints.solve();
        assert_eq!(
            solved,
            Constraints(HashSet::from([(
                Type::Chan(session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; Wait } }.val),
                Type::Chan(session_type! { mu X. +{ a: !Int; X, b: !Bool; ?String; Wait } }.val),
            )]))
        );
    }
}
