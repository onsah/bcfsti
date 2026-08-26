use std::collections::HashSet;

use crate::syntax::{SLabel, Session, Type};

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
            ) => typ1 == typ2 && q1 == q2 && ty1.sem_eq(ty2),
            _ => false,
        }
    }
}

impl Session {
    pub fn sem_eq(&self, other: &Self) -> bool {
        self.sem_eq_(other, &HashSet::new())
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
