use crate::{
    freest::FreestType,
    syntax::{Eff, Mob, Mult, Session, SessionOp, Type},
};

use std::{io::Write, process::Command};

#[allow(dead_code)]
pub enum TypecheckResult {
    Success,
    Error { reason: String },
}

pub fn check_equivalence(type1: &Session, type2: &Session) -> TypecheckResult {
    let mut test_file = tempfile::Builder::new().suffix(".fst").tempfile().unwrap();

    writeln!(test_file, "data Ret = Ret").unwrap();
    // Convert CFSession -> FreestType and then wrap in freest::Type for display
    let freest_type1 = FreestType::from(type1);
    writeln!(test_file, "type T1 = {}", freest_type1).unwrap();
    let freest_type2 = FreestType::from(type2);
    writeln!(test_file, "type T2 = {}", freest_type2).unwrap();

    writeln!(test_file, "left : T1 -> T2").unwrap();
    writeln!(test_file, "left x = x").unwrap();

    writeln!(test_file, "right : T2 -> T1").unwrap();
    writeln!(test_file, "right x = x").unwrap();

    let freest_cmd = Command::new("freest")
        .arg("--subtyping")
        .arg(test_file.path())
        .output()
        .unwrap();

    if freest_cmd.status.success() {
        TypecheckResult::Success
    } else {
        let reason = String::from_utf8_lossy(&freest_cmd.stderr).to_string();
        TypecheckResult::Error { reason }
    }
}

impl FreestType {
    /// Ret -> !Ret, Acq -> ?Ret
    const RET: &str = "Ret";
}

// Implement conversions from the syntax types to freest internal representation here so
// the equivalence module owns the translation logic used for tests.
impl From<&Session> for FreestType {
    /// Assumes type Ret is defined as: `data Ret = Ret`
    fn from(value: &Session) -> FreestType {
        match value {
            Session::Skip => FreestType::Skip,
            Session::Semi { first, second } => FreestType::Semi {
                first: Box::new((&first.val).into()),
                second: Box::new((&second.val).into()),
            },
            Session::End(session_op) => FreestType::End(*session_op),
            Session::Op(session_op, ty) => FreestType::Message {
                dir: *session_op,
                ty: Box::new((&ty.val).into()),
            },
            Session::Choice(session_op, items) => FreestType::Choice {
                dir: *session_op,
                branches: items
                    .into_iter()
                    .map(|(label, ty)| (label.val.clone(), Box::new((&ty.val).into())))
                    .collect(),
            },
            Session::Mu(var, body) => FreestType::Rec {
                var: var.val.clone(),
                body: Box::new((&body.val).into()),
            },
            Session::Var(var) => FreestType::Var(var.val.clone()),
            Session::BorrowEnd(session_op) => FreestType::Message {
                dir: *session_op,
                ty: Box::new(FreestType::Var(FreestType::RET.into())),
            },
            Session::UVar(_) => {
                panic!("Unification variables must be solved before translation to FreeST!")
            }
        }
    }
}

impl From<&Type> for FreestType {
    fn from(value: &Type) -> FreestType {
        match value {
            Type::Chan(cfsession) => cfsession.into(),
            Type::Variant(items) => FreestType::Tuple(vec![
                Box::new(FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: items
                        .into_iter()
                        .map(|(label, ty)| (label.val.clone(), Box::new((&ty.val).into())))
                        .collect(),
                }),
                Box::new(FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: vec![("variant".into(), FreestType::Skip.into())],
                }),
            ]),
            Type::Unit => FreestType::Unit,
            Type::Int => FreestType::Int,
            Type::Bool => FreestType::Bool,
            Type::String => FreestType::String,
            Type::Arr {
                mob,
                mult,
                eff,
                param,
                ret,
            } => {
                let mut labels = vec![mob.to_label(), mult.to_label()];
                if let Some(label) = eff.to_label() {
                    labels.push(label);
                }

                FreestType::Tuple(vec![
                    FreestType::Arrow {
                        param: Box::new((&param.val).into()),
                        ret: Box::new((&ret.val).into()),
                    }
                    .into(),
                    FreestType::Choice {
                        dir: SessionOp::Recv,
                        branches: labels
                            .into_iter()
                            .map(|label| (label.into(), Box::new(FreestType::Skip)))
                            .collect(),
                    }
                    .into(),
                ])
            }
            Type::Prod {
                mult,
                first,
                second,
            } => FreestType::Tuple(vec![
                Box::new((&first.val).into()),
                Box::new((&second.val).into()),
                FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: vec![(mult.to_label().into(), FreestType::Skip.into())],
                }
                .into(),
            ]),
        }
    }
}

impl Mob {
    fn to_label(self) -> &'static str {
        match self {
            Mob::Mobile => "mobile",
            Mob::Static => "static",
        }
    }
}

impl Eff {
    fn to_label(self) -> Option<&'static str> {
        match self {
            Eff::Yes => Some("static"),
            Eff::No => None,
        }
    }
}

impl Mult {
    fn to_label(self) -> &'static str {
        match self {
            Mult::Unr => "unrestricted",
            Mult::Lin => "linear",
            Mult::OrdR => "right",
            Mult::OrdL => "left",
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        equivalence::{check_equivalence, TypecheckResult},
        session_type,
    };

    #[inline(always)]
    fn assert_success(result: TypecheckResult) {
        match result {
            TypecheckResult::Success => (),
            TypecheckResult::Error { reason } => {
                panic!("Expected success but got error: {}", reason);
            }
        }
    }

    #[test]
    fn equivalence_skip_identity() {
        let type1 = session_type! { !Int; Skip };
        let type2 = session_type! { Skip; !Int };
        let type3 = session_type! { !Int };

        assert_success(check_equivalence(&type1, &type2));
        assert_success(check_equivalence(&type2, &type3));
        assert_success(check_equivalence(&type1, &type3));
    }

    #[test]
    fn equivalence_semi_associative() {
        let type1 = session_type! { !Int; (!Bool; !String) };
        let type2 = session_type! { (!Int; !Bool); !String };

        assert_success(check_equivalence(&type1, &type2));
    }

    #[test]
    fn equivalence_branch_semi_commutes() {
        let type1 = session_type! { &{ l1: !Int, l2: !Bool }; ?Int };
        let type2 = session_type! { &{ l1: !Int; ?Int, l2: !Bool; ?Int } };

        assert_success(check_equivalence(&type1, &type2));
    }

    #[test]
    fn equivalence_rec_non_occurence() {
        let type1 = session_type! { mu x. !Int; ?Int };
        let type2 = session_type! { !Int; ?Int };

        assert_success(check_equivalence(&type1, &type2));
    }

    #[test]
    fn equivalence_rec_unfold() {
        let type1 = session_type! { mu x. !Int; x };
        let type2 = session_type! { !Int; (mu x. !Int; x) };

        assert_success(check_equivalence(&type1, &type2));
    }

    #[test]
    fn equivalence_rec_unfold_cf() {
        let type1 = session_type! { mu x. !Int; x; x };
        let type2 = session_type! { !Int; (mu x. !Int; x; x); (mu x. !Int; x; x) };

        assert_success(check_equivalence(&type1, &type2));
    }

    #[test]
    fn equivalence_ret() {
        let type1 = session_type! { Ret };
        let type2 = session_type! { Ret };

        assert_success(check_equivalence(&type1, &type2));
    }
}
