use crate::{
    freest::FreestType,
    syntax::{Eff, Label, Mob, Mult, Session, SessionOp, Type},
    type_alias::AliasEnv,
    util::span::fake_span,
};

use std::{collections::HashMap, io::Write, process::Command};

#[allow(dead_code)]
pub enum EquivalenceResult {
    Success,
    Error { reason: String },
}

pub fn check_equivalence(type1: &Type, type2: &Type, alias_env: &AliasEnv) -> EquivalenceResult {
    let mut test_file = tempfile::Builder::new().suffix(".fst").tempfile().unwrap();

    writeln!(test_file, "module Tmp where").unwrap();

    writeln!(test_file, "type Ret : 1T").unwrap();
    writeln!(test_file, "data Ret = Ret").unwrap();
    // Convert CFSession -> FreestType and then wrap in freest::Type for display
    let mut defs = Definitions::new();

    for (name, session) in alias_env.iter() {
        let alias_type = convert_session_impl(session, &mut defs);
        defs.add(name, alias_type);
    }

    let type1_converted = convert_type_impl(type1, &mut defs);
    let type2_converted = convert_type_impl(type2, &mut defs);

    for def in defs.iter() {
        write_freest_type(&def.0, &def.1, &mut test_file);
    }

    write_freest_type("T1", &type1_converted, &mut test_file);
    write_freest_type("T2", &type2_converted, &mut test_file);

    writeln!(test_file, "left : T1 -> T2").unwrap();
    writeln!(test_file, "left x = x").unwrap();

    writeln!(test_file, "right : T2 -> T1").unwrap();
    writeln!(test_file, "right x = x").unwrap();

    let freest_cmd = Command::new("freest")
        .arg(test_file.path())
        .output()
        .unwrap();

    if freest_cmd.status.success() {
        EquivalenceResult::Success
    } else {
        let reason = String::from_utf8_lossy(&freest_cmd.stderr).to_string();
        EquivalenceResult::Error { reason }
    }
}

fn write_freest_type(name: &str, ty: &FreestType, test_file: &mut impl Write) {
    let kind = if ty.is_session_type() { "1S" } else { "1T" }.to_owned();
    writeln!(test_file, "type {} : {}", name, kind).unwrap();
    writeln!(test_file, "type {} = {}", name, ty).unwrap();
}

pub fn check_equivalence_sessions(type1: &Session, type2: &Session) -> EquivalenceResult {
    check_equivalence(
        &Type::Chan(type1.clone()),
        &Type::Chan(type2.clone()),
        &HashMap::new(),
    )
}

impl FreestType {
    /// Ret -> !Ret, Acq -> ?Ret
    const RET: &str = "Ret";
}

impl Mob {
    fn to_label(self) -> &'static str {
        match self {
            Mob::Mobile => "Mobule",
            Mob::Static => "Static",
        }
    }
}

impl Eff {
    fn to_label(self) -> Option<&'static str> {
        match self {
            Eff::Yes => Some("Static"),
            Eff::No => None,
        }
    }
}

impl Mult {
    fn to_label(self) -> &'static str {
        match self {
            Mult::Unr => "Unrestricted",
            Mult::Lin => "Linear",
            Mult::OrdR => "Right",
            Mult::OrdL => "Left",
        }
    }
}

struct Definitions {
    defs: Vec<(Label, FreestType)>,
    counter: usize,
}

impl Definitions {
    fn new() -> Self {
        Self {
            defs: Vec::new(),
            counter: 0,
        }
    }

    pub fn add(&mut self, label: &Label, ty: FreestType) {
        self.defs.push((label.clone(), ty));
    }

    pub fn iter(&self) -> impl Iterator<Item = &(Label, FreestType)> {
        self.defs.iter()
    }

    pub fn next_label(&mut self) -> Label {
        let label = format!("T_{}", self.counter);
        self.counter += 1;
        label
    }
}

fn convert_type_impl(ty: &Type, defs: &mut Definitions) -> FreestType {
    match ty {
        Type::Chan(session) => convert_session_impl(session, defs),
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

            let param = convert_type_impl(&param.val, defs);
            let ret = convert_type_impl(&ret.val, defs);
            FreestType::Tuple(vec![
                FreestType::Arrow {
                    param: Box::new(param),
                    ret: Box::new(ret),
                }
                .into(),
                FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: labels
                        .into_iter()
                        .map(|label| (label.to_owned(), Box::new(FreestType::Skip)))
                        .collect(),
                }
                .into(),
            ])
        }
        Type::Prod {
            mult,
            first,
            second,
        } => {
            let first = convert_type_impl(&first.val, defs);
            let second = convert_type_impl(&second.val, defs);
            FreestType::Tuple(vec![
                Box::new(first),
                Box::new(second),
                FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: vec![(mult.to_label().to_uppercase(), Box::new(FreestType::Skip))],
                }
                .into(),
            ])
        }
        Type::Variant(items) => FreestType::Tuple(vec![
            Box::new(FreestType::Choice {
                dir: SessionOp::Recv,
                branches: items
                    .into_iter()
                    .map(|(label, ty)| {
                        let ty = convert_type_impl(&ty.val, defs);
                        (label.val.to_uppercase(), Box::new(ty))
                    })
                    .collect(),
            }),
            Box::new(FreestType::Choice {
                dir: SessionOp::Recv,
                branches: vec![("variant".to_uppercase(), Box::new(FreestType::Skip))],
            }),
        ]),
        Type::Unit => FreestType::Unit,
        Type::Int => FreestType::Int,
        Type::Bool => FreestType::Bool,
        Type::String => FreestType::String,
    }
}

fn convert_session_impl(session: &Session, defs: &mut Definitions) -> FreestType {
    match session {
        Session::Skip => FreestType::Skip,
        Session::Semi { first, second } => {
            let first = convert_session_impl(&first.val, defs);
            let second = convert_session_impl(&second.val, defs);
            FreestType::Semi {
                first: Box::new(first),
                second: Box::new(second),
            }
        }
        Session::End(session_op) => FreestType::End(*session_op),
        Session::BorrowEnd(session_op) => FreestType::Message {
            dir: *session_op,
            ty: Box::new(FreestType::Var(FreestType::RET.into())),
        },
        Session::Op(session_op, ty) => {
            let ty = convert_type_impl(&ty.val, defs);
            FreestType::Message {
                dir: *session_op,
                ty: Box::new(ty),
            }
        }
        Session::Choice(session_op, items) => FreestType::Choice {
            dir: *session_op,
            branches: items
                .into_iter()
                .map(|(label, ty)| {
                    let ty = convert_session_impl(&ty.val, defs);
                    (label.val.to_uppercase(), Box::new(ty))
                })
                .collect(),
        },
        Session::Mu(var, body) => {
            let label = defs.next_label();
            // Subst the definition name to the body
            let body = body.subst(&var.val, &Session::Var(fake_span(label.clone())));
            let body = convert_session_impl(&body, defs);
            defs.add(&label, body);
            FreestType::Var(label)
        }
        Session::Var(var) => FreestType::Var(var.val.to_owned()),
        Session::UVar(_) => {
            panic!("Unification variables must be solved before translation to FreeST!")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        equivalence::{EquivalenceResult, check_equivalence_sessions},
        session_type,
    };

    #[inline(always)]
    fn assert_success(result: EquivalenceResult) {
        match result {
            EquivalenceResult::Success => (),
            EquivalenceResult::Error { reason } => {
                panic!("Expected success but got error: {}", reason);
            }
        }
    }

    #[test]
    fn equivalence_skip_identity() {
        let type1 = session_type! { !Int; Skip };
        let type2 = session_type! { Skip; !Int };
        let type3 = session_type! { !Int };

        assert_success(check_equivalence_sessions(&type1, &type2));
        assert_success(check_equivalence_sessions(&type2, &type3));
        assert_success(check_equivalence_sessions(&type1, &type3));
    }

    #[test]
    fn equivalence_semi_associative() {
        let type1 = session_type! { !Int; (!Bool; !String) };
        let type2 = session_type! { (!Int; !Bool); !String };

        assert_success(check_equivalence_sessions(&type1, &type2));
    }

    #[test]
    fn equivalence_branch_semi_commutes() {
        let type1 = session_type! { &{ l1: !Int, l2: !Bool }; ?Int };
        let type2 = session_type! { &{ l1: !Int; ?Int, l2: !Bool; ?Int } };

        assert_success(check_equivalence_sessions(&type1, &type2));
    }

    #[test]
    fn equivalence_rec_non_occurence() {
        let type1 = session_type! { mu x. !Int; ?Int };
        let type2 = session_type! { !Int; ?Int };

        assert_success(check_equivalence_sessions(&type1, &type2));
    }

    #[test]
    fn equivalence_rec_unfold() {
        let type1 = session_type! { mu x. !Int; x };
        let type2 = session_type! { !Int; (mu x. !Int; x) };

        assert_success(check_equivalence_sessions(&type1, &type2));
    }

    #[test]
    fn equivalence_rec_unfold_cf() {
        let type1 = session_type! { mu x. !Int; x; x };
        let type2 = session_type! { !Int; (mu x. !Int; x; x); (mu x. !Int; x; x) };

        assert_success(check_equivalence_sessions(&type1, &type2));
    }

    #[test]
    fn equivalence_ret() {
        let type1 = session_type! { Ret };
        let type2 = session_type! { Ret };

        assert_success(check_equivalence_sessions(&type1, &type2));
    }
}
