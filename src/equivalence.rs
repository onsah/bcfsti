use crate::{
    freest::{FreestType, Kind as FreestKind},
    syntax::{Eff, Id, Kind, Label, Mob, Mult, PVarId, SessionOp, Type},
    type_alias::AliasEnv,
    util::span::fake_span,
};

use std::{collections::HashMap, io::Write, process::Command};

#[allow(dead_code)]
pub enum EquivalenceResult {
    Success,
    Error { reason: String },
}

pub fn check_equivalence(
    type1: &Type,
    type2: &Type,
    alias_env: &AliasEnv,
    pvar_bindings: &HashMap<PVarId, Kind>,
) -> EquivalenceResult {
    let mut test_file = tempfile::Builder::new().suffix(".fst").tempfile().unwrap();

    // writeln!(test_file, "module Tmp where").unwrap();

    writeln!(test_file, "type Ret : 1T").unwrap();
    writeln!(test_file, "data Ret = Ret").unwrap();
    // Convert Type -> FreestType and then wrap in freest::Type for display
    let mut defs = Definitions::new();

    for (name, alias_type) in alias_env.iter() {
        let alias_type = convert_type_impl(
            &alias_type.val,
            &mut defs,
            &HashMap::default(),
            pvar_bindings,
        );
        defs.add(name, alias_type);
    }

    let type1_converted = convert_type_impl(type1, &mut defs, &HashMap::default(), pvar_bindings);
    let type2_converted = convert_type_impl(type2, &mut defs, &HashMap::default(), pvar_bindings);

    for def in defs.iter() {
        write_freest_type(&def.0, &def.1, &mut test_file);
    }

    write_freest_type("T1", &type1_converted, &mut test_file);
    write_freest_type("T2", &type2_converted, &mut test_file);

    write_fn_type(
        &mut test_file,
        "left",
        "T1",
        "T2",
        &type1_converted,
        &type2_converted,
    );
    writeln!(test_file, "left x = x").unwrap();

    write_fn_type(
        &mut test_file,
        "right",
        "T2",
        "T1",
        &type2_converted,
        &type1_converted,
    );
    writeln!(test_file, "right x = x").unwrap();

    // println!(
    //     "file: {}",
    //     std::fs::read_to_string(test_file.path()).unwrap()
    // );

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

/// Writes `{name} : ((forall a ->)* T1 a*) -> ((forall a ->)* T2 a*)`
fn write_fn_type(
    test_file: &mut impl Write,
    name: &str,
    type1_name: &str,
    type2_name: &str,
    type1: &FreestType,
    type2: &FreestType,
) {
    write!(test_file, "{} : ", name).unwrap();

    let mut poly_ids: Vec<_> = type1.free_poly_variables().into_keys().collect();
    poly_ids.extend(type2.free_poly_variables().into_keys());

    if !poly_ids.is_empty() {
        write!(test_file, "forall ").unwrap();
        for id in poly_ids.into_iter() {
            write!(test_file, "{id} ").unwrap();
        }
        write!(test_file, "-> ").unwrap();
    }

    write_inline(type1_name, &type1, test_file);
    write!(test_file, " -> ").unwrap();
    write_inline(type2_name, &type2, test_file);
    writeln!(test_file, "").unwrap();
}

fn write_inline(name: &str, ty: &FreestType, test_file: &mut impl Write) {
    write!(test_file, "{name}").unwrap();
    let pvars = ty.free_poly_variables();
    for (id, _) in pvars.iter() {
        write!(test_file, " {id}").unwrap();
    }
}

fn write_freest_type(name: &str, ty: &FreestType, test_file: &mut impl Write) {
    let kind = if ty.is_session_type() { "1S" } else { "1T" }.to_owned();
    let poly_vars = ty.free_poly_variables();
    write!(test_file, "type {} : ", name).unwrap();
    // CAREFUL: The order of iter is arbitrary but here it works because the iter call
    // later is done on the same collection hence the ordering matches
    for (_, kind) in poly_vars.iter() {
        write!(
            test_file,
            "{} -> ",
            match kind {
                crate::freest::Kind::Type => "1T",
                crate::freest::Kind::Session => "1S",
            }
        )
        .unwrap();
    }
    writeln!(test_file, "{}", kind).unwrap();
    write!(test_file, "type {} ", name).unwrap();
    for (var, _) in poly_vars.iter() {
        write!(test_file, "{} ", var).unwrap();
    }
    writeln!(test_file, "= {}", ty).unwrap();
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

fn get_kind(id: &PVarId, pvar_bindings: &HashMap<PVarId, Kind>) -> FreestKind {
    match pvar_bindings.get(id) {
        Some(Kind::Session) => FreestKind::Session,
        Some(Kind::Type) => FreestKind::Type,
        None => unreachable!(),
    }
}

fn convert_type_impl(
    ty: &Type,
    defs: &mut Definitions,
    // Rec var id -> polymorphic variable cardinality
    rvar_bindings: &HashMap<Id, Vec<PVarId>>,
    pvar_bindings: &HashMap<PVarId, Kind>,
) -> FreestType {
    match ty {
        // Session constructors
        Type::Skip => FreestType::Skip,
        Type::Semi { first, second } => {
            let first = convert_type_impl(&first.val, defs, rvar_bindings, pvar_bindings);
            let second = convert_type_impl(&second.val, defs, rvar_bindings, pvar_bindings);
            FreestType::Semi {
                first: Box::new(first),
                second: Box::new(second),
            }
        }
        Type::End(session_op) => FreestType::End(*session_op),
        Type::BorrowEnd(session_op) => FreestType::Message {
            dir: *session_op,
            ty: Box::new(FreestType::var(FreestType::RET.into())),
        },
        Type::Op(session_op, ty) => {
            // The payload of an Op is a value type; start with empty rvar bindings.
            let ty = convert_type_impl(&ty.val, defs, &HashMap::default(), pvar_bindings);
            FreestType::Message {
                dir: *session_op,
                ty: Box::new(ty),
            }
        }
        Type::Choice(session_op, items) => FreestType::Choice {
            dir: *session_op,
            branches: items
                .into_iter()
                .map(|(label, ty)| {
                    let ty = convert_type_impl(&ty.val, defs, rvar_bindings, pvar_bindings);
                    (label.val.to_uppercase(), Box::new(ty))
                })
                .collect(),
        },
        Type::Mu(var, body) => {
            let label = defs.next_label();
            // Subst the definition name into the body
            let body = body.subst(&var.val, &Type::Var(fake_span(label.clone())));
            let pvars: Vec<_> = body.poly_variables().collect();
            let mut rvar_bindings = rvar_bindings.clone();
            rvar_bindings.insert(label.clone(), pvars.clone());
            let body = convert_type_impl(&body, defs, &rvar_bindings, pvar_bindings);
            defs.add(&label, body);
            FreestType::Var(label, pvars.into_iter().collect())
        }
        Type::Var(var) => FreestType::Var(
            var.val.to_owned(),
            match rvar_bindings.get(&var.val) {
                Some(pvars) => pvars.clone(),
                None => Vec::new(),
            },
        ),
        Type::UVar(_) => {
            panic!("Unification variables must be solved before translation to FreeST!")
        }

        // Value constructors
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

            let param = convert_type_impl(&param.val, defs, &HashMap::default(), pvar_bindings);
            let ret = convert_type_impl(&ret.val, defs, &HashMap::default(), pvar_bindings);
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
            let first = convert_type_impl(&first.val, defs, &HashMap::default(), pvar_bindings);
            let second = convert_type_impl(&second.val, defs, &HashMap::default(), pvar_bindings);
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
                        let ty =
                            convert_type_impl(&ty.val, defs, &HashMap::default(), pvar_bindings);
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
        Type::Abstraction { .. } => todo!(),
        Type::PVar { id, .. } => FreestType::PVar(id.clone(), get_kind(id, pvar_bindings)),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::{
        equivalence::{check_equivalence, EquivalenceResult},
        session_type,
        syntax::Type,
    };

    fn check_equivalence_sessions(type1: &Type, type2: &Type) -> EquivalenceResult {
        check_equivalence(type1, type2, &HashMap::new(), &HashMap::new())
    }

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
