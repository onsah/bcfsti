use std::{
    fmt::{self},
    hash::Hash,
};

use crate::syntax::{Label, SessionOp};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[allow(dead_code)]
pub(crate) enum Kind {
    Type,
    Session,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum FreestType {
    // Simple types
    Unit,
    Int,
    Bool,
    String,
    Tuple(Vec<Box<FreestType>>),
    Arrow {
        param: Box<FreestType>,
        ret: Box<FreestType>,
    },
    // Session Types
    Skip,
    End(SessionOp),
    Semi {
        first: Box<FreestType>,
        second: Box<FreestType>,
    },
    Message {
        dir: SessionOp,
        ty: Box<FreestType>,
    },
    Choice {
        dir: SessionOp,
        branches: Vec<(Label, Box<FreestType>)>,
    },
    // Polymorphism and recursive types
    #[allow(dead_code)]
    Forall {
        var: Label,
        kind: Kind,
        body: Box<FreestType>,
    },
    Var(Label),
}

impl FreestType {
    pub fn is_session_type(&self) -> bool {
        match self {
            FreestType::Skip
            | FreestType::End(_)
            | FreestType::Var(_)
            | FreestType::Semi { .. }
            | FreestType::Message { .. }
            | FreestType::Choice { .. } => true,
            _ => false,
        }
    }
}

impl fmt::Display for FreestType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreestType::Unit => write!(f, "()"),
            FreestType::Int => write!(f, "Int"),
            FreestType::Bool => write!(f, "Bool"),
            FreestType::String => write!(f, "String"),
            FreestType::Tuple(tys) => {
                write!(f, "(")?;
                write!(f, "{}", tys.first().unwrap())?;
                for ty in &tys[1..] {
                    write!(f, ", {}", ty)?;
                }
                write!(f, ")")?;
                Ok(())
            }
            FreestType::Arrow { param, ret } => write!(f, "{} -> {}", param, ret),
            FreestType::Skip => write!(f, "Skip"),
            FreestType::End(session_op) => {
                let session_op = match session_op {
                    SessionOp::Recv => "Wait",
                    SessionOp::Send => "Close",
                };
                write!(f, "{}", session_op)
            }
            FreestType::Semi { first, second } => write!(f, "{}; {}", first, second),
            FreestType::Message { dir, ty } => {
                let dir = match dir {
                    SessionOp::Recv => "?",
                    SessionOp::Send => "!",
                };
                write!(f, "{}({})", dir, ty)
            }
            FreestType::Choice { dir, branches } => {
                write!(
                    f,
                    "{}",
                    match dir {
                        SessionOp::Recv => "&",
                        SessionOp::Send => "+",
                    }
                )?;
                write!(f, "{{ ")?;
                for (label, ty) in branches[..branches.len() - 1].iter() {
                    write!(f, "{}: {}, ", label, ty)?;
                }
                {
                    let (label, ty) = branches.last().unwrap();
                    write!(f, "{}: {}", label, ty)?;
                }
                write!(f, "}}")
            }
            FreestType::Forall { var, kind, body } => {
                let kind = match kind {
                    Kind::Type => "1T",
                    Kind::Session => "1S",
                };
                write!(f, "(forall ({} : {}) -> {})", var, kind, body)
            }
            FreestType::Var(label) => write!(f, "{}", label),
        }
    }
}

// Conversion from CFSession is implemented in the `equivalence` module.

// Conversion from CFType is implemented in the `equivalence` module.

// Conversion helpers for Eff/Mult are implemented in the `equivalence` module.

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use std::sync::OnceLock;
    use std::{io::Write, process::Command};

    // Bring the macros and other important things into scope.
    use proptest::prelude::*;
    use tempfile::Builder;

    use crate::freest::{FreestType, Kind};
    use crate::syntax::{Label, SessionOp};

    impl FreestType {
        fn free_variables(&self) -> HashSet<Label> {
            match self {
                FreestType::Unit | FreestType::Int | FreestType::Bool | FreestType::String => {
                    HashSet::default()
                }
                FreestType::Tuple(fields) => {
                    let mut result = HashSet::new();
                    for ty in fields {
                        result.extend(ty.free_variables());
                    }
                    result
                }
                FreestType::Arrow { param, ret } => {
                    let mut result = param.free_variables();
                    result.extend(ret.free_variables());
                    result
                }
                FreestType::Skip => HashSet::default(),
                FreestType::End(_) => HashSet::default(),
                FreestType::Semi { first, second } => {
                    let mut result = first.free_variables();
                    result.extend(second.free_variables());
                    result
                }
                FreestType::Message { ty, .. } => ty.free_variables(),
                FreestType::Choice { branches, .. } => {
                    let mut result = HashSet::new();
                    for (_, ty) in branches {
                        result.extend(ty.free_variables());
                    }
                    result
                }
                FreestType::Forall { var, body, .. } => {
                    let mut free_in_body = body.free_variables();
                    free_in_body.remove(var);
                    free_in_body
                }
                FreestType::Var(label) => HashSet::from([label.clone()]),
            }
        }
    }

    fn session_op() -> impl Strategy<Value = SessionOp> {
        prop_oneof![Just(SessionOp::Recv), Just(SessionOp::Send)]
    }

    const KEYWORDS: [&str; 2] = ["if", "of"];

    fn ty_label() -> impl Strategy<Value = Label> {
        (
            prop::char::range('a', 'z'),
            prop::collection::vec(
                prop_oneof![prop::char::range('a', 'z'), prop::char::range('A', 'Z')],
                0..4,
            ),
        )
            .prop_map(|(c, cs)| {
                let mut str = String::new();
                str.push(c);
                for c in cs {
                    str.push(c);
                }
                str
            })
            .prop_filter("keyword", |label| !KEYWORDS.contains(&label.as_str()))
    }

    fn choice_label() -> impl Strategy<Value = Label> {
        (
            prop::char::range('A', 'Z'),
            prop::collection::vec(
                prop_oneof![prop::char::range('a', 'z'), prop::char::range('A', 'Z')],
                0..4,
            ),
        )
            .prop_map(|(c, cs)| {
                let mut str = String::new();
                str.push(c);
                for c in cs {
                    str.push(c);
                }
                str
            })
            .prop_filter("keyword", |label| !KEYWORDS.contains(&label.as_str()))
    }

    fn freest_functional_primitive(bound_vars: Vec<String>) -> BoxedStrategy<Box<FreestType>> {
        let basic_primitives = prop_oneof![
            Just(FreestType::Bool),
            Just(FreestType::Int),
            Just(FreestType::String),
            Just(FreestType::Unit),
        ];
        if bound_vars.is_empty() {
            basic_primitives.prop_map(Box::new).boxed()
        } else {
            prop_oneof![
                basic_primitives,
                proptest::sample::select(bound_vars.clone()).prop_map(FreestType::Var)
            ]
            .prop_map(Box::new)
            .boxed()
        }
    }

    fn freest_session_primitive(
        forall_vars: Vec<String>,
        sess_vars: Vec<String>,
    ) -> BoxedStrategy<FreestType> {
        let mut strategy = prop_oneof![
            Just(FreestType::Skip),
            session_op().prop_map(FreestType::End),
            (session_op(), freest_functional_type(forall_vars.clone()))
                .prop_map(|(dir, ty)| FreestType::Message { dir, ty }),
        ]
        .boxed();
        if !sess_vars.is_empty() {
            strategy = prop_oneof![
                strategy,
                proptest::sample::select(sess_vars.clone()).prop_map(FreestType::Var),
            ]
            .boxed();
        }
        strategy.boxed()
    }

    fn freest_functional_type(bound_vars: Vec<String>) -> impl Strategy<Value = Box<FreestType>> {
        let leaf = freest_functional_primitive(bound_vars.clone());
        leaf.prop_recursive(
            4,  // depth
            32, // desired_size
            4,  // expected_branch_size
            |inner| {
                prop_oneof![
                    prop::collection::vec(inner.clone(), 1..10)
                        .prop_map(FreestType::Tuple)
                        .prop_map(Box::new),
                    (inner.clone(), inner.clone())
                        .prop_map(|(param, ret)| FreestType::Arrow { param, ret })
                        .prop_map(Box::new),
                ]
            },
        )
        // Add forall quantifiers on top
        .prop_map(move |ty| {
            let mut ty = ty;
            for var in bound_vars.iter() {
                ty = Box::new(FreestType::Forall {
                    var: var.clone(),
                    kind: Kind::Type,
                    body: ty,
                })
            }
            ty
        })
    }

    fn freest_session_type(
        forall_vars: Vec<String>,
        session_vars: Vec<String>,
    ) -> impl Strategy<Value = Box<FreestType>> {
        let leaf =
            freest_session_primitive(forall_vars.clone(), session_vars.clone()).prop_map(Box::new);

        leaf.prop_recursive(
            4,  // depth
            32, // desired_size
            4,  // expected_branch_size
            |inner| {
                prop_oneof![
                    (inner.clone(), inner.clone())
                        .prop_map(|(first, second)| FreestType::Semi { first, second })
                        .prop_map(Box::new),
                    (
                        session_op(),
                        prop::collection::vec((choice_label(), inner.clone()), 1..3)
                    )
                        .prop_map(|(dir, branches)| { FreestType::Choice { dir, branches } })
                        .prop_map(Box::new)
                ]
            },
        )
        // Add forall quantifiers on top
        .prop_map(move |mut ty| {
            let type_vars = ty
                .free_variables()
                .into_iter()
                .filter(|var| forall_vars.contains(var));
            for var in type_vars {
                ty = Box::new(FreestType::Forall {
                    var: var.to_owned(),
                    kind: Kind::Type,
                    body: ty,
                });
            }
            let sess_vars = ty
                .free_variables()
                .into_iter()
                .filter(|var| session_vars.contains(var));
            for var in sess_vars {
                ty = Box::new(FreestType::Forall {
                    var: var.to_owned(),
                    kind: Kind::Session,
                    body: ty,
                });
            }
            ty
        })
    }

    static FREEST_AVAILABLE: OnceLock<bool> = OnceLock::new();

    fn freest_available() -> bool {
        *FREEST_AVAILABLE.get_or_init(|| {
            Command::new("freest")
                .arg("--help")
                .status()
                .map(|status| status.success())
                .unwrap_or(false)
        })
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            // Setting both fork and timeout is redundant since timeout implies
            // fork, but both are shown for clarity.
            fork: true,
            cases: 10,
            max_global_rejects: 1,
            .. ProptestConfig::default()
        })]
        #[test]
        fn freest_functional_type_display(
            ty in prop::collection::vec(ty_label(), 0..5)
                .prop_flat_map(freest_functional_type)
        ) {
            assert!(freest_available(), "'freest' executable not found on PATH");
            let mut test_file = Builder::new().suffix(".fst").disable_cleanup(true).tempfile()?;
            writeln!(test_file, "
                module Test where
                type T : 1T
                type T = {}", ty)?;
            test_file.flush()?;

            let freest_cmd = Command::new("freest").arg(test_file.path()).output()?;
            let error_output = String::from_utf8(freest_cmd.stderr)?;

            assert!(freest_cmd.status.success(), "TEST OUTPUT: {}", error_output);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            // Setting both fork and timeout is redundant since timeout implies
            // fork, but both are shown for clarity.
            fork: true,
            cases: 10,
            max_global_rejects: 1,
            .. ProptestConfig::default()
        })]
        #[test]
        fn freest_session_type_display(
            ty in (prop::collection::vec(ty_label(), 0..6))
                .prop_flat_map(|vars| {
                    let (ty_vars, sess_vars) = vars.split_at(vars.len() / 2);
                    freest_session_type(Vec::from(ty_vars), Vec::from(sess_vars))
                })
        ) {
            assert!(freest_available(), "'freest' executable not found on PATH");

            let mut test_file = Builder::new().suffix(".fst").disable_cleanup(true).tempfile()?;
            writeln!(test_file, "
                module Test where
                type T : 1S
                type T = {}", ty)?;
            test_file.flush()?;

            let freest_cmd = Command::new("freest").arg(test_file.path()).output()?;
            let error_output = String::from_utf8(freest_cmd.stderr)?;

            assert!(freest_cmd.status.success(), "TEST OUTPUT: {}", error_output);
        }
    }
}
