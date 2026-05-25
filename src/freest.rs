use std::{
    fmt::{self},
    vec,
};

use crate::syntax::{CFSession, CFType, Eff, Label, Mult, SessionOp};

pub fn is_equivalent(_type1: &Type, _type2: &Type) -> bool {
    todo!()
}

pub struct Type(FreestType);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FreestType {
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
    Forall {
        var: Label,
        body: Box<FreestType>,
    },
    Rec {
        var: Label,
        body: Box<FreestType>,
    },
    Var(Label),
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
                for ty in &tys[..tys.len() - 1] {
                    write!(f, "{}, ", ty)?;
                }
                write!(f, "{}", tys.last().unwrap())?;
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
            FreestType::Forall { var, body } => write!(f, "forall {}. {}", var, body),
            FreestType::Rec { var, body } => todo!(),
            FreestType::Var(label) => write!(f, "{}", label),
        }
    }
}

impl From<CFType> for Type {
    fn from(value: CFType) -> Self {
        Type(FreestType::Forall {
            var: RET_VAR_NAME.into(),
            body: FreestType::Forall {
                var: ACQ_VAR_NAME.into(),
                body: Box::new(value.into()),
            }
            .into(),
        })
    }
}

static RET_VAR_NAME: &str = "ret";
static ACQ_VAR_NAME: &str = "acq";

impl From<CFSession> for FreestType {
    fn from(value: CFSession) -> FreestType {
        match value {
            CFSession::Skip => FreestType::Skip,
            CFSession::Semi { first, second } => FreestType::Semi {
                first: Box::new(first.val.into()),
                second: Box::new(second.val.into()),
            },
            CFSession::End(session_op) => FreestType::End(session_op),
            CFSession::Op(session_op, ty) => FreestType::Message {
                dir: session_op,
                ty: Box::new(ty.val.into()),
            },
            CFSession::Choice(session_op, items) => FreestType::Choice {
                dir: session_op,
                branches: items
                    .into_iter()
                    .map(|(label, ty)| (label.val, Box::new(ty.val.into())))
                    .collect(),
            },
            CFSession::Mu(var, body) => FreestType::Rec {
                var: var.val,
                body: Box::new(body.val.into()),
            },
            CFSession::Var(var) => FreestType::Var(var.val),
            CFSession::BorrowEnd(session_op) => match session_op {
                SessionOp::Send => FreestType::Var(RET_VAR_NAME.into()),
                SessionOp::Recv => FreestType::Var(ACQ_VAR_NAME.into()),
            },
        }
    }
}

impl From<CFType> for FreestType {
    fn from(value: CFType) -> FreestType {
        match value {
            CFType::Chan(cfsession) => cfsession.into(),
            CFType::Variant(items) => FreestType::Tuple(vec![
                Box::new(FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: items
                        .into_iter()
                        .map(|(label, ty)| (label.val, Box::new(ty.val.into())))
                        .collect(),
                }),
                Box::new(FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: vec![("variant".into(), FreestType::Skip.into())],
                }),
            ]),
            CFType::Unit => todo!(),
            CFType::Int => todo!(),
            CFType::Bool => todo!(),
            CFType::String => todo!(),
            CFType::Arr {
                mult,
                eff,
                param,
                ret,
            } => {
                let mut labels = vec![mult.to_label()];
                if let Some(label) = eff.to_label() {
                    labels.push(label);
                }

                FreestType::Tuple(vec![
                    FreestType::Arrow {
                        param: Box::new(param.val.into()),
                        ret: Box::new(ret.val.into()),
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
            CFType::Prod {
                mult,
                first,
                second,
            } => FreestType::Tuple(vec![
                Box::new(first.val.into()),
                Box::new(second.val.into()),
                FreestType::Choice {
                    dir: SessionOp::Recv,
                    branches: vec![(mult.to_label().into(), FreestType::Skip.into())],
                }
                .into(),
            ]),
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
    use std::sync::OnceLock;
    use std::{io::Write, process::Command};

    // Bring the macros and other important things into scope.
    use proptest::prelude::*;
    use tempfile::Builder;

    use crate::freest::FreestType;
    use crate::syntax::{Label, SessionOp};

    fn session_op() -> impl Strategy<Value = SessionOp> {
        prop_oneof![Just(SessionOp::Recv), Just(SessionOp::Send)]
    }

    fn label() -> impl Strategy<Value = Label> {
        prop::string::string_regex("[a-zA-Z]+").unwrap()
    }

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

    fn freest_session_primitive() -> impl Strategy<Value = FreestType> {
        prop_oneof![
            Just(FreestType::Skip),
            session_op().prop_map(FreestType::End),
            (session_op(), freest_functional_type(Vec::new()))
                .prop_map(|(dir, ty)| FreestType::Message { dir, ty })
        ]
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
                    body: ty,
                })
            }
            ty
        })
    }

    fn freest_session_type() -> impl Strategy<Value = Box<FreestType>> {
        let leaf = freest_session_primitive().prop_map(Box::new);
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
                        prop::collection::vec((label(), inner.clone()), 1..10)
                    )
                        .prop_map(|(dir, branches)| { FreestType::Choice { dir, branches } })
                        .prop_map(Box::new)
                ]
            },
        )
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
            cases: 100,
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
            writeln!(test_file, "type T = {}", ty)?;
            test_file.flush()?;

            println!("Type: {}", ty);

            let freest_cmd = Command::new("freest").arg("--subtyping").arg(test_file.path()).output()?;
            let error_output = String::from_utf8(freest_cmd.stderr)?;

            assert!(freest_cmd.status.success(), "TEST OUTPUT: {}", error_output);
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig {
            // Setting both fork and timeout is redundant since timeout implies
            // fork, but both are shown for clarity.
            fork: true,
            cases: 100,
            max_global_rejects: 1,
            .. ProptestConfig::default()
        })]
        #[test]
        fn freest_session_type_display(ty in freest_session_type()) {
            assert!(freest_available(), "'freest' executable not found on PATH");

            let mut test_file = Builder::new().suffix(".fst").disable_cleanup(true).tempfile()?;
            writeln!(test_file, "type T = {}", ty)?;
            test_file.flush()?;

            println!("Type: {}", ty);

            let freest_cmd = Command::new("freest").arg("--subtyping").arg(test_file.path()).output()?;
            let error_output = String::from_utf8(freest_cmd.stderr)?;

            assert!(freest_cmd.status.success(), "TEST OUTPUT: {}", error_output);
        }
    }
}
