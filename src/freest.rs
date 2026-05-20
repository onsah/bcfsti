use std::{
    fmt::{self, write},
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
            FreestType::Arrow { param, ret } => todo!(),
            FreestType::Skip => todo!(),
            FreestType::End(session_op) => todo!(),
            FreestType::Semi { first, second } => todo!(),
            FreestType::Message { dir, ty } => todo!(),
            FreestType::Choice { dir, branches } => todo!(),
            FreestType::Forall { var, body } => todo!(),
            FreestType::Rec { var, body } => todo!(),
            FreestType::Var(_) => todo!(),
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
    use std::{
        fs::File,
        io::{Read, Write},
        process::Command,
    };

    // Bring the macros and other important things into scope.
    use proptest::prelude::*;
    use tempfile::{Builder, NamedTempFile};

    use crate::freest::FreestType;

    fn freest_primitive_strategy() -> impl Strategy<Value = FreestType> {
        prop_oneof![
            Just(FreestType::Bool),
            Just(FreestType::Int),
            Just(FreestType::String),
            Just(FreestType::Unit),
        ]
    }

    fn freest_tuple_strategy() -> impl Strategy<Value = Box<FreestType>> {
        let leaf = freest_primitive_strategy().prop_map(Box::new);
        leaf.prop_recursive(
            4, // depth
            16,
            4,
            |inner| {
                prop::collection::vec(inner.clone(), 1..10)
                    .prop_map(FreestType::Tuple)
                    .prop_map(Box::new)
            },
        )
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
        fn primitive(ty in freest_tuple_strategy()) {
            let mut test_file = Builder::new().suffix(".fst").disable_cleanup(true).tempfile()?;
            writeln!(test_file, "type T = {}", ty)?;
            test_file.flush()?;

            let freest_cmd = Command::new("freest").arg("--subtyping").arg(test_file.path()).output()?;

            assert!(freest_cmd.status.success());
        }
    }
}
