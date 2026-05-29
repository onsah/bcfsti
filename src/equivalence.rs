use crate::{freest, syntax::CFSession};

use std::{io::Write, process::Command};

enum TypecheckResult {
    Success,
    Error { reason: String },
}

impl TypecheckResult {
    fn is_success(&self) -> bool {
        matches!(self, TypecheckResult::Success)
    }
}

fn check_equivalence(type1: &CFSession, type2: &CFSession) -> TypecheckResult {
    let mut test_file = tempfile::Builder::new()
        .suffix(".fst")
        .disable_cleanup(true)
        .tempfile()
        .unwrap();

    let freest_type1 = freest::Type::from(type1);
    writeln!(test_file, "type T1 = {}", freest_type1).unwrap();
    let freest_type2 = freest::Type::from(type2);
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

#[cfg(test)]
mod tests {
    use crate::{
        equivalence::check_equivalence,
        session_type,
        syntax::{CFSession, CFType, SCFSession, SCFType, SLabel, SessionOp},
        util::span::Spanned,
    };

    fn spanned_type(cf_type: CFType) -> SCFType {
        Spanned::new(cf_type, 0..0)
    }

    fn spanned_session(cf_session: CFSession) -> SCFSession {
        Spanned::new(cf_session, 0..0)
    }

    fn session_op(session_op: SessionOp, typ: CFType) -> CFSession {
        CFSession::Op(session_op, Box::new(spanned_type(typ)))
    }

    fn label(label: &str) -> SLabel {
        Spanned::new(label.to_string(), 0..0)
    }

    #[test]
    fn equivalence_skip_identity() {
        // !Int; Skip
        let type1 = CFSession::Semi {
            first: Box::new(spanned_session(session_op(SessionOp::Send, CFType::Int))),
            second: Box::new(spanned_session(CFSession::Skip)),
        };

        // Skip; !Int
        let type2 = CFSession::Semi {
            first: Box::new(spanned_session(CFSession::Skip)),
            second: Box::new(spanned_session(session_op(SessionOp::Send, CFType::Int))),
        };

        // !Int
        let type3 = session_op(SessionOp::Send, CFType::Int);

        assert!(check_equivalence(&type1, &type2).is_success());
        assert!(check_equivalence(&type2, &type3).is_success());
        assert!(check_equivalence(&type1, &type3).is_success());
    }

    #[test]
    fn equivalence_semi_associative() {
        // !Int; (!Bool; !String)
        let type1 = session_type! { !Int; (!Bool; !String) };

        // (!Int; !Bool); !String
        let type2 = session_type! { (!Int; !Bool); !String };

        assert!(check_equivalence(&type1, &type2).is_success());
    }

    #[test]
    fn equivalence_branch_semi() {
        // &{ l1: !Int, l2: !Bool }; ?Int
        let type1 = session_type! { &{ l1: !Int, l2: !Bool }; ?Int };

        // &{ l1: !Int; ?Int, l2: !Bool; ?Int }
        let type2 = session_type! { &{ l1: !Int; ?Int, l2: !Bool; ?Int } };

        assert!(check_equivalence(&type1, &type2).is_success());
    }

    #[test]
    fn equivalence_rec_non_occurence() {
        // rec x. !Int; ?Int
        let type1 = session_type! { mu x. !Int; ?Int };

        // !Int; ?Int
        let type2 = session_type! { !Int; ?Int };

        assert!(check_equivalence(&type1, &type2).is_success());
    }
}
