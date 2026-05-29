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
        syntax::{CFSession, CFType, SCFSession, SCFType, SessionOp},
        util::span::Spanned,
    };

    fn spanned_type(cf_type: CFType) -> SCFType {
        Spanned::new(cf_type, 0..0)
    }

    fn spanned_session(cf_session: CFSession) -> Box<SCFSession> {
        Box::new(Spanned::new(cf_session, 0..0))
    }

    fn session_op(session_op: SessionOp, typ: CFType) -> CFSession {
        CFSession::Op(session_op, Box::new(spanned_type(typ)))
    }

    #[test]
    fn equivalence_skip_identity() {
        // !Int; Skip
        let type1 = CFSession::Semi {
            first: spanned_session(session_op(SessionOp::Send, CFType::Int)),
            second: spanned_session(CFSession::Skip),
        };

        // Skip; !Int
        let type2 = CFSession::Semi {
            first: spanned_session(CFSession::Skip),
            second: spanned_session(session_op(SessionOp::Send, CFType::Int)),
        };

        // !Int
        let type3 = session_op(SessionOp::Send, CFType::Int);

        assert!(check_equivalence(&type1, &type2).is_success());
        assert!(check_equivalence(&type2, &type3).is_success());
        assert!(check_equivalence(&type1, &type3).is_success());
    }
}
