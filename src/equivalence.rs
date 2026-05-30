use crate::{freest, syntax::CFSession};

use std::{io::Write, process::Command};

enum TypecheckResult {
    Success,
    Error { reason: String },
}

fn check_equivalence(type1: &CFSession, type2: &CFSession) -> TypecheckResult {
    let mut test_file = tempfile::Builder::new()
        .suffix(".fst")
        .disable_cleanup(true)
        .tempfile()
        .unwrap();

    writeln!(test_file, "data Ret = Ret").unwrap();

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
    fn equivalence_ret() {
        let type1 = session_type! { Ret };
        let type2 = session_type! { Ret };

        assert_success(check_equivalence(&type1, &type2));
    }
}
