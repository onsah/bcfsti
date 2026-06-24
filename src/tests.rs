use std::{io::Write, path::PathBuf};

use crate::{
    constraint::Constraints,
    error_reporting::{IErr, report_error},
    syntax::{Eff, SExpr, Type},
    typecheck,
};

pub fn typecheck_(src: &str, src_path: &str) -> Result<(SExpr, Type, Constraints, Eff), IErr> {
    typecheck(src, false).map_err(|e| {
        report_error(src_path, &src, e.clone());
        e
    })
}

macro_rules! logln {
    ($($args:tt)*) => {
        writeln!(::std::io::stdout(), $($args)*).unwrap()
    };
}

#[cfg(test)]
mod typechecker_tests {
    use std::assert_matches;

    use crate::{
        constraint::Constraints,
        error_reporting::IErr,
        session_type,
        syntax::{Eff, Expr, Mult, Session, Type},
        type_checker::TypeError,
        typecheck,
        util::span::fake_span,
    };

    #[test]
    fn session_type_new() {
        let src = r#"
            new &{ foo: !Int; ?Int, bar: ?Unit }
        "#;
        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::MainReturnsOrd(_, _))));

        let src = r#"
            new Close
        "#;
        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::TypeNotValidForNew(_))));

        let src = r#"
            new &{ foo: Close; ?Int, bar: ?Unit }
        "#;
        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::TypeNotValidForNew(_))));

        let src = r#"
            new &{ foo: !Int; ?Int, bar: Wait }
        "#;
        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::TypeNotValidForNew(_))));
    }

    #[test]
    fn fork() {
        let src = r#"
            let cs, cr = new !Int in
            fork (\ x.
                let cs1, cs2 = lsplit Acq cs in
                acquire cs1;
                send @Int 5 cs2
            );
            let cr1, cr2 = lsplit Acq cr in
            acquire cr1;
            recv @Int cr2
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Int, _, Eff::Yes)));
    }

    #[test]
    fn lsplit_only_skips() {
        let src = r#"
            let c1, c2 = new Skip in
            lsplit (Skip; Skip) c1;
            acquire c2
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::SessionTypeOnlySkips(_))));
    }

    #[test]
    fn new_and_close() {
        let src = r#"
            let cs, cr = new !Int in
            let cs1, cs2 = lsplit Acq cs in
            acquire cs1;
            let cs3, cs4 = lsplit !Int cs2 in
            send @Int 5 cs3;
            wait cs4;
            let cr1, cr2 = lsplit Acq cr in
            acquire cr1;
            let cr3, cr4 = lsplit ?Int cr2 in
            recv @Int cr3;
            drop cr4
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Unit, _, Eff::Yes)));
    }

    #[test]
    fn rsplit() {
        let src = r#"
            let
                foo : !Int; ?Int -[m u 1]-> Acq; ?Int
                foo c =
                    let cp, cs = rsplit !Int c in
                    let cp1, cp2 = lsplit !Int cp in
                    send @Int 5 cp1;
                    drop cp2;
                    cs
            in
            unit
        "#;

        let res = typecheck(src, false);
        let expected_constraints = {
            let mut cs = Constraints::empty();
            cs.add(
                fake_span(Type::Chan(session_type! { Session::UVar(1) })),
                fake_span(Type::Chan(session_type! { Ret }.val)),
            );
            cs.add(
                fake_span(Type::Chan(session_type! { !Int; Ret }.val)),
                fake_span(Type::Chan(
                    session_type! { !Int; fake_span(Session::UVar(1)) }.val,
                )),
            );
            cs.add(
                fake_span(Type::Chan(session_type! { !Int; ?Int }.val)),
                fake_span(Type::Chan(
                    session_type! { !Int; fake_span(Session::UVar(0)) }.val,
                )),
            );
            cs.add(
                fake_span(Type::Chan(
                    session_type! { Acq; fake_span(Session::UVar(0)) }.val,
                )),
                fake_span(Type::Chan(session_type! { Acq; ?Int }.val)),
            );
            cs
        };
        assert_matches!(res, Ok((_, Type::Unit, _, Eff::No)));
        let Ok((_, _, constraints, _)) = res else {
            unreachable!()
        };
        assert_eq!(constraints, expected_constraints);
    }

    #[test]
    fn app() {
        let src = r#"
            let
                foo: !Int; ?Int -[m u 1]-> ?Int
                foo c =
                    let c1, c2 = lsplit !Int c in
                    send @Int 5 c1;
                    c2
            in
            let
                bar : !Int; ?Int -[m u 1]-> ?Int
                bar c = foo c
            in
            unit
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Unit, _, Eff::No)));

        let src = r#"
            let
                foo: !Int; ?Int -[m u 1]-> ?Int
                foo c =
                    let c1, c2 = lsplit !Int c in
                    send @Int 5 c1;
                    c2
            in
            let
                bar : !Int; ?Int -[m u 0]-> ?Int
                bar c = foo c
            in
            unit
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::MismatchEffSub(_, _, _))));
    }

    #[test]
    fn pair() {
        let src = r#"
        let
            foo : Unit -[m u 0]-> Int *[u] Unit
            foo c =
                (7, unit)
        in
        foo unit
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Prod { .. }, _, Eff::No)));
        let Ok((
            _,
            Type::Prod {
                mult,
                first,
                second,
            },
            _,
            _,
        )) = res
        else {
            unreachable!()
        };
        assert_eq!(*mult, Mult::Unr);
        assert_eq!(**first, Type::Int);
        assert_eq!(**second, Type::Unit);

        let src = r#"
        let
            foo : ?Int -[m u 1]-> Int *[r] Unit
            foo c =
                (recv @Int c, unit)
        in
        unit
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::MismatchEff(_, _, _))));
        let Err(IErr::Typing(TypeError::MismatchEff(expr, _, eff))) = res else {
            unreachable!()
        };
        assert_eq!(*eff, Eff::No);
        let Expr::Recv(ty, chan) = &expr.val else {
            unreachable!("{:?}", &expr.val)
        };
        assert_eq!(ty.val, Type::Int);
        assert_matches!(chan.val, Expr::Var(_));
        let Expr::Var(chan_name) = &chan.val else {
            unreachable!()
        };
        assert_eq!(chan_name.val, "c");

        let src = r#"
        let
            foo : ?Int -[m u 1]-> Int *[l] Unit
            foo c =
                (7, recv @Int c)
        in
        unit
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::MismatchEff(_, _, _))));
        let Err(IErr::Typing(TypeError::MismatchEff(expr, _, eff))) = res else {
            unreachable!()
        };
        assert_eq!(*eff, Eff::No);
        // The mismatched expression should be the recv on the right
        let Expr::Recv(ty_r, chan_r) = &expr.val else {
            unreachable!("{:?}", &expr.val)
        };
        assert_eq!(ty_r.val, Type::Int);
        assert_matches!(chan_r.val, Expr::Var(_));
        let Expr::Var(chan_name_r) = &chan_r.val else {
            unreachable!()
        };
        assert_eq!(chan_name_r.val, "c");

        let src = r#"
            (7, recv @Int c)
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::TypeAnnotationMissing(_))));
    }

    #[test]
    fn inj() {
        let src = r#"
            inj foo 5
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::TypeAnnotationMissing(_))));

        let src = r#"
            (inj foo 5) : < foo: Int, bar: String >
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Variant { .. }, _, _)));
    }

    #[test]
    fn case() {
        let src = r#"
          case (inj foo 5 : < foo: Int, bar: String, baz: Bool >) {
            foo i -> { i }
            bar s -> { s }
            baz b -> { b }
          }
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Int, _, _)));
        let Ok((_, Type::Int, cs, _)) = res else {
            unreachable!()
        };
        let expected_constraints = {
            let mut cs = Constraints::empty();
            cs.add(fake_span(Type::Int), fake_span(Type::String));
            cs.add(fake_span(Type::Int), fake_span(Type::Bool));
            cs.add(fake_span(Type::String), fake_span(Type::Bool));
            cs
        };
        assert_eq!(cs, expected_constraints);

        let src = r#"
          case (inj foo 5 : < foo: Int, bar: String >) {
            foo i -> { i }
          }
        "#;

        let res = typecheck(src, false);
        let Err(IErr::Typing(TypeError::CaseMissingLabel(_, _, label))) = res else {
            panic!("Expected MismatchLabel, got {:?}", res);
        };
        assert_eq!(&label, "bar");

        let src = r#"
          case (inj foo 5 : < foo: Int >) {
            foo i -> { i }
            bar s -> { 42 }
          }
        "#;

        let res = typecheck(src, false);
        let Err(IErr::Typing(TypeError::CaseExtraLabel(_, _, label))) = res else {
            panic!("Expected MismatchLabel, got {:?}", res);
        };
        assert_eq!(&label, "bar");

        let src = r#"
          case (inj foo 5 : < foo: Int, bar: String >) {
            foo i -> { i }
            foo j -> { j }
            bar s -> { 42 }
          }
        "#;

        let res = typecheck(src, false);
        let Err(IErr::Typing(TypeError::CaseDuplicateLabel(_, _, label))) = res else {
            panic!("Expected CaseDuplicateLabel, got {:?}", res);
        };
        assert_eq!(&label, "foo");

        let src = r#"
          case (inj foo 5 : < foo: Int, foo: String >) {
            foo i -> { i }
          }
        "#;

        let res = typecheck(src, false);
        let Err(IErr::Typing(TypeError::VariantDuplicateLabel(_, _, label))) = res else {
            panic!("Expected VariantDuplicateLabel, got {:?}", res);
        };
        assert_eq!(&label, "foo");
    }

    #[test]
    fn let_() {
        let src = r#"
            (\f.
            let x = 5 in
            f x) : (Int -[m u 0]-> !Int; ?String) -[m u 1]-> ?String
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Arr { .. }, _, _)));
        let Ok((_, Type::Arr { ret, .. }, _, _)) = res else {
            unreachable!()
        };
        assert_eq!(ret.val, Type::Chan(session_type! { ?String }.val));

        let src = r#"
            let x = 5 in
            let x = 3 in
            x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::Shadowing(_, _))));
    }

    #[test]
    fn select() {
        let src = r#"
            (\c.
            let c1 = select bar c in
            send @Int 42 c1) : +{ foo: ?Int; ?String, bar: !Int } -[m u 1]-> ?String
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Arr { .. }, _, Eff::No)));

        let src = r#"
            (\c.
            let c1, c2 = lsplit !Int c in
            send @Int 42 c1;
            let c3 = select bar c2 in
            send @Int 42 c3) : !Int;+{ foo: ?Int; ?String, bar: !Int } -[m u 1]-> ?String
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::TypeAnnotationMissing(_))));

        let src = r#"
            let c = select foo 5 in
            c
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::Mismatch(_, _, _))));
    }

    #[test]
    fn branch() {
        let src = r#"
            (\c.
            case branch c {
                foo c1 -> { recv @Int c1 }
                bar c2 -> { send @Int 42 c2; 42 }
            }) : &{ foo: ?Int, bar: !Int } -[m u 1]-> Int
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Arr { .. }, _, Eff::No)));

        let src = r#"
            (\c.
            case branch c {
                foo c1 -> { recv @Int c1 }
            }) : &{ foo: ?Int, bar: !Int } -[m u 1]-> Int
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::CaseMissingLabel(_, _, _))));
        let Err(IErr::Typing(TypeError::CaseMissingLabel(_, _, label))) = res else {
            unreachable!()
        };
        assert_eq!(&label, "bar");

        let src = r#"
            (\c.
            case branch c {
                foo c1 -> { recv @Int c1 }

                bar c2 -> { send @Int 42 c2; 42 }
            }) : &{ foo: ?Int } -[m u 1]-> Int
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::CaseExtraLabel(_, _, _))));
        let Err(IErr::Typing(TypeError::CaseExtraLabel(_, _, label))) = res else {
            unreachable!()
        };
        assert_eq!(&label, "bar");
    }

    #[test]
    fn op1() {
        let src = r#"
            let x = 5 in
            -x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Int, _, Eff::No)));

        let src = r#"
            let x = true in
            -x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::Mismatch(_, _, _))));
        let Err(IErr::Typing(TypeError::Mismatch(_, expected_ty, _))) = res else {
            unreachable!()
        };
        assert_eq!(expected_ty, Err("Int".to_owned()));

        let src = r#"
            let x = true in
            !x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Bool, _, Eff::No)));

        let src = r#"
            let x = 5 in
            !x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::Mismatch(_, _, _))));
        let Err(IErr::Typing(TypeError::Mismatch(_, expected_ty, _))) = res else {
            unreachable!()
        };
        assert_eq!(expected_ty, Err("Bool".to_owned()));

        let src = r#"
            let x = true in
            str x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::String, _, Eff::No)));

        let src = r#"
            let x = 5 in
            str x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::String, _, Eff::No)));

        let src = r#"
            let x = true in
            print x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Unit, _, Eff::No)));

        let src = r#"
            let x = 5 in
            print x
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Unit, _, Eff::No)));
    }

    #[test]
    fn op2() {
        let src = r#"
            let x = 5 in
            let y = 10 in
            x + y
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Int, _, Eff::No)));

        let src = r#"
            let x = "foo" in
            let y = "bar" in
            x + y
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::String, _, Eff::No)));

        let src = r#"
            let x = 5 in
            let y = true in
            x + y
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::Op2Mismatch(_, _, _, _))));
        let Err(IErr::Typing(TypeError::Op2Mismatch(_, expected_ty, _, _))) = res else {
            unreachable!()
        };
        assert_eq!(expected_ty, Err("String or Int".to_owned()));

        let src = r#"
            let x = true in
            let y = false in
            x && y
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Bool, _, Eff::No)));

        let src = r#"
            let x = true in
            let y = 5 in
            x || y
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Err(IErr::Typing(TypeError::Op2Mismatch(_, _, _, _))));
        let Err(IErr::Typing(TypeError::Op2Mismatch(_, expected_ty, _, _))) = res else {
            unreachable!()
        };
        assert_eq!(expected_ty, Err("Bool".to_owned()));
    }

    #[test]
    fn if_() {
        let src = r#"
            if true then 5 else 10
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Int, _, Eff::No)));

        let src = r#"
            if true then 5 else "foo"
        "#;

        let res = typecheck(src, false);
        assert_matches!(res, Ok((_, Type::Int, _, Eff::No)));
        let Ok((_, _, cs, _)) = res else {
            unreachable!()
        };

        assert!(cs.into_iter().any(
            |(ty1, ty2)| (ty1.val == Type::Int && ty2.val == Type::String)
                || (ty1.val == Type::String && ty2.val == Type::Int)
        ));
    }
}

#[test]
fn unit_tests() {
    let positives: Vec<PathBuf> = std::fs::read_dir("examples/positive")
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    let negatives: Vec<PathBuf> = std::fs::read_dir("examples/negative")
        .unwrap()
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    let mut failures_pos = vec![];
    for (i, p) in positives.iter().enumerate() {
        let name = p.to_string_lossy().to_string();
        logln!(
            "\n================================================================================"
        );
        logln!(
            "Running positive test {} / {}: {}\n",
            i + 1,
            positives.len(),
            name
        );
        let src = std::fs::read_to_string(p).unwrap();
        let res = typecheck_(&src, &name);
        if res.is_ok() {
            logln!("TEST SUCCEEDED.")
        } else {
            logln!("TEST FAILED.");
            failures_pos.push(name.clone())
        }
    }
    let mut failures_neg = vec![];
    for (i, p) in negatives.iter().enumerate() {
        let name = p.to_string_lossy().to_string();
        logln!(
            "\n================================================================================"
        );
        logln!(
            "Running negative test {} / {}: {}\n",
            i + 1,
            negatives.len(),
            name
        );
        let src = std::fs::read_to_string(p).unwrap();
        let res = typecheck_(&src, &name);
        if res.is_err() {
            logln!("TEST SUCCEEDED.")
        } else {
            logln!("TEST FAILED.");
            failures_neg.push(name.clone())
        }
    }
    logln!("\n================================================================================\n");
    if failures_pos.len() == 0 && failures_neg.len() == 0 {
        logln!("ALL {} TESTS PASSED!", positives.len() + negatives.len())
    } else {
        logln!(
            "{} TESTS FAILED:\n",
            failures_neg.len() + failures_pos.len()
        );
        for n in failures_neg {
            logln!("  {n}")
        }
        for n in failures_pos {
            logln!("  {n}")
        }
        assert!(false)
    }
}
