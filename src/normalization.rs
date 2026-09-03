use crate::{
    kinding,
    syntax::{Id, SSession, SType, Session, Type},
    type_alias::AliasEnv,
    type_checker::TypeError,
    type_context::TypeCtx,
    util::span::{Spanned, fake_span},
};

pub(crate) fn normalise(
    ty_ctx: &TypeCtx,
    alias_env: &AliasEnv,
    ty: &SType,
) -> Result<SType, TypeError> {
    kinding::infer(ty_ctx, alias_env, ty)?;
    Ok(Spanned::new(
        normalise_type(alias_env, &ty.val),
        ty.span.clone(),
    ))
}

pub(crate) fn normalise_session(
    ty_ctx: &TypeCtx,
    alias_env: &AliasEnv,
    session: &SSession,
) -> Result<SSession, TypeError> {
    kinding::check_session(ty_ctx, alias_env, session)?;
    Ok(Spanned::new(
        normalise_session_type(alias_env, &session.val),
        session.span.clone(),
    ))
}

fn normalise_type(alias_env: &AliasEnv, ty: &Type) -> Type {
    match ty {
        Type::Chan(session) => Type::Chan(normalise_session_type(alias_env, session)),
        _ => ty.clone(),
    }
}

fn normalise_session_type(alias_env: &AliasEnv, session: &Session) -> Session {
    match session {
        Session::Semi { first, second } => {
            if first.val.is_only_skips() {
                normalise_session_type(alias_env, &second.val)
            } else {
                let normalised_first = normalise_session_type(alias_env, &first.val);
                match normalised_first {
                    Session::Choice(op, branches) => Session::Choice(
                        op.clone(),
                        branches
                            .iter()
                            .map(|(label, branch)| {
                                (
                                    label.clone(),
                                    fake_span(Session::Semi {
                                        first: Box::new(branch.clone()),
                                        second: second.clone(),
                                    }),
                                )
                            })
                            .collect(),
                    ),
                    _ => concatenate_sessions(&normalised_first, &second.val),
                }
            }
        }
        Session::Mu(var, body) => {
            let normalised_body = normalise_session_type(alias_env, &body.val);
            let recursive_type =
                Session::Mu(var.clone(), Box::new(fake_span(normalised_body.clone())));
            subst_session(&normalised_body, &var.val, &recursive_type)
        }
        Session::Var(id) => {
            let session = alias_env.get(&id.val).expect(
                "Bug: well formed types must have their free recursion variables defined in the alias environment",
            );
            normalise_session_type(alias_env, &session.val)
        }
        _ => session.clone(),
    }
}

fn concatenate_sessions(first: &Session, second: &Session) -> Session {
    match (first, second) {
        (_, Session::Skip) => first.clone(),
        (
            Session::Semi {
                first: f,
                second: s,
            },
            other,
        ) => Session::Semi {
            first: f.clone(),
            second: Box::new(fake_span(concatenate_sessions(&s.val, other))),
        },
        (s1, s2) => Session::Semi {
            first: Box::new(fake_span(s1.clone())),
            second: Box::new(fake_span(s2.clone())),
        },
    }
}

fn subst_session(session: &Session, var: &Id, s_new: &Session) -> Session {
    match session {
        Session::Var(y) if *var == **y => s_new.clone(),
        Session::Var(y) => Session::Var(y.clone()),
        Session::Mu(y, e) => {
            if var != &y.val {
                Session::Mu(
                    y.clone(),
                    Box::new(fake_span(subst_session(&e.val, var, s_new))),
                )
            } else {
                session.clone()
            }
        }
        Session::Op(op, t) => Session::Op(op.clone(), t.clone()),
        Session::Choice(op, cs) => {
            let cs2 = cs
                .iter()
                .map(|(l, s)| (l.clone(), fake_span(subst_session(&s.val, var, s_new))))
                .collect();
            Session::Choice(op.clone(), cs2)
        }
        Session::Semi { first, second } => Session::Semi {
            first: Box::new(fake_span(subst_session(&first.val, var, s_new))),
            second: Box::new(fake_span(subst_session(&second.val, var, s_new))),
        },
        Session::End(_)
        | Session::BorrowEnd(_)
        | Session::Skip
        | Session::UVar(_)
        | Session::PVar { .. } => session.clone(),
    }
}

#[cfg(test)]
mod tests {
    use crate::{normalization::normalise_session_type, session_type, type_alias::AliasEnv};

    #[test]
    fn normalise_rec_idempotency() {
        let session = session_type! { mu X. !Int; X };

        let normalized1 = normalise_session_type(&AliasEnv::new(), &session);

        assert_eq!(normalized1, session_type! { !Int; (mu X. !Int; X) }.val);

        let normalized2 = normalise_session_type(&AliasEnv::new(), &normalized1);

        assert_eq!(normalized1, normalized2);
    }
}
