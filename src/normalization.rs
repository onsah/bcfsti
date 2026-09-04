use crate::{
    kinding,
    syntax::{SType, Type},
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

fn normalise_type(alias_env: &AliasEnv, ty: &Type) -> Type {
    match ty {
        Type::Semi { first, second } => {
            if first.val.is_only_skips() {
                normalise_type(alias_env, &second.val)
            } else {
                let normalised_first = normalise_type(alias_env, &first.val);
                match normalised_first {
                    Type::Choice(op, branches) => Type::Choice(
                        op.clone(),
                        branches
                            .iter()
                            .map(|(label, branch)| {
                                (
                                    label.clone(),
                                    fake_span(Type::Semi {
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
        Type::Mu(var, body) => {
            let normalised_body = normalise_type(alias_env, &body.val);
            let recursive_type =
                Type::Mu(var.clone(), Box::new(fake_span(normalised_body.clone())));
            normalised_body.subst(&var.val, &recursive_type)
        }
        Type::Var(id) => {
            let ty = alias_env.get(&id.val).expect(
                "Bug: well formed types must have their free recursion variables defined in the alias environment",
            );
            normalise_type(alias_env, &ty.val)
        }
        _ => ty.clone(),
    }
}

fn concatenate_sessions(first: &Type, second: &Type) -> Type {
    match (first, second) {
        (_, Type::Skip) => first.clone(),
        (
            Type::Semi {
                first: f,
                second: s,
            },
            other,
        ) => Type::Semi {
            first: f.clone(),
            second: Box::new(fake_span(concatenate_sessions(&s.val, other))),
        },
        (s1, s2) => Type::Semi {
            first: Box::new(fake_span(s1.clone())),
            second: Box::new(fake_span(s2.clone())),
        },
    }
}

#[cfg(test)]
mod tests {
    use crate::{normalization::normalise_type, session_type, type_alias::AliasEnv};

    #[test]
    fn normalise_rec_idempotency() {
        let session = session_type! { mu X. !Int; X };

        let normalized1 = normalise_type(&AliasEnv::new(), &session.val);

        assert_eq!(normalized1, session_type! { !Int; (mu X. !Int; X) }.val);

        let normalized2 = normalise_type(&AliasEnv::new(), &normalized1);

        assert_eq!(normalized1, normalized2);
    }
}
