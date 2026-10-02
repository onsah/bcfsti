# Polymorphic Type Definitions: Type Constructors, Type Application, and Reduction

Status: ready for implementation (all open questions resolved with the user, FreeST
behavior verified locally with scratch tests in `/tmp/opencode/freest_scratch{1,2,3}.fst`).

## Goal

Type definitions can take a list of type parameters, e.g.

```
rec type TreeChannel[a : Type] = &{ leaf: Skip, node: ?'a; TreeChannel['a]; TreeChannel['a] }
```

applied as `TreeChannel[Int]` / `TreeChannel['a]`. Kinds are extended with arrow kinds
(`k1 => k2`); the type syntax gains application `T1[T2]`; kinding gains the rules

```
Phi ⊢ T => (k1 => k2)    Phi ⊢ U <= k1            Phi, X:k1 ⊢ T => k2   (k1 base)
----------------------                      <=>    --------------------------------
       Phi ⊢ T[U] => k2                                Phi ⊢ \X:k1. T => (k1 => k2)
```

and a new private `reduce_ty_apps` in `src/normalization.rs` beta-reduces all type
applications during `normalise`.

## Resolved decisions (from user answers)

1. **Self-references in parameterized `rec type` bodies**: applied self-references
   whose arguments are exactly the parameter poly vars (`TreeChannel['a]`) are
   rewritten to the mu (recursion) variable. Bare self-references (`TreeChannel`
   without application) and self-applications with other arguments (`TreeChannel[Int]`)
   are **ill-formed → static errors**.
   *Consequence*: `examples/temp/polyReceiveTree.bgv` as written (bare refs) becomes
   invalid and must be updated to `TreeChannel['a]` (see Examples).
2. **Mu wrapping**: only `rec` definitions are `Mu`-wrapped (both parameterized and
   unparameterized). Non-`rec` definitions are stored as-is (needed for value-type
   bodies such as `type Pair[a:Type] = <l:'a, r:'a>`). Any self-reference in a
   non-`rec` definition is a **static error** (today every definition is silently
   `Mu`-wrapped; no existing example relies on self-reference without `rec` — verified).
3. **`rec type` with a value-type body** (e.g. `rec type Box[a:Type] = <some: 'a>`)
   is **rejected cleanly** (`Mu` requires a `Session` body); `check_contractive` must
   stop panicking on non-session bodies.
4. **Kinding of unapplied aliases**: on-demand inference of the alias definition
   (no cache), with an in-progress set guarding mutually recursive aliases. Unifies
   with unparameterized aliases: `rec` unparameterized still kind as `Session`
   (stored as `Mu`); non-`rec` unparameterized now get accurate kinds (improvement
   over today's lenient always-`Session`).
5. **FreeST translation**: parameterized (TyAbs-headed) aliases are emitted as
   FreeST type constructors (`type TreeChannel : 1T -> 1S. type TreeChannel a = T_0 a`).
   Verified: this shape passes `freest` (scratch3); unapplied constructor references
   and unbound vars fail (scratch1/2) but cannot arise because `normalise` fully
   inlines parameterized aliases and the converter renames every `Mu` to a fresh
   `T_n` label.

## Core representation (src/syntax.rs)

- `Kind` becomes (drop `Copy`, keep `Clone/Eq/Hash`):
  `Kind::Type | Kind::Session | Kind::Arrow(Box<Kind>, Box<Kind>)`
  - `is_subkind_of`: arrows are only subkinds of structurally equal arrows
    (`a1==a2 && b1==b2`, invariant); base kinds unchanged (`Session <= Type`).
  - Fix `Copy`-removal fallout at use sites (`kind.val` copies → `.clone()`).
- `Type` gains two variants (nested-unary representation, mirroring the unary
  kinding rule):
  - `Type::TyApp(Box<SType>, Box<SType>)` — head, single argument. `T[A, B]`
    curries at parse time into `TyApp(TyApp(T, A), B)`.
  - `Type::TyAbs { id: SPVarId, kind: SKind, body: Box<SType> }` — type-level
    lambda binding a **poly var** (parameters are referenced as `'a`, like
    polymorphic functions), so beta-reduction reuses `subst_poly` and kinding
    extends `TypeCtx` like a quantification binding.
- Extend every exhaustive `match` on `Type` in `syntax.rs`:
  - `is_closed`, `unification_variables`: recurse into both variants.
  - `poly_variables`, `poly_variables_under_prod_and_variant`: `TyApp` = union of
    children; `TyAbs` = body's poly vars minus the bound id (like `Abstraction`).
  - `subst_poly`: `TyApp` recurse; `TyAbs` — if the bound id is in the substitution
    map, return as-is (capture-avoiding: stop at re-binding), else recurse body.
  - `sem_eq_`: structural on both variants (id/kind/body, head/arg).
  - `subst` (mu-var substitution): recurse into both (they bind no `SId`s).
  - `is_only_skips`: `false` for both.
  - `dual`: `TyApp`/`TyAbs` → `panic!` with a clear message (like `BorrowEnd`;
    `dual` of an unreduced application is not computable syntactically).
  - `is_unr`: both → `todo!("Delete this function")` alongside `Abstraction`/`PVar`
    (bind types will be normalised before entering `Ctx`, so unreachable in practice).
- New `TypeError` variants (see Type checker / Errors): rendered in `error_reporting.rs`.
- Convention (AGENTS.md): new free functions/methods use `pub(crate)` (or private).

## Lexer (src/lexer.rs)

No changes — `[`, `]`, `:`, ids, kind keywords already exist.

## Parser (src/parser.rs)

- `session()` rule: add an alternative **before** the bare `x:sid()` arm:
  `x:sid() tok(BracketL) args tok(BracketR)` → `Type::TyApp`, where
  `args = stype() ** tok(Comma)` (**non-empty**), curried left into nested unary
  `TyApp`s. This also covers value-type positions (`type_atom`'s
  `tok(Chan)? s:ssession()` reuses `session()`, so no `type_atom` change is needed).
  Args are full `stype()`s, so `Chan`-prefixed and bare session arguments
  (`T[?Int]`, kind `Session`) parse.
- Type definition rules: capture the parameter list — today `squant()?` is parsed
  and **silently discarded**. Replace with a dedicated rule
  `type_def_params() = tok(BracketL) ids:sid()+ tok(Colon) kind:skind() tok(BracketR)`
  (deliberately **no** `qual_clause` — qualifications on type-def params are a parse
  error) producing `Vec<(SPVarId, SKind)>`. In both `type`/`rec type` actions, fold
  the bindings into nested `TyAbs` (first binding outermost) wrapping the body:
  `rec type TC[a b : Type] = body` → `TypeDef(TC, TyAbs{a,Type, TyAbs{b,Type, body}}, ..., is_rec=true)`.
- Parser tests: parameterized `rec type` (updated example form), `T[A]` in session
  and value positions, curried `T[A, B]`, negative: params with qualifications.

## Alias environment / desugaring (src/type_alias.rs)

`get_alias_env` becomes `Result<(SExpr, AliasEnv), TypeError>` (update the call in
`main.rs::typecheck`; `tests.rs` goes through `typecheck` already). New behavior,
where "self-reference" means any `Var(name)`/`TyApp(Var(name), …)` occurrence of the
defined name that is not shadowed by an intervening `Mu` binder:

- **Unparameterized, non-`rec`**: store the body as-is (**no** `Mu` wrap) and
  reject self-references with a new error (e.g. `TypeDefSelfReference(SId)`).
- **Unparameterized, `rec`**: store `Mu(name, body)` as today.
- **Parameterized (TyAbs-headed), non-`rec`**: store as-is; reject any self-reference.
- **Parameterized, `rec`**: inside the TyAbs layers, rewrite exact self-applications
  `TyApp(Var(name), [PVar(p1), …, PVar(pn)])` (args exactly the parameter ids, in
  order, non-dual) to `Var(name)` (the mu variable), then wrap the core in
  `Mu(name, core)`: alias = `TyAbs{p1,k1, … TyAbs{pn,kn, Mu(name, core')} … }`.
  Bare self-references and non-exact self-applications are static errors (e.g.
  `TypeDefIllFormedSelfReference(SType, SId)`). The walk must respect nested `Mu`
  binders (skip shadowed regions).
- `check_shadowing` / `check_type_shadowing`: add `TyApp` (recurse) and `TyAbs`
  (recurse body; binds a pvar, no alias-name conflict) arms.

## Kinding (src/kinding.rs)

- `KindingCtx` gains an in-progress set `alias_stack: Vec<Id>` (or `HashSet`).
- New `infer` arms:
  - `Type::TyApp(head, arg)`: `let k = self.infer(head)?` must be `Arrow(k1, k2)`
    (else `KindMismatch`); `self.check(arg, k1.clone())?` (subkinding, so a
    `Session` argument may instantiate a `Type` parameter); result `k2`.
  - `Type::TyAbs { id, kind, body }`: if `kind` is not `Type`/`Session` → new error
    (e.g. `KindNotBase(SKind)`); extend `ty_ctx` with `id : kind`; infer body `k2`;
    result `Arrow(kind, k2)`.
- `Type::Var(id)`: if in `rvars` → `Session` (mu variables are session-only). Else
  if in `alias_env`: **on-demand kinding of the alias definition** — run `infer` on
  the stored alias type in a fresh context (`ty_ctx` and `rvars` empty, same
  `alias_env`, `alias_stack` + this id) so ambient poly vars cannot leak into alias
  bodies (this also newly catches undefined pvars inside alias definitions).
  Guard: if `id` is already on the `alias_stack` → `CyclicTypeAlias(SId)`.
  (For `rec` unparameterized aliases the stored `Mu` kind as `Session`, preserving
  today's lenient behavior exactly.)
- `check_contractive`: replace the `_ => unreachable!(…)` arm for non-session
  constructors with a graceful error; reorder the `Mu` arm of `infer` to
  kind-check the body against `Session` **before** contractivity so that
  `rec type Box[a:Type] = <some:'a>` reports a clean `KindMismatch`.
- `Expr::TyAbs` (type_checker `check`): additionally verify that every binding in
  the quantification has a base kind (per the task's TyAbs rule; trivially true for
  parsed programs since the kind grammar has no arrows — defense in depth).

## Normalization (src/normalization.rs)

- New **private** `fn reduce_ty_apps(alias_env: &AliasEnv, ty: &Type) -> Result<Type, TypeError>`:
  - Structural recursion over the whole type (unlike `normalise_type`, which only
    handles `Semi`/`Mu`/`Var` — `reduce_ty_apps` must descend everywhere: `Op`
    payloads, `Choice` branches, `Arr`, `Prod`, `Variant`, `Abstraction`, …).
  - Tracks a set of mu-bound ids; `Var(id)` bound by an enclosing `Mu` is **never**
    unfolded (it is a recursion variable, not an alias reference).
  - `Var(id)` (not mu-bound, in `alias_env`): unfold to the stored alias type and
    keep reducing. Guard with an in-progress set of alias ids being unfolded;
    re-entry (only possible for un-`Mu`-guarded cycles such as mutual recursion) →
    `CyclicTypeAlias(SId)`. Note: `rec` definitions terminate naturally because
    their self-references are mu-bound after the desugaring rewrite.
  - `TyApp(head, arg)`: reduce `arg`; reduce/unfold `head` until it is a `TyAbs`
    (kinding guarantees this for well-kinded types); beta-reduce via
    `subst_poly({id ↦ arg})`; continue reducing the result. Curried applications
    fall out of the nested-unary representation. A head that never becomes a
    `TyAbs` is left as-is (kinding already rejected it in `normalise`).
- `normalise`: `kinding::infer(...)?` → `reduce_ty_apps(alias_env, &ty.val)?` →
  `normalise_type(alias_env, &reduced)` (span preserved).
- `normalise_type`: add arms — `TyAbs` (recurse body; reachable via unfolding a bare
  parameterized alias), `TyApp` (clone; defensive, empty post-reduction).
- Unit tests: single/curried beta reduction with a hand-built `AliasEnv`; alias
  unfolding; mu-bound self-references not unfolded; `CyclicTypeAlias` on a non-`rec`
  applied self-reference (constructed directly).

## Type checker (src/type_checker.rs)

- **Normalise annotations at entry points** so raw `TyApp`/`TyAbs` never reach
  `TypeCtx` predicates, constraints, or `is_unr` (all currently answer `false` for
  unknown constructors, which would cause false positives, e.g. `send[Pair[Int]]`,
  instantiating `unr 'a` with `TC[Int]`, or `is_unr` on a bind type):
  - `Expr::Send`/`Expr::Recv`: normalise the payload type first (mobile/unr checks
    and the expected channel type then see reduced types).
  - `Expr::LSplit`/`Expr::RSplit`: normalise `prefix_session` before `kinding::check`
    and before building `expected_chan_ty`/`ret_ty`.
  - `Expr::LetDecl`: normalise the annotation `var_ty` (with the quantification's
    bindings added to `ty_ctx` first, so parameter pvars are in scope) before
    `desugar_quantification`.
  - `check` for `Expr::Abs`: normalise each `param` (and `ret`) before binding;
    additionally `kinding::check(param, Kind::Type)` — gives a clean `KindMismatch`
    for e.g. `f : TreeChannel -[m u 1]-> Unit` (bare constructor in param position).
  - `Expr::TyApp` (expr): normalise the argument `tys` before building the
    substitution bindings (qualifications instantiated with constructor types must
    be checked against the reduced form). Also add the currently missing arity
    check (`tys.len() == quantification.bindings.len()`; today `zip` silently
    truncates).
- Keep the existing `Expr::TyApp` logic otherwise (it already expects the
  forall-typed `Abstraction` from `desugar_quantification`).

## FreeST translation (src/equivalence.rs)

- Alias-env dump loop: for `TyAbs`-headed aliases, peel the `TyAbs` layers and
  convert the core body (pvars become `FreestType::PVar(id, kind)` via the existing
  `PVar` arm), then `defs.add(name, converted)` — `write_freest_type` already emits
  `type name : <param kinds> -> <kind>. type name <vars> = <ty>`, i.e. a proper
  FreeST type constructor. Verified shape (scratch3):
  `type TreeChannel : 1T -> 1S. type TreeChannel a = T_0 a`.
- `convert_type_impl`: add arms — `TyAbs` → `FreestType::Forall { var, kind, body }`
  (natural encoding; `Forall` already exists); `TyApp` → panic with a clear message
  ("unreduced type application") — defensive; unreachable because constraints only
  contain normalised types.
- No changes needed in `unify` (catch-all `_ => Err(Check)`) or the `TypeCtx`
  predicates in `type_context.rs` (`_ => false` arms already cover the new
  variants conservatively); `constraint.rs::subst` needs recursion arms for both
  variants.

## Pretty printing & errors (src/pretty.rs, src/error_reporting.rs)

- `Kind::Arrow`: render `k1 => k2` (parenthesize arrow-kind operands).
- `Type::TyApp`: `head[arg]` at atom precedence (curried renders `F[A][B]`).
- `Type::TyAbs`: `\ 'id : kind. body`.
- New `TypeError` variants and renderings:
  - `TypeDefSelfReference(SId)` — self-reference in a non-`rec` definition.
  - `TypeDefIllFormedSelfReference(SType, SId)` — bare or non-exact self-reference
    in a parameterized `rec` definition.
  - `CyclicTypeAlias(SId)` — kinding/reduction cycle guard (mutual recursion).
  - `KindNotBase(SKind)` — `TyAbs` binder of arrow kind (internal consistency).

## Examples & tests

- **Update** `examples/temp/polyReceiveTree.bgv`: bare `TreeChannel` refs become
  `TreeChannel['a]` (per decision 1 they are now ill-formed), then move it to
  `examples/positive/polyReceiveTreeTypeDef.bgv` (keep the existing manual-`mu`
  `examples/positive/polyReceiveTree.bgv`; it stays valid).
- New negative examples: bare self-reference in a parameterized `rec type` (the
  original temp-example form); non-exact self-application (`TreeChannel[Int]`
  inside its own body); self-reference in a non-`rec` definition (new behavior for
  unparameterized defs too); wrong argument kind (`type S[a:Session] = …` applied
  as `S[Int]`); `rec type` with a value-type body; optionally mutually recursive
  parameterized aliases (`CyclicTypeAlias`).
- Unit tests: kinding (application rule incl. `Session <= Type` argument, wrong
  arg kind, `TyAbs` base-kind rejection, unapplied parameterized alias kind
  `Type => Session`); normalization (`reduce_ty_apps` cases above); parser tests.
- Existing suites must stay green: parser `parse` test, `unit_tests` (43 examples,
  FreeST available locally), kinding/normalization/constraint/equivalence tests.

## README.md

Extend the grammar section: parameterized type definitions
(`'type' x '[' x+ ':' k ']' '=' t`), type application `t ::= … | t '[' t ',' … ']'`,
arrow kinds (internal only — type constructors can only be introduced by type
definitions), and the self-reference rules (`rec` + exact application only).

## Suggested implementation order (build stays green at each step)

1. `syntax.rs` (kinds, variants, all arms) + `pretty.rs` + `error_reporting.rs`
   placeholders → `cargo build`.
2. `parser.rs` + parser tests.
3. `type_alias.rs` desugaring + static checks (+ `main.rs` `Result` adaptation).
4. `kinding.rs` rules + alias-kind inference + cycle guard + contractivity fix.
5. `normalization.rs` `reduce_ty_apps` + integration + unit tests.
6. `type_checker.rs` normalise-at-entry points + arity check + `KindNotBase`.
7. `equivalence.rs` constructor emission + defensive arms.
8. Examples (positive + negative), README, full verification.

## Verification

- `cargo build`
- `cargo test` (includes the 43-example suite via `unit_tests`; requires `freest`
  on PATH — present at `~/.local/bin/freest`)
- `cargo run -- examples/positive/polyReceiveTreeTypeDef.bgv` (and re-run a few
  existing examples, esp. `receiveTree`, `sendTreeMu`, `renderUser`, `polyGive`)
- `cargo fmt --check` (note: peg block is `rustfmt_skip`), `cargo clippy` if used

## Known limitations (documented, acceptable)

- Mutually recursive **parameterized** type definitions are rejected at runtime by
  the cycle guards (`CyclicTypeAlias`) rather than supported.
- Nested/hierarchical recursion (e.g. `Bush[a] = …Bush[Bush[a]]`) is not supported
  (rejected as a non-exact self-application); the mu encoding only expresses
  regular recursion.
- `dual` of a type application is a parse-time panic with a clear message.
- Type definitions nested deeper than the top-level `in`-chain are not collected by
  `get_alias_env` (pre-existing limitation, unchanged).
