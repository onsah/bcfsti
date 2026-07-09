use crate::lexer::Token;
use crate::syntax::Eff as EffS;
use crate::syntax::Id as IdS;
use crate::syntax::*;
use crate::util::lexer_offside::Braced;
use crate::util::peg_logos::SpannedToks;
use crate::util::span::fake_span;
use crate::util::span::{Span, Spanned};

use Braced::Token as Tok;
use peg::error::ParseError;

pub type Toks<'a> = SpannedToks<'a, Braced<Token<'a>>>;

pub fn parse(toks: &Toks) -> Result<SExpr, ParseError<usize>> {
    rlang_parser::sprogram(toks, toks)
}

#[cfg_attr(rustfmt, rustfmt_skip)]
peg::parser! {
    pub grammar rlang_parser<'a>(toks: &'a Toks<'a>) for Toks<'a> {
        use Token::*;

        rule spanned<T>(t: rule<T>) -> Spanned<T>
            = start:position!() x:t() end:position!() {
                let start = toks.toks.get(start)
                        .map(|t| t.span.start)
                        .unwrap_or_else(|| toks.toks.last().unwrap().span.end);
                let end = if end > 0 { end - 1 } else { end };
                let end = toks.toks.get(end)
                        .map(|t| t.span.end)
                        .unwrap_or_else(|| toks.toks.last().unwrap().span.end);
                Spanned::new(x, Span { start, end })
            }

        // Identifier

        pub rule id() -> IdS = quiet!{[Tok(Id(x))] { x.to_owned() }} / expected!("identifier")
        pub rule sid() -> SId = spanned(<id()>)

        pub rule tok(t: Token<'a>) -> () = quiet!{[Tok(t2) if t == t2] { () }} / expected!(t.to_str())

        // Constants
        pub rule string() -> Const = quiet!{[Tok(Str(x))] { Const::String(x.to_owned()) }} / expected!("string literal")
        pub rule int() -> Const = quiet!{[Tok(Int(x))] { Const::Int(x) }} / expected!("integer literal")
        pub rule unit() -> Const = tok(Unit) { Const::Unit }
        pub rule bool() -> Const
            = quiet!{tok(True) { Const::Bool(true) }}
            / quiet!{tok(False) { Const::Bool(false) }}
            / expected!("boolean literal")
        pub rule constant() -> Const
            = quiet!{ string() / int() / bool() / unit() } / expected!("literal")

        // Mobilities
        pub rule mob() -> Mob
            = [Tok(Id("m"))] { Mob::Mobile }
            / [Tok(Id("s"))] { Mob::Static }
            / expected!("mobility")
        pub rule smob() -> SMob = spanned(<mob()>)

        // Multiplicities

        pub rule mult() -> Mult
            = (tok(Unr) / [Tok(Id("u"))]) { Mult::Unr }
            / (tok(Lin) / [Tok(Id("p"))]) { Mult::Lin }
            / (tok(Right) / [Tok(Id("r"))]) { Mult::OrdR }
            / (tok(Left) / [Tok(Id("l"))]) { Mult::OrdL }
            / expected!("multiplicity")
        pub rule smult() -> SMult = spanned(<mult()>)

        // Effects

        pub rule effect() -> EffS
            = quiet!{[Tok(Int(0))] { EffS::No }}
            / quiet!{[Tok(Int(1))] { EffS::Yes }}
            / expected!("effect")
        pub rule seffect() -> SEff = spanned(<effect()>)

        // Types

        #[cache_left_rec]
        pub rule session() -> Session
            = s1:ssession() tok(Semicolon) s2:ssession()
              { Session::Semi { first: Box::new(s1), second: Box::new(s2) } }
            / tok(Return) { Session::BorrowEnd(SessionOp::Send) }
            / tok(AcqT) { Session::BorrowEnd(SessionOp::Recv) }
            / tok(Wait) { Session::End(SessionOp::Recv) }
            / tok(Close) { Session::End(SessionOp::Send) }
            / tok(Skip) { Session::Skip }
            / tok(Bang) t:stype_atom()
              { Session::Op(SessionOp::Send, Box::new(t)) }
            / tok(QuestionMark) t:stype_atom()
              { Session::Op(SessionOp::Recv, Box::new(t)) }
            / tok(Amp) tok(BraceL) cs:((l:sid() tok(Colon) s:ssession() { (l, s) })** tok(Comma)) tok(Comma)? tok(BraceR)
              { Session::Choice(SessionOp::Recv, cs) }
            / tok(Plus) tok(BraceL) cs:((l:sid() tok(Colon) s:ssession() { (l, s) })** tok(Comma)) tok(Comma)? tok(BraceR)
              { Session::Choice(SessionOp::Send, cs) }
            / tok(Mu) x:sid() tok(Period) s:ssession()
              { Session::Mu(x, Box::new(s)) }
            / x:sid()
              { Session::Var(x) }
            / tok(ParenL) s:session() tok(ParenR) { s }
        pub rule ssession() -> SSession = spanned(<session()>)

        pub rule type_() -> Type = t:type_arrow() { t }
        pub rule stype() -> SType = spanned(<type_()>)

        #[cache_left_rec]
        pub rule type_arrow() -> Type
            = param:stype_prod() tok(Minus) tok(BracketL) mob:smob() tok(Semicolon)? mult:smult() tok(Semicolon)? eff:seffect()
              tok(BracketR) tok(Arrow) ret:stype_arrow()
              { Type::Arr{ mob, mult, eff, param: Box::new(param), ret: Box::new(ret) } }
            / t:type_prod() { t }
        pub rule stype_arrow() -> SType = spanned(<type_arrow()>)

        pub rule type_prod() -> Type
            = first:stype_atom() tok(Star) tok(BracketL) mult:smult() tok(BracketR) second:stype_prod()
              { Type::Prod { mult, first: Box::new(first), second: Box::new(second) } }
            / first:stype_atom() tok(StarOrdL) second:stype_prod()
              { Type::Prod { mult: fake_span(Mult::OrdL), first: Box::new(first), second: Box::new(second) } }
            / first:stype_atom() tok(StarLin) second:stype_prod()
              { Type::Prod { mult: fake_span(Mult::Lin), first: Box::new(first), second: Box::new(second) } }
            / t:type_atom() { t }

        pub rule stype_prod() -> SType = spanned(<type_prod()>)

        pub rule type_atom() -> Type
            = tok(UnitT) { Type::Unit }
            / tok(IntT) { Type::Int }
            / tok(BoolT) { Type::Bool }
            / tok(StringT) { Type::String }
            / tok(ParenL) t:type_() tok(ParenR) { t }
            / tok(Chan)? s:ssession() { Type::Chan(s.val) }
            / tok(Lt) cs:((l:sid() tok(Colon) t:stype() { (l , t) }) ** tok(Comma)) tok(Comma)? tok(Gt) { Type::Variant(cs) }
        pub rule stype_atom() -> SType = spanned(<type_atom()>)

        // Expressions

        pub rule expr() -> Expr = e:expr_ann() { e }
        pub rule sexpr() -> SExpr = spanned(<expr()>)

        pub rule expr_ann() -> Expr
            = e:sexpr_lam() tok(Colon) t:stype() { Expr::Ann(Box::new(e), t) }
            / e:expr_lam() { e }
        pub rule sexpr_ann() -> SExpr = spanned(<expr_ann()>)

        #[cache]
        pub rule expr_lam() -> Expr
            = tok(Lambda) x:sid() tok(Period) e:sexpr_lam()
              { Expr::Abs(x, Box::new(e)) }
            / tok(Rec) tok(TypeKw) x:sid() tok(Equals) t:ssession() tok(In) e:sexpr_lam()
              { Expr::TypeDef(x, t, Box::new(e), true) }
            / tok(TypeKw) x:sid() tok(Equals) t:ssession() tok(In) e:sexpr_lam()
              { Expr::TypeDef(x, t, Box::new(e), false) }
            / tok(Case) e:sexpr() tok(BraceL)
              cs:((tok(Inj)? l:sid() x:sid() tok(Arrow) tok(BraceL) e:sexpr() tok(BraceR) { (l, x, e) }) ** (tok(Semicolon)?))
              tok(Semicolon)? tok(BraceR)
              { Expr::CaseSum(Box::new(e), cs) }
            / tok(Let) tok(ParenL)? x:sid() tok(Comma) y:sid() tok(ParenR)? tok(Equals) e1:sexpr_ann() tok(In) e2:sexpr_lam()
              { Expr::LetPair(x, y, Box::new(e1), Box::new(e2)) }
            / tok(Let) x:sid() tok(Equals) e1:sexpr_ann() tok(In) e2:sexpr_lam()
              { Expr::Let(x, Box::new(e1), Box::new(e2)) }
            / tok(Let) x:sid() tok(Colon) t:stype() c:sclause() tok(In) e:sexpr_lam()
              { Expr::LetDecl(x, t, Box::new(c), Box::new(e)) }
            / tok(If) e:sexpr_lam() tok(Then) e1:sexpr_lam() tok(Else) e2:sexpr_lam()
              { Expr::If(Box::new(e), Box::new(e1), Box::new(e2)) }
            / e1:sexpr_or() tok(Semicolon) e2:sexpr_lam()
              { Expr::Seq(Box::new(e1), Box::new(e2)) }
            / e:expr_or() { e }
        pub rule sexpr_lam() -> SExpr = spanned(<expr_lam()>)

        #[cache_left_rec]
        pub rule expr_or() -> Expr
            = e1:sexpr_and() (tok(DoublePipe) / tok(Or)) e2:sexpr_or() { Expr::Op2(Op2::Or, Box::new(e1), Box::new(e2)) }
            / e:expr_and() { e }
        pub rule sexpr_or() -> SExpr = spanned(<expr_or()>)

        #[cache_left_rec]
        pub rule expr_and() -> Expr
            = e1:sexpr_not() (tok(DoubleAmp) / tok(And)) e2:sexpr_and() { Expr::Op2(Op2::And, Box::new(e1), Box::new(e2)) }
            / e:expr_not() { e }
        pub rule sexpr_and() -> SExpr = spanned(<expr_and()>)

        #[cache_left_rec]
        pub rule expr_not() -> Expr
            = (tok(Not) / tok(Bang)) e:sexpr_not() { Expr::Op1(Op1::Not, Box::new(e)) }
            / e:expr_cmp() { e }
        pub rule sexpr_not() -> SExpr = spanned(<expr_not()>)

        #[cache_left_rec]
        pub rule expr_cmp() -> Expr
            = e1:sexpr_add() tok(Lt) e2:sexpr_add() { Expr::Op2(Op2::Lt, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(Le) e2:sexpr_add() { Expr::Op2(Op2::Le, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(Gt) e2:sexpr_add() { Expr::Op2(Op2::Gt, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(Ge) e2:sexpr_add() { Expr::Op2(Op2::Ge, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(DoubleEquals) e2:sexpr_add() { Expr::Op2(Op2::Eq, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_add() tok(BangEquals) e2:sexpr_add() { Expr::Op2(Op2::Neq, Box::new(e1), Box::new(e2)) }
            / e:expr_add() { e }
        pub rule sexpr_cmp() -> SExpr = spanned(<expr_cmp()>)

        #[cache_left_rec]
        pub rule expr_add() -> Expr
            = e1:sexpr_sub() tok(Plus) e2:sexpr_add() { Expr::Op2(Op2::Add, Box::new(e1), Box::new(e2)) }
            / e:expr_sub() { e }
        pub rule sexpr_add() -> SExpr = spanned(<expr_add()>)

        #[cache_left_rec]
        pub rule expr_sub() -> Expr
            = e1:sexpr_sub() tok(Minus) e2:sexpr_mul() { Expr::Op2(Op2::Sub, Box::new(e1), Box::new(e2)) }
            / e:expr_mul() { e }
        pub rule sexpr_sub() -> SExpr = spanned(<expr_sub()>)

        #[cache_left_rec]
        pub rule expr_mul() -> Expr
            = e1:sexpr_neg() tok(Star) e2:sexpr_mul() { Expr::Op2(Op2::Mul, Box::new(e1), Box::new(e2)) }
            / e1:sexpr_neg() tok(Slash) e2:sexpr_mul() { Expr::Op2(Op2::Div, Box::new(e1), Box::new(e2)) }
            / e:expr_neg() { e }
        pub rule sexpr_mul() -> SExpr = spanned(<expr_mul()>)

        #[cache_left_rec]
        pub rule expr_neg() -> Expr
            = tok(Minus) e:sexpr_neg() { Expr::Op1(Op1::Neg, Box::new(e)) }
            / e:expr_app() { e }
        pub rule sexpr_neg() -> SExpr = spanned(<expr_neg()>)

        #[cache_left_rec]
        pub rule expr_app() -> Expr
            = tok(New) s:ssession() { Expr::New(s) }
            / tok(Send) tok(At) ty:stype() e1:sexpr_atom() e2:sexpr_atom() { Expr::Send(ty, Box::new(e1), Box::new(e2)) }
            / tok(Recv) tok(At) ty:stype() e:sexpr_atom() { Expr::Recv(ty, Box::new(e)) }
            / tok(Discard) e:sexpr_atom() { Expr::Discard(Box::new(e)) }
            / tok(Drop) e:sexpr_atom() { Expr::BorrowEnd(SessionOp::Send, Box::new(e)) }
            / tok(Acquire) e:sexpr_atom() { Expr::BorrowEnd(SessionOp::Recv, Box::new(e)) }
            / tok(Close) e:sexpr_atom() { Expr::End(SessionOp::Send, Box::new(e)) }
            / tok(Wait) e:sexpr_atom() { Expr::End(SessionOp::Recv, Box::new(e)) }
            / tok(Select) l:sid() e:sexpr_atom() { Expr::Select(l, Box::new(e)) }
            / tok(Branch) e:sexpr_atom() { Expr::Branch(Box::new(e)) }
            / tok(Inj) l:sid() e:sexpr_atom() { Expr::Inj(l, Box::new(e)) }
            / tok(Fork) e:sexpr_atom() { Expr::Fork(Box::new(e)) }
            / tok(ToStr) e:sexpr_atom() { Expr::Op1(Op1::ToStr, Box::new(e)) }
            / tok(Print) e:sexpr_atom() { Expr::Op1(Op1::Print, Box::new(e)) }
            / tok(LSplit) s:ssession() e:sexpr_atom() { Expr::LSplit(s, Box::new(e)) }
            / tok(RSplit) s:ssession() e:sexpr_atom() { Expr::RSplit(s, Box::new(e)) }
            / e1:sexpr_app() e2:sexpr_atom() { Expr::App(Box::new(e1), Box::new(e2)) }
            / e:expr_atom() { e }
        pub rule sexpr_app() -> SExpr = spanned(<expr_app()>)

        #[cache]
        pub rule expr_atom() -> Expr
            = tok(ParenL) e:expr() tok(ParenR) { e }
            / tok(ParenL) e1:sexpr() tok(Comma) e2:sexpr() tok(ParenR)
              { Expr::Pair(Box::new(e1), Box::new(e2)) }
            / c:constant() { Expr::Const(c) }
            / x:sid() { Expr::Var(x.to_owned()) }
        pub rule sexpr_atom() -> SExpr = spanned(<expr_atom()>)

        // Declarations

        pub rule pattern() -> Pattern
            = tok(ParenL) p1:spattern() tok(Comma) p2:spattern() tok(ParenR) { Pattern::Pair(Box::new(p1), Box::new(p2)) }
            / x:sid() { Pattern::Var(x.to_owned()) }
        pub rule spattern() -> SPattern = spanned(<pattern()>)

        pub rule clause() -> Clause
            = [Braced::Item]? y:sid() var_id:sid() tok(Equals) e:sexpr() { Clause { id: y, var_id, body: e } }
        pub rule sclause() -> SClause = spanned(<clause()>)

        // Whole Programs

        #[cache]
        pub rule program() -> Expr
            = [Braced::Begin] [Braced::Item]? e:expr() [Braced::End] { e }
        pub rule sprogram() -> SExpr = spanned(<program()>)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::path::PathBuf;

    use crate::{
        lexer::{self, Token},
        parser,
        util::lexer_offside::{self, Braced},
    };

    macro_rules! logln {
        ($($args:tt)*) => {
            writeln!(::std::io::stdout(), $($args)*).unwrap()
        };
    }

    #[test]
    fn parse() {
        let positives: Vec<PathBuf> = std::fs::read_dir("examples/positive")
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .collect();

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

            let toks = lexer::lex(&src).unwrap();
            let mut toks = lexer_offside::process_indent(toks, |_| false, |_| false);
            toks.toks = toks
                .toks
                .into_iter()
                .filter(|t| t.val != Braced::Token(Token::NewLine))
                .collect::<Vec<_>>();

            let mut failures_pos = vec![];

            let res = parser::parse(&toks);
            if res.is_ok() {
                logln!("TEST SUCCEEDED.")
            } else {
                logln!("TEST FAILED.");
                failures_pos.push(name.clone())
            }

            logln!(
                "\n================================================================================\n"
            );
            if failures_pos.len() == 0 {
                logln!("ALL {} TESTS PASSED!", positives.len());
            } else {
                logln!("{} TESTS FAILED:\n", failures_pos.len());
                for n in failures_pos {
                    logln!("  {n}")
                }
                assert!(false)
            }
        }

        let negatives: Vec<PathBuf> = std::fs::read_dir("examples/negative")
            .unwrap()
            .filter_map(|e| e.ok().map(|e| e.path()))
            .collect();

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

            let toks = lexer::lex(&src).unwrap();
            let mut toks = lexer_offside::process_indent(toks, |_| false, |_| false);
            toks.toks = toks
                .toks
                .into_iter()
                .filter(|t| t.val != Braced::Token(Token::NewLine))
                .collect::<Vec<_>>();

            let mut failures_pos = vec![];

            let res = parser::parse(&toks);
            if res.is_ok() {
                logln!("TEST SUCCEEDED.")
            } else {
                logln!("TEST FAILED.");
                failures_pos.push(name.clone())
            }

            logln!(
                "\n================================================================================\n"
            );
            if failures_pos.len() == 0 {
                logln!("ALL {} TESTS PASSED!", negatives.len());
            } else {
                logln!("{} TESTS FAILED:\n", failures_pos.len());
                for n in failures_pos {
                    logln!("  {n}")
                }
                assert!(false)
            }
        }
    }
}
