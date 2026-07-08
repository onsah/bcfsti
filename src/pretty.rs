use crate::{
    syntax::{
        Clause, Const, Eff, Expr, Mob, Mult, Op1, Op2, Pattern, SMult, Session, SessionOp, Type,
    },
    util::{
        pretty::{Assoc, Pretty, PrettyEnv},
        span::Spanned,
    },
};

// #[derive(Clone)]
// pub struct UserState {}
type UserState = ();

use Assoc::Left as L;
use Assoc::None as N;
use Assoc::Right as R;

impl<T: Pretty<UserState>> Pretty<UserState> for Spanned<T> {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        self.val.pp(p)
    }
}

impl Pretty<UserState> for Type {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Type::Arr {
                mob,
                mult,
                eff,
                param,
                ret,
            } => p.infix(2, R, |p| {
                p.pp_arg(L, param);
                p.pp(" –[");
                p.pp(mob);
                p.pp("; ");
                p.pp(mult);
                p.pp("; ");
                p.pp(eff);
                p.pp("]→ ");
                p.pp_arg(R, ret);
            }),
            Type::Prod {
                mult,
                first,
                second,
            } => p.infix(3, N, |p| {
                p.pp_arg(L, first);
                match mult.val {
                    Mult::Lin => {
                        p.pp(" ⊗ ");
                    }
                    Mult::OrdR => {
                        p.pp(" ⊙ ");
                    }
                    _ => {
                        p.pp(" *[");
                        p.pp(mult);
                        p.pp("] ");
                    }
                }
                p.pp_arg(R, second);
            }),
            Type::Chan(s) => p.infix(4, N, |p| {
                p.pp("Chan ");
                p.pp_arg(R, s);
            }),
            Type::Variant(cs) => {
                p.pp("<");
                for (i, (l, t)) in cs.iter().enumerate() {
                    if i != 0 {
                        p.pp(", ");
                    }
                    p.pp(l);
                    p.pp(": ");
                    p.pp_prec(0, t);
                }
                p.pp(">");
            }
            Type::Unit => p.pp("Unit"),
            Type::Int => p.pp("Int"),
            Type::Bool => p.pp("Bool"),
            Type::String => p.pp("String"),
        }
    }
}

impl Pretty<UserState> for Session {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Session::Op(op, t) => {
                match op {
                    SessionOp::Send => p.pp("!"),
                    SessionOp::Recv => p.pp("?"),
                }
                p.pp_prec(10, t);
            }
            Session::End(op) => match op {
                SessionOp::Send => p.pp("Close"),
                SessionOp::Recv => p.pp("Wait"),
            },
            Session::Var(x) => p.pp(&x.val),
            Session::Mu(x, s) => p.infix(0, R, |p| {
                p.pp("µ ");
                p.pp(x);
                p.pp(". ");
                p.pp_arg(R, s);
            }),
            Session::Choice(op, cs) => {
                match op {
                    SessionOp::Send => p.pp("+"),
                    SessionOp::Recv => p.pp("&"),
                }
                p.pp("{");
                for (i, (l, s)) in cs.iter().enumerate() {
                    if i != 0 {
                        p.pp(", ")
                    }
                    p.pp(l);
                    p.pp(": ");
                    p.pp_prec(0, s);
                }
                p.pp("}");
            }
            Session::BorrowEnd(SessionOp::Send) => p.pp("Ret"),
            Session::BorrowEnd(SessionOp::Recv) => p.pp("Acq"),
            Session::Skip => p.pp("Skip"),
            Session::Semi { first, second } => {
                p.pp("(");
                p.pp(first);
                p.pp("; ");
                p.pp(second);
                p.pp(")");
            }
            Session::UVar(id) => {
                p.pp("(uvar ");
                p.pp(&id.to_string());
                p.pp(")");
            }
        }
    }
}

impl Pretty<UserState> for Mob {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Mob::Mobile => p.pp("mobile"),
            Mob::Static => p.pp("static"),
        }
    }
}

impl Pretty<UserState> for Mult {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Mult::Unr => p.pp("unr"),
            Mult::Lin => p.pp("lin"),
            Mult::OrdR => p.pp("right"),
            Mult::OrdL => p.pp("left"),
        }
    }
}

impl Pretty<UserState> for Option<SMult> {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            None => (),
            Some(m) => {
                p.pp("[");
                p.pp(m);
                p.pp("]");
            }
        }
    }
}

impl Pretty<UserState> for Eff {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Eff::Yes => p.pp("1"),
            Eff::No => p.pp("0"),
        }
    }
}

impl Pretty<UserState> for Const {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Const::Unit => p.pp("unit"),
            Const::Int(v) => p.pp(&v.to_string()),
            Const::Bool(v) => p.pp(&v.to_string()),
            Const::String(v) => p.pp(&format!("\"{v}\"")),
        }
    }
}

impl Pretty<UserState> for Expr {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Expr::New(r) => p.infix(3, L, |p| {
                p.pp("new ");
                p.pp_prec(3, r);
            }),
            Expr::BorrowEnd(op, e) => p.infix(2, L, |p| {
                match op {
                    SessionOp::Recv => p.pp("acquire "),
                    SessionOp::Send => p.pp("drop "),
                }
                p.pp_arg(R, e);
            }),
            Expr::Var(x) => p.str(&x.val),
            Expr::Abs(x, e) => p.infix(1, R, |p| {
                p.pp("λ");
                p.pp(x);
                p.pp(". ");
                p.pp_arg(R, e);
                p.pp("");
            }),
            Expr::App(e1, e2) => p.infix(10, L, |p| {
                p.pp_arg(L, e1);
                p.pp(" ");
                p.pp_arg(R, e2);
            }),
            Expr::Inj(l, e) => p.infix(10, L, |p| {
                p.pp("inj ");
                p.pp(l);
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Expr::Fork(e) => p.infix(10, L, |p| {
                p.pp("fork ");
                p.pp_arg(R, e);
            }),
            Expr::Send(ty, e1, e2) => p.infix(10, L, |p| {
                p.pp("send @");
                p.pp_arg(L, ty);
                p.pp_arg(R, e1);
                p.pp(" ");
                p.pp_arg(R, e2);
            }),
            Expr::Recv(ty, e) => p.infix(10, L, |p| {
                p.pp("recv @");
                p.pp_arg(L, ty);
                p.pp_arg(R, e);
            }),
            Expr::End(op, e) => p.infix(10, L, |p| {
                match op {
                    SessionOp::Send => p.pp("term"),
                    SessionOp::Recv => p.pp("wait"),
                }
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Expr::Pair(e1, e2) => {
                p.pp("(");
                p.pp(e1);
                p.pp(", ");
                p.pp(e2);
                p.pp(")");
            }
            Expr::LetPair(x, y, e1, e2) => p.infix(1, R, |p| {
                p.pp("let ");
                p.pp(x);
                p.pp(", ");
                p.pp(y);
                p.pp(" = ");
                p.pp_prec(0, e1);
                p.pp(" in\n");
                p.pp(e2);
            }),
            Expr::Let(x, e1, e2) => p.infix(1, R, |p| {
                p.pp("let ");
                p.pp(x);
                p.pp(" = ");
                p.pp_prec(0, e1);
                p.pp(" in\n");
                p.pp(e2);
            }),
            Expr::If(e1, e2, e3) => p.infix(1, R, |p| {
                p.pp("if ");
                p.pp_prec(0, e1);
                p.pp(" then ");
                p.pp_prec(0, e2);
                p.pp(" else ");
                p.pp_arg(R, e3);
            }),
            Expr::CaseSum(e, cs) => p.infix(1, R, |p| {
                p.pp("case ");
                p.pp(e);
                p.pp(" { ");
                for (l, x, e) in cs {
                    p.pp("inj ");
                    p.pp(l);
                    p.pp(" ");
                    p.pp(x);
                    p.pp(" → ");
                    p.pp_prec(0, e);
                    p.pp(", ")
                }
                p.pp(" }");
            }),
            Expr::Ann(e, t) => {
                p.pp(e);
                p.pp(" : ");
                p.pp(t);
            }
            Expr::Seq(e1, e2) => p.infix(2, R, |p| {
                p.pp_arg(L, e1);
                p.pp(";\n");
                p.pp_arg(R, e2);
            }),
            Expr::Const(c) => p.pp(c),
            Expr::Op1(op1, e) => {
                let (prec, assoc, op_str) = match op1 {
                    Op1::Neg => (9, N, "!"),
                    Op1::Not => (6, N, "!"),
                    Op1::ToStr => (10, N, "str"),
                    Op1::Print => (10, N, "print"),
                };
                p.infix(prec, assoc, |p| {
                    p.pp(op_str);
                    p.pp(" ");
                    p.pp_arg(R, e);
                })
            }
            Expr::Op2(op2, e1, e2) => {
                let (prec, assoc, op_str) = match op2 {
                    Op2::Add => (8, L, "+"),
                    Op2::Sub => (8, L, "-"),
                    Op2::Mul => (9, R, "*"),
                    Op2::Div => (9, R, "/"),
                    Op2::Eq => (7, N, "=="),
                    Op2::Neq => (7, N, "!="),
                    Op2::Lt => (7, N, "<"),
                    Op2::Le => (7, N, "<="),
                    Op2::Gt => (7, N, ">"),
                    Op2::Ge => (7, N, ">="),
                    Op2::And => (5, L, "&&"),
                    Op2::Or => (4, L, "||"),
                };
                p.infix(prec, assoc, |p| {
                    p.pp_arg(L, e1);
                    p.pp(" ");
                    p.pp(op_str);
                    p.pp(" ");
                    p.pp_arg(R, e2);
                })
            }
            Expr::Select(l, e) => p.infix(10, L, |p| {
                p.pp("select ");
                p.pp_arg(L, l);
                p.pp(" ");
                p.pp_arg(R, e);
            }),
            Expr::Branch(e) => p.infix(10, L, |p| {
                p.pp("branch ");
                p.pp_arg(R, e);
            }),
            Expr::LSplit(prefix, expr) => {
                p.pp("lsplit ");
                p.pp_arg(L, prefix);
                p.pp(" ");
                p.pp_arg(R, expr);
            }
            Expr::RSplit(prefix, expr) => {
                p.pp("rsplit ");
                p.pp_arg(L, prefix);
                p.pp_arg(R, expr);
            }
            Expr::LetDecl(x, t, c, e) => {
                p.pp("let");
                p.block(|p| {
                    p.pp(x);
                    p.pp(" : ");
                    p.pp(t);
                    p.pp("\n");
                    p.pp(c);
                });
                p.pp("\nin\n");
                p.pp(e)
            }
            Expr::TypeDef(x, t, e, is_rec) => {
                if *is_rec {
                    p.pp("rec ");
                }
                p.pp("type ");
                p.pp(x);
                p.pp(" = ");
                p.pp(t);
                p.pp(" in\n");
                p.pp(e)
            }
            Expr::Discard(e) => p.infix(10, L, |p| {
                p.pp("discard ");
                p.pp_arg(R, e);
            }),
        }
    }
}

impl Pretty<UserState> for Clause {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        p.pp(&self.id);
        p.pp(" ");
        p.pp(&self.var_id);
        p.pp(" ");
        // for pat in &self.pats {
        //     p.pp(pat);
        //     p.pp(" ");
        // }
        p.pp("= ");
        p.block(|p| {
            p.pp(&self.body);
        });
    }
}

impl Pretty<UserState> for Pattern {
    fn pp(&self, p: &mut PrettyEnv<UserState>) {
        match self {
            Pattern::Var(x) => p.pp(x),
            Pattern::Pair(p1, p2) => {
                p.pp("(");
                p.pp(p1);
                p.pp(", ");
                p.pp(p2);
                p.pp(")");
            }
        }
    }
}
