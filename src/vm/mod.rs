use std::sync::Arc;

use crate::{
    common::*,
    elab::{Builtin, Head, Sym, TElim, TFun, Term, VFun, Val},
};

#[derive(Clone)]
pub enum Value {
    Closure(Arc<Closure>),
    Pair(Arc<Value>, Arc<Value>),
    Unit,
}

#[derive(Clone, PartialEq)]
pub enum Type {
    // Permanent "any" that can never resolve to something else
    Any,
    // Pairs are *not* dependent in L1 IR
    Pair(Arc<Type>, Arc<Type>),
    // Possibly-unboxed immutable reference
    Imm(Arc<Type>),
    // Boxed mutable reference
    Mut(Arc<Type>),
    // (owned, pars, rty)
    // TODO how to incorporate escape analysis information from regions?
    Fun(bool, Vec<Type>, Arc<Type>),
    Sum(Vec<Type>),
    Unit,
}

// In [a b], the top of the stack is b
enum Inst {
    PushConstant(Value),
    PushLocal(u32),
    SetLocal(u32),
    PushClosure(Arc<Function>), // [..upvalues] -> [closure]
    Call(u32),                  // [f ..args] -> [ret]
    SplitPair,                  // [(a, b)] -> [a b]
    MakePair,                   // [a b] -> [(a, b)]
    Drop,                       // [a] -> []
    Ret,
}

#[derive(Default)]
pub struct Block {
    code: Vec<Inst>,
}

pub struct Function {
    // TODO do we need to store `owned` or not? really it's a property of the closure, not the function...
    pars: Vec<(Name, Type)>,
    // Corresponds to a prefix of `locals`
    upvalues: u32,
    // These come after the parameter
    locals: Vec<(Name, Type)>,
    rty: Type,
    body: Block,
}

pub struct Closure {
    fun: Arc<Function>,
    upvalues: Vec<Value>,
}

impl Val {
    fn l1_type(&self) -> Type {
        match self {
            Val::Neutral(Head::Def(def), spine) => todo!("sum types"),
            Val::Neutral(Head::Builtin(Builtin::UnitType | Builtin::Region), _) => Type::Unit,
            Val::Neutral(_, _) => panic!(),
            Val::Fun(f @ VFun { class: Pi(fc), .. }) => {
                let aty = f.pty.l1_type();
                let rty = self.clone().app(Val::Unknown).l1_type();
                Type::Fun(*fc == FCap::Own, vec![aty], Arc::new(rty))
            }
            Val::Fun(
                f @ VFun {
                    class: Sigma(_), ..
                },
            ) => {
                let aty = f.pty.l1_type();
                let rty = self.clone().app(Val::Unknown).l1_type();
                Type::Pair(Arc::new(aty), Arc::new(rty))
            }
            Val::Fun(_) => unreachable!(),
            Val::Pair(_, _) => unreachable!(),
            // TODO region stuff
            Val::Cap(cap, _, val) => match cap {
                Cap::Mut => Type::Mut(Arc::new(val.l1_type())),
                Cap::Imm => Type::Imm(Arc::new(val.l1_type())),
                Cap::Own => val.l1_type(),
            },
            Val::Region(_) | Val::Borrow(_) => unreachable!(),
            Val::Unknown => Type::Any,
            Val::Error => panic!(),
            Val::Type => Type::Unit,
        }
    }
    fn l1_val(&self) -> Option<Value> {
        match self {
            Val::Neutral(Head::Builtin(b), v) if v.is_empty() => match b {
                Builtin::Unit => Some(Value::Unit),
                _ => None,
            },
            Val::Fun(_) => None,
            Val::Pair(val, val1) => Some(Value::Pair(
                Arc::new(val.l1_val()?),
                Arc::new(val1.l1_val()?),
            )),
            // TODO not sure how to do this, in theory no matter what these go to () but then we don't know if they're "known at `meta` time" or whatever...
            Val::Cap(cap, vals, val) => None,
            Val::Region(vals) => None,
            Val::Borrow(borrows) => None,
            Val::Unknown => None,
            Val::Error => None,
            Val::Type => Some(Value::Unit),
            _ => None,
        }
    }
}

#[derive(Default)]
pub struct LCxt {
    block: Block,
    locals: Vec<(Sym, Type)>,
}
impl LCxt {
    fn lookup(&self, s: Sym) -> Option<u32> {
        self.locals
            .iter()
            .enumerate()
            .find(|(_, (n, _))| s == *n)
            .map(|(i, _)| i as u32)
    }
    fn push(&mut self, inst: Inst) {
        self.block.code.push(inst);
    }
    fn define(&mut self, s: Sym, t: Type) -> u32 {
        if self.lookup(s).is_some() {
            panic!()
        }
        let l = self.locals.len() as u32;
        self.locals.push((s, t));
        l
    }
}

impl Term {
    // returns the value of this term at the top of the stack
    fn lower(&self, cxt: &mut LCxt) {
        match self {
            Term::Head(head) => match head {
                Head::Sym(sym) => {
                    let i = cxt.lookup(*sym).unwrap();
                    cxt.push(Inst::PushLocal(i));
                }
                Head::Def(def) => todo!(),
                Head::Meta(_) => unreachable!(),
                Head::Builtin(b) => match b {
                    Builtin::Module => panic!("???"),
                    Builtin::Region | Builtin::Unit | Builtin::UnitType => {
                        cxt.push(Inst::PushConstant(Value::Unit))
                    }
                },
            },
            Term::App(f, TElim::App(_, x)) => {
                f.lower(cxt);
                x.lower(cxt);
                cxt.push(Inst::Call(1));
            }
            Term::App(term, TElim::Match(branches, fallback)) => todo!(),
            Term::Fun(tfun) => {
                // TODO should this function be at global scope or something?
                let (f, upvalues) = tfun.lower(cxt);
                for i in upvalues {
                    cxt.push(Inst::PushLocal(i));
                }
                cxt.push(Inst::PushClosure(Arc::new(f)))
            }
            Term::Pair(term, term1) => {
                term.lower(cxt);
                term1.lower(cxt);
                cxt.push(Inst::MakePair);
            }
            Term::Assign(term, term1) => todo!(),
            // Type erasure: `Type` lowers to `()` (as does e.g. `Region`)
            Term::Cap(_, _)
            | Term::Region(_)
            | Term::RegionAnn(_, _)
            | Term::Type
            | Term::Borrow(_) => cxt.push(Inst::PushConstant(Value::Unit)),
            Term::Unknown => panic!(),
            Term::Error => panic!(),
        }
    }
}

impl TFun {
    pub fn lower(&self, parent: &LCxt) -> (Function, Vec<u32>) {
        let pty = self.pty.eval(&default()).l1_type();
        let mut cxt = LCxt::default();
        // TODO annotate TFun with upvalues ???????? bc we do not have access to those atm...
        cxt.define(self.psym, pty.clone());
        self.body.lower(&mut cxt);
        cxt.push(Inst::Ret);
        (
            Function {
                pars: vec![(self.psym.0, pty)],
                upvalues: 0,
                // skip the parameter, return the rest of the locals
                // TODO upvalue order?
                locals: cxt
                    .locals
                    .iter()
                    .skip(1)
                    .map(|(s, t)| (s.0, t.clone()))
                    .collect(),
                rty: Type::Any, // TODO rty
                body: cxt.block,
            },
            default(),
        )
    }
}

impl Pretty for Value {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            Value::Closure(closure) => Doc::start("<closure>"),
            Value::Pair(a, b) => "(" + a.pretty(db) + ", " + b.pretty(db) + ")",
            Value::Unit => Doc::start("()"),
        }
    }
}

impl Pretty for Type {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            Type::Any => Doc::keyword("any"),
            Type::Pair(a, b) => "(" + a.pretty(db) + ", " + b.pretty(db) + ")",
            Type::Imm(t) => Doc::keyword("imm ") + t.pretty(db),
            Type::Mut(t) => Doc::keyword("mut ") + t.pretty(db),
            Type::Fun(b, pars, rty) => {
                "(" + Doc::intersperse(pars.iter().map(|t| t.pretty(db)), Doc::start(", "))
                    + if *b { ") ~> " } else { ") -> " }
                    + rty.pretty(db)
            }
            Type::Sum(v) => todo!(),
            Type::Unit => Doc::start("()"),
        }
    }
}

impl Pretty for Block {
    fn pretty(&self, db: &DB) -> Doc {
        let mut doc = Doc::none();
        for i in &self.code {
            doc = doc.hardline()
                + match i {
                    Inst::PushConstant(v) => Doc::keyword("pushc ") + v.pretty(db),
                    Inst::PushLocal(i) => Doc::keyword("pushl ").add(i, ()),
                    Inst::SetLocal(i) => Doc::keyword("setl ").add(i, ()),
                    Inst::PushClosure(_) => Doc::keyword("pushclosure ").add("_", ()),
                    Inst::Call(i) => Doc::keyword("call ").add(i, ()),
                    Inst::SplitPair => Doc::keyword("splitpair"),
                    Inst::MakePair => Doc::keyword("makepair"),
                    Inst::Drop => Doc::keyword("drop"),
                    Inst::Ret => Doc::keyword("ret"),
                };
        }
        doc
    }
}

impl Pretty for Function {
    fn pretty(&self, db: &DB) -> Doc {
        Doc::keyword("function ")
            .add("(", ())
            .chain(Doc::intersperse(
                self.pars
                    .iter()
                    .map(|(n, t)| n.pretty(db) + ": " + t.pretty(db)),
                Doc::start(", "),
            ))
            .add(") {", ())
            .add(self.upvalues, ())
            .add("} -> ", ())
            .chain(self.rty.pretty(db))
            .add(":", ())
            .chain(self.body.pretty(db))
            .indent()
    }
}
