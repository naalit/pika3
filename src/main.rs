mod common;
mod lexer;
mod parser;
mod pretty;
mod query;

use std::{fs::File, io::Read};

use lsp_types::Url;
use pretty::Pretty;

use crate::common::*;

// types

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Idx(NonZeroU32);
impl Idx {
    fn at(self, env: &Env) -> Val {
        // [a, b] at 1 is a (vec[0]), at 0 is b (vec[1])
        // and the idx is stored as 1+i since it's a NonZeroU32 so this works
        if env.len() < self.0.get() as usize {
            panic!("idx {} at {}", self.0, env.len())
        }
        env[env.len() - self.0.get() as usize].clone()
    }
}

#[derive(Debug)]
enum Term {
    Var(Name, Idx), // really Spanned<Name>
    App(Box<Term>, Box<Term>),
    /// Argument type annotation
    Fun(Class, Name, Box<Term>, Arc<Term>),
    Error,
    Type,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Sym(Name, NonZeroU32);

type Env = im::Vector<Val>;

#[derive(Debug, Clone)]
enum Val {
    Neutral(Sym, Vec<Val>), // will be im::Vector<Elim> in the future pry?
    Fun(Class, Name, Arc<Val>, Arc<Term>, Env), // oh update im::Vector is *way* bigger than Vec in terms of stack size. 64 vs 24 bytes. so it might be best to stick with Vec(Cow<Vec>?) or roll our own
    Error,
    Type,
}

// eval

impl Val {
    pub fn app(self, other: Val) -> Val {
        match self {
            Val::Neutral(s, vec) => Val::Neutral(s, vec.tap_mut(|v| v.push(other))),
            Val::Fun(_, _, _, body, env) => body.eval(&env.tap_mut(|v| v.push_back(other))),
            Val::Error => Val::Error,
            _ => unreachable!("illegal app to {:?}", self),
        }
    }
}

impl Term {
    pub fn eval(&self, env: &Env) -> Val {
        match self {
            Term::Var(_, idx) => idx.at(env),
            Term::App(f, x) => f.eval(env).app(x.eval(env)),
            Term::Fun(c, s, aty, body) => {
                Val::Fun(*c, *s, Arc::new(aty.eval(env)), body.clone(), env.clone())
            }
            Term::Error => Val::Error,
            Term::Type => Val::Type,
        }
    }
}

#[derive(Copy, Clone)]
struct SymCxt(NonZeroU32);
impl Default for SymCxt {
    fn default() -> Self {
        Self(1.try_into().unwrap())
    }
}
impl SymCxt {
    fn bind(&mut self, s: Name) -> Sym {
        let s = Sym(s, self.0);
        self.0 = self.0.checked_add(1).unwrap();
        s
    }
}

#[derive(Clone, Default)]
struct QEnv {
    lvls: im::HashMap<Sym, u32>,
    scxt: SymCxt,
}
impl QEnv {
    fn get(&self, sym: Sym) -> Idx {
        // i don't *think* this is an off-by-one error...
        Idx((1 + self.lvls.len() as u32 - self.lvls.get(&sym).unwrap())
            .try_into()
            .unwrap())
    }

    fn bind(&self, s: Name, env: &Env) -> (Sym, SEnv) {
        let mut scxt = self.scxt;
        let sym = scxt.bind(s);
        let mut env = env.clone();
        let mut qenv = self.clone();
        env.push_back(Val::Neutral(sym, Vec::new()));
        qenv.scxt = scxt;
        qenv.lvls.insert(sym, qenv.lvls.len() as u32 + 1);
        (sym, SEnv { qenv, env })
    }
}

#[derive(Clone, Default)]
struct SEnv {
    qenv: QEnv,
    env: Env,
}

impl Term {
    pub fn subst(&self, env: &SEnv) -> Term {
        match self {
            Term::Var(_, idx) => idx.at(&env.env).quote(&env.qenv),
            Term::App(f, x) => Term::App(Box::new(f.subst(env)), Box::new(x.subst(env))),
            Term::Fun(c, s, aty, body) => Term::Fun(
                *c,
                *s,
                Box::new(aty.subst(env)),
                Arc::new(body.subst(&env.qenv.bind(*s, &env.env).1)),
            ),
            Term::Error => Term::Error,
            Term::Type => Term::Type,
        }
    }
}

impl Val {
    pub fn quote(&self, env: &QEnv) -> Term {
        match self {
            Val::Neutral(s, spine) => spine.iter().fold(Term::Var(s.0, env.get(*s)), |acc, x| {
                Term::App(Box::new(acc), Box::new(x.quote(env)))
            }),
            Val::Fun(c, s, aty, body, inner_env) => Term::Fun(
                *c,
                *s,
                Box::new(aty.quote(env)),
                Arc::new(body.subst(&env.bind(*s, inner_env).1)),
            ),
            Val::Error => Term::Error,
            Val::Type => Term::Type,
        }
    }
}

// elaboration

use crate::parser::{Pre, PreDef, PrePat, SPre};

#[derive(Clone, Default)]
struct Cxt {
    db: DB,
    // levels, starting at 0
    bindings: im::HashMap<Name, (u32, Val)>,
    env: SEnv,
    errors: Ref<Vec<Error>>,
}
impl Cxt {
    fn err(&self, err: impl Into<Doc>, span: Span) {
        self.errors.with_mut(|v| v.push(Error::simple(err, span)));
    }
    fn lookup(&self, n: Name) -> Option<(Idx, Val)> {
        self.bindings.get(&n).map(|(lvl, val)| {
            (
                Idx(NonZeroU32::new(self.bindings.len() as u32 - lvl).unwrap()),
                val.clone(),
            )
        })
    }
    fn bind(&self, n: Name, ty: Val) -> (Sym, Cxt) {
        let mut s = self.clone();
        s.bindings.insert(n, (s.bindings.len() as u32, ty));
        let (sym, env) = s.env.qenv.bind(n, &s.env.env);
        s.env = env;
        (sym, s)
    }
    fn env(&self) -> &Env {
        &self.env.env
    }
    fn qenv(&self) -> &QEnv {
        &self.env.qenv
    }
    fn senv(&self) -> &SEnv {
        &self.env
    }
    fn scxt(&self) -> SymCxt {
        self.env.qenv.scxt
    }
}

impl Val {
    fn unify(&self, other: &Val, scxt: SymCxt) -> bool {
        match (self, other) {
            (Val::Error, _) | (_, Val::Error) => true,
            (Val::Type, Val::Type) => true,
            (Val::Neutral(s, sp), Val::Neutral(s2, sp2)) if s == s2 => {
                sp.len() == sp2.len() && sp.iter().zip(sp2).all(|(x, y)| x.unify(y, scxt))
            }
            (Val::Fun(Pi, n1, aty, _, _), Val::Fun(Pi, _, aty2, _, _)) => {
                let mut scxt2 = scxt;
                let s = scxt2.bind(*n1);
                let arg = Val::Neutral(s, Vec::new());
                aty.unify(aty2, scxt)
                    && self
                        .clone()
                        .app(arg.clone())
                        .unify(&other.clone().app(arg), scxt2)
            }
            (_, _) => false,
        }
    }
}

impl SPre {
    fn infer(&self, cxt: &Cxt) -> (Term, Val) {
        match &***self {
            Pre::Var(name) => match cxt.lookup(*name) {
                Some((ix, ty)) => (Term::Var(*name, ix), ty),
                None => {
                    cxt.err(&format!("not found: {}", cxt.db.get(*name)), self.span());
                    (Term::Error, Val::Error)
                }
            },
            Pre::App(fs, x) => {
                let (f, fty) = fs.infer(cxt);
                let aty = match &fty {
                    Val::Error => Val::Error,
                    Val::Fun(Pi, _, aty, _, _) => (**aty).clone(),
                    _ => {
                        cxt.err(
                            &format!("not a function type: {}", fty.show(cxt)),
                            fs.span(),
                        );
                        Val::Error
                    }
                };
                let x = x.check(aty, cxt);
                let vx = x.eval(cxt.env());
                (Term::App(Box::new(f), Box::new(x)), fty.app(vx))
            }
            Pre::Pi(n, aty, body) => {
                let aty = aty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let body = body.check(Val::Type, &cxt.bind(*n, vaty).1);
                (Term::Fun(Pi, *n, Box::new(aty), Arc::new(body)), Val::Type)
            }
            Pre::Lam(_, _) => {
                cxt.err("could not infer type of lambda", self.span());
                (Term::Error, Val::Error)
            }
            Pre::Binder(_, _) => {
                cxt.err("binder not allowed in this context", self.span());
                (Term::Error, Val::Error)
            }
            Pre::Type => (Term::Type, Val::Type),
            Pre::Error => (Term::Error, Val::Error),
        }
    }
    fn check(&self, ty: Val, cxt: &Cxt) -> Term {
        match (&***self, &ty) {
            (Pre::Lam(pat, body), Val::Fun(Pi, _, aty2, _, _)) => {
                let (n, aty) = match &**pat {
                    PrePat::Name(s) => (*s, None),
                    PrePat::Binder(s, s1) => (*s, Some(s1.clone())),
                    PrePat::Error => (S(cxt.db.name("_"), pat.span()), None),
                };
                if let Some(aty) = aty {
                    let aty = aty.check(Val::Type, cxt).eval(cxt.env());
                    if !aty.unify(&aty2, cxt.scxt()) {
                        cxt.err(
                            &format!(
                                "wrong parameter type: expected {}, found {}",
                                aty2.show(cxt),
                                aty.show(cxt)
                            ),
                            self.span(),
                        );
                    }
                }
                let aty = aty2.quote(cxt.qenv());
                let (sym, cxt) = cxt.bind(*n, (**aty2).clone());
                let rty = ty.app(Val::Neutral(sym, Vec::new()));
                let body = body.check(rty, &cxt);
                Term::Fun(Lam, *n, Box::new(aty), Arc::new(body))
            }
            (_, _) => {
                let (s, sty) = self.infer(cxt);
                if !ty.unify(&sty, cxt.scxt()) {
                    cxt.err(
                        &format!(
                            "could not match types: expected {}, found {}",
                            ty.show(cxt),
                            sty.show(cxt)
                        ),
                        self.span(),
                    );
                }
                s
            }
        }
    }
}

impl Val {
    fn show(&self, cxt: &Cxt) -> Show {
        self.quote(cxt.qenv()).show(&cxt.db)
    }
}

// simple pretty-printer

struct Show(im_rope::Rope, u32);
impl std::fmt::Display for Show {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}
impl std::ops::Add<Show> for Show {
    type Output = Show;

    fn add(self, rhs: Show) -> Self::Output {
        Show(self.0 + rhs.0, self.1.max(rhs.1))
    }
}
impl std::ops::Add<&str> for Show {
    type Output = Show;

    fn add(self, rhs: &str) -> Self::Output {
        Show(self.0.tap_mut(|x| x.append(rhs)), self.1)
    }
}
impl std::ops::Add<Show> for &str {
    type Output = Show;

    fn add(self, rhs: Show) -> Self::Output {
        Show(rhs.0.tap_mut(|x| x.prepend(self)), rhs.1)
    }
}
impl Show {
    fn nest(self, prec: u32) -> Show {
        if self.1 > prec {
            ("(" + self + ")").with(0)
        } else {
            self
        }
    }

    fn with(self, prec: u32) -> Show {
        Show(self.0, prec)
    }
}

impl Term {
    pub fn show(&self, db: &DB) -> Show {
        match self {
            Term::Var(n, _) => Show(db.get(*n).rope(), 0), // + &*format!("{}", i.0.get() - 1),
            Term::App(f, x) => f.show(db).nest(1) + " " + x.show(db).nest(0),
            Term::Fun(Lam, s, _, body) => Show("λ".into(), 2) + &*db.get(*s) + ". " + body.show(db),
            Term::Fun(Pi, s, aty, body) => {
                Show("(".into(), 2)
                    + &*db.get(*s)
                    + ": "
                    + aty.show(db).nest(1)
                    + ") -> "
                    + body.show(db)
            }
            Term::Error => Show("error".into(), 0),
            Term::Type => Show("Type".into(), 0),
        }
    }
}

fn main() {
    // Hey it works! 100-line evaluator. How many is the Haskell?
    // The Haskell version is ~50 lines lol. It's probably faster too bc the RTS is very well-optimized out of the box.
    // But the Rust version probably has higher like performance potential? Certainly we have more control over representations etc.
    // Well and also the Haskell version is fully-named (but no renaming bc only evaluating to WHNF), whereas we're doing locally nameless which is probably more code.
    // let s = r#"(λzero.λsuc.λplus.λmul.
    //         (λtwo. mul two (plus two two))
    //         (suc (suc zero))
    //     )
    //     (λf.λx. x)
    //     (λz.λf.λx. f (z f x))
    //     (λm.λn.λf.λx. m f (n f x))
    //     (λm.λn.λf.λx. m (n f) x)
    //     (λx.λy. y x) (λx. x)
    //     "#;
    let (input, input_s) = {
        let mut file = File::open("demo.pk").unwrap();
        let mut input = String::new();
        file.read_to_string(&mut input).unwrap();
        (input.rope(), input)
    };
    let mut cxt = Cxt::default();
    let file = cxt.db.ifiles.intern(&FileLoc::Url(
        Url::from_file_path(std::path::Path::new("demo.pk").canonicalize().unwrap()).unwrap(),
    ));
    cxt.db
        .set_file_source(file, input.clone(), Some(input_s.into()));

    let r = crate::parser::parse(input.clone(), &cxt.db);
    // println!("{:?}", r);
    let mut cache = FileCache::new(cxt.db.clone());
    for i in r.defs {
        let ty = i.0.ty.as_ref().map(|ty| ty.check(Val::Type, &cxt));
        if let Some((val, ty)) = i.0.value.as_ref().map(|val| match &ty {
            Some(ty) => {
                let vty = ty.eval(&cxt.env());
                (val.check(vty.clone(), &cxt), vty)
            }
            None => val.infer(&cxt),
        }) {
            i.name
                .pretty(&cxt.db)
                .add(" : ", ())
                .add(ty.show(&cxt), ())
                .add(" = ", ())
                .add(val.show(&cxt.db), ())
                .emit_stderr();
        } else if let Some(ty) = ty {
            i.name
                .pretty(&cxt.db)
                .add(" : ", ())
                .add(ty.show(&cxt.db), ())
                .emit_stderr();
        } else {
            i.name.pretty(&cxt.db).add(" : ??", ()).emit_stderr();
        }
    }
    for i in r.errors {
        i.write_cli(file, &mut cache);
    }
    for i in cxt.errors.take() {
        i.write_cli(file, &mut cache);
    }

    // let cxt = Cxt::default();
    // let mut p = Parser::new(input.clone(), &cxt.db);
    // let pre = p.term();
    // let (x, xty) = pre.infer(&cxt);
    // println!("{}", x.eval(cxt.env()).show(&cxt));
    // println!(": {}", xty.show(&cxt));
    // cxt.errors.with(|e| {
    //     e.iter().for_each(|S(e, sp)| {
    //         eprintln!("{}: error: {}", sp.0, e);
    //         eprintln!(
    //             "|{}",
    //             input.subrope(sp.0 as usize..).lines().next().unwrap()
    //         );
    //     })
    // });
    // for (e, sp) in p.errors {
    //     eprintln!("{}: error: {}", sp, e);
    //     eprintln!("|{}", input.subrope(sp..).lines().next().unwrap());
    // }
}
