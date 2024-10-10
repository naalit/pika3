use crate::common::*;

// entry point (per-file elab query)

pub fn elab_module(file: File, def: Def, db: &DB) -> ModuleElabResult {
    let parsed = db.file_ast(file);
    let mut errors = parsed.errors.clone();
    let mut defs = Vec::new();
    for i in &parsed.defs {
        let def = db.idefs.intern(&DefLoc::Child(def, *i.name));
        if let Some(elab) = db.elab.def_value(def, db) {
            defs.push(elab.def);
            errors.extend(elab.errors.iter().cloned());
        }
    }
    ModuleElabResult {
        module: Arc::new(Module { defs }),
        errors,
    }
}

pub fn elab_def(def: Def, db: &DB) -> Option<DefElabResult> {
    let (file, file_def) = db.def_file(def);
    let def_loc = db.idefs.get(def);
    if def_loc.parent() != Some(file_def) {
        // TODO how do child defs even work in this system?
        return None;
    }
    let name = def_loc.name();
    let parsed = db.file_ast(file);
    let pre = parsed.defs.iter().find(|d| *d.name == name)?;

    eprintln!("[elab def {}]", def.pretty(db));

    let cxt = Cxt::new(def, db.clone());
    let ty = pre.0.ty.as_ref().map(|ty| ty.check(Val::Type, &cxt));
    let (body, ty) = if let Some((val, ty)) = pre.0.value.as_ref().map(|val| match &ty {
        Some(ty) => {
            let vty = ty.eval(&cxt.env());
            (val.check(vty.clone(), &cxt), vty)
        }
        None => val.infer(&cxt),
    }) {
        (Some(val), ty)
    } else if let Some(ty) = ty {
        (None, ty.eval(&cxt.env()))
    } else {
        (None, Val::Error)
    };

    Some(DefElabResult {
        def: Arc::new(DefElab {
            name: pre.name,
            ty,
            body: body.map(|x| x.eval(&cxt.env())),
        }),
        errors: cxt.errors.take(),
    })
}

// types

#[derive(Debug)]
pub struct DefElab {
    pub name: SName,
    pub ty: Val,
    pub body: Option<Val>,
}

#[derive(Debug)]
pub struct Module {
    pub defs: Vec<Arc<DefElab>>,
}

#[derive(Clone, Debug)]
pub struct DefElabResult {
    pub def: Arc<DefElab>,
    pub errors: Vec<Error>,
}

#[derive(Clone, Debug)]
pub struct ModuleElabResult {
    pub module: Arc<Module>,
    pub errors: Vec<Error>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Idx(u32);
impl Idx {
    fn at(self, env: &Env) -> Val {
        // [a, b] at 1 is a (vec[0]), at 0 is b (vec[1])
        if env.len() < self.0 as usize + 1 {
            panic!("idx {} at {}", self.0, env.len())
        }
        env[env.len() - self.0 as usize - 1].clone()
    }
}

#[derive(Debug, PartialEq)]
pub enum Term {
    Var(Name, Idx),
    Def(Def),
    App(Box<Term>, Box<Term>),
    /// Argument type annotation
    Fun(Class, Name, Box<Term>, Arc<Term>),
    Error,
    Type,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(Name, NonZeroU32);

type Env = im::Vector<Val>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VHead {
    Sym(Sym),
    Def(Def),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Neutral(VHead, Vec<Val>), // will be im::Vector<Elim> in the future pry?
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
            Term::Def(d) => Val::Neutral(VHead::Def(*d), Vec::new()),
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
    partial_cxt: bool,
}
impl QEnv {
    fn get(&self, sym: Sym) -> Term {
        // i don't *think* this is an off-by-one error...
        if let Some(l) = self.lvls.get(&sym) {
            Term::Var(sym.0, Idx(self.lvls.len() as u32 - l - 1))
        } else {
            if self.partial_cxt {
                Term::Var(sym.0, Idx(0))
            } else {
                panic!("not in qenv")
            }
        }
    }

    fn bind(&self, s: Name, env: &Env) -> (Sym, SEnv) {
        let mut scxt = self.scxt;
        let sym = scxt.bind(s);
        let mut env = env.clone();
        let mut qenv = self.clone();
        env.push_back(Val::Neutral(VHead::Sym(sym), Vec::new()));
        qenv.scxt = scxt;
        qenv.lvls.insert(sym, qenv.lvls.len() as u32);
        (sym, SEnv { qenv, env })
    }
}

#[derive(Clone, Default)]
struct SEnv {
    qenv: QEnv,
    env: Env,
}

impl Term {
    fn subst(&self, env: &SEnv) -> Term {
        match self {
            Term::Var(_, idx) => idx.at(&env.env).quote(&env.qenv),
            Term::Def(d) => Term::Def(*d),
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
    fn quote(&self, env: &QEnv) -> Term {
        match self {
            Val::Neutral(s, spine) => spine.iter().fold(
                match s {
                    VHead::Sym(s) => env.get(*s),
                    VHead::Def(d) => Term::Def(*d),
                },
                |acc, x| Term::App(Box::new(acc), Box::new(x.quote(env))),
            ),
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

use crate::parser::{Pre, PrePat, SPre};

#[derive(Clone)]
struct Cxt {
    db: DB,
    def: Def,
    // levels, starting at 0
    bindings: im::HashMap<Name, (u32, Val)>,
    env: SEnv,
    errors: Ref<Vec<Error>>,
}
impl Cxt {
    fn new(context: Def, db: DB) -> Cxt {
        Cxt {
            def: context,
            db,
            bindings: default(),
            env: default(),
            errors: default(),
        }
    }
    fn err(&self, err: impl Into<Doc>, span: Span) {
        self.errors.with_mut(|v| v.push(Error::simple(err, span)));
    }
    fn size(&self) -> u32 {
        self.env.env.len() as u32
    }
    fn lookup(&self, n: Name) -> Option<(Term, Val)> {
        // first try locals
        self.bindings
            .get(&n)
            .map(|(lvl, val)| (Term::Var(n, Idx(self.size() - lvl - 1)), val.clone()))
            .or_else(|| {
                self.db
                    .lookup_def_name(self.def, n)
                    .map(|(d, t)| (Term::Def(d), t))
            })
    }
    fn bind(&self, n: Name, ty: Val) -> (Sym, Cxt) {
        let mut s = self.clone();
        s.bindings.insert(n, (s.size(), ty));
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

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum UnfoldState {
    Yes,
    No,
    Maybe,
}
impl UnfoldState {
    fn spine_mode(self) -> UnfoldState {
        match self {
            UnfoldState::Yes => UnfoldState::Yes,
            UnfoldState::No => UnfoldState::No,
            UnfoldState::Maybe => UnfoldState::No,
        }
    }
}

impl Val {
    fn whnf(&mut self, db: &DB) {
        match self {
            Val::Neutral(VHead::Def(d), spine) => {
                if let Some(elab) = db.elab.def_value(*d, db) {
                    if let Some(term) = elab.def.body.as_ref() {
                        *self = spine.iter().fold(term.clone(), |acc, x| acc.app(x.clone()));
                        self.whnf(db);
                    }
                }
            }
            _ => (),
        }
    }
    fn unify(&self, other: &Val, scxt: SymCxt, db: &DB) -> bool {
        self.unify_(other, scxt, db, UnfoldState::Maybe)
    }
    fn unify_(&self, other: &Val, scxt: SymCxt, db: &DB, mode: UnfoldState) -> bool {
        let (mut a, mut b) = (self.clone(), other.clone());
        if mode == UnfoldState::Yes {
            a.whnf(db);
            b.whnf(db);
        }
        match (&a, &b) {
            (Val::Error, _) | (_, Val::Error) => true,
            (Val::Type, Val::Type) => true,
            (Val::Neutral(s, sp), Val::Neutral(s2, sp2))
                if s == s2
                    && sp.len() == sp2.len()
                    && sp
                        .iter()
                        .zip(sp2)
                        .all(|(x, y)| x.unify_(y, scxt, db, mode.spine_mode())) =>
            {
                true
            }
            (Val::Neutral(_, _), _) | (_, Val::Neutral(_, _)) if mode == UnfoldState::Maybe => {
                a.unify_(&b, scxt, db, UnfoldState::Yes)
            }
            (Val::Fun(c, n1, aty, _, _), Val::Fun(c2, _, aty2, _, _)) if c == c2 => {
                let mut scxt2 = scxt;
                let s = scxt2.bind(*n1);
                let arg = Val::Neutral(VHead::Sym(s), Vec::new());
                aty.unify_(aty2, scxt, db, mode) && a.app(arg.clone()).unify(&b.app(arg), scxt2, db)
            }
            (_, _) => false,
        }
    }
}

impl SPre {
    fn infer(&self, cxt: &Cxt) -> (Term, Val) {
        match &***self {
            Pre::Var(name) => match cxt.lookup(*name) {
                Some((term, ty)) => (term, ty),
                None => {
                    cxt.err("not found: {}" + name.pretty(&cxt.db), self.span());
                    (Term::Error, Val::Error)
                }
            },
            Pre::App(fs, x) => {
                let (f, mut fty) = fs.infer(cxt);
                fty.whnf(&cxt.db);
                let aty = match &fty {
                    Val::Error => Val::Error,
                    Val::Fun(Pi, _, aty, _, _) => (**aty).clone(),
                    _ => {
                        cxt.err("not a function type: " + fty.pretty_at(cxt), fs.span());
                        // prevent .app() from panicking
                        fty = Val::Error;
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
    fn check(&self, mut ty: Val, cxt: &Cxt) -> Term {
        ty.whnf(&cxt.db);
        match (&***self, &ty) {
            (Pre::Lam(pat, body), Val::Fun(Pi, _, aty2, _, _)) => {
                let (n, aty) = match &**pat {
                    PrePat::Name(s) => (*s, None),
                    PrePat::Binder(s, s1) => (*s, Some(s1.clone())),
                    PrePat::Error => (S(cxt.db.name("_"), pat.span()), None),
                };
                if let Some(aty) = aty {
                    let aty = aty.check(Val::Type, cxt).eval(cxt.env());
                    if !aty.unify(&aty2, cxt.scxt(), &cxt.db) {
                        cxt.err(
                            "wrong parameter type: expected "
                                + aty2.pretty_at(cxt)
                                + ", found "
                                + aty.pretty_at(cxt),
                            self.span(),
                        );
                    }
                }
                let aty = aty2.quote(cxt.qenv());
                let (sym, cxt) = cxt.bind(*n, (**aty2).clone());
                let rty = ty.app(Val::Neutral(VHead::Sym(sym), Vec::new()));
                let body = body.check(rty, &cxt);
                Term::Fun(Lam, *n, Box::new(aty), Arc::new(body))
            }
            (_, _) => {
                let (s, sty) = self.infer(cxt);
                if !ty.unify(&sty, cxt.scxt(), &cxt.db) {
                    cxt.err(
                        "could not match types: expected "
                            + ty.pretty_at(cxt)
                            + ", found "
                            + sty.pretty_at(cxt),
                        self.span(),
                    );
                }
                s
            }
        }
    }
}

impl Val {
    fn pretty_at(&self, cxt: &Cxt) -> Doc {
        self.quote(cxt.qenv()).pretty(&cxt.db)
    }
    pub fn pretty(&self, db: &DB) -> Doc {
        self.quote(&QEnv {
            partial_cxt: true,
            ..default()
        })
        .pretty(&db)
    }
}

// pretty-printing

impl Pretty for Term {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            // TODO how do we get types of local variables for e.g. semantic highlights or hover?
            Term::Var(n, _i) => Doc::start(db.get(*n)), // + &*format!("{}", _i.0),
            Term::Def(d) => db.idefs.get(*d).name().pretty(db),
            Term::App(f, x) => {
                (f.pretty(db).nest(Prec::App) + " " + x.pretty(db).nest(Prec::Atom)).prec(Prec::App)
            }
            Term::Fun(Lam, s, _, body) => {
                (s.pretty(db) + " => " + body.pretty(db)).prec(Prec::Term)
            }
            Term::Fun(Pi, s, aty, body) if *s == db.name("_") => {
                (aty.pretty(db).nest(Prec::App) + " -> " + body.pretty(db)).prec(Prec::Pi)
            }
            Term::Fun(Pi, s, aty, body) => (Doc::start("(")
                + &*db.get(*s)
                + ": "
                + aty.pretty(db).nest(Prec::Pi)
                + ") -> "
                + body.pretty(db))
            .prec(Prec::Pi),
            Term::Error => Doc::keyword("error"),
            Term::Type => Doc::start("Type"),
        }
    }
}
