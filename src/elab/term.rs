use super::*;
use crate::common::*;

// -- types --

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(pub Name, u32);

/// Meta ?d.0 is reserved for the type of `d`
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Meta(pub(super) Def, pub(super) u32);
impl Pretty for Meta {
    fn pretty(&self, _db: &DB) -> Doc {
        "?" + Doc::start(self.0.num()) + "." + Doc::start(self.1)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Head {
    Sym(Sym),
    Def(Def),
    Meta(Meta),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Head(Head),
    App(Box<Term>, TElim),
    /// Argument type annotation
    Fun(Class, Icit, Sym, Box<Term>, Arc<Term>),
    Pair(Box<Term>, Box<Term>),
    Error,
    Type,
}

// It would be nice for this to be im::HashMap, but that's slower in practice unfortunately. maybe we can make a hybrid or something?
#[derive(Clone, Debug, PartialEq, Educe)]
#[educe(Deref, Default)]
pub struct Env(pub(super) rustc_hash::FxHashMap<Sym, Arc<Val>>);
impl Env {
    fn bind(&self, s: Sym, scxt: &SymCxt) -> (Sym, Env) {
        let s2 = scxt.bind(s.0);
        (
            s2,
            Env(self.0.clone().tap_mut(|v| {
                v.insert(s, Arc::new(Val::sym(s2)));
            })),
        )
    }
}

pub type Spine = Vec<VElim>;

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Neutral(Head, Spine),
    Fun(Class, Icit, Sym, Arc<Val>, Arc<Term>, Arc<Env>),
    Pair(Arc<Val>, Arc<Val>),
    Error,
    Type,
}
impl Val {
    pub fn sym(sym: Sym) -> Val {
        Val::Neutral(Head::Sym(sym), default())
    }
}

// -- evaluation and quoting --

impl Val {
    pub fn app(self, other: Val) -> Val {
        VElim::App(Expl, Arc::new(other)).elim(self)
    }
}

impl Term {
    pub fn eval(&self, env: &Env) -> Val {
        with_stack(|| match self {
            Term::Head(Head::Sym(s)) => env.get(s).map(|x| (**x).clone()).unwrap_or(Val::sym(*s)),
            Term::Head(Head::Def(d)) => Val::Neutral(Head::Def(*d), default()),
            Term::Head(Head::Meta(m)) => Val::Neutral(Head::Meta(*m), default()),
            Term::App(f, x) => x.eval(env).elim(f.eval(env)),
            Term::Fun(c, i, s, aty, body) => Val::Fun(
                *c,
                *i,
                *s,
                Arc::new(aty.eval(env)),
                body.clone(),
                Arc::new(env.clone()),
            ),
            Term::Pair(a, b) => Val::Pair(Arc::new(a.eval(env)), Arc::new(b.eval(env))),
            Term::Error => Val::Error,
            Term::Type => Val::Type,
        })
    }
}

#[derive(Clone, Default)]
pub struct SymCxt(Arc<AtomicU32>);
impl SymCxt {
    pub fn bind(&self, s: Name) -> Sym {
        let n = self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        Sym(s, n)
    }
}

#[derive(Clone, Default)]
pub struct QEnv {
    pub scxt: SymCxt,
    pub partial_cxt: Option<im::HashSet<Sym>>,
    pub errors: Errors,
}
impl QEnv {
    fn senv(&self, env: &Env) -> SEnv {
        SEnv {
            qenv: self.clone(),
            env: env.clone(),
        }
    }
}

#[derive(Clone, Default)]
pub struct SEnv {
    pub qenv: QEnv,
    pub env: Env,
}
impl SEnv {
    fn put(&mut self, s: Sym) {
        if let Some(c) = &mut self.qenv.partial_cxt {
            c.insert(s);
        }
    }
    fn bind(&self, s: Sym) -> (Sym, SEnv) {
        let (s2, env) = self.env.bind(s, &self.qenv.scxt);
        let mut qenv = self.qenv.clone();
        if let Some(c) = &mut qenv.partial_cxt {
            c.insert(s2);
        }
        (s2, SEnv { env, qenv })
    }
    fn get(&self, s: Sym) -> Val {
        self.env
            .get(&s)
            .map(|v| (**v).clone())
            .unwrap_or(Val::sym(s))
    }
}

impl Term {
    fn subst(&self, env: &SEnv) -> Result<Term, Sym> {
        Ok(match self {
            Term::Head(Head::Sym(s)) => env.get(*s).quote_(&env.qenv)?,
            Term::Head(Head::Def(d)) => Term::Head(Head::Def(*d)),
            Term::Head(Head::Meta(m)) => Term::Head(Head::Meta(*m)),
            Term::App(f, x) => Term::App(Box::new(f.subst(env)?), x.subst(env)?),
            Term::Fun(c, i, s, aty, body) => {
                let (s, env2) = env.bind(*s);
                Term::Fun(
                    *c,
                    *i,
                    s,
                    Box::new(aty.subst(env)?),
                    Arc::new(body.subst(&env2)?),
                )
            }
            Term::Pair(a, b) => Term::Pair(Box::new(a.subst(env)?), Box::new(b.subst(env)?)),
            Term::Error => Term::Error,
            Term::Type => Term::Type,
        })
    }
}

impl Val {
    pub(super) fn quote(&self, env: &QEnv) -> Term {
        self.quote_(env).unwrap_or_else(|s| {
            env.errors.push(
                Error::simple(
                    Doc::start("internal error: out-of-scope variable ")
                        + s.0.pretty(&env.errors.db)
                        + " in term "
                        + self.pretty(&env.errors.db),
                    env.errors.span.span(),
                )
                .with_label("while elaborating this definition"),
            );
            // env.errors.panic();
            Term::Error
        })
    }
    pub(super) fn quote_(&self, env: &QEnv) -> Result<Term, Sym> {
        Ok(match self {
            Val::Neutral(s, spine) => spine.iter().fold(
                Ok(match s {
                    Head::Sym(s) if env.partial_cxt.as_ref().map_or(false, |v| !v.contains(s)) => {
                        return Err(*s)
                    }
                    h => Term::Head(*h),
                }),
                |acc, x| Ok(Term::App(Box::new(acc?), x.quote_(env)?)),
            )?,
            // Fast path: if the environment is empty, we don't need to subst the term
            // This is mostly useful for inlining metas in terms
            Val::Fun(c, i, s, aty, body, inner_env) if inner_env.is_empty() => {
                Term::Fun(*c, *i, *s, Box::new(aty.quote_(env)?), body.clone())
            }
            Val::Fun(c, i, s, aty, body, inner_env) => {
                let (sym, senv) = env.senv(inner_env).bind(*s);
                Term::Fun(
                    *c,
                    *i,
                    sym,
                    Box::new(aty.quote_(env)?),
                    Arc::new(body.subst(&senv)?),
                )
            }
            Val::Pair(a, b) => Term::Pair(Box::new(a.quote_(env)?), Box::new(b.quote_(env)?)),
            Val::Error => Term::Error,
            Val::Type => Term::Type,
        })
    }
}

impl Term {
    pub(super) fn zonk(&mut self, cxt: &Cxt, beta_reduce: bool) {
        self.zonk_(cxt, &cxt.qenv(), beta_reduce);
    }
    fn zonk_(&mut self, cxt: &Cxt, qenv: &QEnv, beta_reduce: bool) -> bool {
        match self {
            Term::Head(Head::Meta(meta)) => match cxt.zonked_meta_val(*meta, beta_reduce) {
                // Meta solutions are evaluated with an empty environment, so we can quote them with an empty environment
                Some(t) => {
                    *self = t.quote(&default());
                    // inline further metas in the solution
                    // self.zonk_(cxt, qenv, beta_reduce);
                    // (should be unnecessary with pre-zonked meta solutions)
                    // (however, that only holds as long as we don't zonk until the end of the definition)
                    return true;
                }
                None => (),
            },
            Term::App(term, term1) => {
                // β-reduce meta spines by eval-quoting
                let solved_meta = term.zonk_(cxt, qenv, beta_reduce);
                term1.zonk_(cxt, qenv, beta_reduce);
                if beta_reduce && solved_meta {
                    // we should be able to eval in an empty environment since we dont need to rename
                    *self = self.eval(&default()).quote(&qenv);
                    return true;
                }
            }
            Term::Fun(_, _, _, aty, body) => {
                aty.zonk_(cxt, qenv, beta_reduce);
                Arc::make_mut(body).zonk_(cxt, &qenv, beta_reduce);
            }
            Term::Pair(a, b) => {
                a.zonk_(cxt, qenv, beta_reduce);
                b.zonk_(cxt, qenv, beta_reduce);
            }
            Term::Head(_) | Term::Error | Term::Type => (),
        }
        false
    }
}

impl Val {
    pub(super) fn zonk(&self, cxt: &Cxt, beta_reduce: bool) -> Val {
        // We could do this without quote-eval'ing, but it'd need a bunch of Arc::make_mut()s
        self.quote(&cxt.qenv())
            .tap_mut(|x| x.zonk(cxt, beta_reduce))
            .eval(&cxt.env())
    }
}

// -- eliminations --

#[derive(Debug, Clone, PartialEq)]
pub enum TElim {
    // (branches, fallback)
    Match(Vec<(PCons, Vec<Sym>, Arc<Term>)>, Option<Arc<Term>>),
    App(Icit, Box<Term>),
}
#[derive(Debug, Clone, PartialEq)]
pub enum VElim {
    Match(
        Vec<(PCons, Vec<Sym>, Arc<Term>)>,
        Option<Arc<Term>>,
        Arc<Env>,
    ),
    App(Icit, Arc<Val>),
}
impl VElim {
    pub fn elim(self, v: Val) -> Val {
        match (self, v) {
            (VElim::App(_, x), Val::Fun(_, _, s, _, body, mut env)) => {
                body.eval(&Arc::make_mut(&mut env).tap_mut(|v| {
                    v.0.insert(s, x);
                }))
            }

            (VElim::Match(v, _, mut env), Val::Pair(va, vb))
                if matches!(v.first(), Some((PCons::Pair(_), _, _))) =>
            {
                let (s1, s2) = match v.first() {
                    Some((PCons::Pair(_), v, _)) => (v[0], v[1]),
                    _ => unreachable!(),
                };
                v[0].2
                    .eval(&Arc::make_mut(&mut env).tap_mut(|v| v.0.extend([(s1, va), (s2, vb)])))
            }

            (x, Val::Neutral(s, vec)) => Val::Neutral(s, vec.tap_mut(|v| v.push(x))),
            (_, Val::Error) => Val::Error,
            (s, v) => {
                // TODO how do we get the error out of here?
                eprintln!("illegal elimination {:?}\non {:?}", s, v);
                Val::Error
            }
        }
    }
    fn quote_(&self, env: &QEnv) -> Result<TElim, Sym> {
        Ok(match self {
            VElim::Match(v, fallback, inner_env) => TElim::Match(
                v.iter()
                    .map(|(l, vars, t)| {
                        let mut env = env.senv(&inner_env);
                        let vars = vars
                            .iter()
                            .map(|s| {
                                let (s, e) = env.bind(*s);
                                env = e;
                                s
                            })
                            .collect();
                        Ok((*l, vars, Arc::new(t.subst(&env)?)))
                    })
                    .collect::<Result<_, _>>()?,
                fallback
                    .as_ref()
                    .map(|x| Ok(Arc::new(x.subst(&env.senv(&inner_env))?)))
                    .transpose()?,
            ),
            VElim::App(i, x) => TElim::App(*i, Box::new(x.quote_(env)?)),
        })
    }
}
impl TElim {
    fn subst(&self, env: &SEnv) -> Result<TElim, Sym> {
        Ok(match self {
            TElim::Match(v, fallback) => TElim::Match(
                v.iter()
                    .map(|(l, vars, t)| {
                        let mut env = env.clone();
                        for i in vars {
                            let (_, e) = env.bind(*i);
                            env = e;
                        }
                        Ok((*l, vars.clone(), Arc::new(t.subst(&env)?)))
                    })
                    .collect::<Result<_, _>>()?,
                fallback
                    .as_ref()
                    .map(|x| Ok(Arc::new(x.subst(env)?)))
                    .transpose()?,
            ),
            TElim::App(i, x) => TElim::App(*i, Box::new(x.subst(env)?)),
        })
    }
    fn eval(&self, env: &Env) -> VElim {
        match self {
            TElim::Match(v, fallback) => {
                VElim::Match(v.clone(), fallback.clone(), Arc::new(env.clone()))
            }
            TElim::App(i, x) => VElim::App(*i, Arc::new(x.eval(env))),
        }
    }
    fn zonk_(&mut self, cxt: &Cxt, qenv: &QEnv, beta_reduce: bool) -> bool {
        match self {
            TElim::Match(v, fallback) => {
                for (_, _, t) in v {
                    Arc::make_mut(t).zonk_(cxt, qenv, beta_reduce);
                }
                if let Some(fallback) = fallback {
                    Arc::make_mut(fallback).zonk_(cxt, qenv, beta_reduce);
                }
            }
            TElim::App(_, x) => {
                x.zonk_(cxt, qenv, beta_reduce);
            }
        }
        false
    }
}

// -- whnf and glued evaluation --

#[derive(Clone, Debug)]
pub struct GVal(Val, Val);
impl GVal {
    pub fn whnf(&mut self, cxt: &Cxt) -> &Val {
        self.1.whnf_(cxt);
        &self.1
    }
    pub fn as_small(self) -> Val {
        self.0
    }
    pub fn as_big(self) -> Val {
        self.1
    }
    pub fn small(&self) -> &Val {
        &self.0
    }
    pub fn big(&self) -> &Val {
        &self.1
    }
    pub fn map(self, mut f: impl FnMut(Val) -> Val) -> Self {
        GVal(f(self.0), f(self.1))
    }
}
impl From<Val> for GVal {
    fn from(value: Val) -> Self {
        value.glued()
    }
}

impl Val {
    fn and_whnf(self, cxt: &Cxt) -> Val {
        match self.maybe_whnf(cxt) {
            Some(s) => s,
            None => self,
        }
    }
    fn maybe_whnf(&self, cxt: &Cxt) -> Option<Val> {
        match self {
            Val::Neutral(h, spine) => {
                if let Some(val) = match h {
                    Head::Def(d) => {
                        if let Ok(elab) = cxt.db.elab.def_value(*d, &cxt.db) {
                            elab.def.body.clone()
                        } else {
                            None
                        }
                    }
                    Head::Sym(s) => cxt.local_val(*s),
                    Head::Meta(m) => cxt.meta_val(*m),
                } {
                    Some(
                        match &*val {
                            // fast path for neutrals (this makes like a 5-10% difference on Bench.pk)
                            Val::Neutral(head, v) => {
                                Val::Neutral(*head, v.iter().chain(&*spine).cloned().collect())
                            }
                            term => spine
                                .iter()
                                .fold(term.clone(), |acc, x| x.clone().elim(acc)),
                        }
                        .and_whnf(cxt),
                    )
                } else if spine
                    .last()
                    .iter()
                    .any(|x| matches!(x, VElim::Match(v, None, _) if v.len() == 1))
                {
                    // For a single-branch match, go down a level and reabstract each variable behind the same match
                    // TODO: can we put this in elim()? also this technically benefits from an owned self
                    let mut spine = spine.clone();
                    match spine.pop() {
                        Some(VElim::Match(v2, None, env)) if v2.len() == 1 => {
                            let (l, v, t) = &v2[0];
                            // Avoid infinite recursion - abort if we're already just returning one of the matched variables
                            if let Term::Head(Head::Sym(s)) = &**t {
                                if v.contains(s) {
                                    return None;
                                }
                            }
                            let mut env = (*env).clone();
                            let x = Val::Neutral(*h, spine);
                            for s in v {
                                env.0.insert(
                                    *s,
                                    Arc::new(
                                        VElim::Match(
                                            vec![(
                                                *l,
                                                v.clone(),
                                                Arc::new(Term::Head(Head::Sym(*s))),
                                            )],
                                            None,
                                            Arc::new(env.clone()),
                                        )
                                        .elim(x.clone()),
                                    ),
                                );
                            }
                            Some(t.eval(&env).and_whnf(cxt))
                        }
                        _ => unreachable!(),
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }
    pub(super) fn glued(self) -> GVal {
        GVal(self.clone(), self)
    }
    fn whnf_(&mut self, cxt: &Cxt) {
        if let Some(s) = self.maybe_whnf(cxt) {
            *self = s;
        }
        return;
    }
}

// -- pretty-printing --

impl Pretty for Val {
    fn pretty(&self, db: &DB) -> Doc {
        self.quote(&QEnv {
            partial_cxt: None,
            errors: Errors {
                db: db.clone(),
                ..default()
            },
            ..default()
        })
        .pretty(&db)
    }
}

fn pretty_binder(name: Name, icit: Icit, prec: Prec, rest: Doc, db: &DB) -> Doc {
    let body = if name == db.name("_") {
        rest
    } else {
        let prec = Prec::Pi.min(rest.prec);
        (name.pretty(db) + ": " + rest.nest(Prec::Pi)).prec(prec)
    };
    match icit {
        Impl => "{" + body + "}",
        Expl => body.nest(prec),
    }
}

impl Pretty for Term {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            // TODO how do we get types of local variables for e.g. semantic highlights or hover?
            Term::Head(Head::Sym(s)) => Doc::start(db.get(s.0)), // + &*format!("@{}", s.1),
            Term::Head(Head::Def(d)) => db.idefs.get(*d).name().pretty(db),
            Term::Head(Head::Meta(m)) => m.pretty(db),
            // TODO we probably want to show implicit and explicit application differently, but that requires threading icits through neutral spines...
            Term::App(f, TElim::App(i, x)) => (f.pretty(db).nest(Prec::App)
                + " "
                + pretty_binder(
                    db.name("_"),
                    *i,
                    Prec::Atom,
                    x.pretty(db).nest(Prec::Atom),
                    db,
                ))
            .prec(Prec::App),
            Term::App(x, TElim::Match(v, fallback)) => (x.pretty(db).space()
                + Doc::keyword("match").space()
                + Doc::intersperse(
                    v.iter()
                        .map(|(l, v, t)| match l {
                            PCons::Pair(i) => {
                                pretty_binder(db.name("_"), *i, Prec::Term, v[0].0.pretty(db), db)
                                    + ", "
                                    + v[1].0.pretty(db)
                                    + " => "
                                    + t.pretty(db)
                            }
                        })
                        .chain(fallback.iter().map(|x| "_ => " + x.pretty(db))),
                    Doc::start(";").brk(),
                ))
            .indent()
            .prec(Prec::Term),
            Term::Fun(Lam, i, s, _, body) => (pretty_binder(
                db.name("_"),
                *i,
                Prec::Atom,
                s.0.pretty(db).nest(Prec::Atom),
                db,
            ) + " => "
                + body.pretty(db))
            .prec(Prec::Term),
            Term::Fun(Pi, i, s, aty, body) => {
                (pretty_binder(s.0, *i, Prec::App, aty.pretty(db), db)
                    + " -> "
                    + body.pretty(db).nest(Prec::Pi))
                .prec(Prec::Pi)
            }
            Term::Fun(Sigma(s2), i, s1, aty, body) => {
                (pretty_binder(s1.0, *i, Prec::Pi, aty.pretty(db), db)
                    + ", "
                    + pretty_binder(*s2, Expl, Prec::Pair, body.pretty(db), db))
                .prec(Prec::Pair)
            }
            Term::Pair(a, b) => {
                (a.pretty(db).nest(Prec::Pi) + ", " + b.pretty(db).nest(Prec::Pair))
                    .prec(Prec::Pair)
            }
            Term::Error => Doc::keyword("error"),
            Term::Type => Doc::start("Type"),
        }
    }
}
