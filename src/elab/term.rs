use super::*;

use std::sync::{atomic::AtomicU32, Arc};

// -- types --

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(pub Name, u32);
impl Sym {
    pub fn num(self) -> u32 {
        self.1
    }
}

/// Meta ?d.0 is reserved for the type of `d`
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Meta(pub(super) Def, pub(super) u32);
impl Pretty for Meta {
    fn pretty(&self, _db: &DB) -> Doc {
        "?" + Doc::start(self.0.num()) + "." + Doc::start(self.1)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Builtin {
    Module,
    Region,
    Unit,
    UnitType,
}
impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Builtin::Module => write!(f, "Module"),
            Builtin::Region => write!(f, "Region"),
            Builtin::Unit => write!(f, "()"),
            Builtin::UnitType => write!(f, "()"),
        }
    }
}
impl From<Builtin> for Term {
    fn from(value: Builtin) -> Self {
        Term::Head(Head::Builtin(value))
    }
}
impl From<Builtin> for Val {
    fn from(value: Builtin) -> Self {
        Val::Neutral(Head::Builtin(value), Vec::new())
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Head {
    Sym(Sym),
    Def(Def),
    Meta(Meta),
    Builtin(Builtin),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Borrow {
    pub sym: Sym,
    pub span: Span,
    pub imm_gen: u32,
    pub mut_gen: Option<u32>,
}
impl Borrow {
    pub fn mutable(&self) -> bool {
        self.mut_gen.is_some()
    }
}
// TODO switch to Vec<(Borrow, Option<T>)> or similar
#[derive(Clone, Debug, PartialEq, Educe)]
#[educe(Default)]
pub struct Region {
    pub borrows: FxHashMap<Sym, Borrow>,
    pub values: Vec<Arc<Val>>,
}
impl Region {
    pub fn is_empty(&self) -> bool {
        self.borrows.is_empty() && self.values.is_empty()
    }
    pub fn whnf(&mut self, cxt: &Cxt) {
        let mut i = 0;
        while i < self.values.len() {
            let v = self.values[i].maybe_whnf(cxt);
            match v {
                Some(v @ (Val::Borrow(_) | Val::Region(_))) => {
                    self.add(Region::from_val(vec![Arc::new(v)], &default(), cxt), cxt);
                    self.values.swap_remove(i);
                }
                Some(v) => {
                    self.values[i] = Arc::new(v);
                    i += 1;
                }
                None => i += 1,
            }
        }
    }
    pub fn add(&mut self, other: Region, cxt: &Cxt) {
        self.values.extend(
            other
                .values
                .into_iter()
                //.map(|v| Arc::new((*v).clone().and_whnf(cxt)))
                // .filter_map(|v| match &*v {
                //     Val::Borrow(b) => {
                //         let b: Vec<_> = b
                //             .iter()
                //             .copied()
                //             .filter(|b| {
                //                 !self.borrows.contains_key(&b.sym)
                //                     || (b.mutable() && !self.borrows.get(&b.sym).unwrap().mutable())
                //             })
                //             .collect();
                //         if b.is_empty() {
                //             None
                //         } else {
                //             Some(Arc::new(Val::Borrow(b)))
                //         }
                //     }
                //     _ => Some(v),
                // })
                .filter(|v| {
                    !self.values.iter().any(|v2| {
                        (**v).clone().glued().unify(
                            None,
                            (**v2).clone().glued(),
                            None,
                            cxt.errors.span.span(),
                            cxt,
                        )
                    })
                })
                .collect::<Vec<_>>(),
        );
        for (k, v) in other.borrows {
            match self.borrows.get_mut(&k) {
                None => {
                    self.borrows.insert(k, v);
                }
                Some(v2) => {
                    // the oldest one is the one that matters
                    v2.imm_gen = v.imm_gen.min(v2.imm_gen);
                    v2.mut_gen = v
                        .mut_gen
                        .map(|i| v2.mut_gen.map_or(i, |j| i.min(j)))
                        .or(v2.mut_gen);
                }
            }
        }
    }
    pub fn borrows(&self) -> Box<dyn Iterator<Item = &Borrow> + '_> {
        Box::new(self.borrows.values())
    }
    pub fn borrows_mut(&mut self) -> Box<dyn Iterator<Item = &mut Borrow> + '_> {
        Box::new(self.borrows.values_mut())
    }

    pub fn values(&self) -> Vec<Arc<Val>> {
        let mut values = Vec::new();
        if !self.borrows.is_empty() {
            values.push(Arc::new(Val::Borrow(
                self.borrows.values().copied().collect(),
            )));
        }
        values.extend(self.values.iter().cloned());
        values
    }

    pub fn from_val(values: Vec<Arc<Val>>, base: &Region, cxt: &Cxt) -> Self {
        let mut r = Region::default();
        let mut any_unknown = false;
        for i in values {
            match &*i {
                Val::Region(v) => r.add(Region::from_val(v.clone(), base, cxt), cxt),
                Val::Borrow(b) => {
                    for &i in b {
                        r.add(i.into(), cxt);
                    }
                }
                _ => {
                    r.values.push(i);
                    any_unknown = true;
                }
            }
        }
        if any_unknown {
            r.add(base.clone(), cxt);
        }
        r
    }
}
impl From<Borrow> for Region {
    fn from(value: Borrow) -> Self {
        Region {
            borrows: std::iter::once((value.sym, value)).collect(),
            values: Vec::new(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Head(Head),
    App(Box<Term>, TElim),
    /// Argument type annotation
    Fun(TFun),
    Pair(Box<Term>, Box<Term>),
    Cap(Cap, Box<Term>),
    Assign(Box<Term>, Box<Term>),
    Region(Vec<Term>),
    RegionAnn(Box<Term>, Box<Term>),
    Borrow(Vec<Borrow>),
    Unknown,
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
    Fun(VFun),
    Pair(Arc<Val>, Arc<Val>),
    Cap(Cap, Option<Vec<Arc<Val>>>, Arc<Val>),
    Region(Vec<Arc<Val>>),
    Borrow(Vec<Borrow>),
    Unknown,
    Error,
    Type,
}
impl Val {
    pub fn sym(sym: Sym) -> Val {
        Val::Neutral(Head::Sym(sym), default())
    }
    pub fn as_cap(self, c: Cap) -> Val {
        if c == Cap::Own {
            return self;
        }
        match self {
            Val::Cap(e, r, rest) => Val::Cap(c.min(e), r, rest),
            _ => Val::Cap(c, None, Arc::new(self)),
        }
    }
    fn unregion(self) -> Vec<Arc<Val>> {
        match self {
            Val::Region(r) => r,
            _ => vec![Arc::new(self)],
        }
    }
    pub fn with_region(self, r: Option<Vec<Arc<Val>>>) -> Val {
        match self {
            // Types can't contain (accessible) pointers so they don't care about regions
            // The compiler knowing that makes type-level programming a bit nicer
            // Val::Type => Val::Type,
            Val::Cap(e, r2, rest) if r.is_none() => Val::Cap(e, r2, rest),
            Val::Cap(e, _, rest) => Val::Cap(e, r, rest),
            _ => Val::Cap(Cap::Own, r, Arc::new(self)),
        }
    }
    pub fn uncap(&self) -> (Cap, Option<Vec<Arc<Val>>>, &Val) {
        match self {
            Val::Cap(c, r, rest) => (*c, r.clone(), rest),
            _ => (Cap::Own, None, self),
        }
    }
    pub fn cap(&self) -> Cap {
        match self {
            Val::Cap(c, _, _) => *c,
            _ => Cap::Own,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct VFun {
    pub class: Class,
    pub icit: Icit,
    pub psym: Sym,
    pub rself_sym: Option<Sym>,
    pub pty: Arc<Val>,
    body: Arc<Term>,
    env: Arc<Env>,
}
#[derive(Clone, Debug, PartialEq)]
pub struct TFun {
    pub class: Class,
    pub icit: Icit,
    rself_sym: Option<Sym>,
    psym: Sym,
    pty: Box<Term>,
    body: Arc<Term>,
}
impl VFun {
    fn quote_(&self, env: &QEnv) -> Result<TFun, Sym> {
        // Fast path: if the environment is empty, we don't need to subst the term
        // This is mostly useful for inlining metas in terms
        if self.env.is_empty() {
            Ok(TFun {
                class: self.class,
                icit: self.icit,
                psym: self.psym,
                rself_sym: self.rself_sym,
                pty: Box::new(self.pty.quote_(env)?),
                body: self.body.clone(),
            })
        } else {
            let (sym, senv) = env.senv(&self.env).bind(self.psym);
            let (rself_sym, senv) = self.rself_sym.map_or((None, senv.clone()), |r| {
                let (a, b) = senv.bind(r);
                (Some(a), b)
            });
            Ok(TFun {
                class: self.class,
                icit: self.icit,
                psym: sym,
                rself_sym,
                pty: Box::new(self.pty.quote_(env)?),
                body: Arc::new(self.body.subst(&senv)?),
            })
        }
    }
}
impl TFun {
    fn subst(&self, env: &SEnv) -> Result<TFun, Sym> {
        let (s, env2) = env.bind(self.psym);
        let (rself_sym, env2) = self.rself_sym.map_or((None, env2.clone()), |r| {
            let (a, b) = env2.bind(r);
            (Some(a), b)
        });
        Ok(TFun {
            class: self.class,
            icit: self.icit,
            psym: s,
            rself_sym,
            pty: Box::new(self.pty.subst(env)?),
            body: Arc::new(self.body.subst(&env2)?),
        })
    }
    fn eval(&self, env: &Env) -> VFun {
        VFun {
            class: self.class,
            icit: self.icit,
            psym: self.psym,
            rself_sym: self.rself_sym,
            pty: Arc::new(self.pty.eval(env)),
            body: self.body.clone(),
            env: Arc::new(env.clone()),
        }
    }
    fn zonk_(&mut self, cxt: &Cxt, qenv: &QEnv, beta_reduce: bool) {
        self.pty.zonk_(cxt, qenv, beta_reduce);
        Arc::make_mut(&mut self.body).zonk_(cxt, &qenv, beta_reduce);
    }
}
impl Val {
    pub fn fun(
        class: Class,
        icit: Icit,
        psym: Sym,
        pty: Arc<Val>,
        rself_sym: Option<Sym>,
        body: Arc<Term>,
        env: Arc<Env>,
    ) -> Val {
        Val::Fun(VFun {
            class,
            icit,
            psym,
            rself_sym,
            pty,
            body,
            env,
        })
    }
}
impl Term {
    pub fn fun(
        class: Class,
        icit: Icit,
        psym: Sym,
        rself_sym: Option<Sym>,
        pty: Term,
        body: Arc<Term>,
    ) -> Term {
        Term::Fun(TFun {
            class,
            icit,
            psym,
            rself_sym,
            pty: Box::new(pty),
            body,
        })
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
            Term::Head(h) => Val::Neutral(*h, default()),
            Term::App(f, x) => x.eval(env).elim(f.eval(env)),
            Term::Fun(f) => Val::Fun(f.eval(env)),
            Term::Cap(c, x) => x.eval(env).as_cap(*c),
            Term::Pair(a, b) => Val::Pair(Arc::new(a.eval(env)), Arc::new(b.eval(env))),
            Term::Assign(_, _) => panic!("L0-evaluating term with mutation"),
            Term::Region(r) => {
                let mut v = Vec::new();
                for i in r {
                    match i.eval(env) {
                        Val::Region(mut r) => v.append(&mut r),
                        i => v.push(Arc::new(i)),
                    }
                }
                Val::Region(v)
            }
            Term::RegionAnn(r, x) => x.eval(env).with_region(Some(r.eval(env).unregion())),
            Term::Borrow(b) => Val::Borrow(b.clone()),
            Term::Unknown => Val::Unknown,
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
            Term::Head(h) => Term::Head(*h),
            Term::App(f, x) => Term::App(Box::new(f.subst(env)?), x.subst(env)?),
            Term::Fun(f) => Term::Fun(f.subst(env)?),
            Term::Cap(c, x) => Term::Cap(*c, Box::new(x.subst(env)?)),
            Term::Pair(a, b) => Term::Pair(Box::new(a.subst(env)?), Box::new(b.subst(env)?)),
            Term::Assign(a, b) => Term::Assign(Box::new(a.subst(env)?), Box::new(b.subst(env)?)),
            Term::Region(r) => {
                Term::Region(r.iter().map(|x| x.subst(env)).collect::<Result<_, _>>()?)
            }
            Term::RegionAnn(r, x) => {
                Term::RegionAnn(Box::new(r.subst(env)?), Box::new(x.subst(env)?))
            }
            Term::Borrow(b) => Term::Borrow(b.clone()),
            Term::Unknown => Term::Unknown,
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
            Val::Fun(f) => Term::Fun(f.quote_(env)?),
            Val::Region(r) => {
                Term::Region(r.iter().map(|x| x.quote_(env)).collect::<Result<_, _>>()?)
            }
            Val::Cap(c, None, x) => Term::Cap(*c, Box::new(x.quote_(env)?)),
            Val::Cap(c, Some(r), x) => Term::RegionAnn(
                // TODO skip the Region layer for one element?
                Box::new(Term::Region(
                    r.iter().map(|x| x.quote_(env)).collect::<Result<_, _>>()?,
                )),
                Box::new(Term::Cap(*c, Box::new(x.quote_(env)?))),
            ),
            Val::Pair(a, b) => Term::Pair(Box::new(a.quote_(env)?), Box::new(b.quote_(env)?)),
            Val::Borrow(b) => Term::Borrow(b.clone()),
            Val::Unknown => Term::Unknown,
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
                    // TODO need to respect L0-evaluability !?
                    *self = self.eval(&default()).quote(&qenv);
                    return true;
                }
            }
            Term::Fun(f) => f.zonk_(cxt, qenv, beta_reduce),
            Term::Pair(a, b) | Term::Assign(a, b) => {
                a.zonk_(cxt, qenv, beta_reduce);
                b.zonk_(cxt, qenv, beta_reduce);
            }
            Term::Cap(_, x) => {
                x.zonk_(cxt, qenv, beta_reduce);
            }
            Term::Region(r) => {
                r.iter_mut().for_each(|x| {
                    x.zonk_(cxt, qenv, beta_reduce);
                });
            }
            Term::RegionAnn(r, x) => {
                r.zonk_(cxt, qenv, beta_reduce);
                x.zonk_(cxt, qenv, beta_reduce);
            }
            Term::Head(_) | Term::Borrow(_) | Term::Error | Term::Type | Term::Unknown => (),
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
    Match(Vec<(PCons, Vec<(Icit, Sym)>, Arc<Term>)>, Option<Arc<Term>>),
    App(Icit, Box<Term>),
}
#[derive(Debug, Clone, PartialEq)]
pub enum VElim {
    Match(
        Vec<(PCons, Vec<(Icit, Sym)>, Arc<Term>)>,
        Option<Arc<Term>>,
        Arc<Env>,
    ),
    App(Icit, Arc<Val>),
}
impl Val {
    pub fn app_rself(self, x: Val, r: Val) -> Val {
        match self {
            Val::Fun(mut f) => f.body.eval(&Arc::make_mut(&mut f.env).tap_mut(|v| {
                v.0.insert(f.psym, Arc::new(x));
                if let Some(s) = f.rself_sym {
                    v.0.insert(s, Arc::new(r));
                }
            })),
            _ => self.app(x),
        }
    }
}
impl VElim {
    pub fn elim(self, v: Val) -> Val {
        match (self, v) {
            (VElim::App(_, x), Val::Fun(mut f)) => {
                f.body.eval(&Arc::make_mut(&mut f.env).tap_mut(|v| {
                    v.0.insert(f.psym, x);
                }))
            }

            (VElim::Match(v, _, mut env), Val::Pair(va, vb))
                if matches!(v.first(), Some((PCons::Pair(_), _, _))) =>
            {
                let (s1, s2) = match v.first() {
                    Some((PCons::Pair(_), v, _)) => (v[0], v[1]),
                    _ => unreachable!(),
                };
                v[0].2.eval(
                    &Arc::make_mut(&mut env).tap_mut(|v| v.0.extend([(s1.1, va), (s2.1, vb)])),
                )
            }

            (x, Val::Neutral(s, vec)) => Val::Neutral(s, vec.tap_mut(|v| v.push(x))),
            (_, Val::Error) => Val::Error,

            // Apply functions through caps (for pi types)
            // TODO do we need to do something with this region? it's the function `'self` borrow or whatever
            (s @ VElim::App(_, _), Val::Cap(_, _, v))
                if matches!(*v, Val::Fun { .. } | Val::Neutral(_, _)) =>
            {
                let q = s.elim(Arc::unwrap_or_clone(v));
                if format!("{:?}", q) == "Neutral(Def(Interned(1, PhantomData<pika3::common::DefLoc>)), [App(Expl, Neutral(Sym(Sym(Interned(10, PhantomData<alloc::sync::Arc<str>>), 7)), []))])" {
                    panic!()
                }
                q
            }

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
                            .map(|(i, s)| {
                                let (s, e) = env.bind(*s);
                                env = e;
                                (*i, s)
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
                        for (_, s) in vars {
                            let (_, e) = env.bind(*s);
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
            // We do need to whnf in caps because we call `.whnf().uncap()` and that needs to work
            Val::Cap(c, r, x) => x
                .maybe_whnf(cxt)
                .map(|x| Val::Cap(*c, r.clone(), Arc::new(x))),
            Val::Neutral(h, spine) => {
                if let Some(val) = match h {
                    Head::Def(d) => {
                        if let Ok(elab) = cxt.db.elab.def_value(*d, &cxt.db) {
                            elab.def
                                .can_eval
                                .then(|| {
                                    elab.def.body.and_then(|x| match x {
                                        DefBody::Val(x) => Some(Arc::new(x.eval(cxt.env()))),
                                        DefBody::Type(_) => None,
                                    })
                                })
                                .flatten()
                        } else {
                            None
                        }
                    }
                    Head::Sym(s) => cxt.local_val(*s),
                    Head::Meta(m) => cxt.meta_val(*m),
                    // TODO resolve applicable builtins
                    Head::Builtin(_) => None,
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
                                if v.iter().any(|(_, n)| n == s) {
                                    return None;
                                }
                            }
                            let mut env = (*env).clone();
                            let x = Val::Neutral(*h, spine);
                            for (_, s) in v {
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
    body.nest_icit(icit, prec)
}

fn pretty_branch(db: &DB, l: &PCons, v: &Vec<(Icit, Sym)>, t: &Arc<Term>) -> Doc {
    match l {
        PCons::Pair(i) => {
            v[0].1 .0.pretty(db).nest_icit(*i, Prec::Pi)
                + ", "
                + v[1].1 .0.pretty(db)
                + " => "
                + t.pretty(db)
        }
        PCons::Cons(d) => {
            db.idefs.get(*d).name().pretty(db)
                + Doc::intersperse(
                    v.iter()
                        .map(|(i, x)| " " + x.0.pretty(db).nest_icit(*i, Prec::Atom)),
                    Doc::none(),
                )
                + " => "
                + t.pretty(db)
        }
    }
}
fn pretty_region(db: &DB, r: &Vec<Term>) -> Doc {
    if r.is_empty() {
        Doc::start("'()")
    } else {
        Doc::intersperse(
            r.iter().map(|v| {
                // this is kind of hacky but. it works as a heuristic
                let v = v.pretty(db);
                if v.clone().to_string(false).starts_with("'") {
                    v
                } else {
                    "'(" + v + ")"
                }
            }),
            Doc::start(" "),
        )
    }
}

impl Term {
    fn head(&self) -> &Term {
        match self {
            Term::App(f, TElim::App(_, _)) => f.head(),
            _ => self,
        }
    }
}
impl Pretty for Term {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            // "expected ?42.8 x y y _ 'a _" is likely not a terribly helpful error message
            _ if matches!(self.head(), Term::Head(Head::Meta(_))) => Doc::start("_"),
            Term::Head(Head::Sym(s)) => Doc::start(db.get(s.0)),
            Term::Head(Head::Def(d)) => db.idefs.get(*d).name().pretty(db),
            Term::Head(Head::Meta(m)) => m.pretty(db),
            Term::Head(Head::Builtin(b)) => Doc::start(b),
            Term::App(f, TElim::App(i, x)) => {
                (f.pretty(db).nest(Prec::App) + " " + x.pretty(db).nest_icit(*i, Prec::Atom))
                    .prec(Prec::App)
            }
            Term::App(x, TElim::Match(v, fallback)) if v.len() <= 1 => (x.pretty(db).space()
                + Doc::keyword("case").space()
                + Doc::intersperse(
                    v.iter()
                        .map(|(l, v, t)| pretty_branch(db, l, v, t))
                        .chain(fallback.iter().map(|x| "_ => " + x.pretty(db))),
                    Doc::start(";").brk(),
                ))
            .indent()
            .prec(Prec::Term),
            Term::App(x, TElim::Match(v, fallback)) => (x.pretty(db).space()
                + Doc::keyword("case").hardline()
                + Doc::intersperse(
                    v.iter()
                        .map(|(l, v, t)| pretty_branch(db, l, v, t))
                        .chain(fallback.iter().map(|x| "_ => " + x.pretty(db))),
                    Doc::none().hardline(),
                ))
            .indent()
            .prec(Prec::Term),
            Term::Fun(f @ TFun { class: Lam, .. }) => {
                (f.psym.0.pretty(db).nest_icit(f.icit, Prec::Atom) + " => " + f.body.pretty(db))
                    .prec(Prec::Term)
            }
            Term::Fun(f @ TFun { class: Pi(c), .. }) => {
                (pretty_binder(f.psym.0, f.icit, Prec::App, f.pty.pretty(db), db)
                    + " "
                    + match c {
                        FCap::Own => "~> ",
                        FCap::Imm => "-> ",
                    }
                    + f.body.pretty(db).nest(Prec::Pi))
                .prec(Prec::Pi)
            }
            Term::Fun(
                f @ TFun {
                    class: Sigma(s2), ..
                },
            ) => (pretty_binder(f.psym.0, f.icit, Prec::Pi, f.pty.pretty(db), db)
                + ", "
                + pretty_binder(*s2, Expl, Prec::Pair, f.body.pretty(db), db))
            .prec(Prec::Pair),
            Term::Pair(a, b) => {
                (a.pretty(db).nest(Prec::Pi) + ", " + b.pretty(db).nest(Prec::Pair))
                    .prec(Prec::Pair)
            }
            Term::Assign(a, b) => {
                (a.pretty(db).nest(Prec::Pi) + " = " + b.pretty(db).nest(Prec::Pi)).prec(Prec::Term)
            }
            Term::Cap(c, x) => (if *c == Cap::Own {
                Doc::none()
            } else {
                Doc::keyword(*c).space()
            } + x.pretty(db).nest(Prec::App))
            .prec(Prec::App),
            Term::Unknown => Doc::keyword("??"),
            Term::Error => Doc::keyword("error"),
            Term::Type => Doc::start("Type"),
            Term::Region(r) => pretty_region(db, r),
            // TODO parens on `'a ('b t)`
            Term::RegionAnn(r, x) => {
                (r.pretty(db) + " " + x.pretty(db).nest(Prec::App)).prec(Prec::App)
            }
            Term::Borrow(v) => ("'("
                + Doc::intersperse(v.iter().map(|x| "&" + x.sym.0.pretty(db)), Doc::start(" "))
                + ")")
                .prec(Prec::Atom),
        }
    }
}
