use std::collections::HashMap;

use smallvec::SmallVec;

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
    let (mut body, ty) = if let Some((val, ty)) = pre.0.value.as_ref().map(|val| match &ty {
        Some(ty) => {
            let vty = ty.eval(&cxt.env());
            (val.check(vty.clone(), &cxt), vty)
        }
        None => val.infer(&cxt, true),
    }) {
        (Some(val), ty)
    } else if let Some(ty) = ty {
        (None, ty.eval(&cxt.env()))
    } else {
        (None, Val::Error)
    };
    body.as_mut().map(|x| x.zonk(&cxt, false));
    let ty = ty.zonk(&cxt, true);

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
    fn at(self, env: &Env) -> Arc<Val> {
        // [a, b] at 1 is a (vec[0]), at 0 is b (vec[1])
        if env.len() < self.0 as usize + 1 {
            panic!("idx {} at {}", self.0, env.len())
        }
        env[env.len() - self.0 as usize - 1].clone()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Term {
    Var(Name, Idx),
    Def(Def),
    Meta(Meta),
    App(Box<Term>, Box<Term>),
    /// Argument type annotation
    Fun(Class, Icit, Name, Box<Term>, Arc<Term>),
    Pair(Box<Term>, Box<Term>),
    Error,
    Type,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sym(Name, NonZeroU32);

// It would be nice for this to be im::Vector, but that's slower in practice since it's like 5x the stack size...
type Env = SmallVec<[Arc<Val>; 3]>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VHead {
    Sym(Sym),
    Def(Def),
    Meta(Meta),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Neutral(VHead, SmallVec<[Arc<Val>; 3]>),
    Fun(Class, Icit, Name, Arc<Val>, Arc<Term>, Arc<Env>),
    Pair(Arc<Val>, Arc<Val>),
    Error,
    Type,
}

// eval

impl Val {
    pub fn app(self, other: Val) -> Val {
        match self {
            Val::Neutral(s, vec) => Val::Neutral(s, vec.tap_mut(|v| v.push(Arc::new(other)))),
            Val::Fun(_, _, _, _, body, mut env) => {
                body.eval(&Arc::make_mut(&mut env).tap_mut(|v| v.push(Arc::new(other))))
            }
            Val::Error => Val::Error,
            _ => unreachable!("illegal app to {:?}", self),
        }
    }
}

impl Term {
    pub fn eval(&self, env: &Env) -> Val {
        match self {
            Term::Var(_, idx) => Arc::unwrap_or_clone(idx.at(env)),
            Term::Def(d) => Val::Neutral(VHead::Def(*d), default()),
            Term::Meta(m) => Val::Neutral(VHead::Meta(*m), default()),
            Term::App(f, x) => f.eval(env).app(x.eval(env)),
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
    fn get(&self, sym: Sym) -> Option<Term> {
        // i don't *think* this is an off-by-one error...
        if let Some(l) = self.lvls.get(&sym) {
            Some(Term::Var(sym.0, Idx(self.lvls.len() as u32 - l - 1)))
        } else {
            if self.partial_cxt {
                Some(Term::Var(sym.0, Idx(0)))
            } else {
                None
            }
        }
    }

    fn bind(&self, s: Name, env: &Env) -> (Sym, SEnv) {
        let mut scxt = self.scxt;
        let sym = scxt.bind(s);
        let mut env = env.clone();
        let mut qenv = self.clone();
        env.push(Arc::new(Val::Neutral(VHead::Sym(sym), default())));
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
    fn subst(&self, env: &SEnv) -> Result<Term, Sym> {
        Ok(match self {
            Term::Var(_, idx) => idx.at(&env.env).quote_(&env.qenv)?,
            Term::Def(d) => Term::Def(*d),
            Term::Meta(m) => Term::Meta(*m),
            Term::App(f, x) => Term::App(Box::new(f.subst(env)?), Box::new(x.subst(env)?)),
            Term::Fun(c, i, s, aty, body) => Term::Fun(
                *c,
                *i,
                *s,
                Box::new(aty.subst(env)?),
                Arc::new(body.subst(&env.qenv.bind(*s, &env.env).1)?),
            ),
            Term::Pair(a, b) => Term::Pair(Box::new(a.subst(env)?), Box::new(b.subst(env)?)),
            Term::Error => Term::Error,
            Term::Type => Term::Type,
        })
    }
}

impl Val {
    fn quote(&self, env: &QEnv) -> Term {
        self.quote_(env).unwrap()
    }
    fn quote_(&self, env: &QEnv) -> Result<Term, Sym> {
        Ok(match self {
            Val::Neutral(s, spine) => spine.iter().fold(
                Ok(match s {
                    VHead::Sym(s) => env.get(*s).ok_or(*s)?,
                    VHead::Def(d) => Term::Def(*d),
                    VHead::Meta(m) => Term::Meta(*m),
                }),
                |acc, x| Ok(Term::App(Box::new(acc?), Box::new(x.quote_(env)?))),
            )?,
            // Fast path: if the environment is empty, we don't need to subst the term
            // This is mostly useful for inlining metas in terms
            Val::Fun(c, i, s, aty, body, inner_env) if inner_env.is_empty() => {
                Term::Fun(*c, *i, *s, Box::new(aty.quote_(env)?), body.clone())
            }
            Val::Fun(c, i, s, aty, body, inner_env) => Term::Fun(
                *c,
                *i,
                *s,
                Box::new(aty.quote_(env)?),
                Arc::new(body.subst(&env.bind(*s, inner_env).1)?),
            ),
            Val::Pair(a, b) => Term::Pair(Box::new(a.quote_(env)?), Box::new(b.quote_(env)?)),
            Val::Error => Term::Error,
            Val::Type => Term::Type,
        })
    }
}

impl Term {
    fn zonk(&mut self, cxt: &Cxt, beta_reduce: bool) {
        self.zonk_(cxt, &cxt.senv(), beta_reduce);
    }
    fn zonk_(&mut self, cxt: &Cxt, senv: &SEnv, beta_reduce: bool) -> bool {
        match self {
            Term::Meta(meta) => match cxt.zonked_meta_val(*meta, beta_reduce) {
                // Meta solutions are evaluated with an empty environment, so we can quote them with an empty environment
                Some(t) => {
                    *self = t.quote(&default());
                    // inline further metas in the solution
                    // self.zonk_(cxt, senv);
                    // (should be unnecessary with pre-zonked meta solutions)
                    // (however, that only holds as long as we don't zonk until the end of the definition)
                    return true;
                }
                None => (),
            },
            Term::App(term, term1) => {
                // β-reduce meta spines by eval-quoting
                let solved_meta = term.zonk_(cxt, senv, beta_reduce);
                term1.zonk_(cxt, senv, beta_reduce);
                if beta_reduce && solved_meta {
                    *self = self.eval(&senv.env).quote(&senv.qenv);
                    return true;
                }
            }
            Term::Fun(_, _, n, aty, body) => {
                aty.zonk_(cxt, senv, beta_reduce);
                Arc::make_mut(body).zonk_(cxt, &senv.qenv.bind(*n, &senv.env).1, beta_reduce);
            }
            Term::Pair(a, b) => {
                a.zonk_(cxt, senv, beta_reduce);
                b.zonk_(cxt, senv, beta_reduce);
            }
            Term::Var { .. } | Term::Def { .. } | Term::Error | Term::Type => (),
        }
        false
    }
}

impl Val {
    fn zonk(&self, cxt: &Cxt, beta_reduce: bool) -> Val {
        // We could do this without quote-eval'ing, but it'd need a bunch of Arc::make_mut()s
        self.quote(&cxt.qenv())
            .tap_mut(|x| x.zonk(cxt, beta_reduce))
            .eval(&cxt.env())
    }
}

// elaboration

use crate::parser::{Pre, PrePat, PreStmt, SPre};

enum MetaEntry {
    // The first field is the type; we'll need that eventually for typeclass resolution, but it doesn't matter right now
    // TODO error on unsolved metas (that's why the span is here)
    Unsolved(Arc<Val>, Span),
    Solved(Arc<Val>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Meta(Def, u32);
impl Pretty for Meta {
    fn pretty(&self, _db: &DB) -> Doc {
        "?" + Doc::start(self.0.num()) + "." + Doc::start(self.1)
    }
}

#[derive(Clone)]
struct Cxt {
    db: DB,
    def: Def,
    // levels, starting at 0
    bindings: im::HashMap<Name, (u32, Val)>,
    metas: Ref<HashMap<Meta, MetaEntry>>,
    zonked_metas: Ref<HashMap<(Meta, bool), Val>>,
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
            metas: default(),
            zonked_metas: default(),
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

    fn new_meta(&self, ty: Val, span: Span) -> Val {
        // This can skip numbers in the presence of solved external metas but that shouldn't matter
        let m = Meta(self.def, self.metas.with(|x| x.len()) as u32);
        self.metas
            .with_mut(|x| x.insert(m, MetaEntry::Unsolved(Arc::new(ty), span)));
        let v = Val::Neutral(VHead::Meta(m), self.env.env.clone());
        v
    }
    fn meta_val(&self, m: Meta) -> Option<Arc<Val>> {
        self.metas.with(|x| {
            x.get(&m).and_then(|x| match x {
                MetaEntry::Unsolved(_, _) => None,
                MetaEntry::Solved(arc) => Some(arc.clone()),
            })
        })
    }
    fn zonked_meta_val(&self, m: Meta, beta_reduce: bool) -> Option<Val> {
        self.zonked_metas
            .with(|x| x.get(&(m, beta_reduce)).cloned())
            .or_else(|| {
                let v = self.meta_val(m)?;
                let v = v.zonk(self, beta_reduce);
                self.zonked_metas
                    .with_mut(|x| x.insert((m, beta_reduce), v.clone()));
                Some(v)
            })
    }
    fn solve_meta(&self, meta: Meta, spine: &Env, solution: Val, span: Span) {
        let qenv = QEnv {
            lvls: spine
                .iter()
                .enumerate()
                .filter_map(|(l, v)| match &**v {
                    Val::Neutral(VHead::Sym(s), sp) if sp.is_empty() => Some((*s, l as u32)),
                    _ => None,
                })
                .collect(),
            ..default()
        };
        // There are more checks than this that we could do, that we don't do
        // For now this is enough, but in the future we might need to do more
        match solution.quote_(&qenv) {
            Ok(body) => {
                let term = spine.iter().fold(body, |acc, _| {
                    Term::Fun(
                        Lam,
                        Expl,
                        self.db.name("_"),
                        Box::new(Term::Error),
                        Arc::new(acc),
                    )
                });
                // Eval in an empty environment
                let val = term.eval(&default());
                self.metas
                    .with_mut(|m| m.insert(meta, MetaEntry::Solved(Arc::new(val))));
            }
            Err(s) => {
                self.err(
                    Doc::start("cannot solve meta ")
                        + meta.pretty(&self.db)
                        + " to a term referencing local variable "
                        + s.0.pretty(&self.db)
                        + ": `"
                        + solution.pretty(&self.db)
                        + "`",
                    span,
                );
            }
        }
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
    fn whnf(&mut self, cxt: &Cxt) {
        match self {
            Val::Neutral(VHead::Def(d), spine) => {
                if let Some(elab) = cxt.db.elab.def_value(*d, &cxt.db) {
                    if let Some(val) = elab.def.body.as_ref() {
                        match val {
                            // fast path for neutrals (this makes like a 5-10% difference on Bench.pk)
                            Val::Neutral(head, v) => {
                                *self =
                                    Val::Neutral(*head, v.iter().chain(&*spine).cloned().collect())
                            }
                            term => {
                                *self = spine
                                    .iter()
                                    .fold(term.clone(), |acc, x| acc.app((**x).clone()))
                            }
                        }
                        self.whnf(cxt);
                    }
                }
            }
            Val::Neutral(VHead::Meta(m), spine) => {
                if let Some(val) = cxt.meta_val(*m) {
                    *self = spine
                        .iter()
                        .fold((*val).clone(), |acc, x| acc.app((**x).clone()));
                    self.whnf(cxt);
                }
            }
            _ => (),
        }
    }
    fn unify(&self, other: &Val, scxt: SymCxt, cxt: &Cxt) -> bool {
        self.unify_(other, scxt, cxt, UnfoldState::Maybe)
    }
    fn unify_(&self, other: &Val, mut scxt: SymCxt, cxt: &Cxt, mut mode: UnfoldState) -> bool {
        let (mut a, mut b) = (self.clone(), other.clone());
        loop {
            if mode == UnfoldState::Yes {
                a.whnf(cxt);
                b.whnf(cxt);
            }
            break match (&a, &b) {
                (Val::Error, _) | (_, Val::Error) => true,
                (Val::Type, Val::Type) => true,
                (Val::Neutral(s, sp), Val::Neutral(s2, sp2))
                    if s == s2
                        && sp.len() == sp2.len()
                        && sp
                            .iter()
                            .zip(sp2)
                            .all(|(x, y)| x.unify_(y, scxt, cxt, mode.spine_mode())) =>
                {
                    true
                }
                (Val::Neutral(VHead::Meta(m), spine), b)
                | (b, Val::Neutral(VHead::Meta(m), spine))
                    if !matches!(b, Val::Neutral(VHead::Meta(m2), _) if m2 == m)
                        && cxt.meta_val(*m).is_none() =>
                {
                    cxt.solve_meta(*m, spine, b.clone(), Span(0, 0));
                    true
                }
                (Val::Neutral(_, _), _) | (_, Val::Neutral(_, _)) if mode == UnfoldState::Maybe => {
                    mode = UnfoldState::Yes;
                    continue;
                }
                (Val::Fun(c, i1, n1, aty, _, _), Val::Fun(c2, i2, _, aty2, _, _))
                    if c == c2 && i1 == i2 =>
                {
                    let mut scxt2 = scxt;
                    let s = scxt2.bind(*n1);
                    let arg = Val::Neutral(VHead::Sym(s), default());
                    if !aty.unify_(aty2, scxt, cxt, mode) {
                        false
                    } else {
                        a = a.app(arg.clone());
                        b = b.app(arg);
                        scxt = scxt2;
                        mode = UnfoldState::Maybe;
                        continue;
                    }
                }
                // eta-expand if there's a lambda on only one side
                // TODO this might have problems since we don't make sure the icits match?
                (Val::Fun(Lam, _, n, _, _, _), _) | (_, Val::Fun(Lam, _, n, _, _, _)) => {
                    let mut scxt2 = scxt;
                    let s = scxt2.bind(*n);
                    let arg = Val::Neutral(VHead::Sym(s), default());
                    a = a.app(arg.clone());
                    b = b.app(arg);
                    scxt = scxt2;
                    continue;
                }
                (_, _) => false,
            };
        }
    }
}

// don't call this if checking against an implicit lambda
fn insert_metas(term: Term, mut ty: Val, cxt: &Cxt, span: Span) -> (Term, Val) {
    ty.whnf(cxt);
    match &ty {
        Val::Fun(Pi, Impl, _, aty, _, _) => {
            let m = cxt.new_meta((**aty).clone(), span);
            let term = Term::App(Box::new(term), Box::new(m.quote(&cxt.qenv())));
            let ty = ty.app(m);
            insert_metas(term, ty, cxt, span)
        }
        _ => (term, ty),
    }
}

fn elab_block(block: &[PreStmt], last_: &SPre, ty: Option<Val>, cxt1: &Cxt) -> (Term, Val) {
    let mut cxt = cxt1.clone();
    let mut v = Vec::new();
    for x in block {
        let (n, t, x) = match x {
            PreStmt::Expr(x) => {
                let (x, xty) = x.infer(&cxt, true);
                (cxt.db.name("_"), xty, x)
            }
            PreStmt::Let(pat, body) => {
                let (n, aty) = simple_pat(pat, &cxt);
                let (body, aty) =
                    body.elab(aty.map(|t| t.check(Val::Type, &cxt).eval(&cxt.env())), &cxt);
                (*n, aty, body)
            }
        };
        let t2 = t.quote(&cxt.qenv());
        cxt = cxt.bind(n, t).1;
        v.push((n, t2, x));
    }
    let explicit_ty = ty.is_some();
    let (last, mut lty) = last_.elab(ty, &cxt);
    let term = v.into_iter().rfold(last, |acc, (n, t, x)| {
        Term::App(
            Box::new(Term::Fun(Lam, Expl, n, Box::new(t), Arc::new(acc))),
            Box::new(x),
        )
    });
    // We have to make sure the inferred type of the block return value doesn't depend on locals within the block
    // That means we need to inline metas first so we don't get spurious scope errors
    // Unfortunately, this means we basically can't quickly elaborate smalltt's pairTest - there's no way around inlining all the metas in the final type
    // I'd love to find a way around this at some point but currently it seems pretty inevitable
    // For now, I left `pairTest` in but changed it to return `x1` instead of `x30`. That way we don't have to inline all the metas and we stay fast
    if !explicit_ty {
        lty = lty
            .zonk(&cxt, true)
            .quote_(&cxt1.qenv())
            .unwrap_or_else(|s| {
                cxt.err(
                    Doc::start("type of block return value depends on local `")
                        + s.0.pretty(&cxt.db)
                        + "`: "
                        + lty.pretty(&cxt.db),
                    last_.span(),
                );
                Term::Error
            })
            .eval(&cxt1.env());
    }
    (term, lty)
}

impl SPre {
    // Helper to delegate to infer or check
    fn elab(&self, ty: Option<Val>, cxt: &Cxt) -> (Term, Val) {
        match ty {
            Some(ty) => {
                let s = self.check(ty.clone(), cxt);
                (s, ty)
            }
            None => self.infer(cxt, true),
        }
    }

    fn infer(&self, cxt: &Cxt, should_insert_metas: bool) -> (Term, Val) {
        let (s, sty) = match &***self {
            Pre::Var(name) if cxt.db.name("_") == *name => {
                // hole
                let mty = cxt.new_meta(Val::Type, self.span());
                let m = cxt.new_meta(mty.clone(), self.span()).quote(&cxt.qenv());
                (m, mty)
            }
            Pre::Var(name) => match cxt.lookup(*name) {
                Some((term, ty)) => (term, ty),
                None => {
                    cxt.err("name not found: " + name.pretty(&cxt.db), self.span());
                    (Term::Error, Val::Error)
                }
            },
            Pre::App(fs, x, i) => {
                let (mut f, mut fty) = fs.infer(cxt, *i == Expl);
                fty.whnf(cxt);
                let aty = match &fty {
                    Val::Error => Val::Error,
                    Val::Fun(Pi, i2, _, aty, _, _) if i == i2 => (**aty).clone(),
                    Val::Fun(Pi, _, _, _, _, _) => {
                        cxt.err(
                            "wrong function type: expected "
                                + Doc::start(*i)
                                + " function but got "
                                + fty.pretty_at(cxt),
                            fs.span(),
                        );
                        // prevent .app() from panicking
                        f = Term::Error;
                        fty = Val::Error;
                        Val::Error
                    }
                    _ => {
                        cxt.err("not a function type: " + fty.pretty_at(cxt), fs.span());
                        // prevent .app() from panicking
                        f = Term::Error;
                        fty = Val::Error;
                        Val::Error
                    }
                };
                let x = x.check(aty, cxt);
                let vx = x.eval(cxt.env());
                (Term::App(Box::new(f), Box::new(x)), fty.app(vx))
            }
            Pre::Pi(i, n, aty, body) => {
                let aty = aty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let body = body.check(Val::Type, &cxt.bind(*n, vaty).1);
                (
                    Term::Fun(Pi, *i, *n, Box::new(aty), Arc::new(body)),
                    Val::Type,
                )
            }
            Pre::Sigma(i, Some(n), aty, body) => {
                let aty = aty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let body = body.check(Val::Type, &cxt.bind(*n, vaty).1);
                (
                    Term::Fun(Sigma, *i, *n, Box::new(aty), Arc::new(body)),
                    Val::Type,
                )
            }
            // If no type is given, assume monomorphic lambdas
            Pre::Lam(i, pat, body) => {
                let (n, aty) = simple_pat(pat, cxt);
                let aty = match aty {
                    Some(aty) => aty.check(Val::Type, cxt).eval(&cxt.env()),
                    None => cxt.new_meta(Val::Type, pat.span()),
                };

                let aty2 = aty.quote(cxt.qenv());
                let (_, cxt2) = cxt.bind(*n, aty.clone());
                let (body, rty) = body.infer(&cxt2, true);
                let rty = rty.quote(&cxt2.qenv());
                (
                    Term::Fun(Lam, *i, *n, Box::new(aty2), Arc::new(body)),
                    Val::Fun(
                        Pi,
                        *i,
                        *n,
                        Arc::new(aty),
                        Arc::new(rty),
                        Arc::new(cxt.env().clone()),
                    ),
                )
            }
            // Similarly assume non-dependent pair
            Pre::Sigma(i, None, a, b) => {
                let (a, aty) = a.infer(cxt, true);
                let (b, bty) = b.infer(cxt, true);
                let bty = bty.quote(&cxt.qenv().bind(cxt.db.name("_"), cxt.env()).1.qenv);
                (
                    Term::Pair(Box::new(a), Box::new(b)),
                    Val::Fun(
                        Sigma,
                        *i,
                        cxt.db.name("_"),
                        Arc::new(aty),
                        Arc::new(bty),
                        Arc::new(cxt.env().clone()),
                    ),
                )
            }
            Pre::Binder(_, _) => {
                cxt.err("binder not allowed in this context", self.span());
                (Term::Error, Val::Error)
            }
            Pre::Do(block, last) => elab_block(block, last, None, cxt),
            Pre::Type => (Term::Type, Val::Type),
            Pre::Error => (Term::Error, Val::Error),
        };
        if should_insert_metas {
            insert_metas(s, sty, cxt, self.span())
        } else {
            (s, sty)
        }
    }

    fn check(&self, mut ty: Val, cxt: &Cxt) -> Term {
        ty.whnf(cxt);
        match (&***self, &ty) {
            (Pre::Lam(i, pat, body), Val::Fun(Pi, i2, _, aty2, _, _)) if i == i2 => {
                let (n, aty) = simple_pat(pat, cxt);
                if let Some(aty) = aty {
                    let aty = aty.check(Val::Type, cxt).eval(cxt.env());
                    if !aty.unify(&aty2, cxt.scxt(), cxt) {
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
                let rty = ty.app(Val::Neutral(VHead::Sym(sym), default()));
                let body = body.check(rty, &cxt);
                Term::Fun(Lam, *i, *n, Box::new(aty), Arc::new(body))
            }
            // when checking pair against type, assume sigma
            (Pre::Sigma(i, None, aty, body), Val::Type) => {
                let n = cxt.db.name("_");
                let aty = aty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let body = body.check(Val::Type, &cxt.bind(n, vaty).1);
                Term::Fun(Sigma, *i, n, Box::new(aty), Arc::new(body))
            }
            (Pre::Sigma(i, None, a, b), Val::Fun(Sigma, i2, _, aty, _, _)) if i == i2 => {
                let a = a.check((**aty).clone(), cxt);
                let va = a.eval(&cxt.env());
                let rty = ty.app(va);
                let b = b.check(rty, cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }
            // insert lambda when checking (non-implicit lambda) against implicit function type
            (_, Val::Fun(Pi, Impl, n, aty, _, _)) => {
                let aty2 = aty.quote(cxt.qenv());
                // don't let them access the name in the term (shadowing existing names would be unintuitive)
                let n = cxt.db.inaccessible(*n);
                let (sym, cxt) = cxt.bind(n, (**aty).clone());
                let rty = ty.app(Val::Neutral(VHead::Sym(sym), default()));
                let body = self.check(rty, &cxt);
                Term::Fun(Lam, Impl, n, Box::new(aty2), Arc::new(body))
            }
            // and similar for implicit sigma
            (_, Val::Fun(Sigma, Impl, _, aty, _, _)) => {
                let a = cxt
                    .new_meta((**aty).clone(), self.span())
                    .quote(&cxt.qenv());
                let va = a.eval(&cxt.env());
                let rty = ty.app(va);
                let b = self.check(rty, &cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }
            (Pre::Do(block, last), _) => elab_block(block, last, Some(ty), cxt).0,

            (_, _) => {
                let (s, sty) = self.infer(cxt, !matches!(ty, Val::Fun(Pi, Impl, _, _, _, _)));
                if !ty.unify(&sty, cxt.scxt(), cxt) {
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

fn simple_pat(pat: &S<PrePat>, cxt: &Cxt) -> (S<Interned<Arc<str>>>, Option<S<Box<Pre>>>) {
    match &**pat {
        PrePat::Name(s) => (*s, None),
        PrePat::Binder(s, s1) => (*s, Some(s1.clone())),
        PrePat::Error => (S(cxt.db.name("_"), pat.span()), None),
    }
}

impl Val {
    fn pretty_at(&self, cxt: &Cxt) -> Doc {
        self.quote(cxt.qenv()).pretty(&cxt.db)
    }
}
impl Pretty for Val {
    fn pretty(&self, db: &DB) -> Doc {
        self.quote(&QEnv {
            partial_cxt: true,
            ..default()
        })
        .pretty(&db)
    }
}

// pretty-printing

impl Icit {
    fn pretty_bind(self, x: Doc, parens: bool) -> Doc {
        match self {
            Impl => "{" + x + "}",
            Expl if parens => "(" + x + ")",
            Expl => x,
        }
    }
}

impl Pretty for Term {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            // TODO how do we get types of local variables for e.g. semantic highlights or hover?
            Term::Var(n, _i) => Doc::start(db.get(*n)), // + &*format!("{}", _i.0),
            Term::Def(d) => db.idefs.get(*d).name().pretty(db),
            Term::Meta(m) => m.pretty(db),
            // TODO we probably want to show implicit and explicit application differently, but that requires threading icits through neutral spines...
            Term::App(f, x) => {
                (f.pretty(db).nest(Prec::App) + " " + x.pretty(db).nest(Prec::Atom)).prec(Prec::App)
            }
            Term::Fun(Lam, i, s, _, body) => {
                (i.pretty_bind(s.pretty(db), false) + " => " + body.pretty(db)).prec(Prec::Term)
            }
            Term::Fun(Pi, i, s, aty, body) if *s == db.name("_") => {
                (i.pretty_bind(aty.pretty(db).nest(Prec::App), false) + " -> " + body.pretty(db))
                    .prec(Prec::Pi)
            }
            Term::Fun(Pi, i, s, aty, body) => (i
                .pretty_bind(s.pretty(db) + ": " + aty.pretty(db).nest(Prec::Pi), true)
                + " -> "
                + body.pretty(db))
            .prec(Prec::Pi),
            Term::Fun(Sigma, i, s, aty, body) if *s == db.name("_") => {
                (i.pretty_bind(aty.pretty(db).nest(Prec::Pi), false) + ", " + body.pretty(db))
                    .prec(Prec::Pair)
            }
            Term::Fun(Sigma, i, s, aty, body) => (i
                .pretty_bind(s.pretty(db) + ": " + aty.pretty(db).nest(Prec::Pi), false)
                + ", "
                + body.pretty(db))
            .prec(Prec::Pair),
            Term::Pair(a, b) => a.pretty(db).nest(Prec::Pi) + ", " + b.pretty(db).nest(Prec::Pair),
            Term::Error => Doc::keyword("error"),
            Term::Type => Doc::start("Type"),
        }
    }
}
