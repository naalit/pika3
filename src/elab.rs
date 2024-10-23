use std::collections::HashMap;

use smallvec::SmallVec;
use tap::Pipe;

use crate::common::*;
use crate::parser::{Pre, PrePat, PreStmt, SPre, SPrePat};

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

    let cxt = Cxt::new(def, AbsSpan(file, pre.name.span()), db.clone());
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
    if body.is_none() {
        cxt.err(
            "definition does not have a body: `" + name.pretty(db) + "` of type " + ty.pretty(db),
            pre.name.span(),
        );
    }
    body.as_mut().map(|x| x.zonk(&cxt, false));
    let ty = ty.zonk(&cxt, true);

    Some(DefElabResult {
        def: DefElab {
            name: pre.name,
            ty: Arc::new(ty),
            body: body.map(|x| Arc::new(x.eval(&cxt.env()))),
        },
        errors: cxt.errors.errors.take().into_iter().collect(),
    })
}

// types

#[derive(Clone, Debug)]
pub struct DefElab {
    pub name: SName,
    pub ty: Arc<Val>,
    pub body: Option<Arc<Val>>,
}

#[derive(Debug)]
pub struct Module {
    pub defs: Vec<DefElab>,
}

#[derive(Clone, Debug)]
pub struct DefElabResult {
    pub def: DefElab,
    pub errors: Arc<[Error]>,
}

#[derive(Clone, Debug)]
pub struct ModuleElabResult {
    pub module: Arc<Module>,
    pub errors: Vec<Error>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Idx(u32);
impl Idx {
    fn idx(self, env: &Env) -> Option<usize> {
        // [a, b] at 1 is a (vec[0]), at 0 is b (vec[1])
        if env.len() < self.0 as usize + 1 {
            None
        } else {
            Some(env.len() - self.0 as usize - 1)
        }
    }
    fn at(self, env: &Env) -> Arc<Val> {
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
    App(Box<Term>, TElim),
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

type Spine = Vec<VElim>;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VHead {
    Sym(Sym),
    Def(Def),
    Meta(Meta),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Val {
    Neutral(VHead, Spine),
    Fun(Class, Icit, Name, Arc<Val>, Arc<Term>, Arc<Env>),
    Pair(Arc<Val>, Arc<Val>),
    Error,
    Type,
}
impl Val {
    pub fn sym(sym: Sym) -> Val {
        Val::Neutral(VHead::Sym(sym), default())
    }
}

// eval

impl Val {
    pub fn app(self, other: Val) -> Val {
        VElim::App(Expl, Arc::new(other)).elim(self)
    }
}

impl Term {
    pub fn eval(&self, env: &Env) -> Val {
        with_stack(|| match self {
            Term::Var(_, idx) => Arc::unwrap_or_clone(idx.at(env)),
            Term::Def(d) => Val::Neutral(VHead::Def(*d), default()),
            Term::Meta(m) => Val::Neutral(VHead::Meta(*m), default()),
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

#[derive(Clone)]
struct Errors {
    errors: Ref<Vec<Error>>,
    db: DB,
    span: AbsSpan,
}
impl Errors {
    fn panic(&self) -> ! {
        for i in self.errors.take() {
            i.write_cli(self.span.0, &mut FileCache::new(self.db.clone()));
        }
        panic!()
    }
}

impl Default for Errors {
    fn default() -> Self {
        Self {
            errors: Default::default(),
            db: Default::default(),
            span: AbsSpan(Interned::empty(), Span(0, 0)),
        }
    }
}
impl Errors {
    fn push(&self, error: Error) {
        self.errors.with_mut(|v| v.push(error))
    }
}

#[derive(Clone, Default)]
struct QEnv {
    lvls: im::HashMap<Sym, u32>,
    size: u32,
    scxt: SymCxt,
    partial_cxt: bool,
    errors: Errors,
}
impl QEnv {
    fn cvt(&self, sym: Sym) -> Option<Idx> {
        // i don't *think* this is an off-by-one error...
        if let Some(l) = self.lvls.get(&sym) {
            Some(Idx(self.size as u32 - l - 1))
        } else {
            if self.partial_cxt {
                Some(Idx(555))
            } else {
                None
            }
        }
    }

    fn get(&self, sym: Sym) -> Option<Term> {
        let n = self.name(sym);
        self.cvt(sym).map(|i| Term::Var(n, i)) // (n,) >> Term.Var  # easier and nicer than haskell!
    }

    fn name(&self, sym: Sym) -> Interned<Arc<str>> {
        sym.0
        // (sym.0 != self.errors.db.name("_"))
        //     .then_some(sym.0)
        //     .unwrap_or_else(|| {
        //         self.errors
        //             .db
        //             .name(&format!("{}{}", self.errors.db.get(sym.0), sym.1.get()))
        //     })
    }

    fn bind_raw(&mut self, s: Sym) {
        self.lvls.insert(s, self.size);
        self.size += 1;
    }

    fn bind_(&mut self, s: Name) {
        let sym = self.scxt.bind(s);
        self.lvls.insert(sym, self.size);
        self.size += 1;
    }

    fn bind(&self, s: Name, env: &Env) -> (Sym, SEnv) {
        let mut scxt = self.scxt;
        let sym = scxt.bind(s);
        let mut env = env.clone();
        let mut qenv = self.clone();
        env.push(Arc::new(Val::Neutral(VHead::Sym(sym), default())));
        qenv.scxt = scxt;
        qenv.lvls.insert(sym, self.size);
        qenv.size += 1;
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
            Term::Var(n, idx) if env.qenv.partial_cxt && idx.0 as usize >= env.env.len() => {
                Term::Var(*n, *idx)
            }
            Term::Var(_, idx) => idx.at(&env.env).quote_(&env.qenv)?,
            Term::Def(d) => Term::Def(*d),
            Term::Meta(m) => Term::Meta(*m),
            Term::App(f, x) => Term::App(Box::new(f.subst(env)?), x.subst(env)?),
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
    fn quote_(&self, env: &QEnv) -> Result<Term, Sym> {
        Ok(match self {
            Val::Neutral(s, spine) => spine.iter().fold(
                Ok(match s {
                    VHead::Sym(s) => env.get(*s).ok_or(*s)?,
                    VHead::Def(d) => Term::Def(*d),
                    VHead::Meta(m) => Term::Meta(*m),
                }),
                |acc, x| Ok(Term::App(Box::new(acc?), x.quote_(env)?)),
            )?,
            // Fast path: if the environment is empty, we don't need to subst the term
            // This is mostly useful for inlining metas in terms
            Val::Fun(c, i, s, aty, body, inner_env) if inner_env.is_empty() => {
                Term::Fun(*c, *i, *s, Box::new(aty.quote_(env)?), body.clone())
            }
            Val::Fun(c, i, s, aty, body, inner_env) => {
                let (sym, qenv) = env.bind(*s, inner_env);
                Term::Fun(
                    *c,
                    *i,
                    env.name(sym),
                    Box::new(aty.quote_(env)?),
                    Arc::new(body.subst(&qenv)?),
                )
            }
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

// eliminations

#[derive(Debug, Clone, PartialEq)]
pub enum TElim {
    // (branches, fallback)
    Match(Vec<(PCons, Vec<Name>, Arc<Term>)>, Option<Arc<Term>>),
    App(Icit, Box<Term>),
}
#[derive(Debug, Clone, PartialEq)]
pub enum VElim {
    Match(
        Vec<(PCons, Vec<Name>, Arc<Term>)>,
        Option<Arc<Term>>,
        Arc<Env>,
    ),
    App(Icit, Arc<Val>),
}
impl VElim {
    fn elim(self, v: Val) -> Val {
        match (self, v) {
            (VElim::App(_, x), Val::Fun(_, _, _, _, body, mut env)) => {
                body.eval(&Arc::make_mut(&mut env).tap_mut(|v| v.push(x)))
            }

            (VElim::Match(v, _, mut env), Val::Pair(va, vb))
                if matches!(v.first(), Some((PCons::Pair(_), _, _))) =>
            {
                v[0].2
                    .eval(&Arc::make_mut(&mut env).tap_mut(|v| v.extend([va, vb])))
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
                        let mut env = SEnv {
                            qenv: env.clone(),
                            env: (**inner_env).clone(),
                        };
                        for i in vars {
                            let (_, e) = env.qenv.bind(*i, &env.env);
                            env = e;
                        }
                        Ok((*l, vars.clone(), Arc::new(t.subst(&env)?)))
                    })
                    .collect::<Result<_, _>>()?,
                fallback
                    .as_ref()
                    .map(|x| {
                        Ok(Arc::new(x.subst(&SEnv {
                            qenv: env.clone(),
                            env: (**inner_env).clone(),
                        })?))
                    })
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
                            let (_, e) = env.qenv.bind(*i, &env.env);
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
    fn zonk_(&mut self, cxt: &Cxt, senv: &SEnv, beta_reduce: bool) -> bool {
        match self {
            TElim::Match(v, fallback) => {
                for (_, vars, t) in v {
                    let mut env = senv.clone();
                    for i in vars {
                        let (_, e) = env.qenv.bind(*i, &env.env);
                        env = e;
                    }
                    Arc::make_mut(t).zonk_(cxt, &env, beta_reduce);
                }
                if let Some(fallback) = fallback {
                    Arc::make_mut(fallback).zonk_(cxt, senv, beta_reduce);
                }
            }
            TElim::App(_, x) => {
                x.zonk_(cxt, senv, beta_reduce);
            }
        }
        false
    }
}

// PATTERN MATCHING STUFF

fn ty_pat_bind_needed(pre_ty: &SPre, cxt: &Cxt) -> bool {
    match &***pre_ty {
        Pre::Sigma(_, n1, _, n2, rest) => {
            n1.is_some() || n2.is_some() || ty_pat_bind_needed(rest, cxt)
        }
        _ => false,
    }
}

fn pat_bind_type(
    pre_ty: &SPre,
    val: Val,
    ty: &Val,
    cxt: &Cxt,
    body: impl FnOnce(&Cxt) -> Term,
) -> Term {
    if !ty_pat_bind_needed(pre_ty, cxt) {
        return body(cxt);
    }
    match (&***pre_ty, ty) {
        (Pre::Sigma(i, n1, _, n2, rest), Val::Fun(Sigma(_), i2, _, aty, _, _)) if i == i2 => {
            let n1 = n1.map(|x| *x).unwrap_or(cxt.db.name("_"));
            let (s1, cxt2) = cxt.bind(n1, aty.clone());
            let bty = ty.clone().app(Val::Neutral(VHead::Sym(s1), default()));
            let n2 = n2.map(|x| *x).unwrap_or(cxt2.db.name("_"));
            let (s2, cxt2) = cxt2.bind(n2, bty.clone());
            let body = pat_bind_type(
                rest,
                Val::Neutral(VHead::Sym(s2), default()),
                &bty,
                &cxt2,
                body,
            );
            let val = val.quote(cxt.qenv());
            Term::App(
                Box::new(val),
                TElim::Match(vec![(PCons::Pair(*i), vec![n1, n2], Arc::new(body))], None),
            )
        }
        _ => body(cxt),
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PCons {
    Pair(Icit),
    // Cons(Name),
    // ... literals ...
}
#[derive(Clone, PartialEq)]
struct PConsTy {
    label: PCons,
    var_tys: Vec<(Sym, Arc<Val>)>,
}

fn split_ty(
    var: Sym,
    ty: &Val,
    rows: &[PRow],
    mut names: impl Iterator<Item = Option<Name>>,
    cxt: &mut Cxt,
) -> Option<Vec<PConsTy>> {
    let mut ty = ty.clone();
    ty.whnf(cxt);
    match &ty {
        Val::Fun(Sigma(n2), i, n1, aty, _, _) => {
            // TODO better system for names accessible in types in patterns
            // let n1 = names.next().flatten().unwrap_or(cxt.db.inaccessible(*n1));
            // let n2 = names.next().flatten().unwrap_or(cxt.db.inaccessible(*n2));
            let s1 = cxt.bind_(*n1, aty.clone());
            let bty = ty.clone().app(Val::Neutral(VHead::Sym(s1), default()));
            let s2 = cxt.bind_(*n2, bty.clone());
            // now, we know this is reversible, so we can tell the compiler that
            if cxt.can_solve(var) {
                cxt.solve_local(
                    var,
                    Arc::new(Val::Pair(Arc::new(Val::sym(s1)), Arc::new(Val::sym(s2)))),
                );
            }
            Some(vec![PConsTy {
                label: PCons::Pair(*i),
                var_tys: vec![(s1, aty.clone()), (s2, Arc::new(bty))],
            }])
        }

        // For GADTs, we do the unification here
        // We'll need to add fields for solved locals etc to the PCons though
        Val::Neutral(VHead::Meta(m), spine) => match rows
            .iter()
            .flat_map(|r| &r.cols)
            .find(|(s, _, _)| *s == var)
        {
            Some((
                _,
                _,
                IPat::CPat(
                    _,
                    CPat {
                        label: PCons::Pair(_),
                        vars,
                        span,
                    },
                ),
            )) => {
                // solve metas with more metas
                let n = vars[0].clone().ensure_named(&cxt.db).name().unwrap();
                let n2 = vars[1].clone().ensure_named(&cxt.db).name().unwrap();
                let ta =
                    Arc::new(cxt.new_meta_with_spine(Val::Type, Span(0, 0), spine.iter().cloned()));
                let (s, cxt2) = cxt.bind(n, ta.clone());
                let tb = cxt2
                    .new_meta_with_spine(
                        Val::Type,
                        Span(0, 0),
                        spine
                            .iter()
                            .cloned()
                            .chain(std::iter::once(VElim::App(Expl, Arc::new(Val::sym(s))))),
                    )
                    .quote(cxt2.qenv());
                let t = Val::Fun(
                    Sigma(n2),
                    Expl,
                    n,
                    ta,
                    Arc::new(tb),
                    Arc::new(cxt.env().clone()),
                );
                if cxt.solve_meta(*m, spine, t, Some(*span)) {
                    split_ty(var, &ty, rows, names, cxt)
                } else {
                    None
                }
            }
            _ => None,
        },
        _ => None,
    }
}

#[derive(Clone)]
enum IPat {
    Var(Name, Option<Arc<SPre>>),
    CPat(Option<Name>, CPat),
}
impl IPat {
    fn needs_split(&self, db: &DB) -> bool {
        match self {
            IPat::CPat(_, cpat) => {
                for i in &cpat.vars {
                    if i.needs_split(db) || i.name().map_or(false, |n| n != db.name("_")) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }
}
#[derive(Clone)]
struct CPat {
    span: Span,
    label: PCons,
    vars: Vec<IPat>,
}
impl IPat {
    fn ensure_named(self, db: &DB) -> Self {
        match self {
            IPat::CPat(None, cpat) => IPat::CPat(Some(db.name("_")), cpat),
            x => x,
        }
    }
    fn name(&self) -> Option<Name> {
        match self {
            IPat::CPat(n, _) => *n,
            IPat::Var(n, _) => Some(*n),
        }
    }
}
impl SPrePat {
    fn ipat(&self, db: &DB) -> IPat {
        match &***self {
            PrePat::Name(s) => IPat::Var(**s, None),
            PrePat::Binder(s, s1) => IPat::Var(**s, Some(Arc::new(s1.clone()))),
            PrePat::Pair(icit, s, s1) => IPat::CPat(
                None,
                CPat {
                    span: self.span(),
                    label: PCons::Pair(*icit),
                    // This is a sigma type, we need to make sure we have the first value accessible since it might be relevant for the type of the second
                    // I'm also making the second value accessible so that our local-solving-based reversible pattern matching thing works
                    vars: vec![s.ipat(db).ensure_named(db), s1.ipat(db).ensure_named(db)],
                },
            ),
            PrePat::Error => IPat::Var(db.name("_"), None),
        }
    }
}

#[derive(Clone)]
struct PRow {
    cols: Vec<(Sym, Arc<Val>, IPat)>,
    assignments: Vec<(Name, Sym, Arc<Val>)>,
    body: u32,
}
impl PRow {
    fn remove_column(
        self: &PRow,
        var: Sym,
        label: Option<PCons>,
        vars: &[(Sym, Arc<Val>)],
        cxt: &Cxt,
    ) -> Option<Self> {
        if let Some((i, (_, _, _))) = self
            .cols
            .iter()
            .enumerate()
            .find(|(_, (s, _, _))| *s == var)
        {
            // remove the column and apply its patterns elsewhere
            let mut s = self.clone();
            let (_, t, pat) = s.cols.remove(i);
            match pat {
                IPat::Var(n, None) => {
                    s.assignments.push((n, var, t.clone()));

                    Some(s)
                }
                IPat::Var(n, Some(paty)) => {
                    let aty = paty.check(Val::Type, cxt).eval(cxt.env());
                    if !aty.unify(&t, cxt.scxt(), cxt) {
                        cxt.err(
                            Doc::start("mismatched types: pattern has type ")
                                + aty.pretty(&cxt.db)
                                + " but needs to match value of type "
                                + t.pretty(&cxt.db),
                            paty.span(),
                        );
                    }
                    s.assignments.push((n, var, t.clone()));

                    Some(s)
                }
                IPat::CPat(n, pat) => {
                    if let Some(n) = n {
                        s.assignments.push((n, var, t.clone()));
                    }
                    if label == Some(pat.label) {
                        let mut j = i;
                        assert_eq!(pat.vars.len(), vars.len());
                        for (p, (v, t)) in pat.vars.into_iter().zip(vars) {
                            // these need to be in the right order for GADT/sigma reasons
                            s.cols.insert(j, (*v, t.clone(), p));
                            j += 1;
                        }
                        Some(s)
                    } else {
                        None
                    }
                }
            }
        } else {
            // this pattern doesn't care about this variable
            Some(self.clone())
        }
    }
}

enum PTree {
    Body(u32, Vec<Sym>, Cxt),
    Match(
        Term,
        Vec<(PCons, Vec<(Sym, Arc<Val>)>, PTree)>,
        Option<Box<PTree>>,
    ),
    Error,
}
impl PTree {
    // bodies should be closures
    // the term this returns is in the context that `compile` was called with
    fn apply(&self, bodies: &[Val]) -> Term {
        match self {
            PTree::Body(i, args, cxt) => {
                args.iter()
                    .fold(bodies[*i as usize].quote(cxt.qenv()), |acc, &s| {
                        Term::App(
                            Box::new(acc),
                            TElim::App(Expl, Box::new(cxt.qenv().get(s).unwrap())),
                        )
                    })
            }
            // Issue: we don't have a cxt here, so we can't quote
            // which means we can't quote the types in here
            // not sure whether having these types is actually necessary though?
            // that's a backend question ig
            // well we'll assume for now they're not actually needed
            // otherwise this should work fine
            PTree::Match(term, vec, ptree) => Term::App(
                Box::new(term.clone()),
                TElim::Match(
                    vec.iter()
                        .map(|(l, v, t)| {
                            (
                                *l,
                                v.iter().map(|(s, _)| s.0).collect(),
                                Arc::new(t.apply(bodies)),
                            )
                        })
                        .collect(),
                    ptree.as_ref().map(|x| Arc::new(x.apply(bodies))),
                ),
            ),
            PTree::Error => Term::Error,
        }
    }
}

struct PBody {
    reached: bool,
    solved_locals: Vec<(Sym, Arc<Val>)>,
    vars: Vec<(Name, Sym, Arc<Val>)>,
}
struct PCxt {
    bodies: Vec<PBody>,
    span: Span,
    var: Sym,
    has_error: bool,
}
fn compile_rows(rows: &[PRow], pcxt: &mut PCxt, cxt: &Cxt) -> PTree {
    if rows.is_empty() {
        if !pcxt.has_error {
            pcxt.has_error = true;
            // TODO reconstruct missing cases
            cxt.err("non-exhaustive pattern match", pcxt.span);
        }
        PTree::Error
    } else if rows.first().unwrap().cols.is_empty() {
        let row = rows.first().unwrap();
        if pcxt.bodies[row.body as usize].reached {
            // check for matching bindings
            if pcxt.bodies[row.body as usize].vars.len() != row.assignments.len()
                || pcxt.bodies[row.body as usize]
                    .vars
                    .iter()
                    .zip(&row.assignments)
                    .all(|((n1, _, t1), (n2, _, t2))| *n1 == *n2 && t1.unify(t2, cxt.scxt(), cxt))
            {
                panic!("mismatched bindings for body {}", row.body)
            }
        } else {
            pcxt.bodies[row.body as usize] = PBody {
                reached: true,
                solved_locals: cxt.solved_locals(),
                vars: row
                    .assignments
                    .iter()
                    .map(|(n, s, t)| {
                        (*n, *s, {
                            // Needed to account for locals solved during pattern compilation
                            // TODO but those locals can be in the spine ??? do we even need this?
                            let mut t2 = (**t).clone();
                            t2.whnf(cxt);
                            Arc::new(t2)
                        })
                    })
                    .collect(),
            };
        }
        PTree::Body(
            row.body,
            row.assignments
                .iter()
                .filter(|(_, s, _)| *s != pcxt.var)
                .map(|(_, s, _)| *s)
                .collect(),
            cxt.clone(),
        )
    } else {
        let (var, ty, _) = rows.first().unwrap().cols.first().unwrap();
        let tvar = Val::Neutral(VHead::Sym(*var), default()).quote(&cxt.qenv());
        let mut cxt = cxt.clone();
        let nempty = cxt.db.name("_");
        let names = rows
            .iter()
            .flat_map(|r| &r.cols)
            .filter(|(s, _, _)| s == var)
            .filter_map(|(_, _, p)| match p {
                IPat::CPat(_, cpat) => Some(cpat),
                _ => None,
            })
            .next()
            .iter()
            .flat_map(|x| &x.vars)
            .map(|n| {
                match n {
                    IPat::Var(n, _) => Some(*n),
                    IPat::CPat(n, _) => *n,
                }
                .filter(|n| *n != nempty)
            })
            .collect::<Vec<_>>();

        if rows
            .iter()
            .flat_map(|r| &r.cols)
            .any(|(s, _, p)| s == var && p.needs_split(&cxt.db))
            || matches!(&**ty, Val::Fun(Sigma(_), Impl, _, _, _, _))
        {
            if let Some(ctors) = split_ty(*var, ty, rows, names.into_iter(), &mut cxt) {
                if ctors.len() == 1
                    && ctors[0].label == PCons::Pair(Impl)
                    && !rows.iter().any(|row| {
                        row.cols.iter().any(|(s, _, p)| {
                            s == var
                                && matches!(p, IPat::CPat(_, p) if p.label == PCons::Pair(Impl))
                        })
                    })
                {
                    // Auto-unwrap implicit pairs if we don't match on them explicitly
                    // We do need to add the implicit argument to the assignments for each row
                    let mut rows = rows.to_vec();
                    let (isym, ity) = ctors[0].var_tys[0].clone();
                    let iname = cxt.db.inaccessible(isym.0);
                    let (vsym, vty) = ctors[0].var_tys[1].clone();
                    let vname = cxt.db.inaccessible(vsym.0);
                    // Because we're not calling remove_column(), they can't bind the sym we split on either, so we'll need to do that
                    let rname = cxt.db.inaccessible(var.0);
                    for row in &mut rows {
                        row.assignments.push((rname, *var, ty.clone()));
                        row.assignments.push((iname, isym, ity.clone()));
                        row.assignments.push((vname, vsym, vty.clone()));
                        row.cols.iter_mut().for_each(|(s, t, _)| {
                            if s == var {
                                *s = vsym;
                                *t = vty.clone();
                            }
                        });
                    }
                    let t = compile_rows(&rows, pcxt, &cxt);
                    return PTree::Match(
                        tvar,
                        vec![(ctors[0].label, ctors[0].var_tys.clone(), t)],
                        None,
                    );
                }

                let mut v = Vec::new();
                for row in rows {
                    if let Some((_, _, IPat::CPat(_, cpat))) =
                        row.cols.iter().find(|(s, _, _)| s == var)
                    {
                        if !ctors.iter().any(|x| x.label == cpat.label) {
                            cxt.err("invalid pattern for type " + ty.pretty(&cxt.db), cpat.span);
                            pcxt.has_error = true;
                        }
                    }
                }
                for ctor in ctors {
                    let mut vrows = Vec::new();
                    for row in rows {
                        if let Some(row) =
                            row.remove_column(*var, Some(ctor.label), &ctor.var_tys, &cxt)
                        {
                            vrows.push(row);
                        }
                    }
                    let t = compile_rows(&vrows, pcxt, &cxt);
                    v.push((ctor.label, ctor.var_tys, t));
                }
                return PTree::Match(tvar, v, None);
            }
        }

        for row in rows {
            if let Some((_, _, IPat::CPat(_, cpat))) = row.cols.iter().find(|(s, _, _)| s == var) {
                cxt.err("invalid pattern for type " + ty.pretty(&cxt.db), cpat.span);
                pcxt.has_error = true;
            }
        }
        let mut vrows = Vec::new();
        for row in rows {
            if let Some(row) = row.remove_column(*var, None, &[], &cxt) {
                vrows.push(row);
            }
        }
        compile_rows(&vrows, pcxt, &cxt)
    }
}

struct PMatch {
    tree: PTree,
    body_syms: Vec<Sym>,
    pcxt: PCxt,
    cxt: Cxt,
    ty: Val,
    name: Name,
}
impl PMatch {
    fn bind(&self, body: u32, cxt: &Cxt) -> Cxt {
        let mut cxt = cxt.clone();
        let nvar = Term::Var(self.pcxt.var.0, Idx(0)).eval(cxt.env());
        let nsym = match &nvar {
            Val::Neutral(VHead::Sym(s), _) => *s,
            v => {
                eprintln!("internal warning: nvar is {}", v.pretty(&cxt.db));
                self.pcxt.var
            }
        };
        for (name, sym, ty) in &self.pcxt.bodies[body as usize].vars {
            if *sym == self.pcxt.var {
                cxt.bind_val(*name, nvar.clone(), ty.clone());
            } else {
                cxt.bind_raw(*name, *sym, ty.clone());
            }
        }
        for (sym, val) in &self.pcxt.bodies[body as usize].solved_locals {
            let sym = if *sym == self.pcxt.var { nsym } else { *sym };
            // Make sure the solutions of any solved locals are actually in scope
            if cxt.can_solve(sym) && val.quote_(cxt.qenv()).is_ok() {
                cxt.solve_local(sym, val.clone());
            }
        }
        cxt
    }

    fn compile(&self, bodies: &[Term]) -> Term {
        assert_eq!(bodies.len(), self.pcxt.bodies.len());
        if let PTree::Body(0, v, _) = &self.tree {
            assert_eq!(v.len(), 0);
            return bodies[0].clone();
        }
        let mut term = self.tree.apply(
            &self
                .body_syms
                .iter()
                .map(|&s| Val::Neutral(VHead::Sym(s), default()))
                .collect::<Vec<_>>(),
        );
        for (body, PBody { vars, .. }) in bodies.iter().zip(&self.pcxt.bodies).rev() {
            let mut env = self.cxt.qenv().clone();
            let mut envs: Vec<_> = vars
                .iter()
                .map(|(_, s, _)| {
                    let env2 = env.clone();
                    env.bind_raw(*s);
                    env2
                })
                .collect();
            let body = vars.iter().rfold(body.clone(), |acc, (n, _, ty)| {
                Term::Fun(
                    Lam,
                    Expl,
                    *n,
                    Box::new(ty.quote(&envs.pop().unwrap())),
                    Arc::new(acc),
                )
            });
            term = Term::App(
                Box::new(Term::Fun(
                    Lam,
                    Expl,
                    self.cxt.db.name("_"),
                    // TODO do we care about these types?
                    Box::new(Term::Error),
                    Arc::new(term),
                )),
                TElim::App(Expl, Box::new(body.clone())),
            );
        }
        term
    }

    fn new(ty: Option<Val>, branches: &[SPrePat], ocxt: &Cxt) -> PMatch {
        let (var, cxt_v) = ocxt.bind(ocxt.db.name("_"), Val::Error);
        let mut cxt = cxt_v.clone();

        let mut pcxt = PCxt {
            bodies: branches
                .iter()
                .map(|_| PBody {
                    reached: false,
                    solved_locals: default(),
                    vars: default(),
                })
                .collect(),
            var,
            span: branches[0].span(),
            has_error: false,
        };

        // We attach the bodies as `let`, i.e. lambdas
        // So we need a local for each body, to make sure the contexts match up
        let body_syms = branches
            .iter()
            .map(|_| cxt.bind_(cxt.db.name("_"), Val::Error))
            .collect();

        let mut ty = ty;
        let mut name = None;

        let rows: Vec<_> = branches
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let mut ipat = p.ipat(&cxt.db);
                // TODO this can be merged with the code in `remove_column()`
                match &mut ipat {
                    IPat::Var(n, None) => {
                        if name.is_none() {
                            name = Some(*n);
                        }
                        if ty.is_none() {
                            ty = Some(ocxt.new_meta(Val::Type, Span(0, 0)));
                        }
                    }
                    IPat::Var(n, Some(paty)) => {
                        if name.is_none() {
                            name = Some(*n);
                        }
                        if ty.is_none() {
                            let aty = paty.check(Val::Type, &cxt).eval(cxt.env());
                            ty = Some(aty.clone());
                        }
                    }
                    IPat::CPat(n, _) => {
                        if name.is_none() {
                            name = *n;
                        }
                        if ty.is_none() {
                            ty = Some(ocxt.new_meta(Val::Type, Span(0, 0)));
                        }
                    }
                };
                PRow {
                    cols: vec![(var, Arc::new(ty.clone().unwrap()), ipat)],
                    assignments: default(),
                    body: i as u32,
                }
            })
            .collect();

        let tree = compile_rows(&rows, &mut pcxt, &cxt);

        let name = name.unwrap_or_else(|| cxt.db.name("_"));
        PMatch {
            tree,
            pcxt,
            body_syms,
            cxt: cxt_v,
            ty: ty.unwrap(),
            name,
        }
    }
}

// elaboration

enum MetaEntry {
    // The first field is the type; we'll need that eventually for typeclass resolution, but it doesn't matter right now
    // TODO error on unsolved metas (that's why the span is here)
    Unsolved(Arc<Val>, Span),
    Solved(Arc<Val>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Meta(Def, u32);
impl Pretty for Meta {
    fn pretty(&self, _db: &DB) -> Doc {
        "?" + Doc::start(self.0.num()) + "." + Doc::start(self.1)
    }
}

#[derive(Clone)]
struct Cxt {
    db: DB,
    def: Def,
    bindings: im::HashMap<Name, (Val, Arc<Val>)>,
    metas: Ref<HashMap<Meta, MetaEntry>>,
    zonked_metas: Ref<HashMap<(Meta, bool), Val>>,
    env: SEnv,
    errors: Errors,
}
impl Cxt {
    fn new(context: Def, span: AbsSpan, db: DB) -> Cxt {
        let env = SEnv {
            qenv: QEnv {
                errors: Errors {
                    db: db.clone(),
                    span: span,
                    ..default()
                },
                ..default()
            },
            ..default()
        };
        Cxt {
            def: context,
            db,
            bindings: default(),
            errors: env.qenv.errors.clone(),
            env,
            metas: default(),
            zonked_metas: default(),
        }
    }
    fn err(&self, err: impl Into<Doc>, span: impl Into<Option<Span>>) {
        match span.into() {
            Some(span) => self.errors.push(Error::simple(err, span)),
            None => self.errors.push(
                Error::simple(err, self.errors.span.span())
                    .with_label("while elaborating this definition"),
            ),
        }
    }
    fn size(&self) -> u32 {
        self.env.env.len() as u32
    }
    fn lookup(&self, n: Name) -> Option<(Term, Arc<Val>)> {
        // first try locals
        self.bindings
            .get(&n)
            .map(|(val, ty)| {
                (
                    val.quote(self.qenv()).pipe(|x| match x {
                        Term::Var(_, i) => Term::Var(n, i),
                        x => x,
                    }),
                    ty.clone(),
                )
            })
            .or_else(|| {
                self.db
                    .lookup_def_name(self.def, n)
                    .map(|(d, t)| (Term::Def(d), t.clone()))
            })
    }
    fn solved_locals(&self) -> Vec<(Sym, Arc<Val>)> {
        self.env
            .qenv
            .lvls
            .keys()
            .filter_map(|x| Some((*x, self.local_val(*x)?)))
            .collect()
    }
    fn can_solve(&self, sym: Sym) -> bool {
        if let Some(idx) = self.env.qenv.cvt(sym) {
            idx.idx(&self.env.env)
                .iter()
                .any(|&idx| *self.env.env[idx] == Val::Neutral(VHead::Sym(sym), default()))
        } else {
            false
        }
    }
    fn local_val(&self, sym: Sym) -> Option<Arc<Val>> {
        if let Some(idx) = self.env.qenv.cvt(sym) {
            let idx = idx.idx(&self.env.env)?;
            let val = self.env.env[idx].clone();
            (*val != Val::Neutral(VHead::Sym(sym), default())).then(|| val)
        } else {
            None
        }
    }
    fn solve_local(&mut self, sym: Sym, val: Arc<Val>) {
        if let Some(idx) = self.env.qenv.cvt(sym) {
            if let Some(idx) = idx.idx(&self.env.env) {
                self.env.env[idx] = val;
            } else {
                panic!("call can_solve first")
            }
        } else {
            panic!("call can_solve first")
        }
    }
    fn bind_val(&mut self, n: Name, v: Val, ty: impl Into<Arc<Val>>) {
        self.bindings.insert(n, (v, ty.into()));
    }
    fn bind_raw(&mut self, name: Name, sym: Sym, ty: impl Into<Arc<Val>>) -> Sym {
        self.env.qenv.bind_raw(sym);
        self.bindings
            .insert(name, (Val::Neutral(VHead::Sym(sym), default()), ty.into()));
        self.env
            .env
            .push(Arc::new(Val::Neutral(VHead::Sym(sym), default())));
        sym
    }
    fn bind_(&mut self, n: Name, ty: impl Into<Arc<Val>>) -> Sym {
        let (sym, env) = self.env.qenv.bind(n, &self.env.env);
        self.bindings
            .insert(n, (Val::Neutral(VHead::Sym(sym), default()), ty.into()));
        self.env = env;
        sym
    }
    fn bind(&self, n: Name, ty: impl Into<Arc<Val>>) -> (Sym, Cxt) {
        let mut s = self.clone();
        let sym = s.bind_(n, ty);
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
        // When making a meta with type (a, b), we're more likely to be able to solve it if we can solve each component separately
        // So we make two metas (possibly recursively), and return (?0, ?1)
        // In general this can be applied to any single-constructor datatype, but we probably won't actually implement that
        // But since we usually tuple function arguments, this makes type inference work much better in practice
        if let Val::Fun(Sigma(_), _, _, aty, _, _) = &ty {
            let m1 = self.new_meta((**aty).clone(), span);
            let bty = ty.app(m1.clone());
            let m2 = self.new_meta(bty, span);
            let val = Val::Pair(Arc::new(m1), Arc::new(m2));
            return val;
        }

        // This can skip numbers in the presence of solved external metas but that shouldn't matter
        let m = Meta(self.def, self.metas.with(|x| x.len()) as u32);
        self.metas
            .with_mut(|x| x.insert(m, MetaEntry::Unsolved(Arc::new(ty), span)));
        let v = Val::Neutral(
            VHead::Meta(m),
            self.env
                .env
                .iter()
                .map(|x| VElim::App(Expl, x.clone()))
                .collect(),
        );
        v
    }
    fn new_meta_with_spine(
        &self,
        ty: Val,
        span: Span,
        spine: impl IntoIterator<Item = VElim>,
    ) -> Val {
        // This can skip numbers in the presence of solved external metas but that shouldn't matter
        let m = Meta(self.def, self.metas.with(|x| x.len()) as u32);
        self.metas
            .with_mut(|x| x.insert(m, MetaEntry::Unsolved(Arc::new(ty), span)));
        let v = Val::Neutral(VHead::Meta(m), spine.into_iter().collect());
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
    fn solve_meta(&self, meta: Meta, spine: &Spine, solution: Val, span: Option<Span>) -> bool {
        if spine.iter().any(|x| !matches!(x, VElim::App(_, _))) {
            self.err(
                "cannot solve meta with non-app in spine: "
                    + Val::Neutral(VHead::Meta(meta), spine.clone()).pretty(&self.db),
                span,
            );
        }
        let qenv = QEnv {
            lvls: spine
                .iter()
                .filter_map(|v| match v {
                    VElim::App(_, v) => Some(v),
                    _ => None,
                })
                .enumerate()
                .filter_map(|(l, v)| match &**v {
                    Val::Neutral(VHead::Sym(s), sp) if sp.is_empty() => Some((*s, l as u32)),
                    _ => None,
                })
                .collect(),
            size: spine.len() as u32,
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
                true
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
                false
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

impl VElim {
    fn unify_(&self, other: &VElim, scxt: SymCxt, cxt: &Cxt, mode: UnfoldState) -> bool {
        match (self, other) {
            (VElim::App(_, x), VElim::App(_, y)) => x.unify_(y, scxt, cxt, mode),
            (
                VElim::Match(branches1, fallback1, env1),
                VElim::Match(branches2, fallback2, env2),
            ) if branches1.len() == branches2.len()
                && fallback1.is_some() == fallback2.is_some() =>
            {
                for ((l1, v1, t1), (l2, v2, t2)) in branches1.iter().zip(branches2) {
                    if l1 != l2 {
                        return false;
                    }
                    assert_eq!(v1.len(), v2.len());
                    let mut env1 = (**env1).clone();
                    let mut env2 = (**env2).clone();
                    let mut scxt = scxt;
                    for &n in v1 {
                        let s = scxt.bind(n);
                        env1.push(Arc::new(Val::Neutral(VHead::Sym(s), default())));
                        env2.push(Arc::new(Val::Neutral(VHead::Sym(s), default())));
                    }
                    if !t1.eval(&env1).unify_(&t2.eval(&env2), scxt, cxt, mode) {
                        return false;
                    }
                }
                if let Some(fallback1) = fallback1 {
                    let fallback2 = fallback2.as_ref().unwrap();
                    if !fallback1.eval(env1).unify(&fallback2.eval(env2), scxt, cxt) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}
impl Val {
    fn cow_whnf<'a>(s: Cow<'a, Val>, cxt: &Cxt) -> Cow<'a, Val> {
        match s.maybe_whnf(cxt) {
            Some(s) => Owned(s),
            None => s,
        }
    }
    fn as_whnf(&self, cxt: &Cxt) -> Cow<Val> {
        match self.maybe_whnf(cxt) {
            Some(s) => Owned(s),
            None => Borrowed(self),
        }
    }
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
                    VHead::Def(d) => {
                        if let Some(elab) = cxt.db.elab.def_value(*d, &cxt.db) {
                            elab.def.body.clone()
                        } else {
                            None
                        }
                    }
                    VHead::Sym(s) => cxt.local_val(*s),
                    VHead::Meta(m) => cxt.meta_val(*m),
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
                            if let Term::Var(_, i) = &**t {
                                if (i.0 as usize) < v.len() {
                                    return None;
                                }
                            }
                            let mut env = (*env).clone();
                            let s = Val::Neutral(*h, spine);
                            for (i, n) in v.iter().enumerate() {
                                env.push(Arc::new(
                                    VElim::Match(
                                        vec![(
                                            *l,
                                            v.clone(),
                                            Arc::new(Term::Var(
                                                *n,
                                                Idx(v.len() as u32 - 1 - i as u32),
                                            )),
                                        )],
                                        None,
                                        Arc::new(env.clone()),
                                    )
                                    .elim(s.clone()),
                                ));
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
    fn whnf(&mut self, cxt: &Cxt) {
        if let Some(s) = self.maybe_whnf(cxt) {
            *self = s;
        }
        return;
    }
    fn unify(&self, other: &Val, scxt: SymCxt, cxt: &Cxt) -> bool {
        self.unify_(other, scxt, cxt, UnfoldState::Maybe)
    }
    fn unify_(&self, other: &Val, mut scxt: SymCxt, cxt: &Cxt, mut mode: UnfoldState) -> bool {
        let (mut a, mut b) = (Borrowed(self), Borrowed(other));
        loop {
            if mode == UnfoldState::Yes {
                a = Val::cow_whnf(a, cxt);
                b = Val::cow_whnf(b, cxt);
            }
            break match (&*a, &*b) {
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
                        && spine.iter().all(|x| matches!(x, VElim::App(_, _)))
                        && cxt.meta_val(*m).is_none() =>
                {
                    cxt.solve_meta(*m, spine, b.clone(), None);
                    true
                }
                (Val::Neutral(_, _), _) | (_, Val::Neutral(_, _)) if mode == UnfoldState::Maybe => {
                    mode = UnfoldState::Yes;
                    continue;
                }
                (Val::Fun(c, i1, n1, aty, _, _), Val::Fun(c2, i2, _, aty2, _, _))
                    if (c == c2 || matches!((c, c2), (Sigma(_), Sigma(_)))) && i1 == i2 =>
                {
                    let mut scxt2 = scxt;
                    let s = scxt2.bind(*n1);
                    let arg = Val::Neutral(VHead::Sym(s), default());
                    if !aty.unify_(aty2, scxt, cxt, mode) {
                        false
                    } else {
                        a = Owned(a.into_owned().app(arg.clone()));
                        b = Owned(b.into_owned().app(arg));
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
                    a = Owned(a.into_owned().app(arg.clone()));
                    b = Owned(b.into_owned().app(arg));
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
            let term = Term::App(
                Box::new(term),
                TElim::App(Impl, Box::new(m.quote(&cxt.qenv()))),
            );
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
        let (n, t, p, x) = match x {
            PreStmt::Expr(x) => {
                let (x, xty) = x.infer(&cxt, true);
                (cxt.db.name("_"), xty, None, x)
            }
            PreStmt::Let(pat, body) if matches!(&***pat, PrePat::Binder(_, _)) => {
                let pat = PMatch::new(None, &[pat.clone()], &cxt);
                let aty = pat.ty.clone();
                let body = body.check(aty.clone(), &cxt);
                (pat.name, aty, Some(pat), body)
            }
            PreStmt::Let(pat, body) => {
                let (body, aty) = body.infer(&cxt, true);
                let pat = PMatch::new(Some(aty.clone()), &[pat.clone()], &cxt);
                (pat.name, aty, Some(pat), body)
            }
        };
        let t2 = t.quote(&cxt.qenv());
        cxt = cxt.bind(n, t).1;
        if let Some(p) = &p {
            cxt = p.bind(0, &cxt);
        }
        v.push((n, t2, p, x));
    }
    let explicit_ty = ty.is_some();
    let (last, mut lty) = last_.elab(ty, &cxt);
    let term = v.into_iter().rfold(last, |acc, (n, t, p, x)| {
        let acc = match p {
            Some(p) => p.compile(&[acc]),
            None => acc,
        };
        Term::App(
            Box::new(Term::Fun(Lam, Expl, n, Box::new(t), Arc::new(acc))),
            TElim::App(Expl, Box::new(x)),
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
        with_stack(|| self.infer_(cxt, should_insert_metas))
    }
    fn infer_(&self, cxt: &Cxt, should_insert_metas: bool) -> (Term, Val) {
        let (s, sty) = match &***self {
            Pre::Var(name) if cxt.db.name("_") == *name => {
                // hole
                let mty = cxt.new_meta(Val::Type, self.span());
                let m = cxt.new_meta(mty.clone(), self.span()).quote(&cxt.qenv());
                (m, mty)
            }
            Pre::Var(name) => match cxt.lookup(*name) {
                Some((term, ty)) => (term, Arc::unwrap_or_clone(ty)),
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
                (
                    Term::App(Box::new(f), TElim::App(*i, Box::new(x))),
                    fty.app(vx),
                )
            }
            Pre::Pi(i, n, paty, body) => {
                let aty = paty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let (s, cxt) = cxt.bind(*n, vaty.clone());
                let body = pat_bind_type(
                    &paty,
                    Val::Neutral(VHead::Sym(s), default()),
                    &vaty,
                    &cxt,
                    |cxt| body.check(Val::Type, cxt),
                );
                (
                    Term::Fun(Pi, *i, *n, Box::new(aty), Arc::new(body)),
                    Val::Type,
                )
            }
            Pre::Sigma(_, Some(_), _, _, _) | Pre::Sigma(_, _, _, Some(_), _) => {
                (self.check(Val::Type, cxt), Val::Type)
            }
            // If no type is given, assume monomorphic lambdas
            Pre::Lam(i, pat, body) => {
                let pat = PMatch::new(None, &[pat.clone()], cxt);
                let aty = pat.ty.clone();
                let aty2 = aty.quote(cxt.qenv());

                let (_, cxt2) = cxt.bind(pat.name, aty.clone());
                let cxt3 = pat.bind(0, &cxt2);
                let (body, rty) = body.infer(&cxt3, true);
                let rty = rty.quote(&cxt3.qenv());
                let body = pat.compile(&[body]);
                let rty = pat.compile(&[rty]);
                (
                    Term::Fun(Lam, *i, pat.name, Box::new(aty2), Arc::new(body)),
                    Val::Fun(
                        Pi,
                        *i,
                        pat.name,
                        Arc::new(aty),
                        Arc::new(rty),
                        Arc::new(cxt.env().clone()),
                    ),
                )
            }
            // Similarly assume non-dependent pair
            Pre::Sigma(i, None, a, None, b) => {
                let (a, aty) = a.infer(cxt, true);
                let (b, bty) = b.infer(cxt, true);
                let bty = bty.quote(&cxt.qenv().bind(cxt.db.name("_"), cxt.env()).1.qenv);
                (
                    Term::Pair(Box::new(a), Box::new(b)),
                    Val::Fun(
                        Sigma(cxt.db.name("_")),
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
                let pat = PMatch::new(Some((**aty2).clone()), &[pat.clone()], cxt);

                let aty = aty2.quote(cxt.qenv());
                let (sym, cxt) = cxt.bind(pat.name, aty2.clone());
                let va = Val::Neutral(VHead::Sym(sym), default());
                let rty = ty.clone().app(va.clone());
                let cxt = pat.bind(0, &cxt);
                let body = pat.compile(&[body.check(rty, &cxt)]);
                Term::Fun(Lam, *i, pat.name, Box::new(aty), Arc::new(body))
            }
            // when checking pair against type, assume sigma
            (Pre::Sigma(i, n1, aty, n2, body), Val::Type) => {
                let n1 = n1.map(|x| *x).unwrap_or(cxt.db.name("_"));
                let n2 = n2.map(|x| *x).unwrap_or(cxt.db.name("_"));
                let aty = aty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let body = body.check(Val::Type, &cxt.bind(n1, vaty).1);
                Term::Fun(Sigma(n2), *i, n1, Box::new(aty), Arc::new(body))
            }
            (Pre::Sigma(i, None, a, None, b), Val::Fun(Sigma(_), i2, _, aty, _, _)) if i == i2 => {
                let a = a.check((**aty).clone(), cxt);
                let va = a.eval(&cxt.env());
                let rty = ty.app(va);
                let b = b.check(rty, cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }
            (Pre::Do(block, last), _) => elab_block(block, last, Some(ty), cxt).0,

            // insert lambda when checking (non-implicit lambda) against implicit function type
            (_, Val::Fun(Pi, Impl, n, aty, _, _)) => {
                let aty2 = aty.quote(cxt.qenv());
                // don't let them access the name in the term (shadowing existing names would be unintuitive)
                let n = cxt.db.inaccessible(*n);
                let (sym, cxt) = cxt.bind(n, aty.clone());
                let rty = ty.app(Val::Neutral(VHead::Sym(sym), default()));
                let body = self.check(rty, &cxt);
                Term::Fun(Lam, Impl, n, Box::new(aty2), Arc::new(body))
            }
            // and similar for implicit sigma
            (_, Val::Fun(Sigma(_), Impl, _, aty, _, _)) => {
                let a = cxt
                    .new_meta((**aty).clone(), self.span())
                    .quote(&cxt.qenv());
                let va = a.eval(&cxt.env());
                let rty = ty.app(va);
                let b = self.check(rty, &cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }

            (_, _) => {
                let (s, sty) = self.infer(cxt, !matches!(ty, Val::Fun(Pi, Impl, _, _, _, _)));
                if !ty.unify(&sty, cxt.scxt(), cxt) {
                    cxt.err(
                        "could not match types: expected "
                            + ty.zonk(cxt, true).pretty_at(cxt)
                            + ", found "
                            + sty.zonk(cxt, true).pretty_at(cxt),
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
        self.quote(&QEnv {
            partial_cxt: true,
            ..cxt.qenv().clone()
        })
        .pretty(&cxt.db)
    }
}
impl Pretty for Val {
    fn pretty(&self, db: &DB) -> Doc {
        self.quote(&QEnv {
            partial_cxt: true,
            errors: Errors {
                db: db.clone(),
                ..default()
            },
            ..default()
        })
        .pretty(&db)
    }
}

// pretty-printing

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
            Term::Var(n, _i) => Doc::start(db.get(*n)), // + &*format!("@{}", _i.0),
            Term::Def(d) => db.idefs.get(*d).name().pretty(db),
            Term::Meta(m) => m.pretty(db),
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
                                pretty_binder(db.name("_"), *i, Prec::Term, v[0].pretty(db), db)
                                    + ", "
                                    + v[1].pretty(db)
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
                s.pretty(db).nest(Prec::Atom),
                db,
            ) + " => "
                + body.pretty(db))
            .prec(Prec::Term),
            Term::Fun(Pi, i, s, aty, body) => {
                (pretty_binder(*s, *i, Prec::App, aty.pretty(db), db)
                    + " -> "
                    + body.pretty(db).nest(Prec::Pi))
                .prec(Prec::Pi)
            }
            Term::Fun(Sigma(s2), i, s1, aty, body) => {
                (pretty_binder(*s1, *i, Prec::Pi, aty.pretty(db), db)
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
