mod pattern;
mod term;

use pattern::*;
use term::*;
pub use term::{Term, Val};

use crate::common::*;
use crate::parser::{Pre, PrePat, PreStmt, SPre, SPrePat};

// -- entry point (per-file elab query) --

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
    pub unsolved_metas: Vec<(Meta, S<MetaSource>)>,
    pub solved_metas: Vec<(Meta, Arc<Val>)>,
    pub errors: Arc<[Error]>,
}

#[derive(Clone, Debug)]
pub struct ModuleElabResult {
    pub module: Arc<Module>,
    pub errors: Vec<Error>,
}

pub fn elab_module(file: File, def: Def, db: &DB) -> ModuleElabResult {
    let parsed = db.file_ast(file);
    let mut errors = parsed.errors.clone();
    let mut defs = Vec::new();
    let root_cxt = Cxt::new(def, AbsSpan(file, Span(0, 0)), db.clone());
    let mut source_map = HashMap::new();
    // Avoid making a meta for the type
    root_cxt.metas.take();
    for i in &parsed.defs {
        let def = db.idefs.intern(&DefLoc::Child(def, *i.name));
        if let Ok(elab) = db.elab.def_value(def, db) {
            let span = elab.def.name.span();
            defs.push(elab.def);
            for (m, source) in elab.unsolved_metas {
                if root_cxt.meta_val(m).is_none() {
                    source_map.insert(m, source);
                    root_cxt.metas.with_mut(|v| {
                        v.insert(m, MetaEntry::Unsolved(Arc::new(Val::Error), source))
                    });
                }
            }
            for (m, val) in elab.solved_metas {
                let mval = Val::Neutral(Head::Meta(m), default()).zonk(&root_cxt, true);
                if !mval
                    .clone()
                    .glued()
                    .unify((*val).clone().glued(), span, &root_cxt)
                {
                    errors.push(Error {
                        secondary: if let Some(s) = source_map.get(&m) {
                            vec![Label {
                                span: s.span(),
                                message: "metavariable introduced here".into(),
                                color: Some(Doc::COLOR2),
                            }]
                        } else {
                            vec![]
                        },
                        ..Error::simple(
                            "conflicting meta solutions: "
                                + source_map
                                    .get(&m)
                                    .map_or("metavariable " + m.pretty(db), |s| {
                                        s.pretty(db) + " (" + m.pretty(db) + ")"
                                    })
                                + " previously solved to "
                                + mval.pretty(db)
                                + " but then attempted to solve to "
                                + val.pretty(db),
                            span,
                        )
                        .with_label("metavariable solved here")
                    });
                }
            }
            errors.extend(elab.errors.iter().cloned());
        }
    }
    // Re-zonk metas in types to make sure we get them all
    for elab in &mut defs {
        elab.ty = Arc::new(elab.ty.zonk(&root_cxt, true));
        // We should really also zonk bodies, but that makes some of the smalltt examples slow so i'll wait until we actually need it
    }
    for (m, val) in root_cxt.metas.take() {
        match val {
            MetaEntry::Unsolved(_, source) => errors.push(
                Error::simple(
                    "could not find solution for " + source.pretty(db) + " (" + m.pretty(db) + ")",
                    source.span(),
                )
                .with_label("metavariable introduced here"),
            ),
            MetaEntry::Solved(_) => (),
        }
    }
    errors.append(&mut root_cxt.errors.errors.take());
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
    let solved_ty = match &ty {
        Some(ty) => {
            let ty = ty.eval(cxt.env()).zonk(&cxt, true);
            cxt.solve_meta(Meta(def, 0), &vec![], ty, Some(pre.name.span()));
            true
        }
        None => false,
    };
    let (mut body, ty) = if let Some((val, ty)) = pre.0.value.as_ref().map(|val| match &ty {
        Some(ty) => {
            let vty = ty.eval(&cxt.env());
            (val.check(vty.clone(), &cxt), vty)
        }
        None => val.infer(&cxt, true).pipe(|(x, y)| (x, y.as_small())),
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
    if !solved_ty {
        let ety = Val::Neutral(Head::Meta(Meta(def, 0)), default()).zonk(&cxt, true);
        if !ty
            .clone()
            .glued()
            .unify(ety.clone().glued(), pre.name.span(), &cxt)
        {
            cxt.err(
                "definition body has type "
                    + ty.pretty(&cxt.db)
                    + " but definition was previously inferred to have type "
                    + ety.pretty(&cxt.db),
                pre.name.span(),
            );
        }
    }

    Some(DefElabResult {
        def: DefElab {
            name: pre.name,
            ty: Arc::new(ty),
            body: body.map(|x| Arc::new(x.eval(&cxt.env()))),
        },
        unsolved_metas: cxt.metas.with(|m| {
            m.iter()
                .filter_map(|(m, v)| match v {
                    MetaEntry::Unsolved(_, source) => Some((*m, *source)),
                    MetaEntry::Solved(_) => None,
                })
                .collect()
        }),
        solved_metas: cxt
            .metas
            .take()
            .into_iter()
            .filter(|(m, _)| m.0 != def || m.1 == 0)
            .filter_map(|(m, v)| match v {
                MetaEntry::Unsolved(_, _) => None,
                MetaEntry::Solved(val) => Some((m, val)),
            })
            .collect(),
        errors: cxt.errors.errors.take().into_iter().collect(),
    })
}

// -- elaboration context --

enum MetaEntry {
    // The first field is the type; we'll need that eventually for typeclass resolution, but it doesn't matter right now
    // TODO error on unsolved metas (that's why the span is here)
    Unsolved(Arc<Val>, S<MetaSource>),
    Solved(Arc<Val>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MetaSource {
    TypeOf(Name),
    ImpArg(Name),
    Hole,
}
impl Pretty for MetaSource {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            MetaSource::TypeOf(n) => "type of " + n.pretty(db),
            MetaSource::ImpArg(n) => "implicit argument " + n.pretty(db),
            MetaSource::Hole => "hole".into(),
        }
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
    uquant_stack: Ref<Vec<Vec<(Sym, Arc<Val>)>>>,
    cap_surplus: Ref<Option<u32>>,
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
        let metas = std::iter::once((
            Meta(context, 0),
            MetaEntry::Unsolved(
                Arc::new(Val::Type),
                S(
                    MetaSource::TypeOf(db.idefs.get(context).name()),
                    span.span(),
                ),
            ),
        ))
        .collect::<HashMap<_, _>>()
        .into();
        Cxt {
            def: context,
            db,
            bindings: default(),
            errors: env.qenv.errors.clone(),
            env,
            metas,
            uquant_stack: default(),
            cap_surplus: None.into(),
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
    fn has_uquant(&self) -> bool {
        self.uquant_stack.with(|v| !v.is_empty())
    }
    fn push_uquant(&self) {
        self.uquant_stack.with_mut(|v| v.push(default()));
    }
    fn pop_uquant(&self) -> Option<Vec<(Sym, Arc<Val>)>> {
        self.uquant_stack.with_mut(|v| v.pop())
    }

    fn report_surplus(&self, v: u32) {
        self.cap_surplus
            .with_mut(|t| *t = Some(t.map_or(v, |t| t.min(v))))
    }
    fn record_surplus<R>(&self, f: impl FnOnce() -> R) -> (Option<u32>, R) {
        let before = self.cap_surplus.take();
        let r = f();
        (self.cap_surplus.set(before), r)
    }

    fn lookup(&self, n: Name) -> Option<(Term, Arc<Val>)> {
        // first try locals
        self.bindings
            .get(&n)
            .map(|(val, ty)| {
                self.report_surplus(0);
                (val.quote(&self.qenv()), ty.clone())
            })
            .or_else(|| {
                self.db.lookup_def_name(self.def, n).map(|(d, t)| {
                    (
                        Term::Head(Head::Def(d)),
                        match t {
                            Some(t) => t.clone(),
                            // TODO solve these across definitions
                            None => Arc::new(Val::Neutral(Head::Meta(Meta(d, 0)), default())),
                        },
                    )
                })
            })
            .or_else(|| {
                let (sym, ty) = self
                    .uquant_stack
                    .with(|v| {
                        v.iter()
                            .rev()
                            .flatten()
                            .find(|(s, _)| s.0 == n)
                            .map(|(s, v)| (*s, v.clone()))
                    })
                    .or_else(|| {
                        self.uquant_stack.with_mut(|v| {
                            v.last_mut().map(|v| {
                                assert!(!v.iter().any(|(s, _)| s.0 == n));
                                let s = self.scxt().bind(n);
                                // TODO span for the name
                                let ty = Arc::new(self.new_meta(
                                    Val::Type,
                                    MetaSource::TypeOf(n),
                                    self.errors.span.span(),
                                ));
                                v.push((s, ty.clone()));
                                (s, ty)
                            })
                        })
                    })?;
                Some((Term::Head(Head::Sym(sym)), ty))
            })
    }
    fn solved_locals(&self) -> Vec<(Sym, Arc<Val>)> {
        self.env
            .env
            .keys()
            .filter_map(|x| Some((*x, self.local_val(*x)?)))
            .collect()
    }
    fn can_solve(&self, sym: Sym) -> bool {
        self.env
            .env
            .get(&sym)
            .iter()
            .any(|v| ***v == Val::Neutral(Head::Sym(sym), default()))
    }
    fn local_val(&self, sym: Sym) -> Option<Arc<Val>> {
        let val = self.env.env.get(&sym)?;
        (**val != Val::sym(sym)).then(|| val.clone())
    }
    fn solve_local(&mut self, sym: Sym, val: Arc<Val>) {
        if self.can_solve(sym) {
            self.env.env.0.insert(sym, val);
        } else {
            panic!("call can_solve first")
        }
    }
    fn bind_val(&mut self, n: Name, v: Val, ty: impl Into<Arc<Val>>) {
        self.bindings.insert(n, (v, ty.into()));
    }
    fn bind_raw(&mut self, name: Name, sym: Sym, ty: impl Into<Arc<Val>>) -> Sym {
        self.env.env.0.insert(sym, Arc::new(Val::sym(sym)));
        self.bindings
            .insert(name, (Val::Neutral(Head::Sym(sym), default()), ty.into()));
        sym
    }
    fn bind_(&mut self, n: Name, ty: impl Into<Arc<Val>>) -> Sym {
        let sym = self.scxt().bind(n);
        self.bind_raw(n, sym, ty)
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
    fn scxt(&self) -> &SymCxt {
        &self.env.qenv.scxt
    }

    fn new_meta(&self, ty: Val, source: MetaSource, span: Span) -> Val {
        // When making a meta with type (a, b), we're more likely to be able to solve it if we can solve each component separately
        // So we make two metas (possibly recursively), and return (?0, ?1)
        // In general this can be applied to any single-constructor datatype, but we probably won't actually implement that
        // But since we usually tuple function arguments, this makes type inference work much better in practice
        if let Val::Fun(Sigma(_), _, _, aty, _, _) = &ty {
            let m1 = self.new_meta((**aty).clone(), source, span);
            let bty = ty.app(m1.clone());
            let m2 = self.new_meta(bty, source, span);
            let val = Val::Pair(Arc::new(m1), Arc::new(m2));
            return val;
        }

        // This can skip numbers in the presence of solved external metas but that shouldn't matter
        let m = Meta(self.def, self.metas.with(|x| x.len()) as u32);
        self.metas
            .with_mut(|x| x.insert(m, MetaEntry::Unsolved(Arc::new(ty), S(source, span))));
        let v = Val::Neutral(
            Head::Meta(m),
            self.env
                .env
                .keys()
                // TODO is this correct?
                .map(|s| VElim::App(Expl, Arc::new(Val::sym(*s))))
                .collect(),
        );
        v
    }
    fn new_meta_with_spine(
        &self,
        ty: Val,
        source: MetaSource,
        span: Span,
        spine: impl IntoIterator<Item = VElim>,
    ) -> Val {
        // This can skip numbers in the presence of solved external metas but that shouldn't matter
        let m = Meta(self.def, self.metas.with(|x| x.len()) as u32);
        self.metas
            .with_mut(|x| x.insert(m, MetaEntry::Unsolved(Arc::new(ty), S(source, span))));
        let v = Val::Neutral(Head::Meta(m), spine.into_iter().collect());
        v
    }
    fn meta_source(&self, m: Meta) -> Option<S<MetaSource>> {
        self.metas.with(|x| {
            x.get(&m).and_then(|x| match x {
                MetaEntry::Unsolved(_, source) => Some(*source),
                MetaEntry::Solved(_) => None,
            })
        })
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
        self.solve_meta_(meta, spine, solution, span, false)
    }
    fn solve_meta_(
        &self,
        meta: Meta,
        spine: &Spine,
        solution: Val,
        span: Option<Span>,
        zonked: bool,
    ) -> bool {
        if spine.iter().any(|x| !matches!(x, VElim::App(_, _))) {
            self.err(
                "cannot solve meta with non-app in spine: "
                    + Val::Neutral(Head::Meta(meta), spine.clone()).pretty(&self.db),
                span,
            );
        }
        let syms: Vec<_> = spine
            .iter()
            .filter_map(|v| match v {
                VElim::App(_, v) => Some(v),
                _ => None,
            })
            .map(|v| match &**v {
                Val::Neutral(Head::Sym(s), sp) if sp.is_empty() => Some(*s),
                _ => None,
            })
            .collect();
        let qenv = QEnv {
            partial_cxt: Some(syms.iter().copied().flatten().collect()),
            ..default()
        };
        // There are more checks than this that we could do, that we don't do
        // For now this is enough, but in the future we might need to do more
        match solution.quote_(&qenv) {
            Ok(body) => {
                let term = spine.iter().zip(syms).rfold(body, |acc, (_, s)| {
                    Term::Fun(
                        Lam,
                        Expl,
                        s.unwrap_or(self.scxt().bind(self.db.name("_"))),
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
            Err(_) if !zonked => {
                // If we get a scope error, try zonking (with β-reduction) to inline already-solved metas and see if that helps
                // This is important in lots of cases!
                self.solve_meta_(meta, spine, solution.zonk(self, true), span, true)
            }
            Err(s) => {
                self.err(
                    Doc::start("cannot solve meta ")
                        + self
                            .meta_source(meta)
                            .map_or(meta.pretty(&self.db), |m| m.pretty(&self.db))
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

// -- unification --

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
    fn unify_(&self, other: &VElim, span: Span, cxt: &Cxt, mode: UnfoldState) -> bool {
        match (self, other) {
            (VElim::App(_, x), VElim::App(_, y)) => {
                (**x)
                    .clone()
                    .glued()
                    .unify_((**y).clone().glued(), span, cxt, mode)
            }
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
                    for (&s1, &s2) in v1.iter().zip(v2) {
                        let s = cxt.scxt().bind(s1.0);
                        env1.0
                            .insert(s1, Arc::new(Val::Neutral(Head::Sym(s), default())));
                        env2.0
                            .insert(s2, Arc::new(Val::Neutral(Head::Sym(s), default())));
                    }
                    if !t1
                        .eval(&env1)
                        .glued()
                        .unify_(t2.eval(&env2).glued(), span, cxt, mode)
                    {
                        return false;
                    }
                }
                if let Some(fallback1) = fallback1 {
                    let fallback2 = fallback2.as_ref().unwrap();
                    if !fallback1
                        .eval(env1)
                        .glued()
                        .unify(fallback2.eval(env2).glued(), span, cxt)
                    {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

impl GVal {
    fn unify(self, other: GVal, span: Span, cxt: &Cxt) -> bool {
        self.unify_(other, span, cxt, UnfoldState::Maybe)
    }
    fn unify_(self, other: GVal, span: Span, cxt: &Cxt, mut mode: UnfoldState) -> bool {
        let (mut a, mut b) = (self, other);
        loop {
            if mode == UnfoldState::Yes {
                a.whnf(cxt);
                b.whnf(cxt);
            }
            break match (a.big(), b.big()) {
                (Val::Error, _) | (_, Val::Error) => true,
                (Val::Type, Val::Type) => true,
                (Val::Neutral(s, sp), Val::Neutral(s2, sp2))
                    if s == s2
                        && sp.len() == sp2.len()
                        && sp
                            .iter()
                            .zip(sp2)
                            .all(|(x, y)| x.unify_(y, span, cxt, mode.spine_mode())) =>
                {
                    true
                }
                (Val::Fun(c, i1, n1, aty, _, _), Val::Fun(c2, i2, _, aty2, _, _))
                    if (c == c2 || matches!((c, c2), (Sigma(_), Sigma(_)))) && i1 == i2 =>
                {
                    let s = cxt.scxt().bind(n1.0);
                    let arg = Val::Neutral(Head::Sym(s), default());
                    if !(**aty)
                        .clone()
                        .glued()
                        .unify_((**aty2).clone().glued(), span, cxt, mode)
                    {
                        false
                    } else {
                        a = a.as_big().app(arg.clone()).glued();
                        b = b.as_big().app(arg).glued();
                        mode = UnfoldState::Maybe;
                        continue;
                    }
                }
                (Val::Cap(l, t), Val::Cap(l2, t2)) if *l == *l2 => {
                    a = (**t).clone().glued();
                    b = (**t2).clone().glued();
                    continue;
                }

                (Val::Neutral(Head::Meta(m), spine), _)
                    if !matches!(b.big(), Val::Neutral(Head::Meta(m2), _) if m2 == m)
                        && spine.iter().all(|x| matches!(x, VElim::App(_, _)))
                        && cxt.meta_val(*m).is_none() =>
                {
                    cxt.solve_meta(*m, spine, b.small().clone(), Some(span));
                    true
                }
                (_, Val::Neutral(Head::Meta(m), spine))
                    if !matches!(a.big(), Val::Neutral(Head::Meta(m2), _) if m2 == m)
                        && spine.iter().all(|x| matches!(x, VElim::App(_, _)))
                        && cxt.meta_val(*m).is_none() =>
                {
                    cxt.solve_meta(*m, spine, a.small().clone(), Some(span));
                    true
                }

                (Val::Neutral(_, _), _) | (_, Val::Neutral(_, _)) if mode == UnfoldState::Maybe => {
                    mode = UnfoldState::Yes;
                    continue;
                }
                // eta-expand if there's a lambda on only one side
                // TODO this might have problems since we don't make sure the icits match?
                (Val::Fun(Lam, _, n, _, _, _), _) | (_, Val::Fun(Lam, _, n, _, _, _)) => {
                    let s = cxt.scxt().bind(n.0);
                    let arg = Val::Neutral(Head::Sym(s), default());
                    a = a.as_big().app(arg.clone()).glued();
                    b = b.as_big().app(arg).glued();
                    continue;
                }

                (_, _) => false,
            };
        }
    }
}

// -- elaboration --

// don't call this if checking against an implicit lambda
fn insert_metas(term: Term, mut ty: GVal, cxt: &Cxt, span: Span) -> (Term, GVal) {
    match ty.whnf(cxt) {
        Val::Fun(Pi, Impl, n, aty, _, _) => {
            let m = cxt.new_meta((**aty).clone(), MetaSource::ImpArg(n.0), span);
            let term = Term::App(
                Box::new(term),
                TElim::App(Impl, Box::new(m.quote(&cxt.qenv()))),
            );
            let ty = ty.map(|x| x.app(m.clone()));
            insert_metas(term, ty, cxt, span)
        }
        _ => (term, ty),
    }
}

fn elab_block(block: &[PreStmt], last_: &SPre, ty: Option<GVal>, cxt1: &Cxt) -> (Term, Val) {
    let mut cxt = cxt1.clone();
    let mut v = Vec::new();
    for x in block {
        let (vsym, t, p, x) = match x {
            PreStmt::Expr(x) => {
                let (x, xty) = x.infer(&cxt, true);
                let vsym = cxt.bind_(cxt.db.name("_"), xty.small().clone());
                (vsym, xty.as_small(), None, x)
            }
            PreStmt::Let(pat, body) if matches!(&***pat, PrePat::Binder(_, _)) => {
                let cxt_start = cxt.clone();
                let (sym, pat) = PMatch::new(None, &[pat.clone()], &mut cxt);
                let aty = (*pat.ty).clone();
                let body = body.check(aty.clone(), &cxt_start);
                (sym, aty, Some(pat), body)
            }
            PreStmt::Let(pat, body) => {
                let (body, aty) = body.infer(&cxt, true);
                let (sym, pat) = PMatch::new(Some(aty.clone()), &[pat.clone()], &mut cxt);
                (sym, aty.as_small(), Some(pat), body)
            }
        };
        let t2 = t.quote(&cxt.qenv());
        if let Some(p) = &p {
            cxt = p.bind(0, &cxt);
        }
        v.push((vsym, t2, p, x));
    }
    let explicit_ty = ty.is_some();
    let (last, lty) = last_.elab(ty, &cxt);
    let mut lty = lty.as_small();
    let term = v.into_iter().rfold(last, |acc, (s, t, p, x)| {
        let acc = match p {
            Some(p) => p.compile(&[acc], &cxt),
            None => acc,
        };
        Term::App(
            Box::new(Term::Fun(Lam, Expl, s, Box::new(t), Arc::new(acc))),
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
    fn elab(&self, ty: Option<GVal>, cxt: &Cxt) -> (Term, GVal) {
        match ty {
            Some(ty) => {
                let s = self.check(ty.clone(), cxt);
                (s, ty)
            }
            None => self.infer(cxt, true),
        }
    }

    fn infer(&self, cxt: &Cxt, should_insert_metas: bool) -> (Term, GVal) {
        with_stack(|| self.infer_(cxt, should_insert_metas))
    }
    fn infer_(&self, cxt: &Cxt, mut should_insert_metas: bool) -> (Term, GVal) {
        let (s, sty) = match &***self {
            Pre::Var(name) if cxt.db.name("_") == *name => {
                // hole
                let mty = cxt.new_meta(Val::Type, MetaSource::TypeOf(*name), self.span());
                let m = cxt
                    .new_meta(mty.clone(), MetaSource::Hole, self.span())
                    .quote(&cxt.qenv());
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
                let aty = match fty.whnf(cxt) {
                    Val::Error => Val::Error,
                    Val::Fun(Pi, i2, _, aty, _, _) if i == i2 => (**aty).clone(),
                    Val::Fun(Pi, _, _, _, _, _) => {
                        cxt.err(
                            "wrong function type: expected "
                                + Doc::start(*i)
                                + " function but got "
                                + fty.small().pretty(&cxt.db),
                            fs.span(),
                        );
                        // prevent .app() from panicking
                        f = Term::Error;
                        fty = Val::Error.glued();
                        Val::Error
                    }
                    Val::Neutral(Head::Meta(m), spine) if cxt.meta_val(*m).is_none() => {
                        // Solve it to a pi type with more metas
                        // The new metas will use the same scope as the old ones
                        // TODO extend that scoping principle to other areas where metas are solved to more metas
                        let m1 = cxt.new_meta_with_spine(
                            Val::Type,
                            cxt.meta_source(*m)
                                .as_deref()
                                .copied()
                                .unwrap_or(MetaSource::Hole),
                            fs.span(),
                            spine.clone(),
                        );
                        let (s, cxt2) = cxt.bind(cxt.db.name("_"), m1.clone());
                        let m2 = cxt2.new_meta_with_spine(
                            Val::Type,
                            cxt.meta_source(*m)
                                .as_deref()
                                .copied()
                                .unwrap_or(MetaSource::Hole),
                            fs.span(),
                            spine
                                .iter()
                                .cloned()
                                .chain(std::iter::once(VElim::App(Expl, Arc::new(Val::sym(s))))),
                        );
                        cxt.solve_meta(
                            *m,
                            spine,
                            Val::Fun(
                                Pi,
                                *i,
                                s,
                                Arc::new(m1.clone()),
                                Arc::new(m2.quote(cxt2.qenv())),
                                Arc::new(cxt.env().clone()),
                            ),
                            Some(self.span()),
                        );
                        m1
                    }
                    _ => {
                        cxt.err(
                            "not a function type: " + fty.small().pretty(&cxt.db),
                            fs.span(),
                        );
                        // prevent .app() from panicking
                        f = Term::Error;
                        fty = Val::Error.glued();
                        Val::Error
                    }
                };
                let x = x.check(aty, cxt);
                let vx = x.eval(cxt.env());
                (
                    Term::App(Box::new(f), TElim::App(*i, Box::new(x))),
                    fty.as_small().app(vx),
                )
            }
            Pre::Pi(i, n, paty, body) => {
                let q = !cxt.has_uquant();
                if q {
                    cxt.push_uquant();
                }
                let aty = paty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let (s, cxt) = cxt.bind(*n, vaty.clone());
                let body = pat_bind_type(
                    &paty,
                    Val::Neutral(Head::Sym(s), default()),
                    &vaty,
                    &cxt,
                    |cxt| body.check(Val::Type, cxt),
                );
                let scope = q.then(|| cxt.pop_uquant().unwrap());
                (
                    scope.into_iter().flatten().rfold(
                        Term::Fun(Pi, *i, s, Box::new(aty), Arc::new(body)),
                        |acc, (s, ty)| {
                            Term::Fun(Pi, Impl, s, Box::new(ty.quote(cxt.qenv())), Arc::new(acc))
                        },
                    ),
                    Val::Type,
                )
            }
            Pre::Sigma(_, Some(_), _, _, _) | Pre::Sigma(_, _, _, Some(_), _) => {
                (self.check(Val::Type, cxt), Val::Type)
            }
            // If no type is given, assume monomorphic lambdas
            Pre::Lam(i, pat, body) => {
                let q = !cxt.has_uquant();
                if q {
                    cxt.push_uquant();
                }
                let mut cxt2 = cxt.clone();
                let (s, pat) = PMatch::new(None, &[pat.clone()], &mut cxt2);
                let aty = pat.ty.clone();
                let aty2 = aty.quote(cxt.qenv());

                let cxt3 = pat.bind(0, &cxt2);
                let (body, rty) = body.infer(&cxt3, true);
                let rty = rty.small().quote(&cxt3.qenv());
                let body = pat.compile(&[body], &cxt2);
                let rty = pat.compile(&[rty], &cxt2);
                let scope = q.then(|| cxt.pop_uquant().unwrap());
                (
                    scope.iter().flatten().rfold(
                        Term::Fun(Lam, *i, s, Box::new(aty2.clone()), Arc::new(body)),
                        |acc, (s, ty)| {
                            // Don't introduce a redex, the user clearly intended to make a polymorphic lambda
                            should_insert_metas = false;
                            Term::Fun(Lam, Impl, *s, Box::new(ty.quote(cxt.qenv())), Arc::new(acc))
                        },
                    ),
                    scope
                        .into_iter()
                        .flatten()
                        .fold(
                            Term::Fun(Pi, *i, s, Box::new(aty2), Arc::new(rty)),
                            |acc, (s, ty)| {
                                Term::Fun(
                                    Pi,
                                    Impl,
                                    s,
                                    Box::new(ty.quote(cxt.qenv())),
                                    Arc::new(acc),
                                )
                            },
                        )
                        .eval(cxt.env()),
                )
            }
            // Similarly assume non-dependent pair
            Pre::Sigma(i, None, a, None, b) => {
                let (a, aty) = a.infer(cxt, true);
                let aty = Arc::new(aty.as_small());
                let (s, cxt) = cxt.bind(cxt.db.name("_"), aty.clone());
                let (b, bty) = b.infer(&cxt, true);
                let bty = bty.small().quote(cxt.qenv());
                (
                    Term::Pair(Box::new(a), Box::new(b)),
                    Val::Fun(
                        Sigma(cxt.db.name("_")),
                        *i,
                        s,
                        aty,
                        Arc::new(bty),
                        Arc::new(cxt.env().clone()),
                    ),
                )
            }
            Pre::Cap(l, x) => {
                let x = x.check(Val::Type, cxt);
                (Term::Cap(*l, Box::new(x)), Val::Type)
            }
            Pre::Binder(_, _) => {
                cxt.err("binder not allowed in this context", self.span());
                (Term::Error, Val::Error)
            }
            Pre::Do(block, last) => elab_block(block, last, None, cxt),
            Pre::Type => (Term::Type, Val::Type),
            Pre::Error => (Term::Error, Val::Error),
        };
        let sty = sty.glued();
        if should_insert_metas {
            insert_metas(s, sty, cxt, self.span())
        } else {
            (s, sty)
        }
    }

    fn check(&self, ty: impl Into<GVal>, cxt: &Cxt) -> Term {
        let mut ty: GVal = ty.into();
        match (&***self, ty.whnf(cxt)) {
            (Pre::Lam(i, pat, body), Val::Fun(Pi, i2, _, aty2, _, _)) if i == i2 => {
                let mut cxt = cxt.clone();
                let (sym, pat) =
                    PMatch::new(Some((**aty2).clone().glued()), &[pat.clone()], &mut cxt);
                let aty = aty2.quote(cxt.qenv());

                let va = Val::Neutral(Head::Sym(sym), default());
                // TODO why doesn't as_small() work here
                let rty = ty.as_big().app(va.clone());
                let cxt = pat.bind(0, &cxt);
                let body = pat.compile(&[body.check(rty, &cxt)], &cxt);
                Term::Fun(Lam, *i, sym, Box::new(aty), Arc::new(body))
            }
            // when checking pair against type, assume sigma
            (Pre::Sigma(i, n1, aty, n2, body), Val::Type) => {
                let n1 = n1.map(|x| *x).unwrap_or(cxt.db.name("_"));
                let n2 = n2.map(|x| *x).unwrap_or(cxt.db.name("_"));
                let aty = aty.check(Val::Type, cxt);
                let vaty = aty.eval(cxt.env());
                let (s, cxt) = cxt.bind(n1, vaty);
                let body = body.check(Val::Type, &cxt);
                Term::Fun(Sigma(n2), *i, s, Box::new(aty), Arc::new(body))
            }
            (Pre::Sigma(i, None, a, None, b), Val::Fun(Sigma(_), i2, _, aty, _, _)) if i == i2 => {
                let a = a.check((**aty).clone(), cxt);
                let va = a.eval(&cxt.env());
                let rty = ty.as_small().app(va);
                let b = b.check(rty, cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }
            (Pre::Do(block, last), _) => elab_block(block, last, Some(ty), cxt).0,

            // insert lambda when checking (non-implicit lambda) against implicit function type
            (_, Val::Fun(Pi, Impl, n, aty, _, _)) => {
                let aty2 = aty.quote(cxt.qenv());
                // don't let them access the name in the term (shadowing existing names would be unintuitive)
                let n = cxt.db.inaccessible(n.0);
                let (sym, cxt) = cxt.bind(n, aty.clone());
                let rty = ty.as_small().app(Val::Neutral(Head::Sym(sym), default()));
                let body = self.check(rty, &cxt);
                Term::Fun(Lam, Impl, sym, Box::new(aty2), Arc::new(body))
            }
            // and similar for implicit sigma
            (_, Val::Fun(Sigma(_), Impl, n, aty, _, _)) => {
                let a = cxt
                    .new_meta((**aty).clone(), MetaSource::ImpArg(n.0), self.span())
                    .quote(&cxt.qenv());
                let va = a.eval(&cxt.env());
                let rty = ty.as_small().app(va);
                let b = self.check(rty, &cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }

            (_, _) => {
                let (r, (s, mut sty)) = cxt.record_surplus(|| {
                    self.infer(cxt, !matches!(ty.big(), Val::Fun(Pi, Impl, _, _, _, _)))
                });
                if !ty.clone().unify(sty.clone(), self.span(), cxt) {
                    // Try to coerce if possible
                    match (ty.whnf(cxt), sty.whnf(cxt)) {
                        // demotion is always available
                        (ty_, Val::Cap(l2, sty)) if !matches!(ty_, Val::Cap(_, _)) => {
                            if ty.clone().unify((**sty).clone().glued(), self.span(), cxt) {
                                r.map(|r| cxt.report_surplus(r + l2));
                                return s;
                            }
                        }
                        (Val::Cap(l1, ty), Val::Cap(l2, sty)) if *l1 < *l2 => {
                            if (**ty).clone().glued().unify(
                                (**sty).clone().glued(),
                                self.span(),
                                cxt,
                            ) {
                                r.map(|r| cxt.report_surplus(r + (l2 - l1)));
                                return s;
                            }
                        }
                        // TODO we can promote for auto-copy types
                        (Val::Cap(l1, ty), _) if r.map_or(true, |r| r >= *l1) => {
                            if (**ty).clone().glued().unify(sty.clone(), self.span(), cxt) {
                                r.map(|r| cxt.report_surplus(r - l1));
                                return s;
                            }
                        }
                        (Val::Cap(l1, ty), Val::Cap(l2, sty))
                            if *l1 > *l2 && r.map_or(true, |r| r >= l1 - l2) =>
                        {
                            if (**ty).clone().glued().unify(
                                (**sty).clone().glued(),
                                self.span(),
                                cxt,
                            ) {
                                r.map(|r| cxt.report_surplus(r - (l1 - l2)));
                                return s;
                            }
                        }
                        _ => (),
                    }

                    cxt.err(
                        "could not match types: expected "
                            + ty.small().zonk(cxt, true).pretty(&cxt.db)
                            + ", found "
                            + sty.small().zonk(cxt, true).pretty(&cxt.db),
                        self.span(),
                    );
                }
                r.map(|r| cxt.report_surplus(r));
                s
            }
        }
    }
}
