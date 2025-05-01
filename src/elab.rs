mod pattern;
mod term;

use std::sync::Arc;

use pattern::*;
use rustc_hash::{FxHashMap, FxHashSet};
use term::*;
pub use term::{Builtin, Head, Term, Val};

use crate::common::*;
use crate::parser::{Pre, PreDef, PrePat, PreStmt, SPre, SPrePat};

// -- entry point (per-file elab query) --

#[derive(Clone, Debug, PartialEq)]
pub enum DefBody {
    Val(Arc<Term>),
    Type(Vec<Def>),
}

#[derive(Clone, Debug)]
pub struct DefElab {
    pub name: SName,
    pub ty: Arc<Val>,
    pub body: Option<DefBody>,
    pub can_eval: bool,
    pub children: Vec<(Def, DefElab)>,
}

#[derive(Debug)]
pub struct Module {
    pub defs: Vec<DefElab>,
}

#[derive(Clone, Debug)]
pub struct DefElabResult {
    pub def: DefElab,
    pub unsolved_metas: Vec<(Meta, S<MetaSource>, Arc<Val>)>,
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
        let def = db.idefs.intern(&DefLoc::Child(def, *i.name()));
        if let Ok(elab) = db.elab.def_value(def, db) {
            let span = elab.def.name.span();
            defs.push(elab.def);
            for (m, source, ty) in elab.unsolved_metas {
                if root_cxt.meta_val(m).is_none() {
                    source_map.insert(m, source);
                    root_cxt
                        .metas
                        .with_mut(|v| v.insert(m, MetaEntry::Unsolved(ty, source)));
                }
            }
            for (m, val) in elab.solved_metas {
                let mval = Val::Neutral(Head::Meta(m), default()).zonk(&root_cxt, true);
                if !mval
                    .clone()
                    .glued()
                    .unify(None, (*val).clone().glued(), None, span, &root_cxt)
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
            MetaEntry::Unsolved(ty, source) => {
                // Regions get solved to '() by default, () only has one possible value
                if matches!(
                    *ty,
                    Val::Neutral(Head::Builtin(Builtin::Region | Builtin::UnitType), _)
                ) {
                    continue;
                }
                errors.push(
                    Error::simple(
                        "could not find solution for "
                            + source.pretty(db)
                            + " ("
                            + m.pretty(db)
                            + ")"
                            + " of type "
                            + ty.pretty(db),
                        source.span(),
                    )
                    .with_label("metavariable introduced here"),
                )
            }
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
    let (file, file_def) = db.def_file(def)?;
    let def_loc = db.idefs.get(def);
    if def_loc.parent() != Some(file_def) {
        // The parent will have elaborated child defs, so find that and return it
        let elab = db.elab.def_value(def_loc.parent()?, db).ok()?;
        let (_, elab) = elab.def.children.iter().find(|(d, _)| *d == def)?;
        return Some(DefElabResult {
            def: elab.clone(),
            unsolved_metas: default(),
            solved_metas: default(),
            errors: default(),
        });
    }
    let name = def_loc.name();
    let parsed = db.file_ast(file);
    let pre = parsed.defs.iter().find(|d| *d.name() == name)?;

    eprintln!("[elab def {}]", def.pretty(db));

    let mut cxt = Cxt::new(def, AbsSpan(file, pre.name().span()), db.clone());
    let def_elab = match &**pre {
        PreDef::Val { name, ty, value } => {
            let ty = ty
                .as_ref()
                .map(|ty| cxt.as_eval(|| ty.check(Val::Type, &cxt)));
            let solved_ty = match &ty {
                Some(ty) => {
                    let ty = ty.eval(cxt.env()).zonk(&cxt, true);
                    cxt.solve_meta(Meta(def, 0), &vec![], ty, Some(name.span()));
                    true
                }
                None => false,
            };
            let (mut body, ty) = if let Some((val, ty)) = value.as_ref().map(|val| match &ty {
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
                    "definition does not have a body: `"
                        + name.pretty(db)
                        + "` of type "
                        + ty.pretty(db),
                    name.span(),
                );
            }

            cxt.current_deps
                .take()
                .check(&cxt, value.as_ref().map_or(name.span(), |x| x.span()));

            // Solve unsolved regions to '()
            cxt.metas.with_mut(|m| {
                m.iter_mut().for_each(|(m, e)| match e {
                    MetaEntry::Unsolved(t, _)
                        if matches!(**t, Val::Neutral(Head::Builtin(Builtin::Region), _)) =>
                    {
                        *e = MetaEntry::Solved(Arc::new(Val::Region(Vec::new())))
                    }
                    _ => (),
                })
            });

            body.as_mut().map(|x| x.zonk(&cxt, false));
            let ty = ty.zonk(&cxt, true);
            if !solved_ty {
                let ety = Val::Neutral(Head::Meta(Meta(def, 0)), default()).zonk(&cxt, true);
                if !ty
                    .clone()
                    .glued()
                    .unify(None, ety.clone().glued(), None, name.span(), &cxt)
                {
                    cxt.err(
                        "definition body has type "
                            + ty.pretty(&cxt.db)
                            + " but definition was previously inferred to have type "
                            + ety.pretty(&cxt.db),
                        name.span(),
                    );
                }
            }

            DefElab {
                name: *name,
                ty: Arc::new(ty),
                body: body.map(|x| DefBody::Val(Arc::new(x))),
                can_eval: cxt.can_eval.take().is_none(),
                children: Vec::new(),
            }
        }
        PreDef::Type {
            name,
            args,
            variants,
        } => {
            let before_cxt = cxt.clone();
            let m: Vec<_> = args
                .iter()
                .map(|(icit, arg)| (*icit, PMatch::new(None, &[arg.clone()], None, &mut cxt)))
                .collect();
            let ty = m
                .iter()
                .rfold(Term::Type, |acc, (i, (s, m))| {
                    let aty = m.ty.quote(cxt.qenv());
                    let body = m.compile(&[acc], &cxt);
                    Term::fun(Pi(FCap::Imm), *i, *s, None, aty, Arc::new(body))
                })
                .eval(cxt.env())
                .zonk(&cxt, true);
            cxt.solve_meta(Meta(def, 0), &vec![], ty.clone(), Some(name.span()));

            let mut children = Vec::new();
            for (vname, vargs, vty) in variants {
                let vty = match vty {
                    Some(vty) => {
                        if vargs.is_some() {
                            cxt.err(
                                "parameters to constructor should come after :",
                                vargs.as_ref().unwrap().1.span(),
                            );
                        }
                        // TODO check for correct return type
                        vty.check(Val::Type, &before_cxt)
                    }
                    None => {
                        let mut cxt = cxt.clone();
                        for (_, (_, m)) in &m {
                            cxt = m.bind(0, &default(), &cxt);
                        }
                        let rty = m
                            .iter()
                            .fold(Term::Head(Head::Def(def)), |acc, (i, (s, _))| {
                                Term::App(
                                    Box::new(acc),
                                    TElim::App(*i, Box::new(Term::Head(Head::Sym(*s)))),
                                )
                            });
                        let vty = vargs.as_ref().map_or(rty.clone(), |(i, paty)| {
                            let aty = cxt.as_eval(|| paty.check(Val::Type, &cxt));
                            let vaty = aty.eval(cxt.env());
                            let (s, cxt) = cxt.bind(db.name("_"), vaty.clone());
                            let body = pat_bind_type(
                                &paty,
                                Val::Neutral(Head::Sym(s), default()),
                                &vaty,
                                &cxt,
                                |_| rty,
                            );
                            Term::fun(Pi(FCap::Imm), *i, s, None, aty, Arc::new(body))
                        });
                        m.iter().rfold(vty, |acc, (_, (s, m))| {
                            let aty = m.ty.quote(cxt.qenv());
                            let body = m.compile(&[acc], &cxt);
                            Term::fun(Pi(FCap::Imm), Impl, *s, None, aty, Arc::new(body))
                        })
                    }
                };
                let vty = vty.eval(cxt.env()).zonk(&cxt, true);
                children.push((
                    // TODO error on duplicate names
                    db.idefs.intern(&DefLoc::Child(def, **vname)),
                    DefElab {
                        name: *vname,
                        ty: Arc::new(vty),
                        body: None,
                        can_eval: false,
                        children: default(),
                    },
                ));
            }
            let ty = ty.zonk(&cxt, true);
            // Re-zonk metas in variant types to make sure we get them all
            for (_, elab) in &mut children {
                elab.ty = Arc::new(elab.ty.zonk(&cxt, true));
            }

            DefElab {
                name: *name,
                ty: Arc::new(ty),
                body: Some(DefBody::Type(children.iter().map(|(x, _)| *x).collect())),
                can_eval: false,
                children,
            }
        }
    };
    Some(DefElabResult {
        def: def_elab,
        unsolved_metas: cxt.metas.with(|m| {
            m.iter()
                .filter_map(|(m, v)| match v {
                    MetaEntry::Unsolved(t, source) => Some((*m, *source, t.clone())),
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

impl Val {
    fn is_owned(&self) -> bool {
        match self {
            Val::Neutral(Head::Builtin(Builtin::Region), v) if v.is_empty() => false,
            Val::Neutral(_, _) => true,
            Val::Fun(VFun {
                class: Sigma(_),
                psym: s,
                pty: a,
                ..
            }) => a.is_owned() || self.clone().app(Val::sym(*s)).is_owned(),
            Val::Fun(VFun { class: Pi(c), .. }) => *c == FCap::Own,
            Val::Fun { .. } => true,
            Val::Pair(_, _) | Val::Region(_) | Val::Borrow(_) => unreachable!(),
            Val::Cap(c, _, t) => *c != Cap::Imm && t.is_owned(),
            Val::Unknown => true,
            Val::Error => false,
            Val::Type => false,
        }
    }
}

#[derive(Clone)]
struct VarEntry {
    name: Name,
    sym: Sym,
    ty: Arc<Val>,
    invalidated: Ref<Option<Span>>,
    deps: Ref<Region>,
    borrow_gen_imm: Ref<(u32, Span)>,
    borrow_gen_mut: Ref<(u32, Span)>,
    mutable: bool,
}
enum VarResult<'a> {
    Local(Span, &'a VarEntry),
    Other(Term, Arc<Val>),
}
impl VarResult<'_> {
    fn ty(&self) -> &Val {
        match self {
            VarResult::Local(_, entry) => &entry.ty,
            VarResult::Other(_, ty) => &ty,
        }
    }
    fn access(self, cap: Cap, cxt: &Cxt) -> (Term, Arc<Val>) {
        match self {
            VarResult::Local(span, entry) => {
                // Before we do anything else, make sure this variable is still valid!
                entry.deps.with(|x| x.check(cxt, span));
                let is_owned = (*entry.ty).clone().glued().whnf(cxt).is_owned();
                if is_owned {
                    if let Some(ispan) = entry.invalidated.get() {
                        cxt.errors.push(
                            Error::simple(
                                "tried to access variable "
                                    + entry.name.pretty(&cxt.db)
                                    + " which has already been consumed",
                                span,
                            )
                            .with_secondary(Label {
                                span: ispan,
                                message: "variable "
                                    + entry.name.pretty(&cxt.db)
                                    + " was consumed here",
                                color: Some(Doc::COLOR2),
                            }),
                        );
                    } else if cap == Cap::Own {
                        entry.invalidated.set(Some(span));
                    }
                    if cap >= Cap::Mut {
                        entry.borrow_gen_imm.with_mut(|x| *x = (x.0 + 1, span));
                    }
                    entry.borrow_gen_mut.with_mut(|x| *x = (x.0 + 1, span));
                }
                if entry.mutable && cxt.can_eval.with(Option::is_none) {
                    cxt.can_eval.set(Some(span));
                }
                if cap == Cap::Mut && !entry.mutable {
                    cxt.err(
                        "cannot borrow immutable variable "
                            + entry.name.pretty(&cxt.db)
                            + " as "
                            + Doc::keyword("mut"),
                        span,
                    );
                }
                let acap = if is_owned || cap == Cap::Mut {
                    cap
                } else {
                    Cap::Imm
                };
                for (set, map) in &cxt.closure_stack {
                    if set.contains(&entry.sym) {
                        map.with_mut(|map| match map.get_mut(&entry.sym) {
                            None => {
                                map.insert(entry.sym, (span, acap));
                            }
                            Some((_, c)) if *c >= acap => (),
                            Some(c) => {
                                *c = (span, acap);
                            }
                        });
                    }
                }
                // Re-mutate all the mutable borrows in `entry.deps`
                // TODO we re-access immutably too right
                let deps = entry.deps.with(|edeps| {
                    let mut deps = edeps.clone();
                    for (s, v) in deps.borrows.iter_mut() {
                        cxt.vars.get(s).unwrap().borrow_gen_mut.with_mut(|x| {
                            let old = *x;
                            let g = {
                                *x = (x.0 + 1, span);
                                x.0
                            };
                            if let Some(m) = &mut v.mut_gen {
                                // don't suppress borrow errors though
                                if *m == g - 1 {
                                    *m = g;
                                } else {
                                    *x = old;
                                }
                            }
                        });
                        if v.mutable() {
                            cxt.vars.get(s).unwrap().borrow_gen_imm.with_mut(|x| {
                                let old = *x;
                                let g = {
                                    *x = (x.0 + 1, span);
                                    x.0
                                };
                                // don't suppress borrow errors though
                                if v.imm_gen == g - 1 {
                                    v.imm_gen = g;
                                } else {
                                    *x = old;
                                }
                            });
                        }
                    }
                    if is_owned && acap < Cap::Own {
                        deps.add(
                            Region::from(Borrow {
                                sym: entry.sym,
                                span,
                                imm_gen: entry.borrow_gen_imm.get().0,
                                mut_gen: (acap == Cap::Mut).then(|| entry.borrow_gen_mut.get().0),
                            }),
                            cxt,
                        );
                    }
                    deps
                });
                let mut ty = (*entry.ty).clone().as_cap(if is_owned || acap == Cap::Mut {
                    acap
                } else {
                    Cap::Own
                });

                cxt.add_deps(deps.clone());
                if let Val::Cap(_, Some(r), _) = &mut ty {
                    // eprintln!(
                    //     "{} / {}",
                    //     Val::Region(r.clone()).pretty(&cxt.db),
                    //     Val::Region(deps.values()).pretty(&cxt.db)
                    // );
                    *r = Region::from_val(r.clone(), &default(), cxt)
                        .tap_mut(|r| r.add(deps, cxt))
                        .values();
                    // eprintln!("-> {}", Val::Region(r.clone()).pretty(&cxt.db));
                    //r.extend(deps.values);
                }

                (Term::Head(Head::Sym(entry.sym)), Arc::new(ty))
            }
            VarResult::Other(term, ty) => (term, ty),
        }
    }
}

impl Region {
    /// returns whether we're okay
    fn check(&self, cxt: &Cxt, span: Span) -> bool {
        let mut okay = true;
        for (s, b) in &self.borrows {
            if let Some(e) = cxt.vars.get(&s) {
                if e.borrow_gen_imm.get().0 > b.imm_gen {
                    okay = false;
                    cxt.errors.push(
                        Error::simple(
                            "this expression borrows "
                                + s.0.pretty(&cxt.db)
                                + " which has been mutated or consumed",
                            span,
                        )
                        .with_secondary(Label {
                            span: e.borrow_gen_imm.get().1,
                            message: s.0.pretty(&cxt.db) + " was mutated or consumed here",
                            color: Some(Doc::COLOR2),
                        })
                        .with_secondary(Label {
                            span: b.span,
                            message: s.0.pretty(&cxt.db) + " was borrowed here",
                            color: Some(Doc::COLOR3),
                        }),
                    );
                }
                if let Some(g) = b.mut_gen {
                    if e.borrow_gen_mut.get().0 > g {
                        okay = false;
                        cxt.errors.push(
                            Error::simple(
                                "cannot access "
                                    + s.0.pretty(&cxt.db)
                                    + " while it is mutably borrowed",
                                e.borrow_gen_mut.get().1,
                            )
                            .with_secondary(Label {
                                span: span,
                                message: s.0.pretty(&cxt.db) + " mutable borrow later used here",
                                color: Some(Doc::COLOR2),
                            })
                            .with_secondary(Label {
                                span: b.span,
                                message: s.0.pretty(&cxt.db) + " was mutably borrowed here",
                                color: Some(Doc::COLOR3),
                            }),
                        );
                    }
                }
            } else {
                okay = false;
                cxt.errors.push(Error::simple(
                    "internal error: couldnt find " + s.0.pretty(&cxt.db),
                    b.span,
                ));
            }
        }
        okay
    }
}

#[derive(Clone)]
struct Cxt {
    db: DB,
    def: Def,
    bindings: im::HashMap<Name, Sym>,
    vars: im::HashMap<Sym, VarEntry>,
    metas: Ref<FxHashMap<Meta, MetaEntry>>,
    zonked_metas: Ref<FxHashMap<(Meta, bool), Val>>,
    env: SEnv,
    uquant_stack: Ref<Vec<Vec<(Sym, Arc<Val>)>>>,
    closure_stack: Vec<(Arc<FxHashSet<Sym>>, Ref<FxHashMap<Sym, (Span, Cap)>>)>,
    current_deps: Ref<Region>,
    rself: Option<Sym>,
    can_eval: Ref<Option<Span>>,
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
        .collect::<FxHashMap<_, _>>()
        .into();
        Cxt {
            def: context,
            db,
            bindings: default(),
            vars: default(),
            errors: env.qenv.errors.clone(),
            env,
            metas,
            uquant_stack: default(),
            closure_stack: default(),
            current_deps: default(),
            rself: None,
            can_eval: default(),
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
    fn push_closure(&mut self, ignore: Sym) {
        let hs = self.vars.keys().copied().filter(|x| *x != ignore).collect();
        self.closure_stack.push((Arc::new(hs), default()));
    }
    fn pop_closure(&mut self) -> Option<FxHashMap<Sym, (Span, Cap)>> {
        self.closure_stack.pop().map(|(_, x)| x.take())
    }
    fn as_eval<R>(&self, f: impl FnOnce() -> R) -> R {
        let old = self.can_eval.take();
        let r = f();
        if let Some(span) = self.can_eval.set(old) {
            self.err("cannot access mutable variables in types", span);
        }
        r
    }
    fn maybe_as_eval<R>(&self, f: impl FnOnce() -> R) -> (Option<Span>, R) {
        let old = self.can_eval.take();
        let r = f();
        (self.can_eval.set(old), r)
    }

    fn add_deps(&self, deps: Region) {
        self.current_deps.with_mut(|t| t.add(deps, self))
    }
    fn record_deps<R>(&self, f: impl FnOnce() -> R) -> (Region, R) {
        let before = self.current_deps.take();
        let r = f();
        (self.current_deps.set(before), r)
    }

    fn lookup(&self, n: SName) -> Option<VarResult> {
        // first try locals
        self.bindings
            .get(&n.0)
            .and_then(|s| self.vars.get(s))
            .map(|entry| VarResult::Local(n.span(), entry))
            .or_else(|| {
                self.db.lookup_def_name(self.def, n.0).map(|(d, t)| {
                    VarResult::Other(
                        Term::Head(Head::Def(d)),
                        match t {
                            Some(t) => t.clone(),
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
                            .find(|(s, _)| s.0 == n.0)
                            .map(|(s, v)| (*s, v.clone()))
                    })
                    .or_else(|| {
                        if self.uquant_stack.with(|v| v.is_empty()) {
                            return None;
                        }
                        let ty =
                            Arc::new(self.new_meta(Val::Type, MetaSource::TypeOf(n.0), n.span()));
                        self.uquant_stack.with_mut(|v| {
                            v.last_mut().map(|v| {
                                assert!(!v.iter().any(|(s, _)| s.0 == n.0));
                                let s = self.scxt().bind(n.0);
                                v.push((s, ty.clone()));
                                (s, ty)
                            })
                        })
                    })?;
                Some(VarResult::Other(Term::Head(Head::Sym(sym)), ty))
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
    fn get_deps(&self, s: Sym) -> Region {
        let e = self.vars.get(&s).unwrap();
        e.deps.with(Clone::clone)
    }
    fn set_deps(&self, s: Sym, deps: Region) {
        let e = self.vars.get(&s).unwrap();
        e.deps.set(deps);
    }
    fn set_mutable(&mut self, s: Sym, mutable: bool) {
        let e = self.vars.get_mut(&s).unwrap();
        if !mutable && e.mutable {
            eprintln!(
                "internal warning: un-mutable-ing {}.{}",
                s.0.pretty(&self.db),
                s.num()
            )
        }
        e.mutable = mutable;
    }
    fn bind_existing_var(&mut self, n: Name, sym: Sym) {
        self.bindings.insert(n, sym);
    }
    fn bind_raw(&mut self, name: Name, sym: Sym, ty: impl Into<Arc<Val>>) -> Sym {
        self.env.env.0.insert(sym, Arc::new(Val::sym(sym)));
        self.bindings.insert(name, sym);
        assert!(
            self.vars
                .insert(
                    sym,
                    VarEntry {
                        name,
                        sym,
                        invalidated: default(),
                        ty: ty.into(),
                        deps: default(),
                        borrow_gen_imm: (0, Span(0, 0)).into(),
                        borrow_gen_mut: (0, Span(0, 0)).into(),
                        mutable: false,
                    },
                )
                .is_none(),
            "sym {}.{} has already been bound in this cxt",
            sym.0.pretty(&self.db),
            sym.num(),
        );
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
        if let Val::Fun(VFun {
            class: Sigma(_),
            pty: aty,
            ..
        }) = &ty
        {
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
            self.vars
                .keys()
                .copied()
                .chain(self.uquant_stack.with(|v| {
                    v.iter()
                        .flatten()
                        .map(|(s, _)| s)
                        .copied()
                        .collect::<Vec<_>>()
                }))
                .map(|s| VElim::App(Expl, Arc::new(Val::sym(s))))
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
                // TODO occurs check, this keeps coming up
                let term = spine.iter().zip(syms).rfold(body, |acc, (_, s)| {
                    Term::fun(
                        Lam,
                        Expl,
                        s.unwrap_or(self.scxt().bind(self.db.name("_"))),
                        None,
                        Term::Error,
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
                    .unify_(None, (**y).clone().glued(), None, span, cxt, mode)
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
                    for (&(_, s1), &(_, s2)) in v1.iter().zip(v2) {
                        let s = cxt.scxt().bind(s1.0);
                        env1.0
                            .insert(s1, Arc::new(Val::Neutral(Head::Sym(s), default())));
                        env2.0
                            .insert(s2, Arc::new(Val::Neutral(Head::Sym(s), default())));
                    }
                    if !t1.eval(&env1).glued().unify_(
                        None,
                        t2.eval(&env2).glued(),
                        None,
                        span,
                        cxt,
                        mode,
                    ) {
                        return false;
                    }
                }
                if let Some(fallback1) = fallback1 {
                    let fallback2 = fallback2.as_ref().unwrap();
                    if !fallback1.eval(env1).glued().unify(
                        None,
                        fallback2.eval(env2).glued(),
                        None,
                        span,
                        cxt,
                    ) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }
}

fn unify_regions(
    r: &Vec<Arc<Val>>,
    r2: &Vec<Arc<Val>>,
    span: Span,
    cxt: &Cxt,
    mode: UnfoldState,
) -> bool {
    // if mode == UnfoldState::Maybe {
    //     return unify_regions(r, r2, span, cxt, UnfoldState::No)
    //         || unify_regions(r, r2, span, cxt, UnfoldState::Yes);
    // }
    let (mut r, mut r2) = (r.clone(), r2.clone());
    // if mode == UnfoldState::Yes {
    //     r.whnf(cxt);
    //     r2.whnf(cxt);
    // }

    loop {
        if r.len() == 1 {
            return (*r[0]).clone().glued().unify_(
                None,
                Val::Region(r2).glued(),
                None,
                span,
                cxt,
                mode,
            );
        }
        if r2.len() == 1 {
            return Val::Region(r).glued().unify_(
                None,
                (*r2[0]).clone().glued(),
                None,
                span,
                cxt,
                mode,
            );
        }
        if r.is_empty() || r2.is_empty() {
            return r.is_empty() && r2.is_empty();
        }
        let a = (*r.pop().unwrap()).clone().glued();
        let mut found = false;
        for i in 0..r2.len() {
            if a.clone()
                .unify_(None, (*r2[i]).clone().glued(), None, span, cxt, mode)
            {
                r2.remove(i);
                found = true;
                break;
            }
        }
        if !found {
            return false;
        }
    }
}

impl GVal {
    fn unify(
        self,
        ra: impl Into<Option<Vec<Arc<Val>>>>,
        other: GVal,
        rb: impl Into<Option<Vec<Arc<Val>>>>,
        span: Span,
        cxt: &Cxt,
    ) -> bool {
        self.unify_(ra.into(), other, rb.into(), span, cxt, UnfoldState::Maybe)
    }
    fn unify_(
        self,
        mut ra: Option<Vec<Arc<Val>>>,
        other: GVal,
        mut rb: Option<Vec<Arc<Val>>>,
        span: Span,
        cxt: &Cxt,
        mut mode: UnfoldState,
    ) -> bool {
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
                (Val::Fun(f), Val::Fun(f2))
                    if (f.class == f2.class
                        || matches!((f.class, f2.class), (Sigma(_), Sigma(_))))
                        && f.icit == f2.icit =>
                {
                    let s = cxt.scxt().bind(f.psym.0);
                    let arg = Val::Neutral(Head::Sym(s), default());
                    if !(*f.pty).clone().glued().unify_(
                        ra.clone(),
                        (*f2.pty).clone().glued(),
                        rb.clone(),
                        span,
                        cxt,
                        mode,
                    ) {
                        false
                    } else {
                        a = a.as_big().app(arg.clone()).glued();
                        b = b.as_big().app(arg).glued();
                        mode = UnfoldState::Maybe;
                        continue;
                    }
                }
                (Val::Cap(c, r, t), Val::Cap(c2, r2, t2))
                    if *c == *c2
                        && r.as_ref().map_or(r2.is_none(), |r| {
                            r2.is_some() && unify_regions(r, r2.as_ref().unwrap(), span, cxt, mode)
                        }) =>
                {
                    a = (**t).clone().glued();
                    b = (**t2).clone().glued();
                    continue;
                }
                (Val::Region(r), Val::Region(r2)) => unify_regions(r, r2, span, cxt, mode),
                (Val::Region(r), _) if r.len() == 1 => {
                    a = (*r[0]).clone().glued();
                    continue;
                }
                (_, Val::Region(r)) if r.len() == 1 => {
                    b = (*r[0]).clone().glued();
                    continue;
                }
                (Val::Cap(Cap::Own, None, rest), _) => {
                    a = (**rest).clone().glued();
                    continue;
                }
                (_, Val::Cap(Cap::Own, None, rest)) => {
                    b = (**rest).clone().glued();
                    continue;
                }
                (Val::Cap(c, Some(r), rest), _)
                    if rb.is_some() && unify_regions(r, rb.as_ref().unwrap(), span, cxt, mode) =>
                {
                    ra = Some(r.clone());
                    a = Val::Cap(*c, None, rest.clone()).glued();
                    continue;
                }
                (_, Val::Cap(c, Some(r), rest))
                    if ra.is_some() && unify_regions(ra.as_ref().unwrap(), r, span, cxt, mode) =>
                {
                    rb = Some(r.clone());
                    b = Val::Cap(*c, None, rest.clone()).glued();
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
                (
                    Val::Fun(VFun {
                        class: Lam,
                        psym: n,
                        ..
                    }),
                    _,
                )
                | (
                    _,
                    Val::Fun(VFun {
                        class: Lam,
                        psym: n,
                        ..
                    }),
                ) => {
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
    match ty.whnf(cxt).uncap().2 {
        Val::Fun(VFun {
            class: Pi(_),
            icit: Impl,
            psym: n,
            pty: aty,
            ..
        }) => {
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
        let (vsym, deps, t, p, x, span) = match x {
            PreStmt::Expr(x) => {
                let span = x.span();
                let (deps, (x, xty)) = cxt.record_deps(|| x.infer(&cxt, true));
                let vsym = cxt.bind_(cxt.db.name("_"), xty.small().clone());
                (vsym, deps, xty.as_small(), None, x, span)
            }
            PreStmt::Let(pat, body) if matches!(&***pat, PrePat::Binder(_, _)) => {
                let span = body.span();
                let cxt_start = cxt.clone();
                let (sym, pat) = PMatch::new(None, &[pat.clone()], None, &mut cxt);
                let aty = (*pat.ty).clone();
                let (deps, body) = cxt.record_deps(|| body.check(aty.clone(), &cxt_start));
                (sym, deps, aty, Some(pat), body, span)
            }
            PreStmt::Let(pat, body) => {
                let span = body.span();
                let (deps, (body, aty)) = cxt.record_deps(|| body.infer(&cxt, true));
                let (sym, pat) = PMatch::new(Some(aty.clone()), &[pat.clone()], None, &mut cxt);
                (sym, deps, aty.as_small(), Some(pat), body, span)
            }
        };
        let deps = t
            .uncap()
            .1
            .map(|v| Region::from_val(v, &deps, &cxt))
            .unwrap_or(deps);
        deps.check(&cxt, span);
        let t2 = t.quote(&cxt.qenv());
        if let Some(p) = &p {
            cxt = p.bind(0, &deps, &cxt);
            cxt.set_deps(vsym, deps);
        }
        v.push((vsym, t2, p, x));
    }
    let explicit_ty = ty.is_some();
    // give better error messages on block return dependencies
    let (r, (last, lty)) = cxt.record_deps(|| last_.elab(ty, &cxt));
    // we don't need the errors twice though
    if r.check(&cxt, last_.span()) {
        cxt.add_deps(r);
    }
    let mut lty = lty.as_small();
    let term = v.into_iter().rfold(last, |acc, (s, t, p, x)| {
        let acc = match p {
            Some(p) => p.compile(&[acc], &cxt),
            None => acc,
        };
        Term::App(
            Box::new(Term::fun(Lam, Expl, s, None, t, Arc::new(acc))),
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
    fn insert_par_regions(&self, name: Name, bucket: &mut Vec<Name>, db: &DB) -> SPre {
        match &***self {
            Pre::Sigma(i, n1, left, n2, right) => S(
                Box::new(Pre::Sigma(
                    *i,
                    *n1,
                    left.insert_par_regions(
                        n1.as_deref().copied().unwrap_or_else(|| db.name("_")),
                        bucket,
                        db,
                    ),
                    *n2,
                    right.insert_par_regions(
                        n2.as_deref().copied().unwrap_or_else(|| db.name("_")),
                        bucket,
                        db,
                    ),
                )),
                self.span(),
            ),
            Pre::RegionAnn(_, _) => self.clone(),
            _ => {
                let name = db.name(&format!("'{}", db.get(name)));
                bucket.push(name);
                S(
                    Box::new(Pre::RegionAnn(
                        vec![S(Box::new(Pre::Var(name)), self.span())],
                        self.clone(),
                    )),
                    self.span(),
                )
            }
        }
    }
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
        with_stack(|| self.infer_(cxt, should_insert_metas, Cap::Own))
    }
    fn infer_(&self, cxt: &Cxt, mut should_insert_metas: bool, borrow_as: Cap) -> (Term, GVal) {
        let (s, sty) = match &***self {
            Pre::Var(name) if cxt.db.name("_") == *name => {
                // hole
                let mty = cxt.new_meta(Val::Type, MetaSource::TypeOf(*name), self.span());
                let m = cxt
                    .new_meta(mty.clone(), MetaSource::Hole, self.span())
                    .quote(&cxt.qenv());
                (m, mty)
            }
            // TODO proper builtin name lookup
            Pre::Var(name) if cxt.db.name("Region") == *name => {
                (Term::Head(Head::Builtin(Builtin::Region)), Val::Type)
            }
            Pre::Var(name) if cxt.db.name("'self") == *name => match cxt.rself {
                Some(s) => (Term::Head(Head::Sym(s)), Builtin::Region.into()),
                None => {
                    cxt.err("'self used outside a function type", self.span());
                    (Term::Error, Val::Error)
                }
            },
            Pre::Var(name) => match cxt.lookup(S(*name, self.span())) {
                Some(entry) => {
                    let (term, ty) = entry.access(borrow_as, cxt);
                    (term, Arc::unwrap_or_clone(ty))
                }
                None => {
                    cxt.err("name not found: " + name.pretty(&cxt.db), self.span());
                    (Term::Error, Val::Error)
                }
            },
            Pre::Unit => (Builtin::Unit.into(), Builtin::UnitType.into()),
            Pre::App(fs, x, i) => {
                let (fr, (mut f, mut fty)) = cxt.record_deps(|| fs.infer(cxt, *i == Expl));
                let (fc, fr_, vfty) = fty.whnf(cxt).uncap();
                let aty = match vfty {
                    Val::Error => Val::Error,
                    // TODO: calling `-1 (+1 t, +0 u) -> ()` with `(+0 t, +0 u)` should be fine, right?
                    // TODO: and also how does this affect the surplus of the result?
                    Val::Fun(VFun {
                        class: Pi(c),
                        icit: i2,
                        pty: aty,
                        ..
                    }) if i == i2 && fc >= c.cap() => (**aty).clone(),
                    Val::Fun(VFun { class: Pi(c), .. }) if fc >= c.cap() => {
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
                    Val::Fun(VFun {
                        class: Pi(FCap::Own),
                        ..
                    }) if fc < Cap::Own => {
                        cxt.err(
                            "cannot call owned ~> function through "
                                + Doc::keyword(fc)
                                + " reference of type "
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
                            Val::fun(
                                Pi(FCap::Imm),
                                *i,
                                s,
                                Arc::new(m1.clone()),
                                None, // TODO does 'self make sense here?
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
                let (mut r, (can_eval, x)) =
                    cxt.record_deps(|| cxt.maybe_as_eval(|| x.check(aty, cxt)));
                // put it back - if we can't eval the argument, we can't eval the whole thing
                if can_eval.is_some() && cxt.can_eval.get().is_none() {
                    cxt.can_eval.set(can_eval);
                }
                r.add(fr.clone(), cxt);
                for (s, b) in &r.borrows {
                    if b.mutable() {
                        // if we depend on `mut x`, then all the other dependencies get added to `x`'s dependencies
                        let mut deps = cxt.get_deps(*s);
                        let mut r2 = r.clone();
                        // it doesn't depend on itself tho
                        r2.borrows.remove(s);
                        deps.add(r2, cxt);
                        cxt.set_deps(*s, deps);
                    }
                }
                let vx = if can_eval.is_none() {
                    x.eval(cxt.env())
                } else {
                    Val::Unknown
                };
                let rty = fty.as_small().app_rself(vx, Val::Region(fr.values()));
                if let (_, Some(r2), _) = rty.uncap() {
                    cxt.add_deps(Region::from_val(r2, &r, cxt));
                } else {
                    cxt.add_deps(r);
                }
                (Term::App(Box::new(f), TElim::App(*i, Box::new(x))), rty)
            }
            Pre::Pi(i, n, c, paty, body) => {
                let q = !cxt.has_uquant();
                if q {
                    cxt.push_uquant();
                }
                //let mut borrows = Vec::new();

                let (rself_sym, mut cxt) =
                    cxt.bind(cxt.db.name("'self"), Arc::new(Builtin::Region.into()));
                cxt.rself = Some(rself_sym);
                // let ra = cxt.bind_(cxt.db.name("'_"), Arc::new(Builtin::Region.into()));

                //let paty = paty.insert_par_regions(*n, &mut borrows, &cxt.db);
                let aty = cxt.as_eval(|| paty.check(Val::Type, &cxt));
                let vaty = aty.eval(cxt.env());
                //.with_region(Some(vec![Arc::new(Val::sym(ra))]));
                let aty = vaty.quote(cxt.qenv());
                let (s, cxt) = cxt.bind(*n, vaty.clone());
                let body = pat_bind_type(
                    &paty,
                    Val::Neutral(Head::Sym(s), default()),
                    &vaty,
                    &cxt,
                    |cxt| {
                        // we don't want just leaving off the return type (which then generates a hole) to mean anything about the return region, that should be inferred
                        // let body = if matches!(&***body, Pre::RegionAnn(_, _))
                        //     || matches!(&***body, Pre::Var(v) if *v == cxt.db.name("_"))
                        // {
                        //     body.clone()
                        // } else {
                        //     // TODO:
                        //     // (_: a, _: b) -> a
                        //     // ->
                        //     // (_: '_ a, _: '_ b) -> '_ '_ a
                        //     // but this is a *presyntax* transformation - those '_s aren't separate, they're literally the same variable!
                        //     // which... is not really what we want, to be *perfectly* honest.
                        //     // partly because '_ should never be the same variable as another '_ - it's the *anonymous* lifetime.
                        //     // and partly because, even if you have `(x: a, x: b)`, we probably shouldn't do this transformation at presyntax -
                        //     // we should do it in actual syntax, or at least have some way of keeping the two `'x`s separate.
                        //     // basicanlly, this should be hygienic in the macro sense, and the way we are currently doing it is not.
                        //     S(
                        //         Box::new(Pre::RegionAnn(
                        //             borrows
                        //                 .into_iter()
                        //                 .map(|x| S(Box::new(Pre::Var(x)), body.span()))
                        //                 // also include 'self on the return type by default
                        //                 .chain(std::iter::once(S(
                        //                     Box::new(Pre::Var(cxt.db.name("'self"))),
                        //                     body.span(),
                        //                 )))
                        //                 .collect(),
                        //             body.clone(),
                        //         )),
                        //         body.span(),
                        //     )
                        // };
                        body.check(Val::Type, cxt)
                    },
                );
                let scope = q.then(|| cxt.pop_uquant().unwrap());
                (
                    scope
                        .into_iter()
                        .flatten()
                        // .chain(std::iter::once((ra, Arc::new(Builtin::Region.into()))))
                        .rfold(
                            Term::fun(Pi(*c), *i, s, Some(rself_sym), aty, Arc::new(body)),
                            |acc, (s, ty)| {
                                Term::fun(
                                    // use imm for the uquant pis
                                    Pi(FCap::Imm),
                                    Impl,
                                    s,
                                    None, // TODO what is the proper region assignment for uquant pis?
                                    ty.quote(cxt.qenv()),
                                    Arc::new(acc),
                                )
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
                let before_syms: FxHashSet<_> = cxt.vars.keys().copied().collect();
                let (s, pat) = PMatch::new(None, &[pat.clone()], None, &mut cxt2);
                let aty = pat.ty.clone();
                // // TODO do we need this region??
                // let ra = cxt2.bind_(cxt.db.name("'_"), Arc::new(Builtin::Region.into()));
                // let aty3 = (*pat.ty)
                //     .clone()
                //     .with_region(Some(vec![Arc::new(Val::sym(ra))]));
                let aty2 = aty.quote(cxt.qenv());

                cxt2.push_closure(s);
                let mut cxt3 = pat.bind(0, &default(), &cxt2);
                // TODO should we do anything with this dependency?
                let bspan = body.span();
                let (deps, (body, rty)) = cxt.record_deps(|| body.infer(&cxt3, true));
                deps.check(&cxt3, bspan);
                let cap = cxt3
                    .pop_closure()
                    .into_iter()
                    .flatten()
                    .any(|(_, (_, v))| v == Cap::Own)
                    .then_some(FCap::Own)
                    .unwrap_or(FCap::Imm);
                // non-unique closure return value can't have unique (mutable) dependencies (from outside the closure)
                // TODO should we instead just make this a ~> closure? probably?
                if cap == FCap::Imm {
                    if let Some((s, Borrow { span, .. })) = deps
                        .borrows
                        .iter()
                        .find(|(s, b)| b.mutable() && before_syms.contains(s))
                    {
                        cxt.err(
                            "immutable function -> cannot return value that borrows mutable "
                                + s.0.pretty(&cxt.db),
                            *span,
                        );
                    }
                }
                let rty = rty.small().quote(&cxt3.qenv());
                let body = pat.compile(&[body], &cxt2);
                let rty = pat.compile(&[rty], &cxt2);
                let scope = q.then(|| cxt.pop_uquant().unwrap());
                (
                    scope.iter().flatten().rfold(
                        Term::fun(Lam, *i, s, None, aty2.clone(), Arc::new(body)),
                        |acc, (s, ty)| {
                            // Don't introduce a redex, the user clearly intended to make a polymorphic lambda
                            should_insert_metas = false;
                            Term::fun(Lam, Impl, *s, None, ty.quote(cxt.qenv()), Arc::new(acc))
                        },
                    ),
                    scope
                        .into_iter()
                        .flatten()
                        .fold(
                            // TODO 'self region assignment
                            Term::fun(Pi(cap), *i, s, None, aty2, Arc::new(rty)),
                            |acc, (s, ty)| {
                                Term::fun(
                                    Pi(FCap::Imm),
                                    Impl,
                                    s,
                                    None,
                                    ty.quote(cxt.qenv()),
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
                    Val::fun(
                        Sigma(cxt.db.name("_")),
                        *i,
                        s,
                        aty,
                        None,
                        Arc::new(bty),
                        Arc::new(cxt.env().clone()),
                    ),
                )
            }
            Pre::Region(r) => {
                let r = r
                    .iter()
                    .map(|x| x.check(Val::from(Builtin::Region), cxt))
                    .collect();
                (Term::Region(r), Builtin::Region.into())
            }
            Pre::RegionAnn(r, x) => {
                let r = r
                    .iter()
                    .map(|x| x.check(Val::from(Builtin::Region), cxt))
                    .collect();
                let x = x.check(Val::Type, cxt);
                (
                    Term::RegionAnn(Box::new(Term::Region(r)), Box::new(x)),
                    Val::Type,
                )
            }
            // temporary desugaring (eventually we do need the larger structure for method syntax)
            Pre::Dot(lhs, dot, Some((icit, rhs))) => {
                return S(
                    Box::new(Pre::App(
                        S(Box::new(Pre::Dot(lhs.clone(), *dot, None)), self.span()),
                        rhs.clone(),
                        *icit,
                    )),
                    self.span(),
                )
                .infer_(cxt, should_insert_metas, borrow_as)
            }
            Pre::Dot(lhs, dot, None) => {
                let lspan = lhs.span();
                let (lhs, mut lty) = lhs.infer(cxt, true);
                // TODO this is messy
                let mut r = None;
                match lhs.eval(cxt.env()) {
                    Val::Neutral(Head::Def(d), v) if v.is_empty() => {
                        let child = cxt.db.idefs.intern(&DefLoc::Child(d, **dot));
                        match cxt.db.elab.def_type(child, &cxt.db) {
                            Ok(t) => r = Some((Term::Head(Head::Def(child)), (*t).clone())),
                            Err(crate::query::DefElabError::NotFound) => {
                                cxt.err(
                                    "definition "
                                        + lhs.pretty(&cxt.db)
                                        + " has no member "
                                        + dot.pretty(&cxt.db),
                                    lspan,
                                );
                                r = Some((Term::Error, Val::Error));
                            }
                            Err(crate::query::DefElabError::Recursive) => {
                                r = Some((
                                    Term::Head(Head::Def(child)),
                                    Val::Neutral(Head::Meta(Meta(child, 0)), default()),
                                ))
                            }
                        }
                    }
                    _ => (),
                }
                if let Some(r) = r {
                    r
                } else {
                    match lty.whnf(cxt) {
                        t => {
                            cxt.err(
                                "value of type " + t.pretty(&cxt.db) + " does not have members",
                                lspan,
                            );
                            (Term::Error, Val::Error)
                        }
                    }
                }
            }
            Pre::Case(x, branches) => {
                let span = x.span();
                let (xdeps, (x, xty)) = cxt.record_deps(|| x.infer(cxt, true));
                let pats: Vec<_> = branches.iter().map(|(a, _)| a.clone()).collect();
                let mut cxt = cxt.clone();
                let (s, p) = PMatch::new(Some(xty), &pats, Some(span), &mut cxt);
                let rty = cxt.new_meta(Val::Type, MetaSource::Hole, self.span());
                let mut bodies = Vec::new();
                for (i, (_, v)) in branches.iter().enumerate() {
                    if !p.reached(i as u32) {
                        // Really, this should probably be a warning, but that would require checking the body anyway for other type errors
                        // Which is not super easy to do with the current pattern matching system, so we're leaving this for now
                        cxt.err("unreachable match branch", v.span());
                        bodies.push(Term::Error);
                    } else {
                        let cxt = p.bind(i as u32, &xdeps, &cxt);
                        let v = v.check(rty.clone(), &cxt);
                        bodies.push(v);
                    }
                }
                let t = p.compile(&bodies, &cxt);
                // TODO do we need 'self regions here?
                let t = Term::fun(Lam, Expl, s, None, p.ty.quote(cxt.qenv()), Arc::new(t));
                (Term::App(Box::new(t), TElim::App(Expl, Box::new(x))), rty)
            }
            Pre::Assign(a, b) => {
                let (a, aty) = a.infer_(cxt, true, Cap::Mut);
                let ity = match aty.big() {
                    // TODO check that b region ⊆ r
                    Val::Cap(Cap::Mut, r, a) => (**a).clone(),
                    Val::Error => Val::Error,
                    _ => unreachable!("hopefully?"),
                };
                let b = b.check(ity.clone(), cxt);
                // returns the *previous* value
                (Term::Assign(Box::new(a), Box::new(b)), ity)
            }
            Pre::Cap(c, x) => {
                let x = x.check(Val::Type, cxt);
                (Term::Cap(*c, Box::new(x)), Val::Type)
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
        if should_insert_metas
            && !matches!(
                s,
                Term::Fun(TFun {
                    class: Lam,
                    icit: Impl,
                    ..
                })
            )
        {
            insert_metas(s, sty, cxt, self.span())
        } else {
            (s, sty)
        }
    }

    fn check(&self, ty: impl Into<GVal>, cxt: &Cxt) -> Term {
        let mut ty: GVal = ty.into();
        let (tcap, treg, t) = ty.whnf(cxt).uncap();
        let r = match (&***self, t) {
            (
                Pre::Lam(i, pat, body),
                Val::Fun(VFun {
                    class: Pi(c),
                    icit: i2,
                    pty: aty2,
                    psym,
                    ..
                }),
            ) if i == i2
                // if the pi has an implicit '_ region parameter, only match that one if the lambda also has a region variable '_
                // that way you can write `def t : {a} -> a = {a} => a` without accidentally matching on the anonymous region created by region inference
                && (*i == Expl
                    || !cxt.db.get(psym.0).starts_with("'")
                    || pat
                        .name()
                        .map_or(false, |n| cxt.db.get(n.0).starts_with("'"))) =>
            {
                let c = *c;
                let mut cxt = cxt.clone();
                let before_syms: FxHashSet<_> = cxt.vars.keys().copied().collect();
                let aty = aty2.quote(cxt.qenv());
                let ra = cxt.bind_(cxt.db.name("'_"), Arc::new(Builtin::Region.into()));
                let aty3 = (**aty2)
                    .clone()
                    .with_region(Some(vec![Arc::new(Val::sym(ra))]));
                let (sym, pat) =
                    PMatch::new(Some(aty3.clone().glued()), &[pat.clone()], None, &mut cxt);

                let va = Val::Neutral(Head::Sym(sym), default());
                // TODO why doesn't as_small() work here
                let rty = match treg.clone() {
                    None => ty.as_big().app(va.clone()),
                    Some(treg) => ty.as_big().app_rself(va.clone(), Val::Region(treg)),
                };
                cxt.push_closure(sym);
                let mut cxt = pat.bind(0, &default(), &cxt);
                // TODO should we do anything with this dependency?
                let bspan = body.span();
                let (deps, body) = cxt.record_deps(|| body.check(rty, &cxt));
                deps.check(&cxt, bspan);
                let (cs, (cspan, cap)) = cxt
                    .pop_closure()
                    .into_iter()
                    .flatten()
                    .find(|(_, (_, v))| *v == Cap::Own)
                    .unwrap_or((sym, (self.span(), Cap::Imm)));
                // non-unique closure return value can't have unique (mutable) dependencies (from outside the closure)
                if c == FCap::Imm {
                    if let Some((s, Borrow { span, .. })) = deps
                        .borrows
                        .iter()
                        .find(|(s, b)| b.mutable() && before_syms.contains(s))
                    {
                        cxt.err(
                            "immutable function -> cannot return value that borrows mutable "
                                + s.0.pretty(&cxt.db),
                            *span,
                        );
                    }
                }
                if cap > c.cap() {
                    cxt.errors.push(
                        Error::simple(
                            "lambda is expected to have capability "
                                + Doc::start(c)
                                + " but captures local "
                                + cs.0.pretty(&cxt.db)
                                + " with capability "
                                + Doc::start(cap),
                            self.span(),
                        )
                        .with_secondary(Label {
                            span: cspan,
                            message: "local "
                                + cs.0.pretty(&cxt.db)
                                + " captured here as "
                                + Doc::start(cap),
                            color: Some(Doc::COLOR2),
                        }),
                    );
                }
                let body = pat.compile(&[body], &cxt);
                Term::fun(Lam, *i, sym, None, aty, Arc::new(body))
            }
            // when checking pair against type, assume sigma
            (Pre::Sigma(i, n1, aty, n2, body), Val::Type) => {
                let n1 = n1.map(|x| *x).unwrap_or(cxt.db.name("_"));
                let n2 = n2.map(|x| *x).unwrap_or(cxt.db.name("_"));
                let aty = cxt.as_eval(|| aty.check(Val::Type, cxt));
                let vaty = aty.eval(cxt.env());
                let (s, cxt) = cxt.bind(n1, vaty);
                let body = body.check(Val::Type, &cxt);
                Term::fun(Sigma(n2), *i, s, None, aty, Arc::new(body))
            }
            (
                Pre::Sigma(i, None, a, None, b),
                Val::Fun(VFun {
                    class: Sigma(_),
                    icit: i2,
                    pty: aty,
                    ..
                }),
            ) if i == i2 => {
                let (can_eval, a) = cxt.maybe_as_eval(|| a.check((**aty).clone(), cxt));
                // put it back - if we can't eval the lhs, we can't eval the whole thing
                if can_eval.is_some() && cxt.can_eval.get().is_none() {
                    cxt.can_eval.set(can_eval);
                }
                let va = if can_eval.is_none() {
                    a.eval(&cxt.env())
                } else {
                    Val::Unknown
                };
                let rty = ty.as_small().app(va);
                let b = b.check(rty, cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }
            (Pre::Do(block, last), _) => return elab_block(block, last, Some(ty), cxt).0,
            (Pre::Unit, Val::Type) => Builtin::UnitType.into(),

            // insert lambda when checking (non-implicit lambda) against implicit function type
            (
                _,
                Val::Fun(VFun {
                    class: Pi(_),
                    icit: Impl,
                    psym: n,
                    pty: aty,
                    ..
                }),
            ) => {
                let aty2 = aty.quote(cxt.qenv());
                // don't let them access the name in the term (shadowing existing names would be unintuitive)
                // TODO that should be true but we're having problems with uquant in fun-definition syntax
                let n = n.0; //cxt.db.inaccessible(n.0);
                let mut cxt = cxt.clone();
                let (sym, cxt) = cxt.bind(n, aty.clone());
                let rty = ty.as_small().app(Val::Neutral(Head::Sym(sym), default()));
                let body = self.check(rty, &cxt);
                // TODO does 'self matter here?
                Term::fun(Lam, Impl, sym, None, aty2, Arc::new(body))
            }
            // and similar for implicit sigma
            (
                _,
                Val::Fun(VFun {
                    class: Sigma(_),
                    icit: Impl,
                    psym: n,
                    pty: aty,
                    ..
                }),
            ) => {
                let a = cxt
                    .new_meta((**aty).clone(), MetaSource::ImpArg(n.0), self.span())
                    .quote(&cxt.qenv());
                let va = a.eval(&cxt.env());
                let rty = ty.as_small().app(va);
                let b = self.check(rty, &cxt);
                Term::Pair(Box::new(a), Box::new(b))
            }

            (_, _) => {
                let (r, (s, sty)) = cxt.record_deps(|| {
                    self.infer_(
                        cxt,
                        !matches!(
                            ty.big(),
                            Val::Fun(VFun {
                                class: Pi(_),
                                icit: Impl,
                                ..
                            })
                        ),
                        tcap,
                    )
                });
                if !sty.clone().coerce(ty.clone(), r.clone(), self.span(), cxt) {
                    cxt.err(
                        "could not match types: expected "
                            + ty.small().zonk(cxt, true).pretty(&cxt.db)
                            + ", found "
                            + if ty.small().uncap().1.is_some() && !sty.small().uncap().1.is_some()
                            {
                                Val::Region(r.values()).pretty(&cxt.db) + " "
                            } else {
                                Doc::none()
                            }
                            + sty.small().zonk(cxt, true).pretty(&cxt.db),
                        self.span(),
                    );
                }
                return s;
            }
        };
        if let Some(treg) = treg {
            let creg = cxt.current_deps.with(Clone::clone);
            if !coerce_region(
                &creg,
                &Region::from_val(treg.clone(), &default(), cxt),
                self.span(),
                cxt,
            ) {
                cxt.err(
                    "could not match regions: expected "
                        + Val::Region(treg).pretty(&cxt.db)
                        + ", found "
                        + Val::Region(creg.values()).pretty(&cxt.db),
                    self.span(),
                );
            }
        }
        r
    }
}
fn coerce_region(from: &Region, to: &Region, span: Span, cxt: &Cxt) -> bool {
    // Necessary to deal with metas solved to borrows
    let mut from = from.clone();
    let mut to = to.clone();
    from.whnf(cxt);
    to.whnf(cxt);

    for (s, borrow) in &from.borrows {
        if !to.borrows.contains_key(s)
            || (!to.borrows.get(s).unwrap().mutable() && borrow.mutable())
        {
            // We can coerce away borrows by invalidating the thing we're borrowing so nobody can modify it (bc Pika has a GC, unlike Rust)
            cxt.vars[&borrow.sym].invalidated.set(Some(span));
        }
    }
    // if from.values.len() == 1 {
    //     return (*from.values[0]).clone().glued().unify(
    //         None,
    //         Val::Region(to.values.clone()).glued(),
    //         None,
    //         span,
    //         cxt,
    //     );
    // }
    // if to.values.len() == 1 {
    //     return (*to.values[0]).clone().glued().unify(
    //         None,
    //         Val::Region(from.values.clone()).glued(),
    //         None,
    //         span,
    //         cxt,
    //     );
    // }
    for v in &from.values {
        if to.values.iter().any(|v2| {
            (**v)
                .clone()
                .glued()
                .unify(None, (**v2).clone().glued(), None, span, cxt)
        }) {
            continue;
        } else {
            return false;
        }
    }
    true
}
impl GVal {
    pub(super) fn coerce(mut self, mut to: GVal, r: Region, span: Span, cxt: &Cxt) -> bool {
        let r = self
            .big()
            .uncap()
            .1
            .map(|x| Region::from_val(x, &r, cxt))
            .unwrap_or(r);
        if matches!((to.whnf(cxt), self.whnf(cxt)), (Val::Neutral(Head::Meta(m), v), Val::Cap(Cap::Own, r, _))
            if cxt.meta_val(*m).is_none()
            && r.iter().flatten().any(|p| matches!(&**p, Val::Neutral(Head::Sym(s), v2) if v2.is_empty() && !v.contains(&VElim::App(Expl, Arc::new(Val::sym(*s)))))))
        {
            // We're trying to solve `?1 a b c` to `'d t`, where `'d` is *not* in scope for `?1`
            // That's actually fine (since we know we're coercing - this needs to be here and not in `unify`), we just coerce `'d t` to `t`
            return self
                .as_big()
                .uncap()
                .2
                .clone()
                .glued()
                .coerce(to, r, span, cxt);
        }
        if !to.clone().unify(None, self.clone(), r.values(), span, cxt) {
            // Try to coerce if possible
            match (to.whnf(cxt), self.whnf(cxt)) {
                // demotion is always available
                (Val::Cap(_, r1, ty), _sty) if !matches!(_sty, Val::Cap(_, _, _)) => {
                    if r1.as_ref().map_or(true, |r1| {
                        coerce_region(
                            &r,
                            &Region::from_val(r1.clone(), &default(), cxt),
                            span,
                            cxt,
                        )
                    }) && (**ty).clone().glued().unify(
                        r1.clone(),
                        self.clone(),
                        r.values(),
                        span,
                        cxt,
                    ) {
                        cxt.add_deps(r);
                        return true;
                    }
                }
                (Val::Cap(c1, r1, ty), Val::Cap(c2, r2, sty)) if c2 >= c1 => {
                    if (r1.is_none()
                        || coerce_region(
                            &r2.clone()
                                .map(|r2| Region::from_val(r2, &default(), cxt))
                                .unwrap_or_else(|| r.clone()),
                            &Region::from_val(r1.clone().unwrap(), &default(), cxt),
                            span,
                            cxt,
                        ))
                        && (**ty).clone().glued().unify(
                            r1.clone(),
                            (**sty).clone().glued(),
                            r2.clone().or_else(|| Some(r.values())),
                            span,
                            cxt,
                        )
                    {
                        cxt.add_deps(r);
                        return true;
                    }
                }
                (_ity, Val::Cap(Cap::Own, r1, ty)) if !matches!(_ity, Val::Cap(_, _, _)) => {
                    if (**ty)
                        .clone()
                        .glued()
                        .unify(r1.clone(), to.clone(), None, span, cxt)
                    {
                        cxt.add_deps(r);
                        return true;
                    }
                }
                _ => (),
            }

            cxt.add_deps(r);
            return false;
        } else {
            cxt.add_deps(r);
            return true;
        }
    }
}
