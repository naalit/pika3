use super::*;

fn ty_pat_bind_needed(pre_ty: &SPre, cxt: &Cxt) -> bool {
    match &***pre_ty {
        Pre::Sigma(_, n1, _, n2, rest) => {
            n1.is_some() || n2.is_some() || ty_pat_bind_needed(rest, cxt)
        }
        _ => false,
    }
}

pub fn pat_bind_type(
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
        (
            Pre::Sigma(i, n1, _, n2, rest),
            Val::Fun(VFun {
                class: Sigma(_),
                icit: i2,
                pty: aty,
                ..
            }),
        ) if i == i2 => {
            let n1 = n1.map(|x| *x).unwrap_or(cxt.db.name("_"));
            let (s1, cxt2) = cxt.bind(n1, aty.clone());
            let bty = ty.clone().app(Val::Neutral(Head::Sym(s1), default()));
            let n2 = n2.map(|x| *x).unwrap_or(cxt2.db.name("_"));
            let (s2, cxt2) = cxt2.bind(n2, bty.clone());
            let body = pat_bind_type(
                rest,
                Val::Neutral(Head::Sym(s2), default()),
                &bty,
                &cxt2,
                body,
            );
            let val = val.quote(&cxt.qenv());
            Term::App(
                Box::new(val),
                TElim::Match(
                    vec![(
                        PCons::Pair(*i),
                        vec![(Expl, s1), (Expl, s2)],
                        Arc::new(body),
                    )],
                    None,
                ),
            )
        }
        _ => body(cxt),
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum PCons {
    Pair(Icit),
    Cons(Def),
    // ... literals ...
}
#[derive(Clone, PartialEq)]
struct PConsTy {
    label: PCons,
    var_tys: Vec<(Icit, Sym, Arc<Val>)>,
    solved_locals: Vec<(Sym, Arc<Val>)>,
}

fn split_ty(
    var: Sym,
    ty: &Val,
    rows: &[PRow],
    mut names: impl Iterator<Item = Option<Name>>,
    cxt: &mut Cxt,
) -> Option<Vec<PConsTy>> {
    match &ty.clone().glued().whnf(cxt) {
        Val::Cap(c, r, t) => split_ty(var, t, rows, names, cxt).map(|v| {
            v.into_iter()
                .map(
                    |PConsTy {
                         label,
                         var_tys,
                         solved_locals,
                     }| PConsTy {
                        label,
                        var_tys: var_tys
                            .into_iter()
                            .map(|(i, s, t)| {
                                (
                                    i,
                                    s,
                                    Arc::new(
                                        Arc::unwrap_or_clone(t).as_cap(*c).with_region(r.clone()),
                                    ),
                                )
                            })
                            .collect(),
                        solved_locals,
                    },
                )
                .collect()
        }),

        Val::Fun(VFun {
            class: Sigma(n2),
            icit: i,
            psym: n1,
            pty: aty,
            ..
        }) => {
            // TODO better system for names accessible in types in patterns
            // let n1 = names.next().flatten().unwrap_or(cxt.db.inaccessible(*n1));
            // let n2 = names.next().flatten().unwrap_or(cxt.db.inaccessible(*n2));
            let s1 = cxt.bind_(n1.0, aty.clone());
            let bty = ty.clone().app(Val::Neutral(Head::Sym(s1), default()));
            let s2 = cxt.bind_(*n2, bty.clone());
            // now, we know this is reversible, so we can tell the compiler that
            // we *could* add this to `solved_locals` instead, but since this pattern is irrefutable, this is okay
            if cxt.can_solve(var) {
                cxt.solve_local(
                    var,
                    Arc::new(Val::Pair(Arc::new(Val::sym(s1)), Arc::new(Val::sym(s2)))),
                );
            }
            Some(vec![PConsTy {
                label: PCons::Pair(*i),
                var_tys: vec![(Expl, s1, aty.clone()), (Expl, s2, Arc::new(bty))],
                solved_locals: default(),
            }])
        }

        Val::Neutral(Head::Def(d), _) => match cxt.db.elab.def_value(*d, &cxt.db) {
            Ok(DefElabResult {
                def:
                    DefElab {
                        body: Some(DefBody::Type(ctors)),
                        ..
                    },
                ..
            }) => Some(
                ctors
                    .into_iter()
                    .filter_map(|cons| {
                        let mut cty = cxt
                            .db
                            .elab
                            .def_type(cons, &cxt.db)
                            .map(Arc::unwrap_or_clone)
                            .unwrap_or(Val::Error);
                        let mut var_tys = Vec::new();
                        let mut metas = Vec::new();
                        loop {
                            match &cty {
                                Val::Fun(VFun {
                                    class: Pi(_),
                                    icit: Impl,
                                    psym: s,
                                    pty: t,
                                    ..
                                }) => {
                                    let s1 = cxt.bind_(cxt.db.inaccessible(s.0), t.clone());
                                    var_tys.push((Impl, s1, t.clone()));
                                    let mv = cxt.new_meta(
                                        (**t).clone(),
                                        MetaSource::ImpArg(s.0),
                                        cxt.errors.span.span(),
                                    );
                                    let (m, s) = match mv.clone() {
                                        Val::Neutral(Head::Meta(m), s) => (m, s),
                                        _ => unreachable!(),
                                    };
                                    cty = cty.app(mv);
                                    metas.push(Some((m, s)));
                                }
                                Val::Fun(VFun {
                                    class: Pi(_),
                                    icit: Expl,
                                    psym: s,
                                    pty: t,
                                    ..
                                }) => {
                                    let s1 = cxt.bind_(cxt.db.inaccessible(s.0), t.clone());
                                    var_tys.push((Expl, s1, t.clone()));
                                    cty = cty.app(Val::sym(s1));
                                    metas.push(None);
                                }
                                _ => break,
                            }
                        }
                        if !cty.glued().unify(
                            None,
                            ty.clone().glued(),
                            None,
                            cxt.errors.span.span(),
                            cxt,
                        ) {
                            eprintln!(
                                "ruling out cons {} for type {}",
                                cons.pretty(&cxt.db),
                                ty.pretty(&cxt.db)
                            );
                            None
                        } else {
                            let solved_locals = var_tys
                                .iter()
                                .zip(metas)
                                .filter_map(|((_, s, _), m)| {
                                    m.and_then(|(m, sp)| {
                                        Some(sp.into_iter().fold(
                                            cxt.meta_val(m).map(Arc::unwrap_or_clone)?,
                                            |v, e| e.elim(v),
                                        ))
                                    })
                                    .map(|v| (*s, Arc::new(v)))
                                })
                                .collect();
                            Some(PConsTy {
                                label: PCons::Cons(cons),
                                var_tys,
                                solved_locals,
                            })
                        }
                    })
                    .collect(),
            ),
            _ => None,
        },

        Val::Neutral(Head::Meta(m), spine) => match rows
            .iter()
            .flat_map(|r| &r.cols)
            .find(|(s, _, _)| *s == var)
        {
            Some((
                _,
                _,
                S(
                    IPat::CPat(
                        _,
                        CPat {
                            label: PCons::Pair(_),
                            vars,
                            span,
                        },
                    ),
                    _,
                ),
            )) => {
                // solve metas with more metas
                let n = (*vars[0]).clone().ensure_named(&cxt.db).name().unwrap();
                let n2 = (*vars[1]).clone().ensure_named(&cxt.db).name().unwrap();
                let ta = Arc::new(cxt.new_meta_with_spine(
                    Val::Type,
                    MetaSource::TypeOf(n),
                    vars[0].span(),
                    spine.iter().cloned(),
                ));
                let (s, cxt2) = cxt.bind(n, ta.clone());
                let tb = cxt2
                    .new_meta_with_spine(
                        Val::Type,
                        MetaSource::TypeOf(n2),
                        vars[1].span(),
                        spine
                            .iter()
                            .cloned()
                            .chain(std::iter::once(VElim::App(Expl, Arc::new(Val::sym(s))))),
                    )
                    .quote(&cxt2.qenv());
                let t = Val::fun(
                    Sigma(n2),
                    Expl,
                    s,
                    ta,
                    None,
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
    Var(bool, Name, Option<Arc<SPre>>),
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
    vars: Vec<S<IPat>>,
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
            IPat::Var(_, n, _) => Some(*n),
        }
    }
}
impl SPrePat {
    fn ipat(&self, cxt: &Cxt) -> S<IPat> {
        S(
            match &***self {
                PrePat::Name(m, s) => IPat::Var(*m, **s, None),
                PrePat::Binder(p, s1) => match *p.ipat(cxt) {
                    IPat::Var(m, s, None) => IPat::Var(m, s, Some(Arc::new(s1.clone()))),
                    _ => {
                        cxt.err(
                            "binder pattern currently requires a name on left-hand side",
                            p.span(),
                        );
                        IPat::Var(false, cxt.db.name("_"), None)
                    }
                },
                PrePat::Pair(icit, s, s1) => IPat::CPat(
                    None,
                    CPat {
                        span: self.span(),
                        label: PCons::Pair(*icit),
                        // This is a sigma type, we need to make sure we have the first value accessible since it might be relevant for the type of the second
                        // I'm also making the second value accessible so that our local-solving-based reversible pattern matching thing works
                        vars: vec![
                            s.ipat(cxt).map(|x| x.ensure_named(&cxt.db)),
                            s1.ipat(cxt).map(|x| x.ensure_named(&cxt.db)),
                        ],
                    },
                ),
                PrePat::Cons(s, arg) => {
                    let (c, mut cty) = s.infer(cxt, false);
                    let mut vars = Vec::new();
                    while let Val::Fun(VFun {
                        class: Pi(_),
                        icit: Impl,
                        psym: n,
                        ..
                    }) = cty.whnf(cxt)
                    {
                        if !matches!(arg, Some((Impl, _))) {
                            vars.push(S(
                                IPat::Var(false, cxt.db.inaccessible(n.0), None),
                                s.span(),
                            ));
                            // This argument shouldn't matter, this type doesn't leave here
                            cty = cty.as_big().app(Val::Unknown).glued();
                        } else {
                            break;
                        }
                    }
                    if let Some((_, arg)) = arg {
                        vars.push(arg.ipat(cxt))
                    }
                    match c.eval(cxt.env()).glued().whnf(cxt) {
                        Val::Neutral(Head::Def(d), v) if v.is_empty() => IPat::CPat(
                            None,
                            CPat {
                                span: self.span(),
                                label: PCons::Cons(*d),
                                vars,
                            },
                        ),
                        v => {
                            cxt.err(
                                "expected data constructor in pattern, found " + v.pretty(&cxt.db),
                                s.span(),
                            );
                            IPat::Var(false, cxt.db.name("_"), None)
                        }
                    }
                }
                PrePat::Error => IPat::Var(false, cxt.db.name("_"), None),
            },
            self.span(),
        )
    }
}

#[derive(Clone)]
struct PRow {
    cols: Vec<(Sym, Arc<Val>, S<IPat>)>,
    assignments: Vec<(bool, Name, Sym, Arc<Val>, bool)>,
    body: u32,
}
impl PRow {
    // Avoid redundant bindings of the same symbol
    // Soft bind = "we need this accessible for type reasons"; hard bind = "the user bound this to a name"
    fn soft_bind(&mut self, s: Sym, ty: Arc<Val>, cxt: &Cxt) {
        if !self.assignments.iter().any(|(_, _, s2, _, _)| s == *s2) {
            let n = cxt.db.inaccessible(s.0);
            self.assignments.push((false, n, s, ty, false));
        }
    }
    fn hard_bind(&mut self, m: bool, n: Name, s: Sym, ty: Arc<Val>) {
        self.assignments.push((m, n, s, ty, true));
        self.assignments.retain(|(_, _, s2, _, b)| *b || s != *s2);
    }

    fn remove_column(
        self: &PRow,
        var: Sym,
        label: Option<PCons>,
        vars: &[(Icit, Sym, Arc<Val>)],
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
            match pat.0 {
                IPat::Var(m, n, None) => {
                    s.hard_bind(m, n, var, t.clone());

                    Some(s)
                }
                IPat::Var(m, n, Some(paty)) => {
                    let aty = cxt.as_eval(|| paty.check(Val::Type, cxt)).eval(cxt.env());
                    if !(*t).clone().glued().coerce(
                        aty.clone().glued(),
                        cxt.current_deps.with(Clone::clone),
                        pat.1,
                        cxt,
                    ) {
                        cxt.err(
                            Doc::start("mismatched types: pattern has type ")
                                + aty.pretty(&cxt.db)
                                + " but needs to match value of type "
                                + t.pretty(&cxt.db),
                            paty.span(),
                        );
                    }
                    s.hard_bind(m, n, var, t.clone());

                    Some(s)
                }
                IPat::CPat(n, pat) => {
                    if let Some(n) = n {
                        s.hard_bind(false, n, var, t.clone());
                    }
                    if label == Some(pat.label) {
                        let mut j = i;
                        assert_eq!(pat.vars.len(), vars.len());
                        for (p, (_, v, t)) in pat.vars.into_iter().zip(vars) {
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
        Vec<(PCons, Vec<(Icit, Sym, Arc<Val>)>, PTree)>,
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
                    .fold(bodies[*i as usize].quote(&cxt.qenv()), |acc, &s| {
                        Term::App(
                            Box::new(acc),
                            TElim::App(Expl, Box::new(Term::Head(Head::Sym(s)))),
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
                                v.iter().map(|&(i, s, _)| (i, s)).collect(),
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
    span: Span,
    reached: bool,
    solved_locals: Vec<(Sym, Arc<Val>)>,
    vars: Vec<(bool, Name, Sym, Arc<Val>)>,
}
struct PCxt {
    bodies: Vec<PBody>,
    span: Span,
    var: Sym,
    has_error: bool,
}
#[derive(Clone)]
enum PState {
    Any(Sym),
    Cons(PCons, Vec<(Icit, PState)>),
}
impl PState {
    fn with(&self, var: Sym, new: &PState) -> PState {
        match self {
            PState::Any(sym) if *sym == var => new.clone(),
            PState::Any(sym) => PState::Any(*sym),
            PState::Cons(pcons, vec) => PState::Cons(
                *pcons,
                vec.iter().map(|(i, x)| (*i, x.with(var, new))).collect(),
            ),
        }
    }
}
impl Pretty for PState {
    fn pretty(&self, db: &DB) -> Doc {
        match self {
            PState::Any(_) => Doc::start("_"),
            PState::Cons(pcons, v) => match pcons {
                PCons::Pair(i) => {
                    (v[0].1.pretty(db).nest_icit(*i, Prec::Pi) + ", " + v[1].1.pretty(db))
                        .prec(Prec::Pair)
                }
                PCons::Cons(d) => (db.idefs.get(*d).name().pretty(db)
                    + Doc::intersperse(
                        v.iter()
                            .map(|(i, x)| " " + x.pretty(db).nest_icit(*i, Prec::Atom)),
                        Doc::none(),
                    ))
                .prec(Prec::App),
            },
        }
    }
}
fn compile_rows(rows: &[PRow], pcxt: &mut PCxt, state: &PState, cxt: &Cxt) -> PTree {
    if rows.is_empty() {
        if !pcxt.has_error {
            pcxt.has_error = true;
            cxt.err(
                "non-exhaustive pattern match, not covered: " + state.pretty(&cxt.db),
                pcxt.span,
            );
        }
        PTree::Error
    } else if rows.first().unwrap().cols.is_empty() {
        let row = rows.first().unwrap();
        if pcxt.bodies[row.body as usize].reached {
            // check for matching bindings
            if pcxt.bodies[row.body as usize].vars.len() != row.assignments.len()
                || !pcxt.bodies[row.body as usize]
                    .vars
                    .iter()
                    .zip(&row.assignments)
                    // TODO better span?
                    .all(|((m1, n1, _, t1), (m2, n2, _, t2, _))| {
                        m1 == m2
                            && n1 == n2
                            && (**t1).clone().glued().unify(
                                None,
                                (**t2).clone().glued(),
                                None,
                                pcxt.span,
                                cxt,
                            )
                    })
            {
                cxt.err(
                    "mismatched bindings for match branch: ["
                        + Doc::intersperse(
                            pcxt.bodies[row.body as usize]
                                .vars
                                .iter()
                                .map(|(_, n, _, t)| {
                                    n.pretty(&cxt.db) + ": " + t.zonk(cxt, true).pretty(&cxt.db)
                                }),
                            Doc::start(", "),
                        )
                        + "] vs ["
                        + Doc::intersperse(
                            row.assignments.iter().map(|(_, n, _, t, _)| {
                                n.pretty(&cxt.db) + ": " + t.zonk(cxt, true).pretty(&cxt.db)
                            }),
                            Doc::start(", "),
                        )
                        + "]",
                    pcxt.bodies[row.body as usize].span,
                );
            }
        } else {
            pcxt.bodies[row.body as usize] = PBody {
                span: pcxt.bodies[row.body as usize].span,
                reached: true,
                solved_locals: cxt.solved_locals(),
                vars: row
                    .assignments
                    .iter()
                    .map(|(m, n, s, t, _)| {
                        (*m, *n, *s, {
                            // Needed to account for locals solved during pattern compilation
                            // TODO but those locals can be in the spine ??? do we even need this?
                            // Arc::new((**t).clone().glued().whnf(cxt).clone())
                            t.clone()
                        })
                    })
                    .collect(),
            };
        }
        PTree::Body(
            row.body,
            row.assignments
                .iter()
                .filter(|(_, _, s, _, _)| *s != pcxt.var)
                .map(|(_, _, s, _, _)| *s)
                .collect(),
            cxt.clone(),
        )
    } else {
        let (var, ty, _) = rows.first().unwrap().cols.first().unwrap();
        let tvar = Val::Neutral(Head::Sym(*var), default()).quote(&cxt.qenv());
        let mut cxt = cxt.clone();
        let nempty = cxt.db.name("_");
        let names = rows
            .iter()
            .flat_map(|r| &r.cols)
            .filter(|(s, _, _)| s == var)
            .filter_map(|(_, _, p)| match &**p {
                IPat::CPat(_, cpat) => Some(cpat),
                _ => None,
            })
            .next()
            .iter()
            .flat_map(|x| &x.vars)
            .map(|n| {
                match &**n {
                    IPat::Var(_, n, _) => Some(*n),
                    IPat::CPat(n, _) => *n,
                }
                .filter(|n| *n != nempty)
            })
            .collect::<Vec<_>>();

        if rows
            .iter()
            .flat_map(|r| &r.cols)
            .any(|(s, _, p)| s == var && p.needs_split(&cxt.db))
            || matches!(
                &**ty,
                Val::Fun(VFun {
                    class: Sigma(_),
                    icit: Impl,
                    ..
                })
            )
        {
            if let Some(ctors) = split_ty(*var, ty, rows, names.into_iter(), &mut cxt) {
                if ctors.len() == 1
                    && ctors[0].label == PCons::Pair(Impl)
                    && !rows.iter().any(|row| {
                        row.cols.iter().any(|(s, _, p)| {
                            s == var
                                && matches!(&**p, IPat::CPat(_, p) if p.label == PCons::Pair(Impl))
                        })
                    })
                {
                    // Auto-unwrap implicit pairs if we don't match on them explicitly
                    // We do need to add the implicit argument to the assignments for each row
                    let mut rows = rows.to_vec();
                    let (_, isym, ity) = ctors[0].var_tys[0].clone();
                    let (_, vsym, vty) = ctors[0].var_tys[1].clone();
                    for row in &mut rows {
                        // Because we're not calling remove_column(), they can't bind the sym we split on either, so we'll need to do that
                        row.soft_bind(*var, ty.clone(), &cxt);
                        row.soft_bind(isym, ity.clone(), &cxt);
                        row.soft_bind(vsym, vty.clone(), &cxt);
                        row.cols.iter_mut().for_each(|(s, t, _)| {
                            if s == var {
                                *s = vsym;
                                *t = vty.clone();
                            }
                        });
                    }
                    let state = state.with(
                        *var,
                        &PState::Cons(
                            ctors[0].label,
                            ctors[0]
                                .var_tys
                                .iter()
                                .map(|(i, s, _)| (*i, PState::Any(*s)))
                                .collect(),
                        ),
                    );
                    let t = compile_rows(&rows, pcxt, &state, &cxt);
                    return PTree::Match(
                        tvar,
                        vec![(ctors[0].label, ctors[0].var_tys.clone(), t)],
                        None,
                    );
                }

                let mut v = Vec::new();
                for row in rows {
                    if let Some((_, _, S(IPat::CPat(_, cpat), _))) =
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
                    let mut cxt = cxt.clone();
                    for (s, val) in ctor.solved_locals {
                        cxt.solve_local(s, val);
                    }
                    let state = state.with(
                        *var,
                        &PState::Cons(
                            ctor.label,
                            ctor.var_tys
                                .iter()
                                .map(|(i, s, _)| (*i, PState::Any(*s)))
                                .collect(),
                        ),
                    );
                    let t = compile_rows(&vrows, pcxt, &state, &cxt);
                    v.push((ctor.label, ctor.var_tys, t));
                }
                return PTree::Match(tvar, v, None);
            }
        }

        for row in rows {
            if let Some((_, _, S(IPat::CPat(_, cpat), _))) =
                row.cols.iter().find(|(s, _, _)| s == var)
            {
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
        compile_rows(&vrows, pcxt, &state, &cxt)
    }
}

pub(super) struct PMatch {
    tree: PTree,
    body_syms: Vec<Sym>,
    pcxt: PCxt,
    pub ty: Arc<Val>,
}
impl PMatch {
    pub fn reached(&self, body: u32) -> bool {
        self.pcxt.bodies[body as usize].reached
    }

    pub fn bind(&self, body: u32, deps: &Region, cxt: &Cxt) -> Cxt {
        let mut cxt = cxt.clone();
        for (m, name, sym, ty) in &self.pcxt.bodies[body as usize].vars {
            if *sym == self.pcxt.var {
                cxt.bind_existing_var(*name, *sym);
            } else {
                cxt.bind_raw(*name, *sym, ty.clone());
            }
            cxt.set_mutable(*sym, *m);
            cxt.set_deps(*sym, deps.clone());
        }
        for (sym, val) in &self.pcxt.bodies[body as usize].solved_locals {
            // Make sure the solutions of any solved locals are actually in scope
            if cxt.can_solve(*sym) && val.quote_(&cxt.qenv()).is_ok() {
                cxt.solve_local(*sym, val.clone());
            }
        }
        cxt
    }

    pub fn compile(&self, bodies: &[Term], cxt: &Cxt) -> Term {
        assert_eq!(bodies.len(), self.pcxt.bodies.len());
        if let PTree::Body(0, v, _) = &self.tree {
            assert_eq!(v.len(), 0);
            return bodies[0].clone();
        }
        let mut term = self.tree.apply(
            &self
                .body_syms
                .iter()
                .map(|&s| Val::Neutral(Head::Sym(s), default()))
                .collect::<Vec<_>>(),
        );
        for ((body, PBody { vars, .. }), body_sym) in bodies
            .iter()
            .zip(&self.pcxt.bodies)
            .zip(&self.body_syms)
            .rev()
        {
            let body = vars.iter().rfold(body.clone(), |acc, (_, _, s, ty)| {
                Term::fun(Lam, Expl, *s, None, ty.quote(cxt.qenv()), Arc::new(acc))
            });
            term = Term::App(
                Box::new(Term::fun(
                    Lam,
                    Expl,
                    *body_sym,
                    None,
                    // TODO do we care about these types?
                    Term::Error,
                    Arc::new(term),
                )),
                TElim::App(Expl, Box::new(body.clone())),
            );
        }
        term
    }

    pub fn new(
        ty: Option<GVal>,
        branches: &[SPrePat],
        span: Option<Span>,
        ocxt: &mut Cxt,
    ) -> (Sym, PMatch) {
        let (m, name, ty) = branches
            .first()
            .map(|p| match p.ipat(ocxt).0 {
                IPat::Var(m, n, None) => (
                    m,
                    n,
                    ty.unwrap_or_else(|| {
                        ocxt.new_meta(Val::Type, MetaSource::TypeOf(n), p.span())
                            .glued()
                    }),
                ),
                IPat::Var(m, n, Some(paty)) => (
                    m,
                    n,
                    ty.unwrap_or_else(|| {
                        ocxt.as_eval(|| paty.check(Val::Type, &ocxt))
                            .eval(ocxt.env())
                            .glued()
                    }),
                ),
                IPat::CPat(n, _) => (
                    false,
                    n.unwrap_or(ocxt.db.name("_")),
                    ty.unwrap_or_else(|| {
                        ocxt.new_meta(
                            Val::Type,
                            MetaSource::TypeOf(n.unwrap_or(ocxt.db.name("_"))),
                            p.span(),
                        )
                        .glued()
                    }),
                ),
            })
            .unwrap();
        let ty = Arc::new(ty.as_small());

        let var = ocxt.bind_(name, ty.clone());
        ocxt.set_mutable(var, m);
        let mut cxt = ocxt.clone();

        let mut pcxt = PCxt {
            bodies: branches
                .iter()
                .map(|x| PBody {
                    span: x.span(),
                    reached: false,
                    solved_locals: default(),
                    vars: default(),
                })
                .collect(),
            var,
            span: span.unwrap_or(branches[0].span()),
            has_error: false,
        };

        // We attach the bodies as `let`, i.e. lambdas
        // So we need a local for each body, to make sure the contexts match up
        let body_syms = branches
            .iter()
            .map(|_| cxt.bind_(cxt.db.name("_"), Val::Error))
            .collect();

        let rows: Vec<_> = branches
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let ipat = p.ipat(&cxt);
                PRow {
                    cols: vec![(var, ty.clone(), ipat)],
                    assignments: default(),
                    body: i as u32,
                }
            })
            .collect();

        let tree = compile_rows(&rows, &mut pcxt, &PState::Any(var), &cxt);

        (
            var,
            PMatch {
                tree,
                pcxt,
                body_syms,
                ty,
            },
        )
    }
}
