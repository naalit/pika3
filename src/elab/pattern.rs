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
        (Pre::Sigma(i, n1, _, n2, rest), Val::Fun(Sigma(_), i2, _, aty, _, _)) if i == i2 => {
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
                TElim::Match(vec![(PCons::Pair(*i), vec![s1, s2], Arc::new(body))], None),
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
    match &ty.clone().glued().whnf(cxt) {
        Val::Fun(Sigma(n2), i, n1, aty, _, _) => {
            // TODO better system for names accessible in types in patterns
            // let n1 = names.next().flatten().unwrap_or(cxt.db.inaccessible(*n1));
            // let n2 = names.next().flatten().unwrap_or(cxt.db.inaccessible(*n2));
            let s1 = cxt.bind_(n1.0, aty.clone());
            let bty = ty.clone().app(Val::Neutral(Head::Sym(s1), default()));
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
                let ta = Arc::new(cxt.type_meta_with_spine(
                    MetaSource::TypeOf(n),
                    vars[0].span(),
                    spine.iter().cloned(),
                ));
                let (s, cxt2) = cxt.bind(n, ta.clone());
                let tb = cxt2
                    .type_meta_with_spine(
                        MetaSource::TypeOf(n2),
                        vars[1].span(),
                        spine
                            .iter()
                            .cloned()
                            .chain(std::iter::once(VElim::App(Expl, Arc::new(Val::sym(s))))),
                    )
                    .quote(&cxt2.qenv());
                let t = Val::Fun(
                    Sigma(n2),
                    Expl,
                    s,
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
            IPat::Var(n, _) => Some(*n),
        }
    }
}
impl SPrePat {
    fn ipat(&self, db: &DB) -> S<IPat> {
        S(
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
                        vars: vec![
                            s.ipat(db).map(|x| x.ensure_named(db)),
                            s1.ipat(db).map(|x| x.ensure_named(db)),
                        ],
                    },
                ),
                PrePat::Error => IPat::Var(db.name("_"), None),
            },
            self.span(),
        )
    }
}

#[derive(Clone)]
struct PRow {
    cols: Vec<(Sym, Arc<Val>, S<IPat>)>,
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
            match pat.0 {
                IPat::Var(n, None) => {
                    s.assignments.push((n, var, t.clone()));

                    Some(s)
                }
                IPat::Var(n, Some(paty)) => {
                    let aty = paty.check_type(cxt).eval(cxt.env());
                    if !aty.clone().glued().unify((*t).clone().glued(), pat.1, cxt) {
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
                                v.iter().map(|&(s, _)| s).collect(),
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
                    // TODO better span?
                    .all(|((n1, _, t1), (n2, _, t2))| {
                        *n1 == *n2
                            && (**t1)
                                .clone()
                                .glued()
                                .unify((**t2).clone().glued(), pcxt.span, cxt)
                    })
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
                .filter(|(_, s, _)| *s != pcxt.var)
                .map(|(_, s, _)| *s)
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
                                && matches!(&**p, IPat::CPat(_, p) if p.label == PCons::Pair(Impl))
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
                    let t = compile_rows(&vrows, pcxt, &cxt);
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
        compile_rows(&vrows, pcxt, &cxt)
    }
}

pub(super) struct PMatch {
    tree: PTree,
    body_syms: Vec<Sym>,
    pcxt: PCxt,
    pub ty: Arc<Val>,
}
impl PMatch {
    pub fn bind(&self, body: u32, cxt: &Cxt) -> Cxt {
        let mut cxt = cxt.clone();
        for (name, sym, ty) in &self.pcxt.bodies[body as usize].vars {
            if *sym == self.pcxt.var {
                cxt.bind_val(*name, Val::sym(*sym), ty.clone());
            } else {
                cxt.bind_raw(*name, *sym, ty.clone());
            }
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
            let body = vars.iter().rfold(body.clone(), |acc, (_, s, ty)| {
                Term::Fun(Lam, Expl, *s, Box::new(ty.quote(cxt.qenv())), Arc::new(acc))
            });
            term = Term::App(
                Box::new(Term::Fun(
                    Lam,
                    Expl,
                    *body_sym,
                    // TODO do we care about these types?
                    Box::new(Term::Error),
                    Arc::new(term),
                )),
                TElim::App(Expl, Box::new(body.clone())),
            );
        }
        term
    }

    pub fn new(ty: Option<GVal>, branches: &[SPrePat], ocxt: &mut Cxt) -> (Sym, PMatch) {
        let (name, ty) = branches
            .first()
            .map(|p| match p.ipat(&ocxt.db).0 {
                IPat::Var(n, None) => (
                    n,
                    ty.unwrap_or_else(|| ocxt.type_meta(MetaSource::TypeOf(n), p.span()).glued()),
                ),
                IPat::Var(n, Some(paty)) => (
                    n,
                    ty.unwrap_or_else(|| paty.check_type(&ocxt).eval(ocxt.env()).glued()),
                ),
                IPat::CPat(n, _) => (
                    n.unwrap_or(ocxt.db.name("_")),
                    ty.unwrap_or_else(|| {
                        ocxt.type_meta(MetaSource::TypeOf(n.unwrap_or(ocxt.db.name("_"))), p.span())
                            .glued()
                    }),
                ),
            })
            .unwrap();
        let ty = Arc::new(ty.as_small());

        let var = ocxt.bind_(name, ty.clone());
        let mut cxt = ocxt.clone();

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

        let rows: Vec<_> = branches
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let ipat = p.ipat(&cxt.db);
                PRow {
                    cols: vec![(var, ty.clone(), ipat)],
                    assignments: default(),
                    body: i as u32,
                }
            })
            .collect();

        let tree = compile_rows(&rows, &mut pcxt, &cxt);

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
