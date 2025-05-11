use crate::common::*;
use crate::lexer::*;

// `def f {x y} {z w} (a b): t = ...`
// but for now:
// `def f : t = ...`
#[derive(Debug, Clone)]
pub enum PreDef {
    Val {
        name: SName,
        ty: Option<SPre>,
        value: Option<SPre>,
    },
    Type {
        name: SName,
        args: Vec<(Icit, SPrePat)>,
        // (name, args, return type)
        variants: Vec<(SName, Option<(Icit, SPre)>, Option<SPre>)>,
    },
}
impl PreDef {
    pub fn name(&self) -> SName {
        match self {
            PreDef::Val { name, .. } => *name,
            PreDef::Type { name, .. } => *name,
        }
    }
}
pub type SPrePat = S<Box<PrePat>>;

#[derive(Debug, Clone)]
pub enum PrePat {
    Name(bool, SName),
    Binder(SPrePat, SPre),
    Pair(Icit, SPrePat, SPrePat),
    Cons(SPre, Option<(Icit, SPrePat)>),
    Error,
}
impl PrePat {
    pub fn name(&self) -> Option<SName> {
        match self {
            PrePat::Name(_, s) => Some(*s),
            PrePat::Binder(s, _) => s.name(),
            PrePat::Pair(_, _, _) => None,
            PrePat::Cons(_, _) => None,
            PrePat::Error => None,
        }
    }
}
#[derive(Debug, Clone)]
pub enum PreStmt {
    Expr(SPre),
    Let(SPrePat, SPre),
    Def(S<PreDef>),
}
#[derive(Debug, Clone, Copy)]
pub enum HoleSource {
    TypeOf(SName),
}
#[derive(Debug, Clone)]
pub enum Pre {
    Type,
    Hole(HoleSource),
    Var(Name),
    Binder(SPre, SPre),
    App(SPre, SPre, Icit),
    // FCap is ommitted in function syntax so we can infer -> or ~> with currying
    Pi(Icit, Name, Option<FCap>, SPre, SPre),
    // if the bool is true it means this is obligatorily interpreted as a term not a type (only used by `mod` currently)
    Sigma(bool, Icit, Option<SName>, SPre, Option<SName>, SPre),
    Lam(Icit, SPrePat, SPre),
    Do(Vec<PreStmt>, SPre),
    Cap(Cap, SPre),
    Region(Vec<SPre>),
    RegionAnn(Vec<SPre>, SPre),
    Assign(SPre, SPre),
    // x.f y
    Dot(SPre, SName, Option<(Icit, SPre)>),
    Case(SPre, Vec<(SPrePat, SPre)>),
    Unit,
    Error,
}
pub type SPre = S<Box<Pre>>;

#[derive(Debug)]
pub struct ParseResult {
    pub defs: Vec<S<PreDef>>,
    pub errors: Vec<Error>,
}

pub fn parse(input: Rope, db: &DB) -> ParseResult {
    let mut lexer = Lexer::new(input.clone());
    let tokens = lexer.lex();
    // eprintln!("{:?}", tokens.kind);
    // eprintln!("{:?}", tokens.start);
    let mut parser = Parser::new(input, tokens, db.clone());
    let defs = parser.defs();
    ParseResult {
        defs,
        errors: parser.errors,
    }
}

struct Parser {
    input: Rope,
    tokens: Vec<Tok>,
    starts: Vec<u32>,
    pos: usize,
    pos_non_trivia: usize,
    indent_stack: Vec<bool>,
    errors: Vec<Error>,
    // once we emit a parse error on a given token, we don't emit errors for subsequent expect()s that fail on the same token
    this_tok_err: bool,
    db: DB,
}
impl Parser {
    // meta

    fn new(input: Rope, r: LexResult, db: DB) -> Parser {
        Parser {
            input,
            tokens: r.kind,
            starts: r.start,
            pos: 0,
            pos_non_trivia: 0,
            indent_stack: Vec::new(),
            errors: r
                .errors
                .into_iter()
                .map(|e| lexerror_to_error(e.0, e.1))
                .collect(),
            this_tok_err: false,
            db,
        }
    }

    fn peek(&self) -> Tok {
        match self.tokens.get(self.pos) {
            Some(t) => *t,
            None => Tok::Eof,
        }
    }
    fn next_raw(&mut self) -> Tok {
        let t = self.peek();
        if t != Tok::Eof {
            self.pos += 1;
            // Significant whitespace shouldn't actually be included in spans
            if !(t.is_trivia() || t == Tok::Indent || t == Tok::Newline || t == Tok::Dedent) {
                self.pos_non_trivia = self.pos;
            }
            self.this_tok_err = false;
        }
        t
    }
    fn skip_trivia_(&mut self) {
        while self.peek().is_trivia() {
            self.next_raw();
        }
    }
    fn skip_trivia(&mut self, skip_newline: bool) {
        loop {
            if self.peek().is_trivia()
                || ((skip_newline || self.indent_stack.last().iter().any(|x| **x))
                    && self.peek() == Tok::Newline)
            {
                self.next_raw();
            } else if self.peek() == Tok::Indent {
                self.indent_stack.push(true);
                self.next_raw();
            } else if self.peek() == Tok::Dedent && !self.indent_stack.is_empty() {
                self.indent_stack.pop();
                self.next_raw();
            } else {
                break;
            }
        }
    }
    fn next(&mut self) -> Tok {
        self.next_raw();
        self.skip_trivia(false);
        self.peek()
    }
    fn peekn(&self, n: usize) -> Tok {
        match self.tokens[self.pos..]
            .iter()
            .filter(|x| !x.is_trivia())
            .nth(n)
        {
            Some(t) => *t,
            None => Tok::Eof,
        }
    }
    fn reset_to(&mut self, tok: Tok) {
        while !self.maybe(tok) && self.peek() != Tok::Eof {
            self.next();
        }
    }

    fn pos(&self) -> u32 {
        *self
            .starts
            .get(self.pos)
            .unwrap_or_else(|| self.starts.last().unwrap_or(&0))
    }
    fn pos_right(&self) -> u32 {
        *self
            .starts
            .get(self.pos_non_trivia)
            .unwrap_or_else(|| self.starts.last().unwrap())
    }
    fn tok_span(&self) -> Span {
        let a = self.pos();
        let b = self.starts.get(self.pos + 1).copied().unwrap_or(a);
        Span(a, b)
    }
    fn tok_rope(&self) -> Rope {
        let Span(a, b) = self.tok_span();
        self.input.subrope(a as usize..b as usize)
    }
    fn tok_name(&self) -> Name {
        self.db.name(self.tok_rope().to_string().trim())
    }
    fn error(&mut self, e: impl Into<Doc>, span: Span) {
        if self.this_tok_err {
            return;
        }
        let message = Doc::start("parse error: ").chain(e.into());
        self.this_tok_err = true;
        self.errors.push(Error {
            severity: Severity::Error,
            message: message.clone(),
            message_lsp: None,
            primary: Label {
                span,
                message,
                color: Some(Doc::COLOR1),
            },
            secondary: Vec::new(),
            note: None,
        });
    }

    fn maybe(&mut self, t: Tok) -> bool {
        if self.peek() == t {
            self.next();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: Tok) -> bool {
        if !self.maybe(t) {
            self.error(
                &format!("expected {}, found {}", t, self.peek()),
                self.tok_span(),
            );
            false
        } else {
            true
        }
    }
    fn maybe_raw(&mut self, t: Tok) -> bool {
        if self.peek() == t {
            self.next_raw();
            true
        } else {
            false
        }
    }
    fn expect_raw(&mut self, t: Tok) {
        if !self.maybe_raw(t) {
            self.error(
                &format!("expected {}, found {}", t, self.peek()),
                self.tok_span(),
            );
        }
    }

    fn spanned<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> S<T> {
        let start = self.pos();
        let r = f(self);
        S(r, Span(start, self.pos_right()))
    }

    /// Captures an indent after the current token
    fn push_indent(&mut self, tok: Option<Tok>) -> Option<usize> {
        let plen = self.indent_stack.len();
        if let Some(tok) = tok {
            self.expect(tok);
        } else {
            self.next();
        }
        let ilen = self.indent_stack.len();
        (ilen > plen).then(|| {
            *self.indent_stack.last_mut().unwrap() = false;
            plen
        })
    }
    /// Returns `true` if the given indent hasn't ended.
    /// Also returns `true` if there was no indent (`p` is `None`)
    fn has_indent(&mut self, p: Option<usize>) -> bool {
        if let Some(plen) = p {
            self.indent_stack.len() > plen
        } else {
            true
        }
    }
    fn pop_indent(&mut self, p: Option<usize>) {
        if let Some(plen) = p {
            if self.indent_stack.len() > plen {
                self.error("expected dedent", self.tok_span());
                while self.indent_stack.len() > plen {
                    self.next();
                }
            }
        }
    }

    // reparsing

    fn reparse_pi_param(&mut self, param: SPre) -> (Option<SName>, SPre) {
        match &**param {
            Pre::Binder(lhs, rhs) => {
                match &***lhs {
                    Pre::Var(name) => (Some(S(*name, lhs.span())), rhs.clone()),
                    Pre::Region(v) if v.len() == 1 => match &**v[0] {
                        Pre::Var(name) => (Some(S(*name, lhs.span())), rhs.clone()),
                        _ => (None, param),
                    },
                    // TODO what's the correct thing to do here? what happens to the below error case with this branch present
                    _ => (None, param),
                    _ => {
                        // TODO uhh wait we totally allow `(a: T, b: U) -> R`... maybe these should just be patterns too
                        // this is a weird situation. `(T, U)` is treated as a type, so it's not just a pattern here,
                        // but `(a: T, b: U)` is treated as a pattern... and `(a: T, U)` is a pattern and a type, in a tuple.
                        // this may need special-case handling...
                        // TODO figure out if there's a way to avoid this
                        self.error("parameter binding in function type must be a simple name, not a pattern", lhs.span());
                        (None, rhs.clone())
                    }
                }
            }
            _ => (None, param),
        }
    }
    fn reparse_pattern(&mut self, param: &SPre, message: &Doc) -> PrePat {
        match &***param {
            Pre::Binder(lhs, rhs) => PrePat::Binder(
                S(Box::new(self.reparse_pattern(lhs, message)), lhs.span()),
                rhs.clone(),
            ),
            Pre::Unit => PrePat::Binder(
                S(
                    Box::new(PrePat::Name(false, S(self.db.name("_"), param.span()))),
                    param.span(),
                ),
                S(Box::new(Pre::Unit), param.span()),
            ),
            Pre::Cap(Cap::Mut, p) => match &***p {
                Pre::Var(name) => PrePat::Name(true, S(*name, param.span())),
                _ => {
                    self.error("invalid pattern", param.span());
                    PrePat::Error
                }
            },
            Pre::Var(name) => PrePat::Name(false, S(*name, param.span())),
            // TODO (mut a : T, mut b : T)
            Pre::Sigma(_, i, n1, a, n2, b) => {
                let a = match n1 {
                    Some(n) => S(
                        Box::new(PrePat::Binder(
                            S(Box::new(PrePat::Name(false, *n)), n.span()),
                            a.clone(),
                        )),
                        a.span(),
                    ),
                    None => S(Box::new(self.reparse_pattern(a, message)), a.span()),
                };
                let b = match n2 {
                    Some(n) => S(
                        Box::new(PrePat::Binder(
                            S(Box::new(PrePat::Name(false, *n)), n.span()),
                            b.clone(),
                        )),
                        b.span(),
                    ),
                    None => S(Box::new(self.reparse_pattern(b, message)), b.span()),
                };
                PrePat::Pair(*i, a, b)
            }
            Pre::App(f, x, icit) => {
                let x = S(Box::new(self.reparse_pattern(x, message)), x.span());
                PrePat::Cons(f.clone(), Some((*icit, x)))
            }
            Pre::Dot(x, m, arg) => {
                let x = S(Box::new(Pre::Dot(x.clone(), *m, None)), x.span());
                if let Some((icit, arg)) = arg {
                    let arg = S(Box::new(self.reparse_pattern(arg, message)), arg.span());
                    PrePat::Cons(x, Some((*icit, arg)))
                } else {
                    PrePat::Cons(x, None)
                }
            }
            _ => {
                self.error(message, param.span());
                PrePat::Error
            }
        }
    }
    // lambda params are just patterns, so reparsing doesn't happen here
    // we might want to put pattern parsing in here in the future though. in which case we would reparse lambda params here

    // object-level parsing

    fn name(&mut self) -> Name {
        let n = self.tok_name();
        self.expect(Tok::Name);
        n
    }
    fn atom(&mut self) -> SPre {
        self.spanned(|s| {
            Box::new(match s.peek() {
                Tok::TypeTypeKw => {
                    s.next();
                    Pre::Type
                }
                Tok::Name => Pre::Var(s.name()),
                Tok::POpen => {
                    s.next();
                    if s.maybe(Tok::PClose) {
                        return Box::new(Pre::Unit);
                    }
                    let t = s.term();
                    s.expect(Tok::PClose);
                    *t.0
                }
                Tok::ModKw => {
                    // Desugar `mod` to a `do` block with a bunch of local defs and a pair at the end
                    let kw_span = s.tok_span();
                    s.next_raw();
                    s.skip_trivia_();
                    if s.expect(Tok::Indent) {
                        s.indent_stack.push(false);
                    }

                    let r = s.indent_stack.len();
                    let mut v = Vec::new();
                    let mut any_term = false;
                    loop {
                        v.push(PreStmt::Def(s.spanned(|s| {
                            let d = s.def();
                            if !any_term
                                && matches!(
                                    d,
                                    PreDef::Type { .. } | PreDef::Val { value: Some(_), .. }
                                )
                            {
                                any_term = true;
                            }
                            d
                        })));
                        if s.indent_stack.len() < r || !s.maybe(Tok::Newline) {
                            break;
                        }
                    }
                    let last = v
                        .iter()
                        .rfold::<Option<SPre>, _>(None, |acc, x| {
                            let name = match x {
                                PreStmt::Def(def) => def.name(),
                                _ => unreachable!(),
                            };
                            let t = S(Box::new(Pre::Var(*name)), name.span());
                            Some(match acc {
                                None => t,
                                Some(x) => match &**x {
                                    Pre::Var(n2) => S(
                                        Box::new(Pre::Sigma(
                                            true,
                                            Expl,
                                            Some(name),
                                            t,
                                            Some(S(*n2, x.span())),
                                            x,
                                        )),
                                        kw_span,
                                    ),
                                    Pre::Sigma { .. } => S(
                                        Box::new(Pre::Sigma(
                                            any_term,
                                            Expl,
                                            Some(name),
                                            t,
                                            None,
                                            x,
                                        )),
                                        kw_span,
                                    ),
                                    _ => unreachable!(),
                                },
                            })
                        })
                        .unwrap_or_else(|| S(Box::new(Pre::Error), kw_span));
                    Pre::Do(v, last)
                }
                Tok::DoKw => {
                    let kw_span = s.tok_span();
                    s.next_raw();
                    s.skip_trivia_();
                    let pat = if s.maybe(Tok::Indent) {
                        s.indent_stack.push(false);
                        None
                    } else {
                        // Do-lambda!!
                        let icit = s.maybe(Tok::COpen);
                        let lhs = (s.peek() != Tok::WideArrow && s.peek() != Tok::CClose)
                            .then(|| s.app());
                        let pat = S(
                            Box::new(match &lhs {
                                Some(lhs) => s.reparse_pattern(
                                    lhs,
                                    &Doc::start("expected pattern in lambda argument"),
                                ),
                                None => PrePat::Binder(
                                    S(
                                        Box::new(PrePat::Name(false, S(s.db.name("_"), kw_span))),
                                        kw_span,
                                    ),
                                    S(Box::new(Pre::Unit), kw_span),
                                ),
                            }),
                            lhs.map_or(kw_span, |x| x.span()),
                        );
                        if icit {
                            s.expect(Tok::CClose);
                        }
                        s.expect_raw(Tok::WideArrow);
                        s.expect(Tok::Indent);
                        s.indent_stack.push(false);
                        Some((pat, icit))
                    };
                    let r = s.indent_stack.len();
                    let mut v = Vec::new();
                    loop {
                        if s.maybe(Tok::LetKw) || s.peek() == Tok::MutKw {
                            let pat = s.spanned(|s| {
                                let pat = s.fun(true);
                                Box::new(s.reparse_pattern(
                                    &pat,
                                    &Doc::start("expected pattern after `let`/`mut` in block"),
                                ))
                            });
                            s.expect(Tok::Equals);
                            let body = s.term();
                            v.push(PreStmt::Let(pat, body));
                        } else if s.peek().starts_def() {
                            let def = s.spanned(|s| s.def());
                            v.push(PreStmt::Def(def));
                        } else {
                            let body = s.term();
                            v.push(PreStmt::Expr(body));
                        }
                        if s.indent_stack.len() < r || !s.maybe(Tok::Newline) {
                            break;
                        }
                    }
                    s.skip_trivia(false);
                    let last = v
                        .pop()
                        .and_then(|x| match x {
                            PreStmt::Expr(x) => Some(x),
                            _ => None,
                        })
                        .unwrap_or_else(|| {
                            s.error(
                                "expected an expression for the return value of this block",
                                s.tok_span(),
                            );
                            s.spanned(|_| Box::new(Pre::Error))
                        });
                    let t = Pre::Do(v, last);
                    match pat {
                        None => t,
                        Some((pat, implicit)) => {
                            let t = S(Box::new(t), Span(kw_span.0, s.pos_right()));
                            Pre::Lam(if implicit { Impl } else { Expl }, pat, t)
                        }
                    }
                }
                _ => {
                    s.error("expected expression", s.tok_span());
                    Pre::Error
                }
            })
        })
    }
    fn app(&mut self) -> SPre {
        let start = self.pos();
        if self.maybe(Tok::ImmKw) {
            let rest = self.app();
            return S(
                Box::new(Pre::Cap(Cap::Imm, rest)),
                Span(start, self.pos_right()),
            );
        } else if self.maybe(Tok::MutKw) {
            let rest = self.app();
            return S(
                Box::new(Pre::Cap(Cap::Mut, rest)),
                Span(start, self.pos_right()),
            );
        }
        if self.peek() == Tok::SingleQuote {
            let mut r = Vec::new();
            while self.maybe(Tok::SingleQuote) {
                if self.peek() == Tok::Name {
                    let x = self.spanned(|s| {
                        let n = s.name();
                        Box::new(Pre::Var(s.db.name(&format!("'{}", s.db.get(n)))))
                    });
                    r.push(x);
                } else {
                    let a = self.atom();
                    match &**a {
                        Pre::Unit => (),
                        _ => r.push(a),
                    }
                }
            }
            if self.peek().starts_atom() {
                let rest = self.app();
                return S(
                    Box::new(Pre::RegionAnn(r, rest)),
                    Span(start, self.pos_right()),
                );
            } else {
                return S(Box::new(Pre::Region(r)), Span(start, self.pos_right()));
            }
        }
        let mut a = self.atom();
        // make sure we don't get in an infinite loop - stop looking for atoms if we don't consume any input
        let mut last = start;
        while (self.peek().starts_atom() || self.peek() == Tok::Dot || self.peek() == Tok::CaseKw)
            && last != self.pos()
        {
            last = self.pos();
            if self.peek() == Tok::CaseKw {
                let p = self.push_indent(Some(Tok::CaseKw));
                let mut v = Vec::new();
                while self.has_indent(p) {
                    let pat = self.app();
                    let pat = S(
                        Box::new(self.reparse_pattern(
                            &pat,
                            &Doc::start("expected pattern in `case` branch"),
                        )),
                        pat.span(),
                    );
                    self.expect(Tok::WideArrow);
                    let body = self.term();
                    if p.is_none() {
                        break;
                    }
                    v.push((pat, body));
                    if self.has_indent(p) {
                        self.expect(Tok::Newline);
                    }
                }
                a = S(Box::new(Pre::Case(a, v)), Span(start, self.pos_right()));
                continue;
            }
            let dot = self.maybe(Tok::Dot).then(|| self.spanned(|s| s.name()));
            let sstart = self.pos();
            let (icit, arg) = if self.maybe(Tok::COpen) {
                if self.maybe(Tok::CClose) {
                    (Impl, S(Box::new(Pre::Unit), Span(sstart, self.pos_right())))
                } else {
                    let term = self.term();
                    self.expect(Tok::CClose);
                    (Impl, term)
                }
            } else if !self.peek().starts_atom() && dot.is_some() {
                let dot = dot.unwrap();
                a = S(
                    Box::new(Pre::Dot(a, dot, None)),
                    Span(start, self.pos_right()),
                );
                continue;
            } else {
                (Expl, self.atom())
            };
            match dot {
                None => {
                    a = S(
                        Box::new(Pre::App(a, arg, icit)),
                        Span(start, self.pos_right()),
                    )
                }
                Some(n) => {
                    a = S(
                        Box::new(Pre::Dot(a, n, Some((icit, arg)))),
                        Span(start, self.pos_right()),
                    )
                }
            }
        }
        a
    }
    fn binder(&mut self) -> SPre {
        let start = self.pos();
        let lhs = self.app();
        if self.maybe(Tok::Colon) {
            let rhs = self.fun(false);
            S(
                Box::new(Pre::Binder(lhs, rhs)),
                Span(start, self.pos_right()),
            )
        } else {
            lhs
        }
    }
    fn fun(&mut self, pair: bool) -> SPre {
        let start = self.pos();
        let implicit = self.maybe(Tok::COpen);
        let lhs = if implicit {
            if self.peek() == Tok::CClose {
                S(Box::new(Pre::Unit), Span(start, self.tok_span().1))
            } else {
                self.term()
            }
        } else if pair {
            self.fun(false)
        } else {
            self.binder()
        };
        if implicit {
            self.expect(Tok::CClose);
        }
        let icit = if implicit { Impl } else { Expl };
        if matches!(self.peek(), Tok::Arrow | Tok::WavyArrow) {
            // pi
            let c = if self.maybe(Tok::WavyArrow) {
                FCap::Own
            } else {
                self.expect(Tok::Arrow);
                FCap::Imm
            };
            let rhs = self.fun(false);
            let (name, lhs) = self.reparse_pi_param(lhs);
            let name = name.map(|x| *x).unwrap_or(self.db.name("_"));
            S(
                Box::new(Pre::Pi(icit, name, Some(c), lhs, rhs)),
                Span(start, self.pos_right()),
            )
        } else if self.maybe(Tok::WideArrow) {
            // lambda
            let rhs = self.fun(true); // TODO do we allow `x => x, x`?
            let pat = S(
                Box::new(
                    self.reparse_pattern(&lhs, &Doc::start("expected pattern in lambda argument")),
                ),
                lhs.span(),
            );
            S(
                Box::new(Pre::Lam(icit, pat, rhs)),
                Span(start, self.pos_right()),
            )
        } else if pair && self.maybe_raw(Tok::Comma) {
            // Ignore trailing commas when they're immediately followed by a dedent
            self.skip_trivia_();
            if self.peek() == Tok::Dedent {
                self.skip_trivia(false);
                lhs
            } else {
                self.skip_trivia(false);
                // sigma
                let rhs = self.fun(true);
                let (name, lhs) = self.reparse_pi_param(lhs);
                let (name2, rhs) = self.reparse_pi_param(rhs);
                S(
                    Box::new(Pre::Sigma(false, icit, name, lhs, name2, rhs)),
                    Span(start, self.pos_right()),
                )
            }
        } else {
            lhs
        }
    }
    fn term(&mut self) -> SPre {
        let a = self.fun(true);
        if self.maybe(Tok::Equals) {
            let b = self.term();
            let span = Span(a.span().0, b.span().1);
            S(Box::new(Pre::Assign(a, b)), span)
        } else {
            a
        }
    }
    fn def(&mut self) -> PreDef {
        if self.maybe(Tok::TypeKw) {
            let name = self.spanned(Self::name);
            let args: Vec<_> = std::iter::from_fn(|| {
                let sstart = self.pos();
                self.maybe(Tok::COpen)
                    .then(|| {
                        if self.maybe(Tok::CClose) {
                            (Impl, S(Box::new(Pre::Unit), Span(sstart, self.pos_right())))
                        } else {
                            let a = self.term();
                            self.expect(Tok::CClose);
                            (Impl, a)
                        }
                    })
                    .or_else(|| self.peek().starts_atom().then(|| (Expl, self.atom())))
                    .map(|(i, p)| {
                        (
                            i,
                            S(
                                Box::new(self.reparse_pattern(
                                    &p,
                                    &Doc::start("expected pattern in type parameters"),
                                )),
                                p.span(),
                            ),
                        )
                    })
            })
            .collect();
            let plen = self.push_indent(Some(Tok::OfKw));
            let mut variants = Vec::new();
            while self.has_indent(plen) {
                let name = self.spanned(Self::name);
                let sstart = self.pos();
                let arg = self
                    .maybe(Tok::COpen)
                    .then(|| {
                        if self.maybe(Tok::CClose) {
                            (Impl, S(Box::new(Pre::Unit), Span(sstart, self.pos_right())))
                        } else {
                            let a = self.term();
                            self.expect(Tok::CClose);
                            (Impl, a)
                        }
                    })
                    .or_else(|| self.peek().starts_atom().then(|| (Expl, self.atom())));
                let ty = self
                    .maybe(Tok::Colon)
                    .then(|| self.fun(true))
                    .map(|mut ty| {
                        if let Some((icit, arg)) = &arg {
                            let span = Span(arg.span().0, ty.span().1);
                            let (name, aty) = self.reparse_pi_param(arg.clone());
                            ty = S(
                                Box::new(Pre::Pi(
                                    *icit,
                                    name.as_deref().copied().unwrap_or(self.db.name("_")),
                                    None,
                                    aty,
                                    ty,
                                )),
                                span,
                            );
                        }
                        ty
                    });
                variants.push((name, arg, ty));
                if plen.is_none() {
                    break;
                }
                if self.has_indent(plen) {
                    self.expect(Tok::Newline);
                }
            }
            return PreDef::Type {
                name,
                args,
                variants,
            };
        }

        self.expect(Tok::DefKw);
        let name = self.spanned(Self::name);
        let mut last = self.pos - 1;
        let args: Vec<_> = std::iter::from_fn(|| {
            // make sure this iterator doesn't run infinitely (possible in weird edge cases)
            if self.pos == last {
                return None;
            }
            last = self.pos;
            let sstart = self.pos();
            self.maybe(Tok::COpen)
                .then(|| {
                    if self.maybe(Tok::CClose) {
                        (Impl, S(Box::new(Pre::Unit), Span(sstart, self.pos_right())))
                    } else {
                        let a = self.term();
                        self.expect(Tok::CClose);
                        (Impl, a)
                    }
                })
                .or_else(|| self.peek().starts_atom().then(|| (Expl, self.atom())))
                .map(|(i, p)| {
                    (
                        i,
                        S(
                            Box::new(self.reparse_pattern(
                                &p,
                                &Doc::start("expected pattern in function argument"),
                            )),
                            p.span(),
                        ),
                    )
                })
        })
        .collect();
        let ty = self
            .maybe(Tok::Colon)
            .then(|| self.fun(true))
            .or_else(|| {
                (!args.is_empty())
                    .then(|| S(Box::new(Pre::Hole(HoleSource::TypeOf(name))), name.span()))
            })
            .map(|mut ty| {
                for (icit, arg) in args.iter().rev() {
                    let span = Span(arg.span().0, ty.span().1);
                    // TODO ???
                    let arg = arg.extract_ty(&self.db).unwrap_or_else(|| {
                        self.error("illegal type argument (??)", arg.span());
                        S(Box::new(Pre::Error), arg.span())
                    });
                    let (name, aty) = self.reparse_pi_param(arg.clone());
                    ty = S(
                        Box::new(Pre::Pi(
                            *icit,
                            name.as_deref().copied().unwrap_or(self.db.name("_")),
                            // TODO how do we specify these on function definitions?
                            None,
                            aty,
                            ty,
                        )),
                        span,
                    );
                }
                ty
            });
        let value = self
            .maybe(Tok::Equals)
            .then(|| self.term())
            .map(|mut value| {
                for (icit, arg) in args.into_iter().rev() {
                    let span = Span(arg.span().0, value.span().1);
                    value = S(Box::new(Pre::Lam(icit, arg, value)), span);
                }
                value
            });
        PreDef::Val { name, ty, value }
    }

    fn defs(&mut self) -> Vec<S<PreDef>> {
        self.skip_trivia(true);

        let mut v = Vec::new();
        let mut last = self.pos();
        while self.peek() != Tok::Eof {
            let n_errs = self.errors.len();
            v.push(self.spanned(Self::def));
            if self.errors.len() > n_errs {
                self.reset_to(Tok::Newline);
            } else if self.peek() != Tok::Eof {
                self.expect(Tok::Newline);
            }
            if last == self.pos() {
                self.error(
                    &format!("expected end of file, found {}", self.peek()),
                    self.tok_span(),
                );
                break;
            }
            last = self.pos();
        }
        v
    }
}

impl SPrePat {
    pub fn extract_ty(&self, db: &DB) -> Option<SPre> {
        Some(S(
            Box::new(match &***self {
                PrePat::Name(_, s) => Pre::Binder(
                    S(Box::new(Pre::Var(**s)), s.span()),
                    S(Box::new(Pre::Hole(HoleSource::TypeOf(*s))), s.span()),
                ),
                PrePat::Binder(s, s1) => {
                    let s = s.extract_ty(db)?;
                    match &**s {
                        // Hopefully we're not ignoring anything important!
                        Pre::Binder(x, _) => Pre::Binder(x.clone(), s1.clone()),
                        _ => Pre::Binder(s, s1.clone()),
                    }
                }
                PrePat::Pair(icit, a, b) => {
                    let mut a = a.extract_ty(db)?;
                    let n1 = match &**a {
                        Pre::Binder(x, y) => match &***x {
                            Pre::Var(n) => {
                                let n = S(*n, x.span());
                                a = y.clone();
                                Some(n)
                            }
                            _ => None,
                        },
                        _ => None,
                    };
                    let mut b = b.extract_ty(db)?;
                    let n2 = match &**b {
                        Pre::Binder(x, y) => match &***x {
                            Pre::Var(n) => {
                                let n = S(*n, x.span());
                                b = y.clone();
                                Some(n)
                            }
                            _ => None,
                        },
                        _ => None,
                    };
                    Pre::Sigma(false, *icit, n1, a, n2, b)
                }
                PrePat::Cons(s, _) => return None,
                PrePat::Error => Pre::Error,
            }),
            self.span(),
        ))
    }
}

// Properties of tokens
impl Tok {
    fn starts_atom(self) -> bool {
        matches!(
            self,
            Tok::POpen
                | Tok::Name
                | Tok::COpen
                | Tok::SOpen
                | Tok::DoKw
                | Tok::IfKw
                | Tok::TypeTypeKw
                | Tok::ImmKw
                | Tok::MutKw
                | Tok::OwnKw
                | Tok::Minus
                | Tok::IntLit
                | Tok::StringLit
                | Tok::FloatLit
        )
    }
    fn starts_def(self) -> bool {
        matches!(
            self,
            Tok::DefKw | Tok::TypeKw | Tok::TraitKw | Tok::EffKw | Tok::ImplKw
        )
    }
    fn is_trivia(self) -> bool {
        matches!(self, Tok::Whitespace | Tok::Comment)
    }
}
