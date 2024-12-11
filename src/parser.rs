use crate::common::*;
use crate::lexer::*;

// `def f {x y} {z w} (a b): t = ...`
// but for now:
// `def f : t = ...`
#[derive(Debug)]
pub struct PreDef {
    pub name: SName,
    pub ty: Option<SPre>,
    pub value: Option<SPre>,
}
pub type SPrePat = S<Box<PrePat>>;

#[derive(Debug, Clone)]
pub enum PrePat {
    Name(bool, SName),
    Binder(SPrePat, SPre),
    Pair(Icit, SPrePat, SPrePat),
    Error,
}
#[derive(Debug, Clone)]
pub enum PreStmt {
    Expr(SPre),
    Let(SPrePat, SPre),
}
#[derive(Debug, Clone)]
pub enum Pre {
    Type,
    Var(Name),
    Binder(SPre, SPre),
    App(SPre, SPre, Icit),
    Pi(Icit, Name, u32, FCap, SPre, SPre),
    Sigma(Icit, Option<SName>, SPre, Option<SName>, SPre),
    Lam(Icit, SPrePat, SPre),
    Do(Vec<PreStmt>, SPre),
    Cap(u32, Cap, SPre),
    Assign(SPre, SPre),
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
            .unwrap_or_else(|| self.starts.last().unwrap())
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
    fn expect(&mut self, t: Tok) {
        if !self.maybe(t) {
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

    // reparsing

    fn reparse_pi_param(&mut self, param: SPre) -> (Option<SName>, SPre) {
        match &**param {
            Pre::Binder(lhs, rhs) => {
                match &***lhs {
                    Pre::Var(name) => (Some(S(*name, lhs.span())), rhs.clone()),
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
            Pre::Cap(0, Cap::Mut, p) => match &***p {
                Pre::Var(name) => PrePat::Name(true, S(*name, param.span())),
                _ => {
                    self.error("invalid pattern", param.span());
                    PrePat::Error
                }
            },
            Pre::Var(name) => PrePat::Name(false, S(*name, param.span())),
            // TODO (mut a : T, mut b : T)
            Pre::Sigma(i, n1, a, n2, b) => {
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
                    let t = s.term();
                    s.expect(Tok::PClose);
                    *t.0
                }
                Tok::DoKw => {
                    s.next_raw();
                    s.skip_trivia_();
                    if s.maybe(Tok::Indent) {
                        s.indent_stack.push(false);
                    }
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
                    Pre::Do(v, last)
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
        if self.maybe(Tok::OwnKw) {
            let rest = self.app();
            return S(
                Box::new(Pre::Cap(1, Cap::Own, rest)),
                Span(start, self.pos_right()),
            );
        } else if self.maybe(Tok::ImmKw) {
            let rest = self.app();
            return S(
                Box::new(Pre::Cap(1, Cap::Imm, rest)),
                Span(start, self.pos_right()),
            );
        } else if self.maybe(Tok::RefKw) {
            let rest = self.app();
            return S(
                Box::new(Pre::Cap(0, Cap::Imm, rest)),
                Span(start, self.pos_right()),
            );
        } else if self.maybe(Tok::MutKw) {
            let rest = self.app();
            return S(
                Box::new(Pre::Cap(0, Cap::Mut, rest)),
                Span(start, self.pos_right()),
            );
        }
        let mut a = self.atom();
        // make sure we don't get in an infinite loop - stop looking for atoms if we don't consume any input
        let mut last = start;
        while self.peek().starts_atom() && last != self.pos() {
            last = self.pos();
            if self.maybe(Tok::COpen) {
                let term = self.term();
                self.expect(Tok::CClose);
                a = S(
                    Box::new(Pre::App(a, term, Impl)),
                    Span(start, self.pos_right()),
                );
            } else {
                a = S(
                    Box::new(Pre::App(a, self.atom(), Expl)),
                    Span(start, self.pos_right()),
                );
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
            self.term()
        } else if pair {
            self.fun(false)
        } else {
            self.binder()
        };
        if implicit {
            self.expect(Tok::CClose);
        }
        let icit = if implicit { Impl } else { Expl };
        if matches!(self.peek(), Tok::BitAnd | Tok::Arrow | Tok::WavyArrow) {
            // pi (possibly &->)
            let mut n = 0;
            while self.maybe(Tok::BitAnd) {
                n += 1;
            }
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
                Box::new(Pre::Pi(icit, name, n, c, lhs, rhs)),
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
        } else if pair && self.maybe(Tok::Comma) {
            // sigma
            let rhs = self.fun(true);
            let (name, lhs) = self.reparse_pi_param(lhs);
            let (name2, rhs) = self.reparse_pi_param(rhs);
            S(
                Box::new(Pre::Sigma(icit, name, lhs, name2, rhs)),
                Span(start, self.pos_right()),
            )
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
        self.expect(Tok::DefKw);
        let name = self.spanned(Self::name);
        let ty = self.maybe(Tok::Colon).then(|| self.fun(true));
        let value = self.maybe(Tok::Equals).then(|| self.term());
        PreDef { name, ty, value }
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
    fn is_trivia(self) -> bool {
        matches!(self, Tok::Whitespace | Tok::Comment)
    }
}
