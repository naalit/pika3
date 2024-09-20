use std::{num::NonZeroU32, sync::Arc};

use tap::Tap;

fn default<T: Default>() -> T {
    Default::default()
}

// types

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Idx(NonZeroU32);
impl Idx {
    fn at(self, env: &Env) -> Val {
        // [a, b] at 1 is a (vec[0]), at 0 is b (vec[1])
        // and the idx is stored as 1+i since it's a NonZeroU32 so this works
        if env.len() < self.0.get() as usize {
            panic!("idx {} at {}", self.0, env.len())
        }
        env[env.len() - self.0.get() as usize].clone()
    }
}

type Name = &'static str;

enum Term {
    Var(Name, Idx), // really Spanned<Name>
    App(Box<Term>, Box<Term>),
    Lam(Name, Arc<Term>), // no type annotations for now
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Sym(Name, NonZeroU32);

type Env = im::Vector<Val>;

#[derive(Clone)]
enum Val {
    Neutral(Sym, Vec<Val>),    // will be im::Vector<Elim> in the future pry?
    Lam(Name, Arc<Term>, Env), // oh update im::Vector is *way* bigger than Vec in terms of stack size
}

// eval

impl Val {
    pub fn app(self, other: Val) -> Val {
        match self {
            Val::Neutral(s, vec) => Val::Neutral(s, vec.tap_mut(|v| v.push(other))),
            Val::Lam(_, body, env) => body.eval(&env.tap_mut(|v| v.push_back(other))),
        }
    }
}

impl Term {
    pub fn eval(&self, env: &Env) -> Val {
        match self {
            Term::Var(_, idx) => idx.at(env),
            Term::App(f, x) => f.eval(env).app(x.eval(env)),
            Term::Lam(s, body) => Val::Lam(*s, body.clone(), env.clone()),
        }
    }
}

type QEnv = (im::HashMap<Sym, u32>, NonZeroU32);
impl Sym {
    fn at(self, qenv: &QEnv) -> Idx {
        // i don't *think* this is an off-by-one error...
        Idx((1 + qenv.0.len() as u32 - qenv.0.get(&self).unwrap())
            .try_into()
            .unwrap())
    }
}

impl Term {
    pub fn subst(&self, env: &Env, qenv: &QEnv) -> Term {
        match self {
            Term::Var(_, idx) => idx.at(env).quote(qenv),
            Term::App(f, x) => {
                Term::App(Box::new(f.subst(env, qenv)), Box::new(x.subst(env, qenv)))
            }
            Term::Lam(s, body) => {
                let sym = Sym(*s, qenv.1);
                let mut env = env.clone();
                let mut qenv = qenv.clone();
                env.push_back(Val::Neutral(sym, Vec::new()));
                qenv.1 = qenv.1.checked_add(1).unwrap();
                qenv.0.insert(sym, qenv.0.len() as u32 + 1);
                Term::Lam(*s, Arc::new(body.subst(&env, &qenv)))
            }
        }
    }
}

impl Val {
    pub fn quote(&self, qenv: &QEnv) -> Term {
        match self {
            Val::Neutral(s, spine) => spine.iter().fold(Term::Var(s.0, s.at(qenv)), |acc, x| {
                Term::App(Box::new(acc), Box::new(x.quote(qenv)))
            }),
            Val::Lam(s, body, env) => {
                let sym = Sym(*s, qenv.1);
                let mut env = env.clone();
                let mut qenv = qenv.clone();
                env.push_back(Val::Neutral(sym, Vec::new()));
                qenv.1 = qenv.1.checked_add(1).unwrap();
                qenv.0.insert(sym, qenv.0.len() as u32 + 1);

                Term::Lam(*s, Arc::new(body.subst(&env, &qenv)))
            }
        }
    }
}

// simple parser

type ParseError = String;

// not as nice as combinators :(
struct Parser {
    input: &'static str,
    pos: usize,
    errors: Vec<(ParseError, usize)>,
}
impl Parser {
    fn new(input: &'static str) -> Parser {
        Parser {
            input,
            pos: 0,
            errors: Vec::new(),
        }
    }
    fn peek(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }
    fn peekn(&self, n: usize) -> Option<char> {
        self.input[self.pos..].chars().nth(n)
    }
    fn skip_ws(&mut self) {
        while self.peek().map_or(false, |x| x.is_whitespace()) {
            self.next_raw();
        }
    }
    fn next_raw(&mut self) -> Option<char> {
        let r = self.peek()?;
        self.pos += r.len_utf8();
        Some(r)
    }
    fn next(&mut self) -> Option<char> {
        let n = self.next_raw();
        self.skip_ws();
        n
    }
    fn error(&mut self, e: impl Into<String>) {
        self.errors.push((e.into(), self.pos));
    }

    fn expect(&mut self, s: &str) {
        if !self.maybe(s) {
            self.error(format!("expected {}", s));
        }
    }
    fn maybe(&mut self, s: &str) -> bool {
        for (i, c) in s.chars().enumerate() {
            if self.peekn(i) != Some(c) {
                return false;
            }
        }
        self.pos += s.len();
        self.skip_ws();
        true
    }

    fn name(&mut self) -> &'static str {
        let start = self.pos;
        while self.peek().map_or(false, |x| x.is_alphabetic()) {
            self.next_raw();
        }
        let end = self.pos;
        if start == end {
            self.error("expected name");
        }
        self.skip_ws();
        &self.input[start..end]
    }
    fn atom(&mut self, bindings: &im::HashMap<Name, u32>) -> Term {
        if self.maybe("λ") {
            // lambda
            let s = self.name();
            self.expect(".");
            let body = self.term(&bindings.clone().tap_mut(|v| {
                v.insert(s, bindings.len() as u32);
            }));
            Term::Lam(s, Arc::new(body))
        } else if self.maybe("(") {
            // paren
            let term = self.term(bindings);
            self.expect(")");
            term
        } else {
            // var
            let s = self.name();
            Term::Var(
                s,
                Idx((bindings.len() as u32
                    - bindings.get(&s).copied().unwrap_or_else(|| {
                        self.error(format!("not found: {}", s));
                        0
                    }))
                .try_into()
                .unwrap()),
            )
        }
    }
    fn term(&mut self, bindings: &im::HashMap<Name, u32>) -> Term {
        let mut a = self.atom(bindings);
        while self.peek().map_or(false, |x| x != ')') && self.errors.is_empty() {
            a = Term::App(Box::new(a), Box::new(self.atom(bindings)));
        }
        a
    }
}

// simple pretty-printer

struct Show(im_rope::Rope, u32);
impl std::ops::Add<Show> for Show {
    type Output = Show;

    fn add(self, rhs: Show) -> Self::Output {
        Show(self.0 + rhs.0, self.1.max(rhs.1))
    }
}
impl std::ops::Add<&str> for Show {
    type Output = Show;

    fn add(self, rhs: &str) -> Self::Output {
        Show(self.0.tap_mut(|x| x.append(rhs)), self.1)
    }
}
impl std::ops::Add<Show> for &str {
    type Output = Show;

    fn add(self, rhs: Show) -> Self::Output {
        Show(rhs.0.tap_mut(|x| x.prepend(self)), rhs.1)
    }
}
impl Show {
    fn nest(self, prec: u32) -> Show {
        if self.1 > prec {
            ("(" + self + ")").with(0)
        } else {
            self
        }
    }

    fn with(self, prec: u32) -> Show {
        Show(self.0, prec)
    }
}

impl Term {
    pub fn show(&self) -> Show {
        match self {
            Term::Var(n, i) => Show((*n).into(), 0), // + &*format!("{}", i.0.get() - 1),
            Term::App(f, x) => f.show().nest(1) + " " + x.show().nest(0),
            Term::Lam(s, body) => Show("λ".into(), 2) + *s + ". " + body.show(),
        }
    }
}

fn main() {
    // Hey it works! 100-line evaluator. How many is the Haskell?
    // The Haskell version is ~50 lines lol. It's probably faster too bc the RTS is very well-optimized out of the box.
    // But the Rust version probably has higher like performance potential? Certainly we have more control over representations etc.
    // Well and also the Haskell version is fully-named (but no renaming bc only evaluating to WHNF), whereas we're doing locally nameless which is probably more code.
    let s = r#"(λzero.λsuc.λplus.λmul.
            (λtwo. mul two (plus two two))
            (suc (suc zero))
        )
        (λf.λx. x)
        (λz.λf.λx. f (z f x))
        (λm.λn.λf.λx. m f (n f x))
        (λm.λn.λf.λx. m (n f) x)
        (λx.λy. y x) (λx. x)
        "#;
    let mut p = Parser::new(s);
    println!(
        "{}",
        p.term(&default())
            .eval(&default())
            .quote(&(default(), 1.try_into().unwrap()))
            .show()
            .0
    );
    for (e, sp) in p.errors {
        eprintln!("{}: error: {}", sp, e);
        eprintln!("|{}", s[sp..].lines().next().unwrap());
    }
}
