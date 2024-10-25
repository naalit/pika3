use lsp_types::Url;
pub use std::borrow::Cow::{self, Borrowed, Owned};
use std::collections::HashMap;
use std::path::PathBuf;
pub use std::sync::Arc;
use std::{fmt::Display, sync::RwLock};
use yansi::Color;

pub use educe::Educe;
pub use im_rope::Rope;
pub use tap::Tap;

pub use crate::query::DB;
pub use crate::{
    pretty::{Doc, Prec, Pretty},
    query::Interned,
};

#[inline]
pub fn with_stack<A>(c: impl FnOnce() -> A) -> A {
    if cfg!(feature = "segmented-stack") {
        stacker::maybe_grow(32 * 1024, 10 * 1024 * 1024, || c())
    } else {
        c()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Class {
    Lam,
    Pi,
    /// Sigmas, unlike other closures, can have a name assigned to the second value (the closure body)
    Sigma(Name),
}
pub use Class::*;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Icit {
    Impl,
    Expl,
}
pub use Icit::*;
impl Display for Icit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Impl => write!(f, "implicit"),
            Expl => write!(f, "explicit"),
        }
    }
}

pub type Str = Arc<str>;

pub trait ToRope {
    fn rope(self) -> Rope;
}
impl ToRope for &str {
    fn rope(self) -> Rope {
        self.into()
    }
}

pub fn default<T: Default>() -> T {
    Default::default()
}

#[derive(Educe)]
#[educe(Clone, Debug, Default)]
pub struct Ref<A>(Arc<RwLock<A>>);

impl<A: std::hash::Hash> std::hash::Hash for Ref<A> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.with(|a| a.hash(state));
    }
}

impl<A: Ord> Ord for Ref<A> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.with(|a| other.with(|b| a.cmp(b)))
    }
}
impl<A: PartialOrd> PartialOrd for Ref<A> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.with(|a| other.with(|b| a.partial_cmp(b)))
    }
}
impl<A: Eq> Eq for Ref<A> {}
impl<A: PartialEq> PartialEq for Ref<A> {
    fn eq(&self, other: &Self) -> bool {
        self.with(|a| other.with(|b| a == b))
    }
}
impl<A> Ref<A> {
    #[inline]
    pub fn with<R>(&self, f: impl FnOnce(&A) -> R) -> R {
        f(&*self.0.read().unwrap())
    }
    #[inline]
    pub fn with_mut<R>(&self, f: impl FnOnce(&mut A) -> R) -> R {
        f(&mut *self.0.write().unwrap())
    }
    pub fn take(&self) -> A
    where
        A: Default,
    {
        self.with_mut(std::mem::take)
    }
    pub fn set(&self, val: A) -> A {
        self.with_mut(|a| std::mem::replace(a, val))
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span(pub u32, pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct S<A>(pub A, pub Span);
impl<A> S<A> {
    pub fn span(&self) -> Span {
        self.1
    }
}
impl<A> std::ops::Deref for S<A> {
    type Target = A;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<A> std::ops::DerefMut for S<A> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

// TODO should this be a newtype instead of an alias?
pub type Name = Interned<Str>;
impl Pretty for Name {
    fn pretty(&self, db: &DB) -> Doc {
        Doc::start(db.get(*self))
    }
}
pub type SName = S<Name>;

// from pika2
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FileLoc {
    File(PathBuf),
    Input,
}
impl FileLoc {
    pub fn to_url(self) -> Option<Url> {
        match self {
            FileLoc::File(path) => Url::from_file_path(path).ok(),
            FileLoc::Input => None,
        }
    }
    pub fn parent(self) -> Option<FileLoc> {
        match self {
            FileLoc::File(path) => Some(FileLoc::File(path.parent()?.to_owned())),
            FileLoc::Input => None,
        }
    }
    /// The file name without the file extension
    pub fn name(self) -> Str {
        match self {
            FileLoc::File(path) => path.file_stem().unwrap().to_str().unwrap().into(),
            FileLoc::Input => "<input>".into(),
        }
    }
}
impl Display for FileLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FileLoc::File(path) => write!(f, "{}", path.file_name().unwrap().to_str().unwrap()),
            FileLoc::Input => write!(f, "<input>"),
        }
    }
}

pub type File = Interned<FileLoc>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DefLoc {
    Crate(Name),
    Child(Def, Name),
}
impl DefLoc {
    pub fn parent(&self) -> Option<Def> {
        match self {
            DefLoc::Crate(_) => None,
            DefLoc::Child(d, _) => Some(*d),
        }
    }
    pub fn name(&self) -> Name {
        match self {
            DefLoc::Crate(n) => *n,
            DefLoc::Child(_, n) => *n,
        }
    }
}
pub type Def = Interned<DefLoc>;
impl Pretty for Def {
    fn pretty(&self, db: &DB) -> Doc {
        match db.idefs.get(*self) {
            DefLoc::Crate(name) => name.pretty(db),
            DefLoc::Child(parent, name) => parent.pretty(db).add(".", ()).chain(name.pretty(db)),
        }
    }
}

fn byte_to_char(rope: &Rope, byte: usize) -> usize {
    let mut b = 0;
    let mut li = 0;
    for (i, c) in rope.chars().enumerate() {
        li = i;
        if byte < b + c.len_utf8() {
            return i;
        }
        b += c.len_utf8();
    }
    if byte <= b {
        return li + 1;
    }
    panic!(
        "out of bounds: byte position {} in rope len {}",
        byte,
        rope.len()
    )
}
// (line idx, line start byte idx, line text)
fn byte_to_line(rope: &Rope, byte: usize) -> (usize, usize, Rope) {
    let mut b = 0;
    let mut li = 0;
    for (i, r) in rope.lines().enumerate() {
        li = i;
        if byte <= b + r.len() {
            return (i, b, r);
        }
        b += r.len() + 1; // assume that all lines end with \n; if we get \r\n we return the wrong index, so make sure to check for that somewhere else
    }
    if byte <= b {
        return (li + 1, b, Rope::new());
    }
    panic!(
        "out of bounds: byte position {} in rope len {}",
        byte,
        rope.len()
    )
}

/// Uses byte positions
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct AbsSpan(pub File, pub Span);
impl AbsSpan {
    pub fn span(self) -> Span {
        self.1
    }

    pub fn add(self, other: Span) -> Self {
        AbsSpan(
            self.0.clone(),
            Span(self.1 .0 + other.0, self.1 .0 + other.0),
        )
    }

    pub fn chars(self, db: &DB) -> CharSpan {
        let text = db.file_rope(self.0);
        let start = byte_to_char(&text, self.1 .0 as usize) as u32;
        let end = byte_to_char(&text, self.1 .1 as usize) as u32;
        CharSpan(self.0, start..end)
    }

    pub fn lsp_range(self, db: &DB) -> lsp_types::Range {
        let text = db.file_rope(self.0);

        let (line0_idx, line0_byte, line0_text) = byte_to_line(&text, self.1 .0 as usize);
        let (line1_idx, line1_byte, line1_text) = byte_to_line(&text, self.1 .1 as usize);
        let start_char = byte_to_char(&line0_text, self.1 .0 as usize - line0_byte);
        let end_char = byte_to_char(&line1_text, self.1 .1 as usize - line1_byte);

        lsp_types::Range {
            start: lsp_types::Position {
                line: line0_idx as u32,
                character: start_char as u32,
            },
            end: lsp_types::Position {
                line: line1_idx as u32,
                character: end_char as u32,
            },
        }
    }
}
impl Span {
    pub fn abs(self, file: File) -> AbsSpan {
        AbsSpan(file, Span(self.0, self.1))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CharSpan(pub File, pub std::ops::Range<u32>);
impl ariadne::Span for CharSpan {
    type SourceId = File;

    fn source(&self) -> &Self::SourceId {
        &self.0
    }

    fn start(&self) -> usize {
        self.1.start as usize
    }

    fn end(&self) -> usize {
        self.1.end as usize
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    Error,
    Warning,
}
impl Severity {
    fn ariadne(self) -> ariadne::ReportKind<'static> {
        match self {
            Severity::Error => ariadne::ReportKind::Error,
            Severity::Warning => ariadne::ReportKind::Warning,
        }
    }

    fn lsp(self) -> lsp_types::DiagnosticSeverity {
        match self {
            Severity::Error => lsp_types::DiagnosticSeverity::ERROR,
            Severity::Warning => lsp_types::DiagnosticSeverity::WARNING,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: Doc,
    pub color: Option<Color>,
}
impl Label {
    fn ariadne(self, file: File, db: &DB) -> ariadne::Label<CharSpan> {
        let span = self.span.abs(file).chars(db);
        let mut l = ariadne::Label::new(span).with_message(self.message.to_string(true));
        if let Some(color) = self.color {
            l = l.with_color(color);
        }
        l
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Error {
    pub severity: Severity,
    pub message_lsp: Option<Doc>,
    pub message: Doc,
    pub primary: Label,
    pub secondary: Vec<Label>,
    pub note: Option<Doc>,
}

impl Error {
    pub fn simple(message: impl Into<Doc>, span: Span) -> Error {
        let message = message.into();
        Error {
            severity: Severity::Error,
            message_lsp: None,
            message: message.clone(),
            primary: Label {
                span,
                message,
                color: Some(Doc::COLOR1),
            },
            secondary: Vec::new(),
            note: None,
        }
    }

    pub fn with_label(mut self, m: impl Into<Doc>) -> Error {
        self.primary.message = m.into();
        self
    }

    pub fn write_cli(self, file: File, cache: &mut FileCache) {
        let primary_span = self.primary.span.abs(file);
        let mut r = ariadne::Report::build(
            self.severity.ariadne(),
            primary_span.0,
            // TODO wait should this be post converting to CharSpan?
            primary_span.1 .0 as usize,
        )
        .with_message(self.message.to_string(true))
        // The primary label appears first since it's the most important
        .with_label(self.primary.ariadne(file, &cache.db).with_order(-1));
        r.add_labels(
            self.secondary
                .into_iter()
                .enumerate()
                .map(|(i, x)| x.ariadne(file, &cache.db).with_order(i as i32)),
        );
        if let Some(note) = self.note {
            r.set_note(note.to_string(true));
        }
        r.finish().eprint(cache).unwrap();
    }

    pub fn to_lsp(self, split_span: &AbsSpan, db: &DB) -> lsp_types::Diagnostic {
        let span = split_span.add(self.primary.span);

        lsp_types::Diagnostic {
            range: span.lsp_range(db),
            severity: Some(self.severity.lsp()),
            code: None,
            code_description: None,
            source: None,
            message: self.message_lsp.unwrap_or(self.message).to_string(false),
            // TODO: in some cases we may also want separate NOTE-type diagnostics for secondary labels?
            related_information: Some(
                self.secondary
                    .into_iter()
                    .map(|x| lsp_types::DiagnosticRelatedInformation {
                        location: lsp_types::Location {
                            uri: db.ifiles.get(split_span.0).to_url().unwrap(),
                            range: split_span.add(x.span).lsp_range(db),
                        },
                        message: x.message.to_string(false),
                    })
                    .collect(),
            ),
            // TODO: this is useful for deprecated or unnecessary code
            tags: None,
            data: None,
        }
    }
}

pub struct FileCache {
    files: HashMap<File, ariadne::Source<Str>>,
    db: DB,
}
impl FileCache {
    pub fn new(db: DB) -> Self {
        FileCache {
            files: HashMap::new(),
            db,
        }
    }
}

impl ariadne::Cache<File> for FileCache {
    fn fetch(
        &mut self,
        key: &File,
    ) -> Result<&ariadne::Source<Str>, Box<dyn std::fmt::Debug + '_>> {
        Ok(self
            .files
            .entry(*key)
            .or_insert_with(|| ariadne::Source::from(self.db.file_str(*key))))
    }

    fn display<'b>(&self, key: &'b File) -> Option<Box<dyn std::fmt::Display + 'b>> {
        Some(Box::new(self.db.ifiles.get(*key)) as _)
    }

    type Storage = Str;
}
