// Ok, what things do we want to put in our database(s)?
// - Interned names
// - We were also interning e.g. def ids before, do we want to keep doing that?
// - Accumulator layers, with:
//   - Types of definitions
//   - Meta solutions (from one layer down)
//   - Remaining unsolved metas
//  (- Possibly values of definitions ???)
// - Results of hover-type queries?
//   - These do seem storeable... but note that they change much more often (and would pry need to be aggressively GC'd).
//   - Even if we don't store these, the definition itself will be stored, so it doesn't seem that bad, as long as our definition-filtering-and-type-getting are reasonably fast
// - Parse trees for definitions (we'll pry use the same split system as before so spans etc. don't change. but spans should include defid bc we're definitely constantly letting RelSpans escape definitions in pika2)
//   - there's pry no reason to intern lexing results
//   - the span system still isn't terribly incremental - if the whitespace in a type definition changes, suddenly everything using that type either messes up its type errors or has to re-elaborate.
//      is there anything we can do to improve this?
//       - i feel like what we do is at first let things have messed up type errors and then update them later in the background.
//         so i guess that means span mismatch = cache miss? but we don't auto-recompute on cache miss we just use the cached version and queue it for later?
//         still kinda unclear how this system is even going to work... is it different btwn top-level type errors query and e.g. hover type query that depends on it?
//         i mean, it does seem like in general we prefer showing stale results temporarily to showing nothing until new results are ready...
// Note that incrementality should be considered very low hanging fruit - a little goes a very long way. Even rust-analyzer can't produce type errors incrementally (at least, not very incrementally), which ends up being its bottleneck in my experience.
// okay so pipeline:
//
// SOURCE FILE (rope)
// --> splitter
// SOURCE FOR SPLIT (rope)
// --> lexer
// TOKENS FOR SPLIT (?? might just be an iterator)
//  +lex errors?
// --> parser
// PARSE TREE FOR SPLIT (`ParseTree`? `pre::Term`?)
//  +parse errors
// --> def_elab
// CORE SYNTAX (TYPED) FOR DEF (`Term`/`Definition`)
//  +type errors
//  +children
//  +unsolved metas
// --> module accumulator
// CORE SYNTAX (TYPED) FOR MODULE (/source file) (`Definition`? `Module`?)
//  +meta solutions
// --> parent module accumulator
// CORE SYNTAX (TYPED) FOR PARENT MODULE (`Definition`? `Module`?)

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    hash::Hash,
    marker::PhantomData,
    sync::RwLock,
};

use crate::{
    common::*,
    elab::{DefElabResult, Val},
    parser::ParseResult,
};

// For the database, do we want to use internal mutability like Salsa does? Probably, bc we do need to pass it around like literally everywhere
// So I think ideally we have an Arc<DB> that we pass around so we can store it in various cxts
// Or everything inside the DB is in Arc<RwLock<>>s anyway so we can just clone it
//
// So other idea: put everything in im::HashMaps etc
// The idea being we basically make a new db per def elab
// This means doing more work but it also makes the accumulator layers more deterministic
// The thing is, it seems like this could easily be "elaborate the whole module as many times as there are definitions", which sounds not great
// So I'll stick with internal mutability for now

// Other option: put the Str directly in here. Pro: lookup without DB, Con: 8 bytes instead of 4
#[derive(Educe)]
#[educe(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Interned<T>(u32, PhantomData<T>);
impl<T: Clone> Copy for Interned<T> {}
impl<T> Interned<T> {
    pub fn empty() -> Interned<T> {
        Interned(0, PhantomData)
    }
    pub fn num(self) -> u32 {
        self.0
    }
}

#[derive(Educe)]
#[educe(Clone, Default)]
pub struct Interner<T> {
    t_to_x: Arc<RwLock<HashMap<T, Interned<T>>>>,
    x_to_t: Arc<RwLock<Vec<T>>>,
}
impl<T: Clone + Eq + Hash> Interner<T> {
    // TODO determine if these are the right bounds
    pub fn intern(&self, s: &T) -> Interned<T> {
        let str_to_name = self.t_to_x.read().unwrap();
        match str_to_name.get(&s) {
            Some(n) => *n,
            None => {
                drop(str_to_name);
                let mut t_to_x = self.t_to_x.write().unwrap();
                let mut x_to_t = self.x_to_t.write().unwrap();
                let n = Interned(x_to_t.len() as u32, PhantomData);
                let value = s.clone();
                x_to_t.push(value.clone());
                t_to_x.insert(value, n);
                n
            }
        }
    }

    pub fn intern_direct<U: Eq + Hash + ?Sized>(&self, s: &U) -> Interned<T>
    where
        T: Borrow<U>,
        for<'a> &'a U: Into<T>,
    {
        let str_to_name = self.t_to_x.read().unwrap();
        match str_to_name.get(&s) {
            Some(n) => *n,
            None => {
                drop(str_to_name);
                let mut t_to_x = self.t_to_x.write().unwrap();
                let mut x_to_t = self.x_to_t.write().unwrap();
                let n = Interned(x_to_t.len() as u32, PhantomData);
                let value = s.into();
                x_to_t.push(value.clone());
                t_to_x.insert(value, n);
                n
            }
        }
    }

    pub fn get(&self, n: Interned<T>) -> T {
        self.x_to_t
            .read()
            .unwrap()
            .get(n.0 as usize)
            .unwrap()
            .clone()
    }
}

#[derive(Clone, Default)]
struct FileSource {
    rope: Rope,
    str: Option<Str>,
}

#[derive(Clone, Default)]
pub struct DB {
    names: Interner<Str>,
    pub ifiles: Interner<FileLoc>,
    pub idefs: Interner<DefLoc>,
    pub elab: ElabCache,
    files: HashMap<File, FileSource>,
    def_file: HashMap<Def, File>,
    // TODO is this the direction the map should go? should this even be a map?
    crate_roots: HashMap<File, Name>,
    parsed: HashMap<File, Arc<ParseResult>>,
}
impl DB {
    pub fn name(&self, s: &str) -> Name {
        self.names.intern_direct(s)
    }

    pub fn get(&self, n: Name) -> Str {
        self.names.get(n)
    }

    /// Modifies a name to be inaccessible in the source language, for hygiene
    /// Specifically, appends a tilde character ~ which is not legal in identifiers
    pub fn inaccessible(&self, n: Name) -> Name {
        let mut s = self.get(n).to_string();
        s.push('~');
        self.name(&s)
    }

    pub fn def_file(&self, def: Def) -> (File, Def) {
        match self.def_file.get(&def) {
            Some(f) => (*f, def),
            None => match self.idefs.get(def) {
                DefLoc::Crate(n) => panic!("no root file for crate {}", self.get(n)),
                DefLoc::Child(d, _) => self.def_file(d),
            },
        }
    }

    pub fn intern_crate(&mut self, name: Name, path: File) -> Def {
        self.crate_roots.insert(path, name);
        self.idefs.intern(&DefLoc::Crate(name))
    }

    /// If the Option<type> is None, then the definition is recursive and we need a meta
    pub fn lookup_def_name(&self, at: Def, name: Name) -> Option<(Def, Option<Arc<Val>>)> {
        let mut at = at;
        loop {
            let def = self.idefs.intern(&DefLoc::Child(at, name));
            match self.elab.def_type(def, self) {
                Ok(t) => break Some((def, Some(t))),
                Err(DefElabError::Recursive) => break Some((def, None)),
                Err(DefElabError::NotFound) => match self.idefs.get(at).parent() {
                    Some(a) => {
                        at = a;
                        continue;
                    }
                    None => break None,
                },
            }
        }
    }

    pub fn set_file_source(&mut self, f: File, rope: Rope, str: Option<Str>) {
        if self
            .files
            .insert(
                f,
                FileSource {
                    rope: rope.clone(),
                    str,
                },
            )
            .is_none()
        {
            // we just added this file, so we need to establish its root Def
            // this only depends on the path so we only have to do this when a file is first added
            let mut file = f;
            let mut v = Vec::new();
            let crate_root = loop {
                match self.crate_roots.get(&file) {
                    Some(c) => break c,
                    None => match self.ifiles.get(file).parent() {
                        Some(f2) => {
                            v.push(self.name(&self.ifiles.get(file).name()));
                            file = self.ifiles.intern(&f2);
                            continue;
                        }
                        None => panic!("file {} is not in any crate", self.ifiles.get(f)),
                    },
                }
            };
            let def = v
                .into_iter()
                .fold(self.idefs.intern(&DefLoc::Crate(*crate_root)), |acc, x| {
                    self.idefs.intern(&DefLoc::Child(acc, x))
                });
            self.def_file.insert(def, f);
        }
        let parsed = crate::parser::parse(rope, self);
        self.parsed.insert(f, Arc::new(parsed));
        self.elab.invalidate_file(f, self);
    }

    pub fn file_ast(&self, f: File) -> Arc<ParseResult> {
        self.parsed.get(&f).unwrap().clone()
    }

    pub fn file_str(&self, f: File) -> Str {
        let f = self.files.get(&f).unwrap();
        if let Some(str) = &f.str {
            str.clone()
        } else {
            // TODO
            f.rope.to_string().into()
        }
    }

    pub fn file_rope(&self, f: File) -> Rope {
        self.files.get(&f).unwrap().rope.clone()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Query {
    DefType(Def),
    DefVal(Def),
}
impl Query {
    fn def(self) -> Def {
        match self {
            Query::DefType(a) | Query::DefVal(a) => a,
        }
    }
}

struct CacheEntry {
    result: DefElabResult,
    dependencies: HashSet<Query>,
    changed_revision: (u64, u64),
    checked_revision: u64,
}

pub enum DefElabError {
    NotFound,
    Recursive,
}

#[derive(Clone, Default)]
pub struct ElabCache {
    cache: Ref<HashMap<Def, CacheEntry>>,
    current_deps: Ref<HashSet<Query>>,
    in_progress: Ref<HashSet<Def>>,
    revision: u64,
}
impl ElabCache {
    fn recompute(&self, key: Def, db: &DB) {
        let stored = self.current_deps.take();
        // TODO what's the right thing to do with defs that don't exist (this returns None)?
        assert!(!self.in_progress.with(|s| s.contains(&key)));
        self.in_progress.with_mut(|s| s.insert(key));
        if let Some(result) = crate::elab::elab_def(key, db) {
            let dependencies = self.current_deps.set(stored);
            self.cache.with_mut(|c| {
                c.insert(
                    key,
                    CacheEntry {
                        result,
                        dependencies,
                        changed_revision: (self.revision, self.revision),
                        checked_revision: self.revision,
                    },
                )
            });
        }
        self.in_progress.with_mut(|s| s.remove(&key));
    }

    fn check_valid(&self, key: Def, db: &DB) -> bool {
        let t = self.cache.with(|c| match c.get(&key) {
            Some(entry) if entry.checked_revision == self.revision => Some(true),
            Some(entry) => {
                // we've got a cached value but haven't checked it this revision
                // presumably when we change a file contents we delete all the cache entries for that file so we'll assume the file contents didn't change
                // which means we just need to make sure the dependencies haven't changed
                for k in &entry.dependencies {
                    // if *any* dependencies change, bail out early - we know we need to recompute this query and it's possible it might not need all the dependencies now!
                    // the thing we're checking is whether it changed *since the last time we checked*
                    if self.maybe_recompute_(*k, db) > entry.checked_revision {
                        return Some(false);
                    }
                }
                // if all the dependencies are fine, then this is valid, so return true
                // BUT we need to update the checked revision because now we've checked. so we need to get out of the immutable `with` first
                // the option just provides a signal value for that case
                None
            }
            None => Some(false),
        });
        match t {
            Some(t) => t,
            None => {
                self.cache
                    .with_mut(|c| c.get_mut(&key).unwrap().checked_revision = self.revision);
                true
            }
        }
    }

    fn maybe_recompute_(&self, key: Query, db: &DB) -> u64 {
        let (t, v) = self.maybe_recompute(key.def(), db);
        match key {
            Query::DefType(_) => t,
            Query::DefVal(_) => v,
        }
    }

    // Returns the revision where the value last changed, for convenience
    // (type, value)
    fn maybe_recompute(&self, key: Def, db: &DB) -> (u64, u64) {
        if self.check_valid(key.clone(), db) {
            self.cache.with(|x| x.get(&key).unwrap().changed_revision)
        } else if let Some(entry) = self.cache.with_mut(|x| x.remove(&key)) {
            self.recompute(key, db);
            let tb = self.cache.with(|x| {
                x.get(&key)
                    .map_or(false, |x| x.result.def.ty != entry.result.def.ty)
            });
            let vb = self.cache.with(|x| {
                x.get(&key)
                    .map_or(false, |x| x.result.def.body != entry.result.def.body)
            });
            let revision = (
                if tb {
                    self.revision
                } else {
                    entry.changed_revision.0
                },
                // if the type changes and the value doesn't, that still counts as a value change
                if tb || vb {
                    self.revision
                } else {
                    entry.changed_revision.1
                },
            );
            self.cache
                .with_mut(|x| x.get_mut(&key).unwrap().changed_revision = revision);
            revision
        } else {
            self.recompute(key, db);
            (self.revision, self.revision)
        }
    }

    fn invalidate_file(&self, f: File, db: &DB) {
        self.cache
            .with_mut(|m| m.retain(|k, _| db.def_file(*k).0 != f))
    }

    pub fn def_value(&self, key: Def, db: &DB) -> Result<DefElabResult, DefElabError> {
        if self.in_progress.with(|s| s.contains(&key)) {
            return Err(DefElabError::Recursive);
        }
        self.current_deps.with_mut(|a| a.insert(Query::DefVal(key)));
        self.maybe_recompute(key.clone(), db);
        self.cache
            .with(|c| c.get(&key).map(|e| e.result.clone()))
            .ok_or(DefElabError::NotFound)
    }

    pub fn def_type(&self, key: Def, db: &DB) -> Result<Arc<Val>, DefElabError> {
        if self.in_progress.with(|s| s.contains(&key)) {
            return Err(DefElabError::Recursive);
        }
        self.current_deps
            .with_mut(|a| a.insert(Query::DefType(key)));
        self.maybe_recompute(key.clone(), db);
        self.cache
            .with(|c| c.get(&key).map(|e| e.result.def.ty.clone()))
            .ok_or(DefElabError::NotFound)
    }
}
