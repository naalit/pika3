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

use crate::common::*;

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
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Interned<T>(u32, PhantomData<T>);
impl<T: Clone> Copy for Interned<T> {}

#[derive(Clone)]
pub struct Interner<T> {
    t_to_x: Arc<RwLock<HashMap<T, Interned<T>>>>,
    x_to_t: Arc<RwLock<Vec<T>>>,
}
impl<T> Default for Interner<T> {
    fn default() -> Self {
        Self {
            t_to_x: Default::default(),
            x_to_t: Default::default(),
        }
    }
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

#[derive(Clone, PartialEq)]
struct ElabResult {}

#[derive(Clone)]
pub struct DB {
    names: Interner<Str>,
    pub ifiles: Interner<FileLoc>,
    pub idefs: Interner<DefLoc>,
    // elab: Cache<Def, ElabResult>,
    files: HashMap<File, FileSource>,
}
impl Default for DB {
    fn default() -> Self {
        Self {
            names: default(),
            ifiles: default(),
            idefs: default(),
            files: default(),
            // elab: todo!(),
        }
    }
}
impl DB {
    pub fn name(&self, s: &str) -> Name {
        self.names.intern_direct(s)
    }

    pub fn get(&self, n: Name) -> Str {
        self.names.get(n)
    }

    pub fn set_file_source(&mut self, f: File, rope: Rope, str: Option<Str>) {
        self.files.insert(f, FileSource { rope, str });
        // TODO invalidate elab cache
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

// TODO we're going to want the cache to track dependencies on values separately from dependencies on types

#[derive(Clone, Default)]
struct CacheEntry<K, V> {
    value: V,
    dependencies: HashSet<K>,
    changed_revision: u64,
    checked_revision: u64,
}

#[derive(Clone)]
struct Cache<K, V> {
    cache: Ref<HashMap<K, CacheEntry<K, V>>>,
    in_progress: Ref<HashSet<K>>,
    revision: u64,
    func: Arc<dyn Fn(K) -> V>,
}
impl<K: Clone + Eq + Hash, V: Clone + PartialEq> Cache<K, V> {
    fn recompute(&self, key: K) {
        let stored = self.in_progress.take();
        let value = (self.func)(key.clone()); // kind of silly that this syntax is necessary
        let dependencies = self.in_progress.set(stored);
        self.cache.with_mut(|c| {
            c.insert(
                key,
                CacheEntry {
                    value: value.clone(),
                    dependencies,
                    changed_revision: self.revision,
                    checked_revision: self.revision,
                },
            )
        });
    }

    fn check_valid(&self, key: K) -> bool {
        let t = self.cache.with(|c| match c.get(&key) {
            Some(entry) if entry.checked_revision == self.revision => Some(true),
            Some(entry) => {
                // we've got a cached value but haven't checked it this revision
                // presumably when we change a file contents we delete all the cache entries for that file so we'll assume the file contents didn't change
                // which means we just need to make sure the dependencies haven't changed
                for k in &entry.dependencies {
                    // if *any* dependencies change, bail out early - we know we need to recompute this query and it's possible it might not need all the dependencies now!
                    // the thing we're checking is whether it changed *since the last time we checked*
                    if self.maybe_recompute(k.clone()) > entry.checked_revision {
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

    // Returns the revision where the value last changed, for convenience
    fn maybe_recompute(&self, key: K) -> u64 {
        if self.check_valid(key.clone()) {
            self.cache.with(|x| x.get(&key).unwrap().changed_revision)
        } else if let Some((value, revision)) = self
            .cache
            .with(|x| x.get(&key).map(|x| (x.value.clone(), x.changed_revision)))
        {
            self.recompute(key.clone());
            let b = self.cache.with(|x| x.get(&key).unwrap().value != value);
            if !b {
                // put the changed_revision back to where it was since it didn't change
                self.cache
                    .with_mut(|x| x.get_mut(&key).unwrap().changed_revision = revision);
                revision
            } else {
                self.revision
            }
        } else {
            self.recompute(key);
            self.revision
        }
    }

    pub fn get(&self, key: K) -> V {
        self.in_progress.with_mut(|a| a.insert(key.clone()));
        self.maybe_recompute(key.clone());
        self.cache.with(|c| c.get(&key).unwrap().value.clone())
    }
}
