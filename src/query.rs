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

use std::{collections::HashMap, sync::RwLock};

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
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(u32);

#[derive(Clone, Default)]
pub struct DB {
  str_to_name: Arc<RwLock<HashMap<Str, Name>>>,
  name_to_str: Arc<RwLock<Vec<Str>>>,
}
impl DB {
  pub fn name(&self, s: &str) -> Name {
    let str_to_name = self.str_to_name.read().unwrap();
    match str_to_name.get(s) {
        Some(n) => *n,
        None => {
          drop(str_to_name);
          let mut str_to_name = self.str_to_name.write().unwrap();
          let mut name_to_str = self.name_to_str.write().unwrap();
          let n = Name(name_to_str.len() as u32);
          name_to_str.push(s.into());
          str_to_name.insert(s.into(), n);
          n
        }
    }
  }

  pub fn get(&self, n: Name) -> Str {
    self.name_to_str.read().unwrap().get(n.0 as usize).unwrap().clone()
  }
}
