use std::sync::RwLock;
pub use std::{num::NonZeroU32, sync::Arc};

pub use im_rope::Rope;
pub use tap::Tap;

pub use crate::query::{Name, DB};

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

pub struct Fun<A, R>(Arc<dyn Fn(A) -> R>);
pub fn fun<A, R>(f: impl Fn(A) -> R + 'static) -> Fun<A, R> {
    Fun(Arc::new(f))
}
pub struct FunMut<A, R>(Box<dyn FnMut(A) -> R>);

#[derive(Clone, Debug, Default)]
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
    pub fn with<R>(&self, f: impl FnOnce(&A) -> R) -> R {
        f(&*self.0.read().unwrap())
    }
    pub fn with_mut<R>(&self, f: impl FnOnce(&mut A) -> R) -> R {
        f(&mut *self.0.write().unwrap())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span(pub u32, pub u32);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
