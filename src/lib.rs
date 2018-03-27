//! The `linked_array` crate provides access to arbitrarilly sized arrays
//! That use the same in-memory representation as traditional slices.
//! In order to remain performant, this crate depends on optimisations
//! capable of fully executing tail-recursive loops at compile time.

/// A generic trait for arbitarily fixed size arrays.
pub trait Array<T> {
	/// Access the element at idx, or None if out of bounds.
    fn get(&self, idx: usize) -> Option<&T>;

    /// Get the compile-time length of the array.
    fn len() -> usize;

    /// Since the in-memory representation should be the same as a traditional array,
    /// it should be safe to read the pointer as one. However, since the rust
    /// specification makes memory layout undefined, it is held behind unsafe.
    unsafe fn as_slice(&self) -> &[T] {
        ::std::slice::from_raw_parts(self as *const Self as *const T, Self::len())
    }

    /// A conveinence wrapper around len that takes a refernce to facilitate using the right type.
    fn size(&self) -> usize { Self::len() }
}

/// The type used for a non-empty array.
/// Analogous to a cons cell in a linked list.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cons<T,L>(pub T, pub L);

/// The type used for an empty array or array terminator.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Term;

impl <T, L: Array<T>> Array<T> for Cons<T, L> {
    fn get(&self, idx: usize) -> Option<&T> {
        match idx {
            0 => Some(&self.0),
            n => self.1.get(n-1),
        }
    }
    
    fn len() -> usize { 1 + L::len() }
}
impl <T> Array<T> for Term {
    fn get(&self, _: usize) -> Option<&T> { None }
    fn len() -> usize { 0 }
}

/// An extension of Array that allows for transforming the elements.
pub trait Map<T, S> : Array<T> {
	/// The resulting Array from performing the map.
    type Output : Array<S>;

    /// Transform the elements of the array using the provided function.
    fn map<F: Fn(T)->S>(self, f: F) -> Self::Output;
}

impl <T, S, L: Map<T, S>> Map<T, S> for Cons<T, L> {
    type Output = Cons<S, L::Output>;
    fn map<F: Fn(T)->S>(self, f: F) -> Self::Output {
        Cons(f(self.0), self.1.map(f))
    }
}

impl <T, S> Map<T, S> for Term {
    type Output = Term;
    fn map<F: Fn(T)->S>(self, _: F) -> Term {
        Term
    }
}

/// Builds a linked array.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate linked_array;
/// # use linked_array::{Cons, Term};
/// # fn main() {
/// assert_eq!(array![1,2,3,4], Cons(1, Cons(2, Cons(3, Cons(4, Term)))))
/// # }
/// ```
#[macro_export]
macro_rules! array {
    // Base case:
    () => {{$crate::Term}};
    ($x:expr) => {{$crate::Cons($x, $crate::Term)}};
    // `$x` followed by at least one `$y,`
    ($x:expr, $($y:expr),+) => {{$crate::Cons($x, array!($($y),+))}};
}

#[cfg(test)]
mod tests {
	use super::{Cons, Term, Map, Array};
    #[test]
    fn it_works() {
    	let x = array![1,2,3,4];
        assert_eq!(x, Cons(1, Cons(2, Cons(3, Cons(4, Term)))));
        assert_eq!(x.get(5), None);
        assert_eq!(x.get(1), Some(&2));
        assert_eq!(x.map(|x| x*2), array![2,4,6,8]);
    }
}
