//! Copy of the unstable [`std::ops::ControlFlow`] type, scheduled to be stabilized in 1.55.

/// Used to tell an operation whether it should exit early or go on as usual.
///
/// This is used when exposing things (like graph traversals or visitors) where
/// you want the user to be able to choose whether to exit early.
/// Having the enum makes it clearer -- no more wondering "wait, what did `false`
/// mean again?" -- and allows including a value.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ControlFlow<B, C = ()> {
    /// Move on to the next phase of the operation as normal.
    Continue(C),
    /// Exit the operation without running subsequent phases.
    Break(B),
}

impl<B, C> ControlFlow<B, C> {
    /// Returns `true` if this is a `Break` variant.
    #[inline]
    pub fn is_break(&self) -> bool {
        matches!(*self, ControlFlow::Break(_))
    }

    /// Returns `true` if this is a `Continue` variant.
    #[inline]
    pub fn is_continue(&self) -> bool {
        matches!(*self, ControlFlow::Continue(_))
    }

    /// Converts the `ControlFlow` into an `Option` which is `Some` if the
    /// `ControlFlow` was `Break` and `None` otherwise.
    #[inline]
    pub fn break_value(self) -> Option<B> {
        match self {
            ControlFlow::Continue(..) => None,
            ControlFlow::Break(x) => Some(x),
        }
    }

    /// Maps `ControlFlow<B, C>` to `ControlFlow<T, C>` by applying a function
    /// to the break value in case it exists.
    #[inline]
    pub fn map_break<T, F>(self, f: F) -> ControlFlow<T, C>
    where
        F: FnOnce(B) -> T,
    {
        match self {
            ControlFlow::Continue(x) => ControlFlow::Continue(x),
            ControlFlow::Break(x) => ControlFlow::Break(f(x)),
        }
    }
}

impl<B> ControlFlow<B, ()> {
    /// It's frequently the case that there's no value needed with `Continue`,
    /// so this provides a way to avoid typing `(())`, if you prefer it.
    pub const CONTINUE: Self = ControlFlow::Continue(());
}

impl<C> ControlFlow<(), C> {
    /// APIs like `try_for_each` don't need values with `Break`,
    /// so this provides a way to avoid typing `(())`, if you prefer it.
    pub const BREAK: Self = ControlFlow::Break(());
}
