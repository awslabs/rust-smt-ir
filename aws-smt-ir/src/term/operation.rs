use crate::{args, CoreOp, ICoreOp, IOp, ISymbol, Logic, QualIdentifier, Term, Void};
pub use aws_smt_ir_derive::Operation;
use std::fmt;

/// An `Operation` is a type that can be used as the operation of a [`Logic`] i.e. `T::Op` where
/// `T: Logic`. This should usually not be implemented manually; instead, use the derive macro
/// exported along with this trait.
///
/// Operator symbols can be specified with the `#[symbol]` attribute. For instance, to specify a
/// variant should be parsed from the `+` symbol, add `#[symbol("+")]`.
///
/// **Note:** `Operation` can only be derived for `enum`s with a single type parameter corresponding
/// to a term.
///
/// # Examples
///
/// ## Deriving `Operation` for a simple enum.
///
/// ```
/// # fn main() {
/// use aws_smt_ir::{fold::Fold, visit::Visit, Term, Operation, Logic, Void, QualIdentifier, ISort, UnknownSort, Sorted, Ctx};
/// use smt2parser::concrete::Constant;
///
/// #[derive(Operation, Fold, Visit, Clone, Hash, PartialEq, Eq)]
/// enum Math<Term> {
///     #[symbol("+")]
///     Add(Vec<Term>),
///     #[symbol("-")]
///     Neg(Term),
///     #[symbol("-")]
///     Subtract(Term, Term),
/// }
///
/// impl<L: Logic> Sorted<L> for Math<Term<L>> {
///     fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
///         Ok(ISort::int())
///     }
/// }
///
/// #[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
/// struct L;
/// impl Logic for L {
///     type Var = QualIdentifier;
///     type Op = Math<Term<Self>>;
///     type Quantifier = Void;
///     type UninterpretedFunc = Void;
/// }
/// type Op = Math::<Term<L>>;
///
/// let x = || Constant::Numeral(0u8.into()).into();
/// let t = || Term::Constant(x());
/// let func = QualIdentifier::from("-");
/// assert!(matches!(Op::parse(func.clone(), vec![]), Err(_)));
/// assert_eq!(Op::parse(func.clone(), vec![t()]), Ok(Math::Neg(Term::Constant(x()))));
/// assert_eq!(
///     Op::parse(func.clone(), vec![t(), t()]),
///     Ok(Math::Subtract(Term::Constant(x()), Term::Constant(x())))
/// );
/// assert!(matches!(Op::parse(func, vec![t(), t(), t()]), Err(_)));
/// # }
/// ```
pub trait Operation<T: Logic>: Sized {
    /// Parses an operation from a function identifier and list of arguments.
    fn parse(func: QualIdentifier, args: Vec<Term<T>>) -> Result<Self, InvalidOp<T>>;

    /// Produces the function symbol of the application.
    fn func(&self) -> ISymbol;
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct InvalidOp<T: Logic> {
    pub func: QualIdentifier,
    pub args: Vec<Term<T>>,
}

impl<T: Logic> fmt::Display for InvalidOp<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Invalid function application in logic {:?}: ({} ",
            T::default(),
            self.func
        )?;
        args::Format::fmt(&self.args, f, fmt::Display::fmt)?;
        write!(f, ")")
    }
}

impl<T: Logic> std::error::Error for InvalidOp<T> where Self: fmt::Debug + fmt::Display {}

impl<L: Logic> Operation<L> for ICoreOp<L> {
    fn parse(func: QualIdentifier, args: Vec<Term<L>>) -> Result<Self, InvalidOp<L>> {
        CoreOp::parse(func, args).map(Into::into)
    }

    fn func(&self) -> ISymbol {
        self.as_ref().func()
    }
}

impl<L: Logic> Operation<L> for IOp<L> {
    fn parse(func: QualIdentifier, args: Vec<Term<L>>) -> Result<Self, InvalidOp<L>> {
        L::Op::parse(func, args).map(Into::into)
    }

    fn func(&self) -> ISymbol {
        self.as_ref().func()
    }
}

impl<T: Logic> Operation<T> for Void {
    fn parse(func: QualIdentifier, args: Vec<Term<T>>) -> Result<Self, InvalidOp<T>> {
        Err(InvalidOp { func, args })
    }

    fn func(&self) -> ISymbol {
        match *self {}
    }
}

impl<L: Logic> From<Void> for IOp<L> {
    fn from(x: Void) -> Self {
        match x {}
    }
}
