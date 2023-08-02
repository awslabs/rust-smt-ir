// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use super::{
    fold::{Folder, SuperFold},
    visit::{ControlFlow, SuperVisit, Visitor},
    CoreOp, Let, Logic, Match, Quantifier, Term, UF,
};
pub use crate::smt2parser::{
    concrete::{Constant, Identifier, Keyword, Symbol},
    Binary, Decimal, Hexadecimal, Numeral,
};
use internment::Intern;
use num_traits::ToPrimitive;
use once_cell::sync::Lazy;
use std::{
    borrow::Borrow,
    cmp::Ordering,
    collections::hash_map::DefaultHasher,
    fmt,
    hash::{self, Hash, Hasher},
    iter, ops,
};

pub type Command<Term> =
    crate::smt2parser::concrete::Command<Term, ISymbol, ISort, Keyword, IConst, SExpr>;
pub type SExpr = crate::smt2parser::concrete::SExpr<IConst, ISymbol, Keyword>;
pub type Index = crate::smt2parser::visitors::Index<ISymbol>;
pub type DatatypeDec = crate::smt2parser::concrete::DatatypeDec<ISymbol, ISort>;
pub type FunctionDec = crate::smt2parser::concrete::FunctionDec<ISymbol, ISort>;
pub type AttributeValue = crate::smt2parser::concrete::AttributeValue<IConst, ISymbol, SExpr>;

/// An identifier possibly annotated with a sort.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum QualIdentifier<Identifier = IIdentifier, Sort = ISort> {
    Simple { identifier: Identifier },
    Sorted { identifier: Identifier, sort: Sort },
}

/// An SMT-LIB sort i.e. type.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Sort {
    Simple {
        identifier: IIdentifier,
    },
    Parameterized {
        identifier: IIdentifier,
        parameters: Vec<ISort>,
    },
}

impl Sort {
    /// If `self` is of the form `(_ BitVec m)`, extracts `m`.
    pub fn bv_width(&self) -> Option<&Numeral> {
        match self {
            Sort::Simple { identifier } => match identifier.as_ref() {
                crate::smt2parser::concrete::Identifier::Indexed { symbol, indices } => {
                    match (symbol.as_ref().0.as_ref(), indices.as_slice()) {
                        ("BitVec", [Index::Numeral(n)]) => Some(n),
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Simple { identifier } => write!(f, "{}", identifier),
            Self::Parameterized {
                identifier,
                parameters,
            } => {
                write!(f, "({}", identifier)?;
                for param in parameters {
                    write!(f, " {}", param)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<Identifier, Sort> fmt::Display for QualIdentifier<Identifier, Sort>
where
    Identifier: fmt::Display,
    Sort: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Simple { identifier } => identifier.fmt(f),
            Self::Sorted { identifier, sort } => write!(f, "(as {} {})", identifier, sort),
        }
    }
}

impl<Identifier, Sort> QualIdentifier<Identifier, Sort> {
    pub fn sym<Symbol>(&self) -> &Symbol
    where
        Identifier: AsRef<self::Identifier<Symbol>>,
    {
        use self::Identifier::*;
        match self {
            Self::Simple { identifier } | Self::Sorted { identifier, .. } => {
                match identifier.as_ref() {
                    Simple { symbol } | Indexed { symbol, .. } => symbol,
                }
            }
        }
    }

    pub fn sym_str<'a, Symbol: 'a>(&'a self) -> &str
    where
        Identifier: AsRef<self::Identifier<Symbol>>,
        Symbol: AsRef<self::Symbol>,
    {
        self.sym().as_ref().0.as_str()
    }

    pub fn indices(&self) -> &[Index]
    where
        Identifier: AsRef<self::Identifier<ISymbol>>,
    {
        use self::Identifier::*;
        match self {
            Self::Simple { identifier } | Self::Sorted { identifier, .. } => {
                match identifier.as_ref() {
                    Simple { .. } => &[],
                    Indexed { indices, .. } => indices.as_slice(),
                }
            }
        }
    }
}

impl QualIdentifier {
    /// Produces the corresponding binary bit-vector literal `#bY` if `self` is of the form
    /// `(_ bvX n)`.
    pub fn to_bitvec_literal(&self) -> Option<Constant> {
        if let [Index::Numeral(n)] = self.indices() {
            if let Some(x) = self.sym_str().strip_prefix("bv") {
                if let Ok(x) = x.parse::<Numeral>() {
                    let bits = (0..x.bits())
                        .map(|bit| x.bit(bit))
                        .chain(iter::repeat(false))
                        .take(n.to_usize().unwrap());
                    return Some(Constant::Binary(bits.collect()));
                }
            }
        }
        None
    }
}

impl Sort {
    pub fn sym(&self) -> &ISymbol {
        match self {
            Self::Simple { identifier } | Self::Parameterized { identifier, .. } => {
                match identifier.as_ref() {
                    Identifier::Simple { symbol } | Identifier::Indexed { symbol, .. } => symbol,
                }
            }
        }
    }

    pub fn sym_str(&self) -> &str {
        self.sym().as_ref().0.as_str()
    }
}

macro_rules! static_sort {
    ($($name:ident = $sym:expr),*) => {
        $(
            impl ISymbol {
                pub fn $name() -> Self {
                    static SYMBOL: Lazy<ISymbol> = Lazy::new(|| ISymbol::from(Symbol($sym.into())));
                    SYMBOL.clone()
                }
            }

            impl IIdentifier {
                pub fn $name() -> Self {
                    static IDENTIFIER: Lazy<IIdentifier> = Lazy::new(|| {
                        Identifier::Simple {
                            symbol: ISymbol::$name(),
                        }
                        .into()
                    });
                    IDENTIFIER.clone()
                }
            }

            impl ISort {
                pub fn $name() -> Self {
                    static SORT: Lazy<ISort> = Lazy::new(|| {
                        Sort::Simple {
                            identifier: IIdentifier::$name(),
                        }
                        .into()
                    });
                    SORT.clone()
                }
            }
        )*
    };
}

macro_rules! indexed_sort {
    ($($name:ident($($index:ident: $ty:ty),*) = $sym:expr),*) => {
        $(
            impl ISymbol {
                pub fn $name() -> Self {
                    static SYMBOL: Lazy<ISymbol> = Lazy::new(|| ISymbol::from(Symbol($sym.into())));
                    SYMBOL.clone()
                }
            }

            impl IIdentifier {
                pub fn $name($($index: $ty),*) -> Self {
                    Identifier::Indexed {
                        symbol: ISymbol::$name(),
                        indices: vec![$(IntoIndex::into_index($index)),*]
                    }
                    .into()
                }
            }

            impl ISort {
                pub fn $name($($index: $ty),*) -> Self {
                    Sort::Simple {
                        identifier: IIdentifier::$name($($index),*),
                    }
                    .into()
                }
            }
        )*
    };
}

static_sort!(
    bool = "Bool",
    int = "Int",
    real = "Real",
    string = "String",
    regex = "RegLan"
);

indexed_sort!(bitvec(width: Numeral) = "BitVec");

trait IntoIndex {
    fn into_index(self) -> Index;
}

impl IntoIndex for Numeral {
    fn into_index(self) -> Index {
        Index::Numeral(self)
    }
}

impl IntoIndex for ISymbol {
    fn into_index(self) -> Index {
        Index::Symbol(self)
    }
}

impl ISymbol {
    pub fn is_solver_internal(&self) -> bool {
        let inner = &self.as_ref().0;
        inner.starts_with('@') | inner.starts_with('.')
    }
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub struct HashOrdered<T>(pub T);

impl<T: Hash + Eq> PartialOrd for HashOrdered<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Hash + Eq> Ord for HashOrdered<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn hash(x: impl Hash) -> u64 {
            let mut hasher = DefaultHasher::new();
            x.hash(&mut hasher);
            hasher.finish()
        }
        hash(&self.0).cmp(&hash(&other.0))
    }
}

pub trait Internable: 'static + Hash + Eq + Send + Sync {}

impl<T: 'static + Hash + Eq + Send + Sync> Internable for T {}

macro_rules! interned {
    ($name:ident = $inner:ty) => {
        interned!($name<> = $inner);
    };
    ($name:ident<$($param:ident: $bound:path),*> = $inner:ty) => {
        pub struct $name<$($param: $bound),*>(Intern<Wrapper<$inner>>);

        impl<$($param: $bound),*> $name<$($param),*> {
            pub fn new(val: $inner) -> Self {
                Self(Intern::new(Wrapper(val)))
            }
        }

        impl<_L: Logic, $($param: $bound),*> SuperVisit<_L> for $name<$($param),*>
        where
            $inner: SuperVisit<_L>
        {
            fn super_visit_with<V: Visitor<_L>>(&self, v: &mut V) -> ControlFlow<V::BreakTy> {
                self.0.0.super_visit_with(v)
            }
        }

        // TODO: this probably should be the impl that exists
        // impl<_L: Logic, _Out, _Output, $($param: $bound),*> SuperFold<_L, _Out> for $name<$($param),*>
        // where
        //     for<'a> &'a $inner: SuperFold<_L, _Out, Output = _Output>,
        // {
        //     type Output = _Output;
        //     fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
        //     where
        //         F: Folder<_L, M, Output = _Out>
        //     {
        //         self.as_ref().super_fold_with(folder)
        //     }
        // }

        impl<_L: Logic, _Out, $($param: $bound),*> SuperFold<_L, _Out> for $name<$($param),*>
        where
            $inner: SuperFold<_L, _Out> + Clone,
        {
            type Output = <$inner as SuperFold<_L, _Out>>::Output;
            fn super_fold_with<F, M>(self, folder: &mut F) -> Result<Self::Output, F::Error>
            where
                F: Folder<_L, M, Output = _Out>
            {
                let inner: $inner = self.as_ref().clone();
                SuperFold::super_fold_with(inner, folder)
            }
        }

        impl<$($param: $bound),*> ops::Deref for $name<$($param),*> {
            type Target = $inner;
            fn deref(&self) -> &Self::Target {
                &self.0.0
            }
        }

        impl<$($param: $bound),*> AsRef<$inner> for $name<$($param),*> {
            fn as_ref(&self) -> &$inner {
                &self.0.0
            }
        }

        impl<$($param: $bound),*> Clone for $name<$($param),*> {
            fn clone(&self) -> Self {
                Self(Intern::clone(&self.0))
            }
        }

        impl<$($param: $bound),*> fmt::Debug for $name<$($param),*> where $inner: fmt::Debug {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.0.fmt(f)
            }
        }

        impl<$($param: $bound),*> fmt::Display for $name<$($param),*> where $inner: fmt::Display {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                self.0.0.fmt(f)
            }
        }

        impl<$($param: $bound),*> Hash for $name<$($param),*> {
            fn hash<H: hash::Hasher>(&self, state: &mut H) {
                self.0.hash(state)
            }
        }

        impl<$($param: $bound),*> PartialEq for $name<$($param),*> {
            fn eq(&self, other: &Self) -> bool {
                self.0.eq(&other.0)
            }
        }

        impl<$($param: $bound),*> Eq for $name<$($param),*> {}

        impl<_L: Logic, $($param: $bound),*> From<&$name<$($param),*>> for Term<_L>
        where
            $name<$($param),*>: Into<Term<_L>>
        {
            fn from(x: &$name<$($param),*>) -> Self {
                x.clone().into()
            }
        }
    };
}

macro_rules! from_owned {
    ($name:ident = $inner:ty) => {
        from_owned!($name<> = $inner);
    };
    ($name:ident<$($param:ident: $bound:path),*> = $inner:ty) => {
        impl<$($param: $bound),*> From<$inner> for $name<$($param),*> {
            fn from(val: $inner) -> Self {
                Self(Intern::new(Wrapper(val)))
            }
        }
    };
}

macro_rules! from_borrowed {
    ($name:ident = $inner:ty) => {
        from_borrowed!($name<> = $inner);
    };
    ($name:ident<$($param:ident: $bound:path),*> = $inner:ty) => {
        impl<$($param: $bound),*> From<&$inner> for $name<$($param),*>
        where
            $($param: Clone),*
        {
            fn from(val: &$inner) -> Self {
                Self(Intern::from_ref(val))
            }
        }
    };
}

interned!(ISymbol = Symbol);
from_owned!(ISymbol = Symbol);
from_borrowed!(ISymbol = Symbol);

interned!(ISort = Sort);
from_owned!(ISort = Sort);
from_borrowed!(ISort = Sort);

interned!(IConst = Constant);
from_owned!(IConst = Constant);
from_borrowed!(IConst = Constant);

interned!(IIndex = Index);
from_owned!(IIndex = Index);
from_borrowed!(IIndex = Index);

interned!(IIdentifier = Identifier<ISymbol>);
from_owned!(IIdentifier = Identifier<ISymbol>);
from_borrowed!(IIdentifier = Identifier<ISymbol>);

interned!(ISlice<T: Internable> = Vec<T>);
from_owned!(ISlice<T: Internable> = Vec<T>);
from_borrowed!(ISlice<T: Internable> = Vec<T>);

interned!(ICoreOp<L: Logic> = CoreOp<Term<L>>);
from_owned!(ICoreOp<L: Logic> = CoreOp<Term<L>>);
from_borrowed!(ICoreOp<L: Logic> = CoreOp<Term<L>>);

interned!(IOp<L: Logic> = L::Op);

interned!(IUF<L: Logic> = L::UninterpretedFunc);

interned!(ILet<L: Logic> = Let<Term<L>>);
from_owned!(ILet<L: Logic> = Let<Term<L>>);
from_borrowed!(ILet<L: Logic> = Let<Term<L>>);

interned!(IMatch<L: Logic> = Match<Term<L>>);
from_owned!(IMatch<L: Logic> = Match<Term<L>>);
from_borrowed!(IMatch<L: Logic> = Match<Term<L>>);

interned!(IQuantifier<L: Logic> = L::Quantifier);

impl<L: Logic<Quantifier = Quantifier<T>>, T: Internable> From<Quantifier<T>> for IQuantifier<L> {
    fn from(q: Quantifier<T>) -> Self {
        IQuantifier(Wrapper(q).into())
    }
}

impl<L: Logic<UninterpretedFunc = UF<T>>, T: Internable> From<UF<T>> for IUF<L> {
    fn from(uf: UF<T>) -> Self {
        IUF(Wrapper(uf).into())
    }
}

impl From<&QualIdentifier> for QualIdentifier {
    fn from(identifier: &QualIdentifier) -> Self {
        identifier.clone()
    }
}

impl<Identifier> From<Identifier> for QualIdentifier<Identifier> {
    fn from(identifier: Identifier) -> Self {
        Self::Simple { identifier }
    }
}

impl From<ISymbol> for QualIdentifier {
    fn from(symbol: ISymbol) -> Self {
        Self::Simple {
            identifier: Identifier::Simple { symbol }.into(),
        }
    }
}

impl<Symbol> From<Symbol> for QualIdentifier<Identifier<Symbol>> {
    fn from(symbol: Symbol) -> Self {
        Self::from(Identifier::Simple { symbol })
    }
}

impl From<String> for QualIdentifier {
    fn from(s: String) -> Self {
        Self::from(ISymbol::from(s))
    }
}

impl From<&str> for QualIdentifier {
    fn from(s: &str) -> Self {
        Self::from(ISymbol::from(s))
    }
}

impl From<String> for ISymbol {
    fn from(s: String) -> Self {
        ISymbol::from(Symbol(s))
    }
}

impl From<&str> for ISymbol {
    fn from(s: &str) -> Self {
        // TODO: don't clone, which requires a way to lookup interned symbols by &str
        ISymbol::from(&Symbol(s.to_string()))
    }
}

impl PartialOrd for ISymbol {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ISymbol {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct Wrapper<T>(T);

impl<T: Clone> From<&T> for Wrapper<T> {
    fn from(x: &T) -> Self {
        Wrapper(x.clone())
    }
}

impl<T> Borrow<T> for Wrapper<T> {
    fn borrow(&self) -> &T {
        &self.0
    }
}
