// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::{
    fold::Fold, visit::Visit, Ctx, IIndex, ISort, Logic, Operation, Sorted, Term, UnknownSort,
};
use smallvec::SmallVec;

type Args<T> = SmallVec<[T; 2]>;

#[derive(Operation, Visit, Fold, Clone, PartialEq, Eq, Hash)]
pub enum StringOp<Term> {
    /// String concatenation
    #[symbol("str.++")]
    StrConcat(Args<Term>),
    /// String length
    #[symbol("str.len")]
    Len(Term),
    /// Lexicographic ordering
    #[symbol("str.<")]
    LexOrd(Args<Term>),
    /// String to RE injection
    #[symbol("str.to_re")]
    ToRe(Term),
    /// RE membership
    #[symbol("str.in_re")]
    InRe(Term, Term),
    /// Constant denoting the empty set of strings
    #[symbol("re.none")]
    ReNone,
    /// Constant denoting the set of all strings
    #[symbol("re.all")]
    ReAll,
    /// Constant denoting the set of all strings of length 1
    #[symbol("re.allchar")]
    ReAllChar,
    /// RE concatenation
    #[symbol("re.++")]
    ReConcat(Args<Term>),
    /// RE union
    #[symbol("re.union")]
    ReUnion(Args<Term>),
    /// RE intersection
    #[symbol("re.inter")]
    ReIntersect(Args<Term>),
    /// Kleene Closure
    #[symbol("re.*")]
    ReKleeneStar(Term),
    /// Reflexive closure of lexicographic ordering
    #[symbol("str.<=")]
    RefClosLexOrd(Args<Term>),
    /// Singleton string containing a character at given position
    #[symbol("str.at")]
    SingStrAt(Term, Term),
    /// Substring
    #[symbol("str.substr")]
    Substr(Term, Term, Term),
    /// First string is a prefix of second one.
    #[symbol("str.prefixof")]
    PrefixOf(Term, Term),
    /// First string is a suffix of second one.
    #[symbol("str.suffixof")]
    SuffixOf(Term, Term),
    /// First string contains second one
    #[symbol("str.contains")]
    Contains(Term, Term),
    /// Index
    #[symbol("str.indexof")]
    IndexOf(Term, Term, Term),
    /// Replace
    #[symbol("str.replace")]
    Replace(Term, Term, Term),
    #[symbol("str.replace_all")]
    ReplaceAll(Term, Term, Term),
    #[symbol("str.replace_re")]
    ReplaceRe(Term, Term, Term),
    #[symbol("str.replace_re_all")]
    ReplaceReAll(Term, Term, Term),
    /// RE complement
    #[symbol("re.comp")]
    ReCompl(Term),
    /// RE difference
    #[symbol("re.diff")]
    ReDiff(Args<Term>),
    /// RE Kleene cross
    #[symbol("re.+")]
    ReKleeneCross(Term),
    /// RE option
    /// (re.opt e) abbreviates (re.union e (str.to_re ""))
    #[symbol("re.opt")]
    ReOpt(Term),
    /// RE range
    #[symbol("re.range")]
    ReRange(Term, Term),
    #[symbol("re.^")]
    RePow([IIndex; 1], Term),
    #[symbol("re.loop")]
    ReLoop([IIndex; 2], Term),
    /// Digit check
    #[symbol("str.is_digit")]
    IsDigit(Term),
    #[symbol("str.to_code")]
    ToCode(Term),
    #[symbol("str.from_code")]
    FromCode(Term),
    /// Conversion to integers
    #[symbol("str.to_int")]
    ToInt(Term),
    /// Conversion from integers.
    #[symbol("str.from_int")]
    FromInt(Term),
}

impl<L: Logic> Sorted<L> for StringOp<Term<L>> {
    fn sort(&self, _: &mut Ctx) -> Result<ISort, UnknownSort<Term<L>>> {
        use StringOp::*;
        Ok(match self {
            Contains(..) | InRe(..) | IsDigit(..) | LexOrd(..) | PrefixOf(..)
            | RefClosLexOrd(..) | SuffixOf(..) => ISort::bool(),
            ReAll | ReAllChar | ReCompl(..) | ReConcat(..) | ReDiff(..) | ReIntersect(..)
            | ReKleeneCross(..) | ReKleeneStar(..) | ReLoop(..) | ReNone | ReOpt(..)
            | RePow(..) | ReRange(..) | ReUnion(..) | ToRe(..) => ISort::regex(),
            IndexOf(..) | Len(..) | ToCode(..) | ToInt(..) => ISort::int(),
            FromCode(..) | FromInt(..) | Replace(..) | ReplaceAll(..) | ReplaceRe(..)
            | ReplaceReAll(..) | SingStrAt(..) | StrConcat(..) | Substr(..) => ISort::string(),
        })
    }
}
