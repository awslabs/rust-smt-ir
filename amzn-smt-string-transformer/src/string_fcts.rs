//! Module containing the all SMTLIB string functions, and their operator representations
//! For each function, we implement functionality for getting the argument and return types,
//! a representation of these types, and a type-based listing of the string properties that need to
//! be maintained given the usage of each function.
//!
//! Based on the SMTLIB string functions, listed [here](http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml).

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0.
use crate::transpiler::{IdentType, KeepInts, StringSetProperties, VarArgPositionCharSubstring};
use std::collections::HashSet;

/// Enum of all valid string functions
/// NO_OP is not a string function in SMTLIB; it indicates "no string function"
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[allow(non_camel_case_types)] // allow NO_OP without warning
#[allow(missing_docs)] // docs for all functions included below
pub enum StringFct {
    Contains,
    Distinct,
    FromCode,
    FromInt,
    IndexOf,
    InRe,
    IsDigit,
    Len,
    LexOrd,
    PrefixOf,
    ReAll,
    ReAllChar,
    ReCompl,
    ReConcat,
    ReDiff,
    RefClosLexOrd,
    ReIntersect,
    ReKleeneCross,
    ReKleeneStar,
    ReLoop,
    ReNone,
    ReOpt,
    Replace,
    ReplaceAll,
    ReplaceRe,
    ReplaceReAll,
    RePow,
    ReRange,
    ReUnion,
    SingStrAt,
    StrConcat,
    StrEquality,
    Substr,
    SuffixOf,
    ToCode,
    ToInt,
    ToRe,
    NO_OP,
}

/// An enum of the relevant args for determining the string properties
// not just adding these as arguments to the StringFct because
// some of them are strings, and I wanted the StringFcts to be able to
// derive Copy
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub enum StringFctArgs {
    /// no relevant arguments
    NoArgs,
    /// this string function states variables involved need to contain the specified literal as a substring
    Contains(String),
    /// this string function is a range from the first to the second char in this pair
    ReRange(char, char),
}

/// Member functions for the StringFcts: this API allows users to
/// query the type information for a given function
impl StringFct {
    /// get the return type
    pub fn string_fct_return_type(&self) -> IdentType {
        match self {
            Self::Contains
            | Self::Distinct
            | Self::InRe
            | Self::IsDigit
            | Self::LexOrd
            | Self::PrefixOf
            | Self::RefClosLexOrd
            | Self::StrEquality
            | Self::SuffixOf => IdentType::BoolType,
            Self::ReAll
            | Self::ReAllChar
            | Self::ReCompl
            | Self::ReConcat
            | Self::ReDiff
            | Self::ReIntersect
            | Self::ReKleeneCross
            | Self::ReKleeneStar
            | Self::ReLoop
            | Self::ReNone
            | Self::ReOpt
            | Self::RePow
            | Self::ReRange
            | Self::ReUnion
            | Self::ToRe => IdentType::RegexStringType,
            Self::IndexOf | Self::Len | Self::ToCode | Self::ToInt => IdentType::IntType,
            Self::FromCode
            | Self::FromInt
            | Self::Replace
            | Self::ReplaceAll
            | Self::ReplaceRe
            | Self::ReplaceReAll
            | Self::SingStrAt
            | Self::StrConcat
            | Self::Substr => IdentType::StringType,
            Self::NO_OP => IdentType::ConstraintVarType,
        }
    }

    /// get the relevant args (i.e. the args that will actually affect
    /// the string properties that we need to maintain)
    pub fn get_args(&self, lits: &[String]) -> StringFctArgs {
        match self {
            Self::Contains => {
                // we're only handling contains of a hardcoded string
                if let [s] = lits {
                    return StringFctArgs::Contains(s.to_string());
                }
                // otherwise, this is not an error: this just indicates that the arg to contains
                // is not a string constant, so it could be a string var or string function application
                // here we return NoArgs since none of the args are string literals that need to be tracked
                StringFctArgs::NoArgs
            }
            Self::ReRange => {
                // we're only handling range between two hardcoded single-char strings
                if let [s1, s2] = lits {
                    if s2.len() == 1 && s1.len() == 1 {
                        let c1 = s1.chars().next().unwrap();
                        let c2 = s2.chars().next().unwrap();
                        return StringFctArgs::ReRange(
                            std::cmp::min(c1, c2),
                            std::cmp::max(c1, c2),
                        );
                    }
                }
                StringFctArgs::NoArgs
            }
            _ => StringFctArgs::NoArgs,
        }
    }

    /// get the argument positions that imply that all string literals in context need to
    /// be mapped considering each character as a substring
    pub fn get_var_position_implies_char_substrings(&self) -> VarArgPositionCharSubstring {
        match self {
            Self::Distinct
            | Self::FromCode
            | Self::FromInt
            | Self::InRe
            | Self::IsDigit
            | Self::Len
            | Self::LexOrd
            | Self::StrEquality
            | Self::ReRange
            | Self::ReAll
            | Self::ReAllChar
            | Self::ReCompl
            | Self::ReDiff
            | Self::RefClosLexOrd
            | Self::ReIntersect
            | Self::ReKleeneCross
            | Self::ReKleeneStar
            | Self::ReLoop
            | Self::ReNone
            | Self::ReOpt
            | Self::RePow
            | Self::ReUnion
            | Self::SingStrAt
            | Self::ToCode
            | Self::ToInt
            | Self::ToRe
            | Self::NO_OP => VarArgPositionCharSubstring::No,
            Self::IndexOf
            | Self::PrefixOf
            | Self::Replace
            | Self::ReplaceAll
            | Self::ReplaceRe
            | Self::ReplaceReAll
            | Self::SuffixOf => VarArgPositionCharSubstring::LeftMost,
            Self::Contains | Self::Substr => VarArgPositionCharSubstring::RightMost,
            Self::StrConcat | Self::ReConcat => VarArgPositionCharSubstring::Any,
        }
    }

    /// get the string properties that need to be maintained
    /// this is a function of the function (self) *and* the arguments
    pub fn get_required_props(&self, args: StringFctArgs) -> StringSetProperties {
        // properties are specific to some string functions
        let mut set_props = StringSetProperties::new();
        match self {
            // no extra properties needed (equality/non-equality always maintained)
            Self::Distinct
            | Self::StrEquality
            | Self::ReAll
            | Self::ReAllChar
            | Self::ReCompl
            | Self::ReDiff
            | Self::ReIntersect
            | Self::ReKleeneCross
            | Self::ReKleeneStar
            | Self::ReNone
            | Self::ReOpt
            | Self::ReUnion
            | Self::NO_OP => {}
            // substring relationships need to be preserved
            Self::Contains
            | Self::InRe
            | Self::PrefixOf
            | Self::Replace
            | Self::ReplaceAll
            | Self::ReplaceRe
            | Self::ReplaceReAll
            | Self::Substr
            | Self::SuffixOf
            | Self::ToRe => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: false,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: true,
                    keep_prefix_suffix: false,
                })
            }
            // substrings and relative prefix/suffix are relevant
            Self::StrConcat => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: false,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: true,
                    keep_prefix_suffix: true,
                })
            }
            // substrings and relative prefix/suffix are relevant; now length is also relevant
            Self::ReConcat => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: true, // can concat with things like re.allchar that only match if it's one char, etc
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: true,
                    keep_prefix_suffix: true,
                })
            }
            // range
            Self::ReRange => {
                if let StringFctArgs::ReRange(c1, c2) = args {
                    let mut range_set: HashSet<(char, char)> = HashSet::new();
                    range_set.insert((c1, c2));
                    set_props = set_props.update_with_truths(StringSetProperties::Some {
                        len: false,
                        ranges: range_set,
                        keep_ints: KeepInts::No,
                        keep_substrings: true, // specific chars matter with range
                        keep_prefix_suffix: false,
                    });
                } else {
                    // if the range arguments arent available, bail and assume all properties need to be maintained
                    set_props = set_props.update_with_truths(StringSetProperties::Everything);
                }
            }
            // length-specific functions (loop and pow mean a specific number of repetitions)
            Self::Len | Self::ReLoop | Self::RePow => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: true,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: false,
                    keep_prefix_suffix: false,
                })
            }
            // keep digits as digits
            Self::IsDigit => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: false,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::AsInts,
                    keep_substrings: false,
                    keep_prefix_suffix: false,
                })
            }
            // the actual value of digit chars are used as ints: maintain these chars as-is
            Self::FromCode | Self::FromInt | Self::ToCode | Self::ToInt => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: false,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::ExactInts,
                    keep_substrings: false,
                    keep_prefix_suffix: false,
                })
            }
            // keep both length and the relevant substrings
            Self::IndexOf | Self::SingStrAt => {
                set_props = set_props.update_with_truths(StringSetProperties::Some {
                    len: true,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::ExactInts,
                    keep_substrings: true,
                    keep_prefix_suffix: false,
                })
            }

            // if one of the terms is an application of a function we don't handle,
            // then we can't condense the strings at all
            Self::LexOrd | Self::RefClosLexOrd => {
                set_props = set_props.update_with_truths(StringSetProperties::Everything);
            }
        }
        set_props
    }
}

/// list of pairs of all SMTLIB string functions
/// as they are represented in SMTLIB source code, along with their corresponding StringFct
/// signatures included as comments; taken from [this link](http://smtlib.cs.uiowa.edu/theories-UnicodeStrings.shtml)
pub const STRING_FCTS: &[(&str, StringFct)] = &[
    // core functions
    // ; String functions
    // :funs (
    //        ; String concatenation
    //        (str.++ String String String :left-assoc)
    ("str.++", StringFct::StrConcat),
    //        ; String length
    //        (str.len String Int)
    ("str.len", StringFct::Len),
    //        ; Lexicographic ordering
    //        (str.< String String Bool :chainable)
    //       )
    ("str.<", StringFct::LexOrd),
    // ; Regular expression functions
    // :funs (
    //        ; String to RE injection
    //        (str.to_re String RegLan)
    ("str.to.re", StringFct::ToRe),
    ("str.to_re", StringFct::ToRe), // cvc4 syntax
    //        ; RE membership
    //        (str.in_re String RegLan Bool)
    ("str.in.re", StringFct::InRe),
    ("str.in_re", StringFct::InRe), // cvc4 syntax
    //        ; Constant denoting the empty set of strings
    //        (re.none RegLan)
    ("re.none", StringFct::ReNone),
    ("re.nostr", StringFct::ReNone),
    //        ; Constant denoting the set of all strings
    //        (re.all RegLan)
    ("re.all", StringFct::ReAll),
    //        ; Constant denoting the set of all strings of length 1
    //        (re.allchar RegLan)
    ("re.allchar", StringFct::ReAllChar),
    //        ; RE concatenation
    //        (re.++ RegLan RegLan RegLan :left-assoc)
    ("re.++", StringFct::ReConcat),
    //        ; RE union
    //        (re.union RegLan RegLan RegLan :left-assoc)
    ("re.union", StringFct::ReUnion),
    //        ; RE intersection
    //        (re.inter RegLan RegLan RegLan :left-assoc)
    ("re.inter", StringFct::ReIntersect),
    //        ; Kleene Closure
    //        (re.* RegLan RegLan)
    //       )
    ("re.*", StringFct::ReKleeneStar),
    // ;----------------------------
    // ; Additional functions
    // ;----------------------------

    // :fun (
    //       ; Reflexive closure of lexicographic ordering
    //       (str.<= String String Bool :chainable)
    ("str.<=", StringFct::RefClosLexOrd),
    //       ; Singleton string containing a character at given position
    //       (str.at String Int String)
    ("str.at", StringFct::SingStrAt),
    //       ; Substring
    //       (str.substr String Int Int String)
    ("str.substr", StringFct::Substr),
    //       ; First string is a prefix of second one.
    //       (str.prefixof String String Bool)
    ("str.prefixof", StringFct::PrefixOf),
    //       ; First string is a suffix of second one.
    //       (str.suffixof String String Bool)
    ("str.suffixof", StringFct::SuffixOf),
    //       ; First string contains second one
    //       (str.contains String String Bool)
    ("str.contains", StringFct::Contains),
    //       ; Index
    //       (str.indexof String String Int Int)
    ("str.indexof", StringFct::IndexOf),
    //       ; Replace
    //       (str.replace String String String String)
    ("str.replace", StringFct::Replace),
    //       (str.replace_all String String String String)
    ("str.replace_all", StringFct::ReplaceAll),
    //       (str.replace_re String RegLan String String)
    ("str.replace_re", StringFct::ReplaceRe),
    //       (str.replace_re_all String RegLan String String)
    ("str.replace_re_all", StringFct::ReplaceReAll),
    //       ; RE complement
    //       (re.comp RegLan RegLan)
    ("re.comp", StringFct::ReCompl),
    //       ; RE difference
    //       (re.diff RegLan RegLan RegLan :left-assoc)
    ("re.diff", StringFct::ReDiff),
    //       ; RE Kleene cross
    //       (re.+ RegLan RegLan)
    ("re.+", StringFct::ReKleeneCross),
    //       ; RE option
    //       ; (re.opt e) abbreviates (re.union e (str.to_re ""))
    //       (re.opt RegLan RegLan)
    ("re.opt", StringFct::ReOpt),
    //       ; RE range
    //       (re.range String String RegLan)
    ("re.range", StringFct::ReRange),
    //       ; Function symbol indexed by a numeral n.
    //       ((_ re.^ n) RegLan RegLan)
    ("re.^", StringFct::RePow),
    //       ; Function symbol indexed by two numerals n₁ and n₂.
    //       ((_ re.loop n₁ n₂) RegLan RegLan)
    ("re.loop", StringFct::ReLoop),
    // ;---------------------------
    // ; Maps to and from integers
    // ;---------------------------

    // :fun (
    //    ; Digit check
    //    (str.is_digit String Bool)
    ("str.is_digit", StringFct::IsDigit),
    //    (str.to_code String Int)
    ("str.to_code", StringFct::ToCode),
    //    (str.from_code Int String)
    ("str.from_code", StringFct::FromCode),
    //    ; Conversion to integers
    //    (str.to_int String Int)
    ("str.to_int", StringFct::ToInt),
    //    ; Conversion from integers.
    //    (str.from_int Int String)
    ("str.from_int", StringFct::FromInt),
    // STANDALONE: not in smtlib but still a valid operation on strings
    ("=", StringFct::StrEquality),
    // also not in smtlib string theory but still a valid operation on strings
    ("distinct", StringFct::Distinct),
];
