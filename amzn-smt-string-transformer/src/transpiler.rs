//! Module with structs and helper functions required for the transpiler.
//! This contains the main `transform_ast` function that is called to dispatch to the
//! transpiler visitors in the `transpiler_visitors` module.
//!
//! The main contents of this file is the CharMap struct, which represents the
//! data structure that is constructed through the traversal of the AST during transpilation.
//! The CharMap is how the mapping is performed, as it tracks all the string literals and their
//! properties and contexts (interfacing with the transpiler's Callgraph).
//!
//! The mapping function itself is independent of the CharMap.
//! It is invoked in the `construct_mapping` function.
//! Users who want to use a custom mapping instead should call their own function in `construct_mapping`.
//! More information on this is included in the `string_mappings` module, and in the `construct_mapping`
//! function.
//! Note that users are responsible for making sure their custom mapping respects the required string
//! properties; to do this they can make use of the helper structs provided in this module.

// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use crate::callgraph::*;
use crate::forest::AffectErr;
use crate::mapping_tools::*;
use crate::string_fcts::*;
use crate::string_mappings;
use crate::transpiler_visitors::*;
use amzn_smt_ir::fold::IntraLogicFolder;
use amzn_smt_ir::IConst;
use amzn_smt_ir::{
    fold::Fold, logic::ALL, Command as IRCommand, ISymbol, ParseError, Script, Term as IRTerm,
};
use smt2parser::concrete::*;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::convert::Infallible;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

/// parse an smtlib query into an iterator of Commands
pub fn parse(
    smtlib: impl std::io::BufRead,
) -> Result<impl Iterator<Item = Command>, ParseError<ALL>> {
    Ok(Script::<Term>::parse(smtlib)?.into_iter())
}

/// struct representing string properties to maintain when mapping to new strings.
/// note that equality is maintained by default, since the strings are in a set
/// and so there are no duplicates
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum StringSetProperties {
    /// can't change anything in the set
    Everything,
    /// some set of string properties
    Some {
        /// maintain the length of the generated strings
        len: bool,
        /// set of character ranges that must be respected  
        ranges: HashSet<(char, char)>,
        /// status on preserving integer chars (important for functions converting to/from ints)
        keep_ints: KeepInts,
        /// maintain the substring relationships (important for prefix, etc)
        keep_substrings: bool,
        /// maintain if a string has a shared prefix/suffix with another string
        /// eg. "abc" and "bcd" have a shared prefix/suffix of "bc"
        keep_prefix_suffix: bool,
    },
}

/// enum representing argument positions for variables that imply char level substrings
/// be maintained
#[derive(Debug, Clone, Eq, PartialEq, Copy)]
pub enum VarArgPositionCharSubstring {
    /// right-most arg
    RightMost,
    /// left-most arg
    LeftMost,
    /// any arg
    Any,
    /// no arg
    No,
}

/// struct representing the metadata involved in a string mapping;
/// this is the actual mapped string, and the properties and
/// relevant substrings that were considered
#[derive(Debug)]
pub struct MappedStringMetaObj {
    /// string properties that were considered in the mapping
    pub req_props: StringSetProperties,
    /// prefix substring that was maintained
    pub prefix: String,
    /// suffix substring that was maintained
    pub suffix: String,
    /// all substrings that were maintained (note: this list contains the prefix and suffix)
    pub mid_strings: Vec<String>,
    /// string mapped to
    pub mapped_to: String,
}

/// struct representing the various options for integer character preservation requirements
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum KeepInts {
    /// no requirements, treat integers like any other character
    No,
    /// keep ints as ints (in the presence of "isdigit" checks)
    AsInts,
    /// keep ints as their exact value (in the presence of conversion to/from ints)
    ExactInts,
}

/// member functions for the KeepInt struct
impl KeepInts {
    /// merge two KeepInts structs; this takes the strictest requirement.
    /// strictness order: No < AsInts < ExactInts (strictest)
    pub fn merge(ki1: &Self, ki2: Self) -> Self {
        match (ki1, ki2) {
            (Self::ExactInts, _) => Self::ExactInts,
            (_, Self::ExactInts) => Self::ExactInts,
            (Self::AsInts, _) => Self::AsInts,
            (_, Self::AsInts) => Self::AsInts,
            _ => Self::No,
        }
    }
}

/// add to_string functionality to KeepInts struct
impl std::fmt::Display for KeepInts {
    /// display function for KeepInts struct, just print the name of the enum variant
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?}",
            match self {
                Self::No => "No",
                Self::AsInts => "AsInts",
                Self::ExactInts => "ExactInts",
            }
        )
    }
}

/// default implementation for StringSetProperties
impl Default for StringSetProperties {
    fn default() -> Self {
        Self::new()
    }
}

/// member functions for the StringSetProperties enum
impl StringSetProperties {
    /// constructor: default is that there are no requirements
    pub fn new() -> Self {
        Self::Some {
            len: false,
            ranges: HashSet::new(),
            keep_ints: KeepInts::No,
            keep_substrings: false,
            keep_prefix_suffix: false,
        }
    }

    /// function to return a new StringSetProperties that is equal to the current
    /// one updated with the `new_props`.
    /// update is computed as: OR all the props of `self` and `new_props`;
    /// if a prop is true in one object now it's true here
    pub fn update_with_truths(&mut self, new_props: Self) -> Self {
        match (self, new_props) {
            (
                Self::Some {
                    len: sl,
                    ranges: sr,
                    keep_ints: ski,
                    keep_substrings: sks,
                    keep_prefix_suffix: skps,
                },
                Self::Some {
                    len: nl,
                    ranges: nr,
                    keep_ints: nki,
                    keep_substrings: nks,
                    keep_prefix_suffix: nkps,
                },
            ) => Self::Some {
                len: *sl || nl,
                ranges: sr.union(&nr).cloned().collect(),
                keep_ints: KeepInts::merge(ski, nki),
                keep_substrings: *sks || nks,
                keep_prefix_suffix: *skps || nkps,
            },
            _ => Self::Everything,
        }
    }
}

/// function to iterate over the list and see what properties we need to maintain.
/// also collect the set of string constants we're replacing here
fn string_consts_affected(
    cur_sym: &ISymbol,
    // var_defn: &Term,
    callgraph: &mut CallGraph,
) -> Result<BTreeSet<String>, AffectErr> {
    let string_consts = &callgraph.get_data_for_var(cur_sym)?.string_lits_built_from;
    Ok(string_consts.clone())
}

/// in some cases the argument context implies that all chars of a string need
/// to be considered as individual substrings
pub fn char_level_substrings_required(
    arguments: &[Term],
    sfc: StringFct,
    vars: &HashMap<ISymbol, ISymbol>,
) -> HashSet<ISymbol> {
    let mut vars_substring_required: HashSet<ISymbol> = HashSet::new();
    match sfc.get_var_position_implies_char_substrings() {
        VarArgPositionCharSubstring::RightMost => {
            // check last arg in the list
            if let Some(Term::Variable(symbol)) = arguments.last() {
                for val in vars.values() {
                    if val == symbol.sym() {
                        vars_substring_required.insert(symbol.sym().clone());
                        break;
                    }
                }
            }
        }
        VarArgPositionCharSubstring::LeftMost => {
            // check first arg in the list
            if let Some(Term::Variable(symbol)) = arguments.first() {
                for val in vars.values() {
                    if val == symbol.sym() {
                        vars_substring_required.insert(symbol.sym().clone());
                        break;
                    }
                }
            }
        }
        VarArgPositionCharSubstring::Any => {
            // check all args in the list
            for arg in arguments {
                if let Term::Variable(symbol) = arg {
                    for val in vars.values() {
                        if val == symbol.sym() {
                            vars_substring_required.insert(symbol.sym().clone());
                            break;
                        }
                    }
                }
            }
        }
        // if there are no positions that would imply all char substrings, do nothing
        _ => {}
    }
    vars_substring_required
}

/// function to take a list of strings and convert them all.
/// use the mapping strategy specified in the char_map.
/// if users want to use their own mapping function, call this function instead
/// of the `gen_string_keep_substrings` and `map_string_char_to_char` or `map_string_no_reconstruct`
/// used here.
fn construct_mapping(
    sorted_string_list: Vec<&String>,
    char_map: &mut CharMap,
) -> Result<HashMap<String, String>, string_mappings::StringMapError> {
    let mut string_map: HashMap<String, String> = HashMap::new();
    // first, map all the strings where the substrings need to be preserved
    // for the char-->char case it doesn't matter
    // but, for the no_reconstruct case we need to do this first to spot cases
    // where the mapping fails for substring containment
    // in these cases, we bail and map all of them to char-->char
    if !char_map.char_to_char {
        for s in &sorted_string_list {
            if let Some(StringSetProperties::Some {
                len: len_bool,
                ranges: range_set,
                keep_ints: ki,
                keep_substrings: ks,
                keep_prefix_suffix: _kps,
            }) = char_map.string_lit_props.get(&(*s).clone())
            {
                let len_bool = *len_bool;
                let ki = *ki;
                let keep_ranges = !range_set.is_empty();
                if *ks {
                    // this bails out if it's an error; right now behaviour is to try again remapping char_to_char
                    string_mappings::gen_string_keep_substrings(
                        s,
                        char_map,
                        len_bool,
                        ki,
                        keep_ranges,
                    )?;
                }
            }
        }
    }

    // now, iterate over the list and construct the mapping
    // for strings that have already been mapped, this just pulls them back out of the map
    for s in sorted_string_list {
        // foreach char in the string, map it to what that character has already been mapped to
        // or give is a new mapping if it doesn't exist yet in the map
        let mapped_string = if char_map.char_to_char {
            string_mappings::map_string_char_to_char(s, char_map)
        } else {
            string_mappings::map_string_no_reconstruct(s, char_map)
        }?;
        string_map.insert(s.clone(), mapped_string.clone());
    }
    Ok(string_map)
}

struct StringSwapper {
    string_map: HashMap<String, String>,
}

impl IntraLogicFolder<ALL> for StringSwapper {
    type Error = Infallible;

    fn fold_const(&mut self, constant: IConst) -> Result<Term, Self::Error> {
        Ok(match constant.as_ref() {
            Constant::String(s) => Constant::String(self.string_map[s.as_str()].clone()).into(),
            _ => constant.into(),
        })
    }
}

/// function to swap out the strings as described in the string_map
fn replace_args_in_term(string_map: HashMap<String, String>, var_defn: &Term) -> Option<Term> {
    if var_defn.op().is_some() {
        match var_defn.fold_with(&mut StringSwapper { string_map }) {
            Ok(t) => Some(t),
            Err(e) => match e {},
        }
    } else {
        None
    }
}

/// function to take in a list of all string function applications containing a string symbol as a parameter.
/// (also takes in the list of all strings existing in the program, so we can generate a new one and ensure no collisions).
/// returns a map of terms to their replacement terms (i.e., the parameters replaced with the simplified strings)
fn compute_replacement_strings(
    cur_sym: &ISymbol,
    var_defn: &Term,
    callgraph: &mut CallGraph,
    char_map: &mut CharMap,
) -> Result<Option<Term>, AffectErr> {
    // first, iterate over the list and see what properties we need to maintain
    let string_consts = string_consts_affected(cur_sym, callgraph)?;

    // now, create the map of replaced strings
    let mut sorted_string_list = string_consts.iter().collect::<Vec<_>>();
    sorted_string_list.sort();

    // now, construct the mapping
    let string_map = construct_mapping(sorted_string_list, char_map);

    // if we can't do anything, then just bail early and return the same term
    if string_map.is_err() {
        return Ok(None);
    }

    let string_map = string_map.unwrap();
    char_map.string_map.extend(string_map.clone());

    // now that we've computed the replacement strings, we have to go through and swap these out
    // in the term parameters
    Ok(replace_args_in_term(string_map, var_defn))
}

/// struct of potential function return types that we are considering.
/// you may note there are no bitvectors; that's because the string theory functions
/// don't use or return any bitvectors so we don't need to distinguish them.
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum IdentType {
    /// booleans
    BoolType,
    /// strings
    StringType,
    /// integers
    IntType,
    /// regex expression (labelled RegLan in smtlib)
    RegexStringType,
    /// some unknown type (if we saw a bitvector it would get classified here)
    UnknownType,
    /// placeholder type to represent the return of the placeholder NO_OP string function
    /// that represents a constraint variable
    ConstraintVarType,
}

/// add to_string functionality for IdentType
impl std::fmt::Display for IdentType {
    /// display function for IdentType
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BoolType => write!(f, "Bool"),
            Self::StringType => write!(f, "String"),
            Self::IntType => write!(f, "Int"),
            Self::RegexStringType => write!(f, "RegLan"), // smtlib name for regular expression type
            Self::UnknownType => write!(f, "Unknown"),
            Self::ConstraintVarType => write!(f, "ConstraintVarType"),
        }
    }
}

/// struct representing a character range
#[derive(Default, Debug, Eq, PartialEq, Clone)]
pub struct RangeParams {
    /// starting character
    pub start_char: char,
    /// end character
    pub end_char: char,
    /// offset of where we currently are in the range (how far have we mapped into the range?)
    pub cur_offset: u32,
}

/// member functions for the RangeParams struct
impl RangeParams {
    /// constructor: takes values for the start and end character in the range,
    /// and the starting offset
    pub fn new(start_char: char, end_char: char, cur_offset: u32) -> Self {
        Self {
            start_char,
            end_char,
            cur_offset,
        }
    }
}

/// struct representing the CharMap; this is the main data structure involved in storing
/// information required for mapping (built up during the transpilation, and interfacing
/// with the callgraph), and for building up/performing the mapping
pub struct CharMap {
    /// are we mapping char-to-char? currently only two mapping options, so this is a boolean.
    pub char_to_char: bool,
    /// list of character ranges, each of which is represented by a RangeParams struct
    pub ranges: Vec<RangeParams>,
    /// character map; only relevant if we're mapping char-to-char
    pub char_map: HashMap<char, char>,
    /// string map: stores mapping of original string to transpiled string
    pub string_map: HashMap<String, String>,
    /// map of string literals to the properties about them that must be maintained during transpilation
    pub string_lit_props: HashMap<String, StringSetProperties>,
    /// offset of next available character not in a range
    pub non_range_offset: u32,
    /// starting point of first character after the ranges
    pub non_range_start: u32,
    /// list of "illegal" characters; these are characters that get skipped over when mapping because
    /// they have been observed to have adverse effects when included in the mapping (e.g., \ since it is
    /// an escape character)
    pub illegal_chars: Vec<char>,
    /// persistent string map: this is an enhanced version of the `string_map` field, that also stores
    /// all the metadata involved with the transpilation
    pub persist_string_map: HashMap<String, MappedStringMetaObj>,
    /// number of string literals that needed to be mapped char-to-char
    /// (i.e. where every character is treated as an individual substring)
    pub char_to_char_string_lits: HashSet<String>,
}

/// member functions for the CharMap struct
impl CharMap {
    /// set the char_to_char flag to the supplied boolean
    pub fn set_char_to_char(&mut self, char_to_char: bool) {
        self.char_to_char = char_to_char;
    }

    /// check if the given range is in the CharMap
    pub fn has_range(&self, c1: char, c2: char) -> bool {
        for range in &self.ranges {
            if range.start_char == c1 && range.end_char == c2 {
                return true;
            }
        }
        false
    }

    /// get the range that the given character is in (None if not in a range)
    pub fn get_range_for_char(&self, c: char) -> Option<&RangeParams> {
        for r in &self.ranges {
            if c >= r.start_char && c <= r.end_char {
                return Some(r);
            }
        }
        None
    }

    /// given a character that has been mapped, get the mapped range that this
    /// character belongs to (None if not in a range)
    pub fn get_backwards_range_for_char(&self, c: char) -> Option<RangeParams> {
        for r in &self.ranges {
            let mapped_start = self.char_map.get(&r.start_char).unwrap();
            let mapped_end = self.char_map.get(&r.end_char).unwrap();
            if &c >= mapped_start && &c <= mapped_end {
                return Some(RangeParams {
                    start_char: *mapped_start,
                    end_char: *mapped_end,
                    cur_offset: 0, // placeholder
                });
            }
        }
        None
    }

    /// find if something is a prefix of s1 that is also a suffix of s2
    fn get_prefix_suffix<'a>(s1: &'a str, s2: &'a str) -> Option<&'a str> {
        // start at 1 so we are comparing at least one char always
        // if one string is empty bail and return None
        // if either string is just one character then the prefix/suffix is
        // the entire string, so it'll already be in the map
        for i in (1..std::cmp::min(s1.len(), s2.len())).rev() {
            // if they're never not equal then the entire string
            // is contained, so already in the map (return None)
            if s1[0..i] == s2[s2.len() - i..s2.len()] {
                return Some(&s1[0..i]);
            }
        }
        None
    }

    /// for strings where substrings need to be preserved, if we are not in char_to_char mode
    /// then it adds strings to the map for anything that's a prefix of the given string and a suffix of another
    /// example: "12" and "2345" --> should store "2"
    fn add_keep_substring_prefix_suffixes(&mut self) {
        if !self.char_to_char {
            let mut suffix_prefixes: HashMap<String, StringSetProperties> = HashMap::new();
            for (string_lit, props) in &self.string_lit_props {
                if matches!(
                    props,
                    StringSetProperties::Some {
                        len: _,
                        ranges: _,
                        keep_ints: _,
                        keep_substrings: _,
                        keep_prefix_suffix: true,
                    }
                ) {
                    for (sub_string_lit, sub_props) in &self.string_lit_props {
                        if matches!(
                            sub_props,
                            StringSetProperties::Some {
                                len: _,
                                ranges: _,
                                keep_ints: _,
                                keep_substrings: _,
                                keep_prefix_suffix: true,
                            }
                        ) && string_lit != sub_string_lit
                        {
                            if let Some(new_rel_string) =
                                Self::get_prefix_suffix(string_lit, sub_string_lit)
                            {
                                if !new_rel_string.is_empty() {
                                    suffix_prefixes.insert(
                                        new_rel_string.to_string(),
                                        sub_props.clone().update_with_truths(props.clone()),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            self.string_lit_props.extend(suffix_prefixes);
        }
    }

    /// method to collect the string properties associated with each string literal.
    /// this is the union of properties of all the contexts in which the string literals are used
    pub fn setup_string_lit_oriented_props(
        &mut self,
        partitions: &[NodeSetData],
        char_level_substring_vars: &HashSet<Option<&NodeId>>,
    ) {
        for p in partitions {
            let mut strings_char_level_substring = false;
            for var in &p.vars {
                if char_level_substring_vars.contains(&Some(var)) {
                    strings_char_level_substring = true;
                }
            }
            let mut seen_prefix = false;
            let mut seen_suffix = false;
            let mut p_string_props = p.string_fcts.iter().fold(
                StringSetProperties::Some {
                    len: false,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: false,
                    keep_prefix_suffix: false,
                },
                |mut overall, (sfc, sfc_args)| {
                    seen_prefix |= sfc == &StringFct::PrefixOf;
                    seen_suffix |= sfc == &StringFct::SuffixOf;
                    overall = overall.update_with_truths(sfc.get_required_props(sfc_args.clone()));
                    overall
                },
            );
            if seen_suffix && seen_prefix {
                p_string_props = p_string_props.update_with_truths(StringSetProperties::Some {
                    len: true,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: false,
                    keep_prefix_suffix: false,
                });
            }
            for string_lit in &p.string_lits {
                // let mut cur_string_props = p_string_props.clone();
                if let Some(props) = self.string_lit_props.get(string_lit) {
                    p_string_props = p_string_props.update_with_truths(props.clone());
                }
            }
            if strings_char_level_substring {
                p_string_props = p_string_props.update_with_truths(StringSetProperties::Some {
                    len: false,
                    ranges: HashSet::new(),
                    keep_ints: KeepInts::No,
                    keep_substrings: true,
                    keep_prefix_suffix: false,
                })
            }
            for string_lit in &p.string_lits {
                self.string_lit_props
                    .insert(string_lit.to_string(), p_string_props.clone());
                if strings_char_level_substring {
                    self.char_to_char_string_lits.insert(string_lit.to_string());
                }
            }
        }
        self.add_keep_substring_prefix_suffixes();
        for string_lit in &self.char_to_char_string_lits {
            let p_string_props = self.string_lit_props.get(string_lit).unwrap().clone();
            for c in string_lit.chars() {
                let mut cur_props = p_string_props.clone();
                if let Some(props) = self.string_lit_props.get(&c.to_string()) {
                    cur_props = cur_props.update_with_truths(props.clone());
                }
                self.string_lit_props
                    .insert(c.to_string(), cur_props.clone());
            }
        }
    }

    /// get rid of strings that have their mid_strings remapped but aren't remapped themselves.
    /// no need to check prefix/suffix separately, bc these are included in the mid_strings.
    /// this is required because mappings of one string where the substrings are remapped but their
    /// mapped version doesn't contain the remapped substring means that the substring was either
    /// not mapped or mapped to something else before, and so the substring relationship is not
    /// preserved with the current mapping (and therefore need to be removed from the persistent map).
    pub fn prune_persist_string_map(&mut self) {
        let string_map = self.string_map.clone();
        self.persist_string_map.retain(|_s, mapping_obj| {
            for mid_string in &mapping_obj.mid_strings {
                if let Some(remapped_mid) = string_map.get(mid_string) {
                    if !mapping_obj.mapped_to.contains(remapped_mid) {
                        return false;
                    }
                }
            }
            true
        });
    }
}

/// default constructor for CharMap struct
impl Default for CharMap {
    /// default: empty property sets, and set some default illegal chars.
    /// default mapping is no_reconstruct (i.e., char_to_char is false)
    fn default() -> Self {
        Self {
            char_to_char: false,
            ranges: Vec::default(),
            char_map: HashMap::default(),
            string_map: HashMap::default(),
            string_lit_props: HashMap::default(),
            non_range_offset: 0u32,
            non_range_start: 0u32,
            illegal_chars: vec!['\\', '\r', '"', '\u{f}', '\u{7f}'],
            persist_string_map: HashMap::default(),
            char_to_char_string_lits: HashSet::new(),
        }
    }
}

/// function to initialize the CharMap given a set of variable partitions from
/// the callgraph.
/// this initializes the required int properties and the ranges first.
/// if no_reconstruct mode, we also build up the string literal-oriented string properties
/// which creates the prefix/suffix implied substrings where relevant.
fn initialize_charmap(
    partitions: &[NodeSetData],
    char_level_substring_vars: &HashSet<Option<&NodeId>>,
) -> CharMap {
    let mut offset = 35u32; // start with printable non-quote chars
    let mut char_map = CharMap::default();

    offset = initialize_charmap_with_keep_ints(partitions, offset, &mut char_map);
    offset = initialize_charmap_with_ranges(partitions, offset, &mut char_map);

    // this is only really relevant for the case where we're mapping strings to strings
    // but, it keeps track of the union of string properties from the perspective of the string
    // literals that are involved
    // also, for strings where substrings need to be preserved, if we are not in char_to_char mode
    // then it adds strings to the map for anything that's a prefix of one string and a suffix of another
    // example: "12" and "2345" --> should store "2"
    char_map.setup_string_lit_oriented_props(partitions, char_level_substring_vars);

    char_map.non_range_offset = offset;
    char_map.non_range_start = offset;
    char_map
}

/// initialize the CharMap with the required integer properties
fn initialize_charmap_with_keep_ints(
    partitions: &[NodeSetData],
    mut offset: u32,
    char_map: &mut CharMap,
) -> u32 {
    // compute the int status over all partitions
    let int_status = partitions
        .iter()
        .fold(KeepInts::No, |overall, cur_partition| {
            KeepInts::merge(
                &overall,
                cur_partition.string_fcts.iter().fold(
                    KeepInts::No,
                    |sub_overall, (sfc, sfc_args)| {
                        KeepInts::merge(
                            &sub_overall,
                            match sfc.get_required_props(sfc_args.clone()) {
                                StringSetProperties::Some {
                                    len: _len_bool,
                                    ranges: _range_set,
                                    keep_ints: ki,
                                    keep_substrings: _ks,
                                    keep_prefix_suffix: _kps,
                                } => ki,
                                StringSetProperties::Everything => KeepInts::ExactInts,
                            },
                        )
                    },
                ),
            )
        });
    // if we need to keep ints, create the relevant mappings (these are just
    // represented as ranges)
    if matches!(int_status, KeepInts::AsInts | KeepInts::ExactInts) {
        offset = '0' as u32;
        let cur_range = RangeParams::new('0', '9', offset + 1);
        char_map.char_map.insert('0', '0');
        offset += 9;
        char_map.char_map.insert('9', '9');
        offset += 1;
        char_map.ranges.push(cur_range);

        // if exact ints are important, map all ints to themselves
        if int_status == KeepInts::ExactInts {
            for c in '1'..='8' {
                char_map.char_map.insert(c, c);
            }
        }
    }
    offset
}

/// initialize ranges to ensure they will be contiguous
/// i.e. range "a" "c" will map to range "1" "3" or some other pairing that properly includes
/// everything in the range.
/// with this setup all the ranges are also contiguous
fn initialize_charmap_with_ranges(
    partitions: &[NodeSetData],
    mut offset: u32,
    char_map: &mut CharMap,
) -> u32 {
    let mut ranges: BTreeSet<(char, char)> = BTreeSet::new();
    for p in partitions {
        for (_sfc, sfc_args) in &p.string_fcts {
            // foreach range
            if let StringFctArgs::ReRange(c1, c2) = sfc_args {
                ranges.insert((*c1, *c2));
            }
        }
    }

    // if we hit an int range and it's already been mapped, no problem
    // that range will just be skipped
    for (c1, c2) in ranges {
        if !char_map.has_range(c1, c2) {
            let orig_offset = offset;
            let cur_range = RangeParams::new(c1, c2, offset + 1);
            char_map
                .char_map
                .insert(c1, char::from_u32(offset).unwrap());
            offset += (c2 as u32) - (c1 as u32);
            for illegal_char in &char_map.illegal_chars {
                if (*illegal_char as u32) <= offset && (*illegal_char as u32) > orig_offset {
                    offset += 1;
                    break;
                }
            }
            char_map
                .char_map
                .insert(c2, char::from_u32(offset).unwrap());
            offset += 1;
            char_map.ranges.push(cur_range);
        }
    }
    offset
}

/// populate the rest of the ranges.
/// we'll just map the characters in the mapped range to one of the unused range chars
/// the purpose: so when we remap, everything in the range gets mapped back to the range
/// (this is really only relevant for char-to-char remapping)
fn populate_ranges(char_map: &CharMap) -> Vec<(char, char)> {
    let mut char_vec = char_map
        .char_map
        .iter()
        .map(|(c1, c2)| (*c1, *c2))
        .collect::<Vec<(char, char)>>();

    for range in char_map.ranges.iter() {
        let mut offset = range.cur_offset; // start offset
        let mut placeholder_char = range.start_char;
        let mut found_char = false;
        for range_char in range.start_char..range.end_char {
            if char_map.char_map.get(&range_char) == None {
                if char_map
                    .illegal_chars
                    .contains(&char::from_u32(offset).unwrap())
                {
                    offset += 1;
                }
                if !found_char {
                    placeholder_char = range_char;
                    found_char = true;
                }
                char_vec.push((placeholder_char, char::from_u32(offset).unwrap()));
                offset += 1;
            }
        }
    }

    char_vec
}

/// function to actually transform the AST into the transpiled version of the query
pub fn transform_ast(
    commands: impl Iterator<Item = Command>,
    use_global_map: bool,
    use_char_to_char: bool,
) -> (Vec<Command>, Mapping) {
    let mut identify_builder = IdentifyStringsBuilder::default();

    // visit the AST, building up the new lists of declarations and
    // assertions (initializations)
    // and, renaming vars where needed
    let mut commands = commands
        .map(|c| c.fold_with(&mut identify_builder))
        .collect::<Result<Vec<Command>, _>>()
        .unwrap();

    // remove the declare-consts from the list,
    // theyre all in the identify_builder list now and need to be lifted up
    commands.retain(|c| !matches!(c, Command::DeclareConst { .. } | Command::DeclareFun { .. }));

    let (start_commands, rest_commands): (Vec<Command>, Vec<Command>) =
        commands.into_iter().partition(|c| {
            matches!(
                c,
                Command::SetLogic { .. } | Command::SetInfo { .. } | Command::SetOption { .. }
            )
        });

    // add new commands
    let mut output = start_commands;
    output.extend(std::mem::take(&mut identify_builder.decl_const_list));
    output.extend(std::mem::take(&mut identify_builder.assert_list));
    output.extend(rest_commands);

    // propagate all information throughout the callgraph
    if matches!(identify_builder.callgraph.propagate_all(), Err(_)) {
        panic!("Error in information propagation: bailing out");
    }

    // now, replace the strings
    let mut replace_terms: HashMap<Term, Term> = HashMap::new();
    let mut callgraph = identify_builder.callgraph.clone();
    let partitions = identify_builder.callgraph.partitions();

    let char_level_substring_vars = identify_builder
        .char_level_substring_vars
        .iter()
        .map(|sym| callgraph.get_id_for_sym(sym))
        .collect();

    // initialize the charmap with the callgraph's partitions
    let mut char_map = initialize_charmap(partitions, &char_level_substring_vars);
    if use_char_to_char {
        char_map.set_char_to_char(true); // default is false
    }
    // if we're using the global (persistent) map, read it in
    if use_global_map {
        let global_map_opt = Mapping::build_from_json_file("global_mapping.json");
        if let Ok(global_map) = global_map_opt {
            char_map.persist_string_map = global_map
                .persistent_string_map
                .into_iter()
                .map(|(cur_string, cur_meta_obj_json)| {
                    (cur_string, cur_meta_obj_json.to_meta_obj())
                })
                .collect::<HashMap<String, MappedStringMetaObj>>();
        }
    }

    let mut mod_constraint_vars = HashSet::new();
    let mut failed_mod_constraint_vars = HashSet::new();

    // get the string vars from the visitor
    let mut string_vars = identify_builder.string_var_list.iter().collect::<Vec<_>>();
    string_vars.sort();

    // iterate over all the string vars
    let mut var_index = 0;
    while var_index < string_vars.len() {
        let sym = string_vars[var_index];
        if let Some(var_defn) = identify_builder.string_var_defn_map.get(sym) {
            // transpile strings related to the current string var
            if let Ok(opt_sym_replace_term) =
                compute_replacement_strings(sym, var_defn, &mut callgraph, &mut char_map)
            {
                if let Some(sym_replace_term) = opt_sym_replace_term {
                    replace_terms.insert(var_defn.clone(), sym_replace_term);
                    // add to list of affected vars, if we're remapping a string wrt this var
                    if let Ok(cvars_affected) = callgraph.get_constraint_vars_in_partition_with(sym)
                    {
                        mod_constraint_vars.extend(cvars_affected);
                    } else {
                        panic!(
                            "Error in getting affected constraint variables for {:?}",
                            sym
                        );
                    }
                } else {
                    // if error while running no_reconstruct, restart with char_to_char
                    if !char_map.char_to_char {
                        // restart
                        char_map.char_to_char = true;
                        char_map.string_map.clear();
                        replace_terms.clear();
                        failed_mod_constraint_vars.clear();
                        mod_constraint_vars.clear();
                        // now, restart the loop
                        var_index = 0;
                        continue;
                    }
                    failed_mod_constraint_vars.insert(sym);
                }
            } else {
                panic!("Error in propagating data for var {:?} in callgraph", sym);
            }
        }
        var_index += 1;
    }

    // if we were mapping strings, then at the end remap the range endpoints to their correct chars
    // remember this wasn't there before, bc we didn't want them to get counted as substrings
    // it's ok for the first char in the range bc this is the default char for the range anyway
    if !char_map.char_to_char {
        for r in &char_map.ranges {
            char_map.string_map.insert(
                r.end_char.to_string(),
                char_map.char_map.get(&r.end_char).unwrap().to_string(),
            );
            char_map.persist_string_map.insert(
                r.end_char.to_string(),
                MappedStringMetaObj {
                    prefix: "".to_string(),
                    suffix: "".to_string(),
                    mapped_to: char_map.char_map.get(&r.end_char).unwrap().to_string(),
                    mid_strings: Vec::new(),
                    req_props: StringSetProperties::Some {
                        len: false,
                        ranges: char_map
                            .ranges
                            .iter()
                            .map(|r| (r.start_char, r.end_char))
                            .collect(),
                        keep_ints: KeepInts::No,
                        keep_substrings: true, // specific chars matter with range
                        keep_prefix_suffix: false,
                    },
                },
            );
        }
    }

    // map of original to renamed variable names
    let alpha_renaming_map = identify_builder.alpha_renaming_map;

    // if we're in char_to_char mode, fill out char map with ranges.
    // otherwise char_map is meaningless so just get an empty list
    let char_vec = if char_map.char_to_char {
        populate_ranges(&char_map)
    } else {
        Vec::new()
    };

    // get rid of now invalid mappings in the persistent map (only relevant
    // if we're using a global persistent map, since we could've invalidated
    // a mapping of a string that came from another query)
    char_map.prune_persist_string_map();

    // construct mapping object
    let mapping_obj = Mapping::new(
        &char_vec,
        &char_map.string_map,
        &mod_constraint_vars,
        &failed_mod_constraint_vars,
        &alpha_renaming_map,
        &char_map.persist_string_map,
        &char_map.char_to_char_string_lits,
    );

    // actually replace the terms with the remapped strings
    let mut simplify_builder = SimplifyStringsBuilder::new(replace_terms);
    output = output
        .into_iter()
        .map(|c| c.fold_with(&mut simplify_builder))
        .collect::<Result<Vec<Command>, _>>()
        .unwrap();

    (output, mapping_obj)
}
