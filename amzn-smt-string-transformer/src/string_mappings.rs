//! Module with all the string mapping functionality.
//! This module provides the options of char-to-char mapping, and no-reconstruction mapping.
//!
//! Char-to-char mapping allows for reconstruction of a satisfying solution to the original
//! query with a simple unmapping of the character replacements.
//!
//! "no-reconstruction" mapping is more complex, as it ensures that a minimal set of string
//! properties are maintained to keep the query and transformed query equisatisfiable.
//! The design choices made that can be modified without affecting equisatisfiability are indicated
//! in comments.
//!
//! If users want to add their own mapping functions, then they can write their own, and call it
//! instead of one of these functions in the `construct_mapping` function in `transpiler.rs`.
//! Users are responsible for ensuring that their mapping functions preserve all the required string
//! properties.
use crate::{transpiler::CharMap, transpiler::*};
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use std::collections::HashSet;

/// Enum of potential errors encountered during string transformation
#[derive(Debug)]
pub enum StringMapError {
    /// attempting to transform a string whose required properties to be maintained are "Everything"
    /// (i.e. trying to transform a string that can't be changed -- this means we're running into
    /// an unsupported string function)
    MaintainEverythingStringProps,
    /// re-attempting to transform a string more than the max allotted number of retries
    RemapRetryCountExceeded,
    /// prefix and suffix substrings overlap (an edge case we don't handle)
    SuffixPrefixOverlap,
    /// required substrings partially overlap (an edge case we don't handle)
    MidstringPartialOverlap,
}

/// update the given CharMap so the next non-range (i.e. not in any of the tracked ranges) character
/// is incremented by one (or 2 if the next character is flagged as illegal).
/// if the update_map_offset argument is false then just return this character and don't update the map.
fn update_and_get_next_char(char_map: &mut CharMap, offset: u32, update_map_offset: bool) -> u32 {
    let mut offset = offset + 1;
    if update_map_offset {
        char_map.non_range_offset = offset + 1;
    }
    if char_map
        .illegal_chars
        .contains(&char::from_u32(offset).unwrap())
    {
        offset += 1;
        if update_map_offset {
            char_map.non_range_offset += 1;
        }
    }
    offset
}

// ------------------------------------------------------------------------------------------------------------- CHAR TO CHAR MAPPING

/// transform a given string using the char-to-char mapping strategy, with the mapping specified
/// in the given CharMap.
pub fn map_string_char_to_char(s: &str, char_map: &mut CharMap) -> Result<String, StringMapError> {
    // error if the string has to maintain all properties
    if matches!(
        char_map.string_lit_props.get(s).unwrap(),
        StringSetProperties::Everything
    ) {
        return Err(StringMapError::MaintainEverythingStringProps);
    }
    // return the string with every character mapped
    Ok(s.chars()
        .map(|c| match char_map.char_map.get(&c) {
            // if the char is already in the map, return this mapped char
            Some(new_c) => *new_c,
            // otherwise, map this char to a new char and return that
            None => {
                let mut in_range = false;
                let mut offset = char_map.non_range_offset;
                // respect range if we're in a range
                for range in &mut char_map.ranges {
                    if c >= range.start_char && c <= range.end_char {
                        offset = range.cur_offset;
                        // use next available char in the range
                        if char_map
                            .illegal_chars
                            .contains(&char::from_u32(offset).unwrap())
                        {
                            offset += 1;
                            range.cur_offset += 1;
                        }
                        range.cur_offset += 1;
                        in_range = true;
                    }
                }
                // if not in a range, use the next available char
                if !in_range {
                    offset = update_and_get_next_char(char_map, offset, true);
                }
                char_map.char_map.insert(c, char::from_u32(offset).unwrap());
                char::from_u32(offset).unwrap()
            }
        })
        .collect::<String>())
}

// ------------------------------------------------------------------------------------------------------------- NO RECONSTRUCT MAPPING

/// map a string to a new string while respecting the ranges specified in the CharMap.
/// keep length, ints, and substrings as specified by these boolean arguments respectively.
/// note that the substrings preservation isn't actually part of this mapping function; this
/// argument is only needed to indicate if the string being mapped is *part* of a string in
/// which substrings need to be preserved, as this flag needs to be passed into the call to
/// fix_repeated_strings.
/// if you want to map a string while preserving substring relationships, call `gen_string_keep_substrings`.
pub fn gen_string_keep_ranges(
    s: &str,
    char_map: &mut CharMap,
    len_bool: bool,
    keep_ints: KeepInts,
    consider_substrings: bool,
) -> String {
    let mut to_ret = "".to_string();
    let mut cur_range: Option<&RangeParams> = None;
    // iterate over the string to be mapped, character by character
    for c in s.chars() {
        // if we're keeping ints (decimal)
        match (keep_ints, c.is_digit(10)) {
            (KeepInts::AsInts, true) => {
                to_ret.push('0');
                break;
            }
            (KeepInts::ExactInts, true) => {
                to_ret.push(c);
                break;
            }
            _ => {}
        }
        let new_range = char_map.get_range_for_char(c);
        // get the next char
        // if it's a range, just use the first value in the range
        // if it's not a range, just get the next available value
        let next_char = match new_range {
            Some(RangeParams { start_char: s, .. }) => *char_map.char_map.get(s).unwrap(),
            None => char::from_u32(char_map.non_range_start).unwrap(),
        };
        // are we reaching a new range?
        if match (cur_range, new_range) {
            (None, None) => false,
            (None, _) => true,
            (_, None) => true,
            (
                Some(RangeParams {
                    start_char: s1,
                    end_char: e1,
                    ..
                }),
                Some(RangeParams {
                    start_char: s2,
                    end_char: e2,
                    ..
                }),
            ) => !(s1 == s2 && e1 == e2),
        } {
            cur_range = new_range;
            if !len_bool {
                to_ret.push(next_char);
            }
        }
        // if we're keeping the length, then add a new char every time
        // there's gotta be at least one character
        if len_bool || to_ret.is_empty() {
            to_ret.push(next_char);
        }
    }
    // deal with the case that this generated string is already in the map
    // this is where we consider substrings if this argument is true
    let repeat_fix = fix_repeated_string(
        s.to_string(),
        to_ret.clone(),
        char_map,
        100u8, // number of retries allowed
        keep_ints,
        consider_substrings,
        len_bool,
    );
    if matches!(repeat_fix, Err(_)) {
        // if there was an error bail and map char-to-char
        to_ret = map_string_char_to_char(s, char_map).unwrap();
    } else {
        to_ret = repeat_fix.unwrap();
    }
    to_ret
}

/// check to see if a mapped string is already in the map.
/// if it is, attempt to fix this (i.e., generate a new string) by perturbing the mapped
/// string passed in, while respecting the properties specified (keep_ints, substrings, length, ranges).
/// return an error if we fail to remap the string successfully after `retries_allowed` retries.
fn fix_repeated_string(
    orig_string: String,
    to_ret: String,
    char_map: &mut CharMap,
    retries_allowed: u8,
    keep_ints: KeepInts,
    consider_substrings: bool,
    len_bool: bool,
) -> Result<String, StringMapError> {
    let mut to_ret = to_ret; // string to return
    let mut retry_ind: usize = 0; // index of the mapped string we're perturbing
    let mut retry_add = 1; // offset to be applied on the current char
    let mut cur_try = 0; // number of attempts
    let mut retry_char = to_ret.chars().nth(retry_ind).unwrap(); // character we're perturbing
    let mut reps = 1; // number of repetitions of the current char we're adding in the perturbation
                      // (this stays 1 if the length or substrings properties need to be maintained)
    while char_map.string_map.iter().any(|(key, val)| {
        // can't map to a string we already used
        val == &to_ret
            // more checks required if we need to keep substrings
            || (consider_substrings
                && ((!orig_string.contains(key) && to_ret.contains(val))
                    || (!key.contains(&orig_string) // check both directions of containment now that len is modified
                && val.contains(&to_ret)))
                && (matches!(
                    char_map.string_lit_props.get(key),
                    Some(StringSetProperties::Some {
                        len: _,
                        ranges: _,
                        keep_ints: _,
                        keep_substrings: true, // only care about substring matches for string literals involved in substrings
                        keep_prefix_suffix: _,
                    })
                )))
    }) {
        // get next non-range char in the charmap
        let next_char = char::from_u32(update_and_get_next_char(
            char_map,
            (retry_char as u32) + retry_add,
            false, // don't modify the charmap
        ));
        // if the next_char is invalid, move to the next index in the string and retry
        if match next_char {
            None => true,
            Some(c) => !c.is_ascii(),
        } {
            retry_ind = 0;
            retry_char = to_ret.chars().nth(retry_ind).unwrap();
            retry_add += 1;
            continue;
        }
        let next_char = next_char.unwrap();

        // get the next char
        // if it's a range, just use the first value in the range
        // if it's not a range, just get the next available value
        if let Some(RangeParams {
            start_char: s,
            end_char: e,
            ..
        }) = char_map.get_backwards_range_for_char(retry_char)
        {
            if next_char < s || next_char > e {
                retry_ind = (retry_ind + 1) % to_ret.len();
                if retry_ind == 0 {
                    retry_add += 1;
                }
                retry_char = to_ret.chars().nth(retry_ind).unwrap();
                continue;
            }
        }
        // respect ints properties if required
        if matches!(keep_ints, KeepInts::AsInts | KeepInts::ExactInts) && retry_char.is_digit(10) {
            retry_ind = (retry_ind + 1) % to_ret.len();
            if retry_ind == 0 {
                retry_add += 1;
            }
            retry_char = to_ret.chars().nth(retry_ind).unwrap();
            continue;
        }
        cur_try += 1;
        if cur_try > retries_allowed {
            // error out if we have exceeded retries allowed
            return Err(StringMapError::RemapRetryCountExceeded);
        }

        // actually modify the string
        // at this point we're guaranteed the modification will maintain relevant properties
        to_ret.replace_range(
            retry_ind..(retry_ind + 1),
            &next_char.to_string().repeat(
                if consider_substrings && (retry_ind == 0 || retry_ind + 1 == to_ret.len()) {
                    // only repeat if not first/last char
                    1 // if we care about substrings
                } else {
                    reps
                },
            ),
        );
        retry_ind = (retry_ind + 1) % to_ret.len();
        if retry_ind == 0 {
            retry_add += 1;
            // if we don't need to keep length or substrings, can start repeating characters
            if !len_bool && !consider_substrings {
                reps += 1;
            }
        }
    }
    Ok(to_ret)
}

/// get the longest string in a set of strings;
/// if there are multiple strings of max length this gets the first instance
fn get_longest_string(string_list: Vec<&String>) -> String {
    string_list
        .iter()
        .fold("".to_string(), |longest_string, cur_string| {
            if longest_string.len() < cur_string.len() {
                cur_string.to_string()
            } else {
                longest_string
            }
        })
}

/// get prefix, suffix, and midpoint sets of substrings of the given string;
/// these substrings are based on the string literals present in the given CharMap
fn get_string_subsets<'a>(
    s: &str,
    char_map: &'a CharMap,
) -> (Vec<&'a String>, Vec<&'a String>, Vec<&'a String>) {
    let mut prefix_strings: Vec<&String> = Vec::new();
    let mut mid_substrings: Vec<&String> = Vec::new();
    let mut suffix_strings: Vec<&String> = Vec::new();

    // collect the prefix, midpoint, and suffix strings
    for (string_lit, s_props) in &char_map.string_lit_props {
        // don't add the current string to any lists
        // also ignore empty strings since theyre contained in everything
        if string_lit == s || string_lit.is_empty() {
            continue;
        }
        if let StringSetProperties::Some {
            len: _len_bool,
            ranges: _,
            keep_ints: _,
            keep_substrings,
            keep_prefix_suffix: _,
        } = s_props
        {
            if *keep_substrings {
                // don't do else_if, so we cover the case of
                // substrings being repeated
                // example: ":" both as suffix and in the middle of a string
                if s.starts_with(string_lit) {
                    prefix_strings.push(string_lit);
                }
                if s.ends_with(string_lit) {
                    suffix_strings.push(string_lit);
                }
                if s.contains(string_lit) {
                    mid_substrings.push(string_lit);
                }
            }
        }
    }
    (prefix_strings, mid_substrings, suffix_strings)
}

/// enum of possible range pair overlaps
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
enum PairOverlap {
    /// no overlap
    No,
    /// first range is fully contained in the second range
    FirstFull,
    /// second range is fully contained in the first range
    SecondFull,
    /// partial overlap of ranges
    Partial,
}

/// check what is the overlap of the pair of ranges
fn is_contained_in(pair1: (usize, usize), pair2: (usize, usize)) -> PairOverlap {
    // subtract 1 bc string index is one less than length
    let (start1, len1) = pair1;
    let (start2, len2) = pair2;
    let end1 = start1 + len1 - 1;
    let end2 = start2 + len2 - 1;
    if start1 > end2 || start2 > end1 {
        return PairOverlap::No;
    }

    // if the pairs are equal it'll return SecondFull but it doesn't matter
    if start1 <= start2 && end2 <= end1 {
        // 2nd pair entirely in first pair
        return PairOverlap::SecondFull;
    } else if start2 <= start1 && end1 <= end2 {
        // first pair entirely in 2nd pair
        return PairOverlap::FirstFull;
    }
    PairOverlap::Partial
}

/// this is the hardest string mapping case.
/// we need to keep substrings. this covers cases like "contains" and "prefixof",
/// where these substring relationships need to be preserved
pub fn gen_string_keep_substrings(
    s: &str,
    char_map: &mut CharMap,
    len_bool: bool,
    keep_ints: KeepInts,
    keep_ranges: bool,
) -> Result<String, StringMapError> {
    if s.is_empty() {
        return Ok(s.to_string()); // empty string always maps to itself
    } else if s.len() == 1 {
        // if we're a range endpoint, just return the char mapping
        for r in &char_map.ranges {
            if r.start_char.to_string() == *s || r.end_char.to_string() == *s {
                let to_ret = char_map
                    .char_map
                    .get(&s.chars().next().unwrap())
                    .unwrap()
                    .to_string();
                // add mapping to both the string map and the persistent map
                char_map.string_map.insert(s.to_string(), to_ret.clone());
                let mut new_props = MappedStringMetaObj {
                    prefix: "".to_string(),
                    suffix: "".to_string(),
                    mapped_to: to_ret.clone(),
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
                };
                if let Some(props) = char_map.string_lit_props.get(s) {
                    new_props.req_props = new_props.req_props.update_with_truths(props.clone());
                }
                char_map.persist_string_map.insert(s.to_string(), new_props);
                return Ok(to_ret);
            }
        }
    }

    // only use the previously mapped string if it also preserves substrings
    // this hits an edge case where we find a substring that's also stored in
    // a non-substring way that breaks this string mapping.
    // if this is the case, just continue and map this string while maintaining
    // substrings.
    if let Some(mapped_string) = char_map.string_map.get(s) {
        if matches!(
            char_map.string_lit_props.get(s),
            Some(StringSetProperties::Some {
                len: _,
                ranges: _,
                keep_ints: _,
                keep_substrings: true,
                keep_prefix_suffix: _,
            })
        ) {
            return Ok(mapped_string.clone());
        }
    }
    let (prefix_strings, mid_substrings, suffix_strings) = get_string_subsets(s, char_map);
    // collect midpoint ranges
    // clone the midpoint strings to get rid of the stupid borrow error
    // get_string_subsets borrows char_map and then this borrow is used later, after we recursively
    // call this function with mutable references to char_map
    // ugh rust sometimes
    let mid_substrings = mid_substrings
        .iter()
        .map(|ms| ms.to_string())
        .collect::<Vec<String>>();

    /*
        We're not going to make this too fancy.
        The idea is:
        -- take the longest prefix
        -- take the longest suffix
        We know in these cases, that all prefixes are prefixes of each other,
        i.e. the longest prefix will contain all the shorter ones. Same idea for suffix.
        If prefix + suffix is longer than the string, this is overlap
            -- we're not handling this case. can maybe handle later, but for now just bail
        If these are not yet mapped, then call this recursively to map them.
        If either of these error, then bail.
        Mid point string: take the midsection of the string, after prefix and before suffix
        For each string in the midpoint string:
            -- get the range it covers
        Sort by ranges:
            - if the range is entirely in the prefix, drop it
            - if the range is entirely in the suffix, drop it
            - if there is partial overlap with the prefix or suffix, bail
        For each midpoint, call recursively to map them (if error, then bail).
        For the characters in between the midpoints, just call gen_strings_keep_ranges(...)
        through the gen_gap_mapped function
    */

    let s_prefix = get_longest_string(prefix_strings);
    let s_suffix = get_longest_string(suffix_strings);
    if s_prefix.len() + s_suffix.len() > s.len() {
        return Err(StringMapError::SuffixPrefixOverlap);
    }

    // call recursively; if it's already in the map then it'll be returned directly
    // bail if either of them error
    let mapped_prefix =
        gen_string_keep_substrings(&s_prefix, char_map, len_bool, keep_ints, keep_ranges)?;
    let mapped_suffix =
        gen_string_keep_substrings(&s_suffix, char_map, len_bool, keep_ints, keep_ranges)?;

    let mut to_ret = mapped_prefix;

    // now, onto the midpoints of the strings
    let mut midpoint_ranges: Vec<(usize, &str)> =
        mid_substrings
            .iter()
            .fold(Vec::<_>::new(), |mut overall, ms| {
                overall.extend(s.match_indices(ms.as_str()).collect::<Vec<(usize, &str)>>());
                overall
            });
    midpoint_ranges.sort_unstable();

    // before we proceed, check to see if this string is already in the persistent string map
    // if the persistent string map is not being used, then it'll be empty and this check won't
    // do anything
    // only use the persistent string map entry if it respects the same properties,
    // AND if it has the same prefix/suffix/mid_strings (hence why we need to compute the prefix/
    // suffix/mid_strings and their mappings before doing this check)
    if let Some(MappedStringMetaObj {
        prefix,
        suffix,
        req_props:
            StringSetProperties::Some {
                len: req_len_bool,
                ranges: req_ranges,
                keep_ints: req_keep_ints,
                keep_substrings: _req_keep_substrings,
                keep_prefix_suffix: _,
            },
        mid_strings,
        mapped_to,
    }) = char_map.persist_string_map.get(s)
    {
        if !char_map.string_map.iter().any(|(_key, val)| { val == mapped_to }) // is it already in the string map
         	&& prefix == &s_prefix
            && suffix == &s_suffix
            && mid_strings == &mid_substrings
            && char_map
                .ranges
                .iter()
                .all(|r| req_ranges.contains(&(r.start_char, r.end_char)))
        {
            // for ranges: if we don't care about ranges it doesn't matter
            // if keep_ranges is true, then req_ranges can't be empty
            if (req_len_bool >= &len_bool)
                && &KeepInts::merge(req_keep_ints, keep_ints) == req_keep_ints
                && (!keep_ranges || !req_ranges.is_empty())
            {
                char_map.string_map.insert(s.to_string(), mapped_to.clone());
                return Ok(mapped_to.clone());
            }
        }
    }

    // now, check the midpoints for validity
    // map those that need to be mapped
    // and, map the in-between strings with gen_strings_keep_ranges (through gen_gap_mapped)

    // keep track of current index of subsection; start at end of prefix
    let mut cur_startpoint = s_prefix.len();
    // we're iterating with an index, because we want to be able to look at the previous prefix
    // we're ignoring ones that are totally contained in each other
    // for example, a vs aws both starting at the same position
    // we can iterate in order because we sorted, and it sorts by position first then length of string
    for index in 0..midpoint_ranges.len() {
        let (mid_ind, mid_string) = midpoint_ranges[index];
        if mid_ind + mid_string.len() == s.len() {
            // if it's the suffix, bail early (suffix is handled after the loop)
            // note: we can't just check equality with s_suffix, since the suffix could be a substring
            // in the middle of the string too (e.g., "a:b:")
            break;
        }
        if cur_startpoint >= mid_ind + mid_string.len() {
            // then it's contained in the previous string, skip it (it's already handled)
            continue;
        }

        // if entirely in previous or next point, continue
        // no need to deal with special cases of prefix or suffix since
        // these are now contained in the mid_strings list
        // if partial overlap, then bail

        // check next string
        if index < midpoint_ranges.len() - 1 {
            let (next_ind, next_string) = midpoint_ranges[index + 1];
            match is_contained_in((mid_ind, mid_string.len()), (next_ind, next_string.len())) {
                PairOverlap::Partial => {
                    return Err(StringMapError::MidstringPartialOverlap);
                }
                PairOverlap::FirstFull => {
                    // if current string is entirely contained in next string, skip it
                    continue;
                }
                _ => {}
            }
        }
        // check previous string
        // if current string is entirely contained in previous string string, skip it
        // this is already contained in the first check with cur_startpoint,
        // so no need to check it again
        if index > 0 {
            let (prev_ind, prev_string) = midpoint_ranges[index - 1];
            if is_contained_in((mid_ind, mid_string.len()), (prev_ind, prev_string.len()))
                == PairOverlap::Partial
            {
                return Err(StringMapError::MidstringPartialOverlap);
            }
        }

        // then we're overlapping the suffix, bail out
        // this is a last check, it needs to happen after cases we can safely skip
        // example: abbb, suffix is bb but bb is in position right after a
        if mid_ind + mid_string.len() + s_suffix.len() > s.len() {
            return Err(StringMapError::MidstringPartialOverlap);
        }

        // ok so now, map the current midpoint
        // if theres some gap here, map the string subsection in between
        if cur_startpoint < mid_ind {
            let gap_string = s[cur_startpoint..mid_ind].to_string();
            let gap_mapped = gen_gap_mapped(s, gap_string, char_map, len_bool, keep_ints)?;
            to_ret.push_str(&gap_mapped);
        }
        // finally map the current mid_string
        let midpoint_mapped =
            gen_string_keep_substrings(mid_string, char_map, len_bool, keep_ints, keep_ranges)?;
        to_ret.push_str(&midpoint_mapped);
        cur_startpoint = mid_ind + mid_string.len();
    }
    // if theres a gap between last mid_string and suffix
    if cur_startpoint < s.len() - s_suffix.len() {
        let gap_string = s[cur_startpoint..s.len() - s_suffix.len()].to_string();
        let gap_mapped = gen_gap_mapped(s, gap_string, char_map, len_bool, keep_ints)?;
        to_ret.push_str(&gap_mapped);
    }

    to_ret.push_str(&mapped_suffix);

    // add the mapped string to the string map and the persistent map
    char_map.string_map.insert(s.to_string(), to_ret.clone());

    char_map.persist_string_map.insert(
        s.to_string(),
        MappedStringMetaObj {
            prefix: s_prefix,
            suffix: s_suffix,
            mapped_to: to_ret.clone(),
            mid_strings: mid_substrings,
            req_props: StringSetProperties::Some {
                len: len_bool,
                keep_ints,
                ranges: if keep_ranges {
                    char_map
                        .ranges
                        .iter()
                        .map(|r| (r.start_char, r.end_char))
                        .collect::<HashSet<(char, char)>>()
                } else {
                    HashSet::new()
                },
                keep_prefix_suffix: true,
                keep_substrings: true,
            },
        },
    );

    Ok(to_ret)
}

/// map a "gap" substring, i.e. a substring thats between required mid_substrings
/// in a string that's being mapped while preserving these substrings.
/// this function respects substrings but does not add itself mapped to the string_map,
/// since it's essentially "filler".
/// it only needs to respect substrings so it doesn't become a substring of something
/// it previously wasn't a substring of.
fn gen_gap_mapped(
    _s: &str,
    gap_string: String,
    char_map: &mut CharMap,
    len_bool: bool,
    keep_ints: KeepInts,
) -> Result<String, StringMapError> {
    let gap_mapped = gen_string_keep_ranges(&gap_string, char_map, len_bool, keep_ints, true);
    // last bool is consider_substrings
    let gap_mapped = fix_repeated_string(
        gap_string, gap_mapped, char_map, 100u8, keep_ints, true, len_bool,
    )?;
    // don't need to add the gap strings to the map
    // the whole point of the gap strings is that they're determined to be irrelevant
    Ok(gap_mapped)
}

/// map a string where no properties need to be maintained.
/// the only thing that needs to be checked is that the mapped string is not already in the
/// string_map.
pub fn gen_string_freeforall(_s: &str, char_map: &mut CharMap) -> Result<String, StringMapError> {
    let offset = char_map.non_range_offset;
    // just do this to make sure it's a valid char (don't actually modify the map)
    let next_char = update_and_get_next_char(char_map, offset, false);
    let mut to_ret = char::from_u32(next_char).unwrap().to_string();
    // fix if already there
    // just do a simpler version than fix_repeated_strings, since we don't need to check properties or
    // substrings or anything
    let retries = 100;
    let mut cur_offset = 1;
    let mut cur_reps = 1; // start with strings of length 1
    let mut cur_tries = 0;
    while char_map.string_map.values().any(|val| val == &to_ret) && cur_tries < retries {
        // get next valid offset, this auto-skips illegal chars
        // but wont update the map
        let next_char = update_and_get_next_char(char_map, cur_offset + offset, false);
        // make sure it's ascii
        if next_char > 127 {
            cur_offset = 1;
            cur_reps += 1;
            cur_tries += 1;
            continue;
        }
        // if we're tried 20 offsets from current char, try increasing repetitions (i.e. increasing the length)
        if cur_offset > 20 || char::from_u32(next_char) == None {
            cur_offset = 1;
            cur_reps += 1;
        }
        to_ret = char::from_u32(next_char)
            .unwrap()
            .to_string()
            .repeat(cur_reps);
        cur_offset += 1;
        cur_tries += 1;
    }
    if cur_tries > retries {
        return Err(StringMapError::RemapRetryCountExceeded);
    }
    Ok(to_ret)
}

/// map a string with the no-reconstruct mapping strategy.
/// this should be called *after* all the substrings-respecting strings have been mapped (these
/// all need to be mapped first).
/// if we reach this function and need to respect substrings, this is indicative of a problem with
/// the earlier mappings and so the string will be mapped char-to-char.
pub fn map_string_no_reconstruct(
    s: &str,
    char_map: &mut CharMap,
) -> Result<String, StringMapError> {
    let req_props = char_map.string_lit_props.get(s).unwrap().clone();
    if matches!(req_props, StringSetProperties::Everything) {
        // if we can't change the string at all, bail out
        return Err(StringMapError::MaintainEverythingStringProps);
    }
    Ok(match char_map.string_map.get(s) {
        Some(s1) => s1.clone(),
        None => {
            let mut to_ret = s.to_string();
            if s.is_empty() {
                return Ok(s.to_string());
            } else if s.len() == 1 {
                // if we're a range endpoint, just return the char mapping
                // but we don't want to add this to the string map, bc we don't want
                // it to be represented in the substring computations
                for r in &char_map.ranges {
                    if r.start_char.to_string() == *s {
                        return Ok(char_map.char_map.get(&r.start_char).unwrap().to_string());
                    } else if r.end_char.to_string() == *s {
                        return Ok(char_map.char_map.get(&r.end_char).unwrap().to_string());
                    }
                }
            }

            // now, we're in longer string territory
            // depending on what properties we need to preserve, we can do different things
            // with the strings
            // the properties are:
            // -- length
            // -- keep substrings
            // -- keep ints (either as is, or just keep them ints)
            // -- respect ranges
            // we also need to make sure not to generate strings that already exist
            match req_props {
                StringSetProperties::Some {
                    len: len_bool,
                    ref ranges,
                    keep_ints,
                    keep_substrings,
                    keep_prefix_suffix,
                } => {
                    // is it already in the persistent map?
                    if let Some(MappedStringMetaObj {
                        prefix: _,
                        suffix: _,
                        req_props:
                            StringSetProperties::Some {
                                len: req_len_bool,
                                ranges: req_ranges,
                                keep_ints: req_keep_ints,
                                keep_substrings: _req_keep_substrings,
                                keep_prefix_suffix: _,
                            },
                        mid_strings: _,
                        mapped_to,
                    }) = char_map.persist_string_map.get(s)
                    {
                        if !char_map.string_map.iter().any(|(_key, val)| { val == mapped_to }) // is it already in the string map
				            && ranges
				                .iter()
				                .all(|r| req_ranges.contains(r))
                        {
                            // for ranges: if we don't care about ranges it doesn't matter
                            // if keep_ranges is true, then req_ranges can't be empty
                            if (req_len_bool >= &len_bool)
                                && &KeepInts::merge(req_keep_ints, keep_ints) == req_keep_ints
                            {
                                char_map.string_map.insert(s.to_string(), mapped_to.clone());
                                return Ok(mapped_to.clone());
                            }
                        }
                    }

                    // if it's not in the persistent map, remap the string
                    if !len_bool
                        && ranges.is_empty()
                        && keep_ints == KeepInts::No
                        && !keep_substrings
                        && !keep_prefix_suffix
                    {
                        // then all bets are off, no constraints are here
                        // just make a new string of length 1
                        to_ret = gen_string_freeforall(s, char_map)?;
                    } else if !keep_substrings {
                        // range case! keep ranges (if there's none, that is fine)
                        to_ret = gen_string_keep_ranges(s, char_map, len_bool, keep_ints, false);
                    } else {
                        // keep substrings should have already been mapped, so now bail and map with char-to-char
                        to_ret = map_string_char_to_char(s, char_map).unwrap();
                    }
                }
                StringSetProperties::Everything => {}
            }

            // add newly mapped string to string_map and char_map
            char_map.string_map.insert(s.to_string(), to_ret.clone());
            char_map.persist_string_map.insert(
                s.to_string(),
                MappedStringMetaObj {
                    prefix: "".to_string(),
                    suffix: "".to_string(),
                    mapped_to: to_ret.clone(),
                    mid_strings: Vec::new(),
                    req_props,
                },
            );
            to_ret
        }
    })
}
