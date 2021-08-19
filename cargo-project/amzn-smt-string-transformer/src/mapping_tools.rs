//! Module of structs and related functions used for mapping metadata to/from JSON files
//! Metadata includes the various maps built during the transpilation process
use amzn_smt_ir::ISymbol;
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
use serde::{Deserialize, Serialize};
use serde_json::Result;
use std::collections::{HashMap, HashSet};

use crate::transpiler::{KeepInts, MappedStringMetaObj, StringSetProperties};

/// JSON representation of the StringSetProperties struct
/// keeps track of the string properties to maintain
#[derive(Serialize, Deserialize, Debug)]
pub struct StringSetPropertiesJson {
    /// are we preserving the length of the string
    pub len: bool,
    /// what ranges of characters are we preserving
    pub ranges: Vec<(char, char)>,
    /// are we keeping the ints? no / as-ints / as their exact value
    pub keep_ints: String,
    /// are we keeping the substrings?
    pub keep_substrings: bool,
    /// are we additionally keeping the prefix/suffix relationships (implied substrings)?
    pub keep_prefix_suffix: bool,
}

/// member functions for StringSetPropertiesJson
impl StringSetPropertiesJson {
    /// constructor: build from a StringSetProperties object
    /// not applicable for the Everything option
    pub fn new(props: &StringSetProperties) -> Self {
        match props {
            StringSetProperties::Some {
                len,
                ranges,
                keep_ints,
                keep_substrings,
                keep_prefix_suffix,
            } => Self {
                len: *len,
                ranges: ranges
                    .iter()
                    .map(|(c1, c2)| (*c1, *c2))
                    .collect::<Vec<(char, char)>>(),
                keep_ints: keep_ints.to_string(),
                keep_substrings: *keep_substrings,
                keep_prefix_suffix: *keep_prefix_suffix,
            },
            StringSetProperties::Everything => {
                panic!("Can't create a StringSetProperties with Everything");
            }
        }
    }

    /// convert back to StringSetProperties
    pub fn to_string_set_props(&self) -> StringSetProperties {
        StringSetProperties::Some {
            len: self.len,
            ranges: self
                .ranges
                .iter()
                .cloned()
                .collect::<HashSet<(char, char)>>(),
            keep_ints: match self.keep_ints.as_str() {
                "\"No\"" => KeepInts::No,
                "\"AsInts\"" => KeepInts::AsInts,
                "\"ExactInts\"" => KeepInts::ExactInts,
                _ => {
                    panic!("Unexpected keep_ints shape {:?}", self.keep_ints);
                }
            },
            keep_substrings: self.keep_substrings,
            keep_prefix_suffix: self.keep_prefix_suffix,
        }
    }
}

/// JSON representation of the MappedStringMetaObj struct
/// tracks the string properties, relevant substrings, and string being mapped to
#[derive(Serialize, Deserialize, Debug)]
pub struct MappedStringMetaObjJson {
    /// JSON representation of the required string properties
    pub req_props: StringSetPropertiesJson,
    /// prefix substring
    pub prefix: String,
    /// suffix substring
    pub suffix: String,
    /// all tracked substrings (including the prefix/suffix)
    pub mid_strings: Vec<String>,
    /// string this is mapped to
    pub mapped_to: String,
}

/// member functions for MappedStringMetaObjJson
impl MappedStringMetaObjJson {
    /// constructor: convert from MappedStringMetaObj
    pub fn new(mapped_meta_obj: &MappedStringMetaObj) -> Self {
        Self {
            req_props: StringSetPropertiesJson::new(&mapped_meta_obj.req_props),
            prefix: mapped_meta_obj.prefix.clone(),
            suffix: mapped_meta_obj.suffix.clone(),
            mid_strings: mapped_meta_obj.mid_strings.clone(),
            mapped_to: mapped_meta_obj.mapped_to.clone(),
        }
    }

    /// convert back to MappedStringMetaObj
    pub fn to_meta_obj(&self) -> MappedStringMetaObj {
        MappedStringMetaObj {
            req_props: self.req_props.to_string_set_props(),
            prefix: self.prefix.clone(),
            suffix: self.suffix.clone(),
            mid_strings: self.mid_strings.clone(),
            mapped_to: self.mapped_to.clone(),
        }
    }
}

/// JSON representation of all the mapping metadata/information from the transpilation
#[derive(Serialize, Deserialize, Debug)]
pub struct Mapping {
    /// character-to-character mapping (will only have entries if the mapping was char-to-char)
    pub char_map: Vec<(char, char)>,
    /// mapping of original strings to transpiled strings
    pub string_map: Vec<(String, String)>,
    /// list of affected constraint variables (i.e., all the string variables in the original query)
    pub affected_constraint_vars: Vec<String>,
    /// list of constraint variables involved in a failed transformation (if this list is non-empty it indicates
    /// a failure in the transformation)
    pub failed_transformed_constraint_vars: Vec<String>,
    /// mapping from the original constraint variable names to their renamed version in the transpiled query
    pub alpha_renaming_map: Vec<(String, String)>,
    /// mapping of original strings to what they have been mapped to, and all the metadata associated with this mapping
    /// this is the string_map with additional metadata
    pub persistent_string_map: Vec<(String, MappedStringMetaObjJson)>,
    /// number of string literals that needed to be mapped char-to-char
    /// (i.e. where every character is treated as an individual substring)
    pub char_to_char_string_lits: Vec<String>,
}

/// member functions for the Mapping struct
impl Mapping {
    /// constructor; converts metadata built up during the transpilation into a JSON serializable form
    pub fn new(
        char_vec: &[(char, char)],
        string_map: &HashMap<String, String>,
        mod_constraint_vars: &HashSet<ISymbol>,
        failed_transformed_constraint_vars: &HashSet<&ISymbol>,
        alpha_renaming_map: &HashMap<ISymbol, ISymbol>,
        persistent_string_map: &HashMap<String, MappedStringMetaObj>,
        char_to_char_string_lits: &HashSet<String>,
    ) -> Self {
        Self {
            char_map: char_vec.to_vec(),
            string_map: string_map
                .iter()
                .map(|(s1, s2)| (s1.clone(), s2.clone()))
                .collect::<Vec<(String, String)>>(),
            affected_constraint_vars: mod_constraint_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<String>>(),
            failed_transformed_constraint_vars: failed_transformed_constraint_vars
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<String>>(),
            alpha_renaming_map: alpha_renaming_map
                .iter()
                .map(|(sym1, sym2)| (sym1.0.clone(), sym2.0.clone()))
                .collect::<Vec<(String, String)>>(),
            persistent_string_map: persistent_string_map
                .iter()
                .map(|(cur_string, cur_map_meta_obj)| {
                    (
                        cur_string.clone(),
                        MappedStringMetaObjJson::new(cur_map_meta_obj),
                    )
                })
                .collect(),
            char_to_char_string_lits: char_to_char_string_lits
                .iter()
                .map(|v| v.to_string())
                .collect::<Vec<String>>(),
        }
    }

    /// convert to a string; pretty-print
    pub fn to_json_string(&self) -> Result<String> {
        serde_json::to_string_pretty(&self)
    }

    /// print self's JSON representation to the specified file
    pub fn print_json_to_file(&self, filename: &str) -> Result<()> {
        let json_string = self.to_json_string()?;
        std::fs::write(filename, json_string).expect("Error in printing to file");
        Ok(())
    }

    /// construct a Mapping object from a JSON file
    pub fn build_from_json_file(filename: &str) -> Result<Self> {
        let file_conts = std::fs::read_to_string(filename);
        let mut file_conts_string = "".to_string();
        if let Ok(fcs) = file_conts {
            file_conts_string = fcs;
        }
        serde_json::from_str(&file_conts_string)
    }

    /// get reverse map: this only makes sense if the mapping was char-to-char
    /// since this would allow us to reconstruct satisfying solutions to the original problem
    /// given a satisfying solution to the transpiled problem
    /// char-map is empty if the mapping was in no_reconstruct mode
    pub fn get_re_map(&self) -> HashMap<char, char> {
        let mut re_map: HashMap<char, char> = HashMap::with_capacity(self.char_map.len());
        for (c1, c2) in &self.char_map {
            re_map.insert(*c2, *c1);
        }
        re_map
    }

    /// get reverse alpha renaming map (for remapping variable names)
    pub fn get_un_alpha_map(&self) -> HashMap<String, String> {
        let mut re_map: HashMap<String, String> =
            HashMap::with_capacity(self.alpha_renaming_map.len());
        for (s1, s2) in &self.alpha_renaming_map {
            re_map.insert(s2.clone(), s1.clone());
        }
        re_map
    }
}
