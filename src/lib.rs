/*
    adventjson – simple json parser in rust
    Copyright (C) 2021 Matthias Kaak

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

#![warn(
    missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_code,
    unstable_features,
    unused_import_braces,
    unused_qualifications,
    rustdoc::missing_crate_level_docs,
    rust_2018_idioms,
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::cargo
)]
#![allow(clippy::suspicious_else_formatting, clippy::match_like_matches_macro)]

//! A simple JSON library
//!
//! This is a simple JSON library I wrote for one of the
//! [advent of code](https://adventofcode.com/) challenges, but became a full,
//! standard complaint JSON parser.  To use it just call the
//! [`JsonObject::read`] function with what you want to have parsed:
//!```
//! # use adventjson::JsonError;
//! use adventjson::JsonObject;
//!
//! # fn main() -> Result<(), JsonError>
//! # {
//! let s = "{\"hello\": \"World\", \"answer\": 42}";
//! let json_object = JsonObject::read(s)?;
//!
//! assert_eq!(format!("{}", json_object), s);
//! # Ok(())
//! # }
//!```

use std::char::decode_utf16;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::error::Error;
use std::fmt::{self, Display, Formatter};
use std::mem;
use std::num::FpCategory;

use JsonError::{
    Empty, EndedOnEscape, InvalidChar, InvalidCodepoint, InvalidNumber, NonStringAsKey,
    UnknownEscapeSequence, UnterminatedString,
};
use JsonObject::{Array, Bool, JsonStr, Null, Number, Obj};

/// A json object
///
/// A full json object
///
/// # Notes
/// In accordance to the specification a `Number` may not be `NaN` or one of
/// the `Infinity`-ies, so it is [`Eq`] and [`Ord`]
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum JsonObject
{
    /// An array of objects (e.g.: \[1,2,3\])
    Array(Vec<Self>),
    /// Key-value pairs (e.g.: {\"first\": 10, \"other\": 15})
    Obj(Vec<(String, Self)>),
    /// A number (e.g.: -0.08333)
    Number(f64),
    /// A string (e.g.: \"Test: \\\"\")
    JsonStr(String),
    /// A boolean (e.g. true)
    Bool(bool),
    /// The null-value
    Null,
}

/// Save because no not-number values are allowed in json
impl Eq for JsonObject {}

/// Save because no not-number values are allowed in json
#[allow(clippy::derive_ord_xor_partial_ord)]
impl Ord for JsonObject
{
    fn cmp(&self, other: &Self) -> Ordering
    {
        self.partial_cmp(other).unwrap()
    }
}

impl Default for JsonObject
{
    /// The default value is [`JsonObject::Null`]
    fn default() -> Self
    {
        Null
    }
}

/// An error that occured while parsing a json file
///
/// The reading functions work recursive, that means major errors might end up
/// in the wrong category, for example mismatched parantheses result in an
/// `Empty` error:
///```
/// # use adventjson::JsonObject;
/// # use adventjson::JsonError::Empty;
/// assert_eq!(JsonObject::read("[[[]]"), Err(Empty));
///```
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum JsonError
{
    /// The input was empty (or only whitespace)
    Empty,
    /// At the given position the given character was read invalidly
    InvalidChar(char, usize),
    /// A string with no closing quote
    UnterminatedString,
    /// The input ended on a backslash
    EndedOnEscape,
    /// An unknown escape sequence was encountered
    UnknownEscapeSequence(char),
    /// A not string was used as key in an [`JsonObject::Obj`]
    NonStringAsKey,
    /// Per '\uXXXX' was an invalid code point specified
    InvalidCodepoint,
    /// A number that is invalid in json, but is a perfectly fine
    /// floating-point number.
    InvalidNumber,
}

impl Display for JsonError
{
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), fmt::Error>
    {
        match self
        {
            Empty => write!(fmt, "The input was empty (or only whitespace)"),
            InvalidChar(c, num) => write!(
                fmt,
                "At the position {} the character {:?} was read, but it is \
invalid at this point",
                c, num
            ),
            UnterminatedString =>
            {
                write!(fmt, "A string with no closing quote was read")
            }
            EndedOnEscape => write!(fmt, "The input ended on a backslash"),
            UnknownEscapeSequence(c) => write!(
                fmt,
                "The unknown escape sequence \'\\{}\' was encountered",
                c
            ),
            NonStringAsKey => write!(
                fmt,
                "Something different than a string was used as the key in an \
json object"
            ),
            InvalidCodepoint => write!(fmt, "Per \'\\uXXXX\' was an invalid code point specified"),
            InvalidNumber => write!(
                fmt,
                "A floating-point number that is not valid in json was read \
(like NaN or Infinity)"
            ),
        }
    }
}

impl Error for JsonError {}

impl Display for JsonObject
{
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result<(), fmt::Error>
    {
        match self
        {
            Array(vec) =>
            {
                write!(fmt, "[")?;
                if !vec.is_empty()
                {
                    write!(fmt, "{}", vec[0])?;
                    for val in vec.iter().skip(1)
                    {
                        write!(fmt, ", {}", val)?;
                    }
                }
                write!(fmt, "]")
            }
            Obj(vec) =>
            {
                write!(fmt, "{{")?;
                if !vec.is_empty()
                {
                    write!(fmt, "{:?}: {}", vec[0].0, vec[0].1)?;
                    for val in vec.iter().skip(1)
                    {
                        write!(fmt, ", {:?}: {}", val.0, val.1)?;
                    }
                }
                write!(fmt, "}}")
            }
            Number(val) => write!(fmt, "{}", val),
            JsonStr(val) => write!(fmt, "{:?}", val),
            Bool(b) => write!(fmt, "{}", b),
            Null => write!(fmt, "null"),
        }
    }
}

macro_rules! skip_whitespace {
    ($s: expr, $newindex: expr) => {
        while $s.len() > $newindex && $s[$newindex].is_whitespace()
        {
            $newindex += 1;
        }
    };
}

impl JsonObject
{
    /// Checks if `s` starts with `goal` and if returns `val`
    fn partial_read_fixed_str(
        s: &[char],
        newindex: usize,
        goal: &str,
        val: Self,
    ) -> Result<(Self, usize), JsonError>
    {
        let len = goal.len();

        if s.len() < (newindex + len)
        {
            return Err(Empty);
        }
        for (i, c) in goal.chars().enumerate()
        {
            if s[newindex + i] != c
            {
                return Err(InvalidChar(s[newindex + i], newindex + i));
            }
        }
        Ok((val, newindex + len))
    }

    fn partial_read_false(s: &[char], newindex: usize) -> Result<(Self, usize), JsonError>
    {
        Self::partial_read_fixed_str(s, newindex, "false", Bool(false))
    }

    fn partial_read_true(s: &[char], newindex: usize) -> Result<(Self, usize), JsonError>
    {
        Self::partial_read_fixed_str(s, newindex, "true", Bool(true))
    }

    fn partial_read_null(s: &[char], newindex: usize) -> Result<(Self, usize), JsonError>
    {
        Self::partial_read_fixed_str(s, newindex, "null", Null)
    }

    /// Reads an array partially, but with arbitrary delimiters and end token
    ///
    /// Reads an array with arbitrary delimiters and end token partially.  It
    /// returns on success all three things: 1) the read object, 2) the
    /// newindex and 3) an array with all the delimiters.
    // The return type is very complex, but it seems as if it cannot be
    // refactored.
    #[allow(clippy::type_complexity)]
    fn partial_read_arrayoid(
        s: &[char],
        mut newindex: usize,
        endtoken: char,
    ) -> Result<(Vec<Self>, usize, Vec<(usize, char)>), JsonError>
    {
        let mut array = vec![];
        let mut delimiters = vec![];
        newindex += 1;

        loop
        {
            match Self::partial_read(s, newindex)
            {
                Ok((val, new)) =>
                {
                    newindex = new;
                    array.push(val);
                    skip_whitespace!(s, newindex);

                    if s.len() <= newindex
                    {
                        return Err(Empty);
                    }
                    else if s[newindex] == endtoken
                    {
                        return Ok((array, newindex + 1, delimiters));
                    }

                    delimiters.push((newindex, s[newindex]));
                    newindex += 1;
                    skip_whitespace!(s, newindex);
                }
                Err(InvalidChar(errendtoken, errindex))
                    if {
                        skip_whitespace!(s, newindex);
                        errindex == newindex && errendtoken == endtoken
                    } =>
                {
                    return Ok((array, newindex + 1, delimiters));
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// Reads an array; part of [`Self::partial_read`]
    ///
    /// Reads an array
    fn partial_read_array(s: &[char], newindex: usize) -> Result<(Self, usize), JsonError>
    {
        match Self::partial_read_arrayoid(s, newindex, ']')
        {
            Ok((rv, newindex, delimiters)) =>
            {
                for (pos, c) in delimiters
                {
                    if c != ','
                    {
                        return Err(InvalidChar(c, pos));
                    }
                }
                Ok((Array(rv), newindex))
            }
            Err(err) => Err(err),
        }
    }

    /// Reads a json objet; part of [`Self::partial_read`]
    ///
    /// Reads a json object; json object means in this context
    /// [`JsonObject::Obj`].
    fn partial_read_obj(s: &[char], newindex: usize) -> Result<(Self, usize), JsonError>
    {
        match Self::partial_read_arrayoid(s, newindex, '}')
        {
            Ok((mut rv, newindex, delimiters)) =>
            {
                let mut obj = Vec::with_capacity(delimiters.len() / 2 + 1);
                for wins in delimiters.windows(2).step_by(2)
                {
                    let ((key_pos, key_c), (val_pos, val_c)) = (wins[0], wins[1]);
                    if key_c != ':'
                    {
                        return Err(InvalidChar(key_c, key_pos));
                    }
                    if val_c != ','
                    {
                        return Err(InvalidChar(val_c, val_pos));
                    }
                }
                for i in 0..rv.len()
                {
                    if i % 2 == 1
                    {
                        match mem::replace(&mut rv[i - 1], Number(0.0))
                        {
                            JsonStr(key) =>
                            {
                                let val = mem::replace(&mut rv[i], Number(0.0));
                                obj.push((key, val));
                            }
                            _ => return Err(NonStringAsKey),
                        }
                    }
                }
                Ok((Obj(obj), newindex))
            }
            Err(err) => Err(err),
        }
    }

    fn partial_read_number(s: &[char], mut newindex: usize) -> Result<(Self, usize), JsonError>
    {
        skip_whitespace!(s, newindex);

        let startindex = newindex;

        if s.len() > newindex && (s[newindex] == '-' || s[newindex] == '+')
        {
            newindex += 1;
        }
        while s.len() > newindex && s[newindex] >= '0' && s[newindex] <= '9'
        {
            newindex += 1;
        }
        if s.len() > newindex && s[newindex] == '.'
        {
            newindex += 1;
            while s.len() > newindex && s[newindex] >= '0' && s[newindex] <= '9'
            {
                newindex += 1;
            }
        }
        if s.len() > newindex && s[newindex].to_ascii_lowercase() == 'e'
        {
            newindex += 1;
            if s.len() > newindex && (s[newindex] == '-' || s[newindex] == '+')
            {
                newindex += 1;
            }

            while s.len() > newindex && s[newindex] >= '0' && s[newindex] <= '9'
            {
                newindex += 1;
            }
        }

        let num: f64 = s[startindex..newindex]
            .iter()
            .collect::<String>()
            .parse()
            .expect("number parsing function called without number");

        if matches!(num.classify(), FpCategory::Infinite | FpCategory::Nan)
        {
            Err(InvalidNumber)
        }
        else
        {
            Ok((Number(num), newindex))
        }
    }

    /// Reads a string; part of [`Self::partial_read`]
    ///
    /// Reads a string
    #[allow(clippy::cast_possible_truncation)]
    fn partial_read_string(s: &[char], mut newindex: usize) -> Result<(Self, usize), JsonError>
    {
        let mut rv: Vec<u16> = Vec::new();
        let mut buf = [0; 2];
        newindex += 1;

        while s.len() > newindex && s[newindex] != '"'
        {
            if s[newindex] == '\\'
            {
                newindex += 1;
                if s.len() <= newindex
                {
                    return Err(EndedOnEscape);
                }
                match s[newindex]
                {
                    '\"' => rv.extend_from_slice('\"'.encode_utf16(&mut buf)),
                    '\\' => rv.extend_from_slice('\\'.encode_utf16(&mut buf)),
                    '/' => rv.extend_from_slice('/'.encode_utf16(&mut buf)),
                    'b' =>
                    {
                        rv.extend_from_slice('\x08'.encode_utf16(&mut buf));
                    }
                    'f' =>
                    {
                        rv.extend_from_slice('\x0c'.encode_utf16(&mut buf));
                    }
                    'n' =>
                    {
                        rv.extend_from_slice('\x0a'.encode_utf16(&mut buf));
                    }
                    'r' =>
                    {
                        rv.extend_from_slice('\x0d'.encode_utf16(&mut buf));
                    }
                    't' =>
                    {
                        rv.extend_from_slice('\x09'.encode_utf16(&mut buf));
                    }
                    c @ ('\x00'..='\x1F') =>
                    {
                        rv.extend_from_slice(c.encode_utf16(&mut buf));
                    }
                    'u' =>
                    {
                        newindex += 1;
                        if s.len() <= (newindex + 4)
                        {
                            return Err(EndedOnEscape);
                        }

                        let codepoint = s[newindex..newindex + 4]
                            .iter()
                            .enumerate()
                            .map(|(i, c)| {
                                c.to_ascii_lowercase()
                                    .to_digit(16)
                                    .map(|v| (v as u16) * 16_u16.pow(3 - i as u32))
                                    .ok_or(InvalidChar(*c, newindex + i))
                            })
                            .collect::<Result<Vec<_>, _>>()?
                            .into_iter()
                            .sum();

                        newindex += 3;

                        rv.push(codepoint);
                    }
                    c => return Err(UnknownEscapeSequence(c)),
                }
            }
            else
            {
                rv.extend_from_slice(s[newindex].encode_utf16(&mut buf));
            }
            newindex += 1;
        }

        if s.len() <= newindex
        {
            return Err(UnterminatedString);
        }

        Ok((
            JsonStr(
                decode_utf16(rv)
                    .map(|x| x.map_err(|_| InvalidCodepoint))
                    .collect::<Result<String, _>>()?,
            ),
            newindex + 1,
        ))
    }

    /// Reads a json object partially
    ///
    /// Reads a `JsonObject` partially and returns both, it and where the
    /// next character should be read.
    ///
    /// # Errors
    /// Returns an [`JsonError`] if the input was invalid.
    pub fn partial_read(s: &[char], newindex: usize) -> Result<(Self, usize), JsonError>
    {
        let mut newindex = newindex;

        skip_whitespace!(s, newindex);

        if s.len() <= newindex
        {
            return Err(Empty);
        }
        match s[newindex]
        {
            '0'..='9' | '+' | '-' => Self::partial_read_number(s, newindex),
            '[' => Self::partial_read_array(s, newindex),
            '{' => Self::partial_read_obj(s, newindex),
            '"' => Self::partial_read_string(s, newindex),
            'f' => Self::partial_read_false(s, newindex),
            't' => Self::partial_read_true(s, newindex),
            'n' => Self::partial_read_null(s, newindex),
            _ =>
            {
                if s.len() >= newindex
                {
                    Err(InvalidChar(s[newindex], newindex))
                }
                else
                {
                    Err(Empty)
                }
            }
        }
    }

    /// Reads a json object
    ///
    /// Reads a `JsonObject` or returns an error.
    ///
    /// # Errors
    /// Returns an [`JsonError`] if the input was invalid.
    pub fn read(s: &str) -> Result<Self, JsonError>
    {
        Self::partial_read(&s.chars().collect::<Vec<_>>(), 0).map(|(x, _)| x)
    }

    /// Checks if all keys are unique
    ///
    /// [RFC 8259](https://tools.ietf.org/html/rfc8259) requires all keys in
    /// objects ("{\"one\": 1, \"twenty\": 20}") to be unique.  This function
    /// checks recursively if that condition is met.
    #[must_use]
    pub fn unique(&self) -> bool
    {
        match self
        {
            Array(vec) => vec.iter().all(Self::unique),
            Obj(vec) =>
            {
                let strs_count = vec.len();
                let strs = vec
                    .iter()
                    .map(|(s, obj)| {
                        if obj.unique()
                        {
                            Some(s)
                        }
                        else
                        {
                            None
                        }
                    })
                    .collect::<Option<HashSet<_>>>();

                strs.map_or(false, |strs| strs_count == strs.len())
            }
            _ => true,
        }
    }
}

#[cfg(test)]
mod tests
{
    use crate::JsonError::{
        Empty, EndedOnEscape, InvalidChar, InvalidNumber, NonStringAsKey, UnknownEscapeSequence,
        UnterminatedString,
    };
    use crate::JsonObject::{self, Array, Bool, JsonStr, Null, Number, Obj};

    #[test]
    fn display_tests()
    {
        let tests = vec![
            (
                Array(vec![Number(42.0), JsonStr("Hello, World!".to_string())]),
                "[42, \"Hello, World!\"]",
            ),
            (
                Obj(vec![
                    ("first".to_string(), Number(5.0)),
                    ("sec".to_string(), JsonStr("val".to_string())),
                    ("last:".to_string(), Number(-1337.0)),
                ]),
                "{\"first\": 5, \"sec\": \"val\", \"last:\": -1337}",
            ),
            (JsonStr("test".to_string()), "\"test\""),
            (JsonStr("\"test\"".to_string()), "\"\\\"test\\\"\""),
            (Bool(true), "true"),
            (Bool(false), "false"),
            (Null, "null"),
        ];

        for (input, output) in tests
        {
            assert_eq!(format!("{}", input), output);
        }
    }

    #[test]
    fn array_read_tests()
    {
        let tests = vec![
            ("[]", "[        ]", Array(vec![])),
            (
                "[[[]]]",
                "     [[[]]]",
                Array(vec![Array(vec![Array(vec![])])]),
            ),
            (
                "[[], []]",
                "[ []  , []]",
                Array(vec![Array(vec![]), Array(vec![])]),
            ),
            (
                "[[[[[]]]], []]",
                " [ [  [ [ [ ] ]  ] ] , [ ] ]  ",
                Array(vec![
                    Array(vec![Array(vec![Array(vec![Array(vec![])])])]),
                    Array(vec![]),
                ]),
            ),
            (
                "[[[[[]]]], []]",
                "[[[[[]]]],[]]",
                Array(vec![
                    Array(vec![Array(vec![Array(vec![Array(vec![])])])]),
                    Array(vec![]),
                ]),
            ),
        ];

        for (input, whitespaced, output) in tests
        {
            assert_eq!(JsonObject::read(input).unwrap(), output);
            assert_eq!(JsonObject::read(whitespaced).unwrap(), output);
            assert_eq!(format!("{}", JsonObject::read(input).unwrap()), input);
        }
    }

    #[test]
    fn number_read_tests()
    {
        let tests = vec![
            ("0", "  -0  ", Number(0.0)),
            #[warn(clippy::cast_possible_truncation)]
            ("10", "  +10  ", Number(10.0)),
            ("-42", "  -42", Number(-42.0)),
            ("10000", "10000   ", Number(10000.0)),
            ("5", "5 0", Number(5.0)),
            ("5.01", " 5.01", Number(5.01)),
            ("501", "5.01E+2", Number(501.0)),
            ("501", "5.01E2", Number(501.0)),
            ("-501", "-5.01E+2", Number(-501.0)),
            ("0.0501", "5.01E-2", Number(0.0501)),
            ("5.042", " 5.042", Number(5.042)),
            (
                "3.141592653589793",
                "3.14159265358979323846264338327950288419716939937508",
                Number(3.141592653589793),
            ),
        ];

        for (input, whitespaced, output) in tests
        {
            assert_eq!(JsonObject::read(input).unwrap(), output);
            assert_eq!(JsonObject::read(whitespaced).unwrap(), output);
            assert_eq!(format!("{}", JsonObject::read(input).unwrap()), input);
        }
    }

    #[test]
    fn read_string_tests()
    {
        let tests = vec![
            (
                "\"Hello, World!\"",
                "  \"Hello, World!\"  ",
                "Hello, World!",
            ),
            (
                "\"Test \\\" tseT\"",
                "\"Test \\\" tseT\"    ",
                "Test \" tseT",
            ),
            ("\"deF \\\\ Abc\"", "\"deF \\\\ Abc\"    ", "deF \\ Abc"),
            (
                "\"deF2 \\\\ 3Abc\"",
                "\"deF2 \\\\ 3Abc\"    ",
                "deF2 \\ 3Abc",
            ),
            ("\"\\n\"", "\"\\n\"", "\n"),
            ("\"Json\"", "\"\\u004ason\"", "Json"),
            ("\"Json\"", "\"\\u004ason\"", "Json"),
            ("\"ä\"", "\"\\u00e4\"", "ä"),
            ("\"𝄞\"", "\"\\uD834\\uDD1E\"", "𝄞"),
        ];

        for (input, whitespaced, output) in tests
        {
            assert_eq!(
                JsonObject::read(input).unwrap(),
                JsonStr(output.to_string())
            );
            assert_eq!(
                JsonObject::read(whitespaced).unwrap(),
                JsonStr(output.to_string())
            );
            assert_eq!(format!("{}", JsonObject::read(input).unwrap()), input);
        }
    }

    #[test]
    fn read_obj_tests()
    {
        let longstr1 = "{\"first\": [10, 42], \"sec\": 15, \"la\\\"st\": \"Hi, World!\"}";
        let longstr2 = "{\"first\" : [10,42],\"sec\":15,\"la\\\"st\": \"Hi, World!\" } ";
        let longstr4 = "  {  \"sec\" : 15 , \"la\\\"st\" : \"Hi, World!\"  }   ";
        let tests = vec![
            (
                longstr1,
                longstr2,
                Obj(vec![
                    ("first".to_string(), Array(vec![Number(10.0), Number(42.0)])),
                    ("sec".to_string(), Number(15.0)),
                    ("la\"st".to_string(), JsonStr("Hi, World!".to_string())),
                ]),
            ),
            (
                "{\"sec\": 15, \"la\\\"st\": \"Hi, World!\"}",
                longstr4,
                Obj(vec![
                    ("sec".to_string(), Number(15.0)),
                    ("la\"st".to_string(), JsonStr("Hi, World!".to_string())),
                ]),
            ),
            ("{}", "{}", Obj(vec![])),
        ];

        for (input, whitespaced, output) in tests
        {
            assert_eq!(JsonObject::read(input).unwrap(), output);
            assert_eq!(JsonObject::read(whitespaced).unwrap(), output);
            assert_eq!(format!("{}", JsonObject::read(input).unwrap()), input);
        }
    }

    #[test]
    fn read_bool_null_tests()
    {
        let tests = vec![
            ("true", "   true   ", Bool(true)),
            ("false", "false     ", Bool(false)),
            ("null", "     null", Null),
        ];

        for (input, whitespaced, output) in tests
        {
            assert_eq!(JsonObject::read(input).unwrap(), output);
            assert_eq!(JsonObject::read(whitespaced).unwrap(), output);
            assert_eq!(format!("{}", JsonObject::read(input).unwrap()), input);
        }
    }

    #[test]
    fn read_mixed_tests()
    {
        let tests = vec![
            (
                "[5, [-4, [10, 30]]]",
                "[  5, [ -4 ,  [ 10 , 30 ] ]]",
                Array(vec![
                    Number(5.0),
                    Array(vec![Number(-4.0), Array(vec![Number(10.0), Number(30.0)])]),
                ]),
            ),
            (
                "[5, \"Hi  !\", -20]",
                "[ 5 ,   \"Hi  !\", -20    ]",
                Array(vec![
                    Number(5.0),
                    JsonStr("Hi  !".to_string()),
                    Number(-20.0),
                ]),
            ),
        ];

        for (input, whitespaced, output) in tests
        {
            assert_eq!(JsonObject::read(input).unwrap(), output);
            assert_eq!(JsonObject::read(whitespaced).unwrap(), output);
            assert_eq!(format!("{}", JsonObject::read(input).unwrap()), input);
        }
    }

    #[test]
    fn read_errors()
    {
        let tests = vec![
            ("", Empty),
            ("]", InvalidChar(']', 0)),
            ("[[[]]", Empty),
            ("[[],[]", Empty),
            ("[[,[]]", InvalidChar(',', 2)),
            ("[[].[]]", InvalidChar('.', 3)),
            ("[[]:[]]", InvalidChar(':', 3)),
            ("[[]#[]]", InvalidChar('#', 3)),
            ("[[] []]", InvalidChar('[', 4)),
            ("[[54,[]]", Empty),
            ("\"\\a\"", UnknownEscapeSequence('a')),
            ("\"\\", EndedOnEscape),
            ("\"", UnterminatedString),
            ("{\"first\":[10,42],[50]:15}", NonStringAsKey),
            ("fals", Empty),
            ("5e2147483649", InvalidNumber),
        ];

        for (input, output) in tests
        {
            assert_eq!(JsonObject::read(input), Err(output));
        }
    }

    #[test]
    fn display_jsonerror_tests()
    {
        let tests = vec![
            (
                JsonObject::read(""),
                "The input was empty (or only whitespace)",
            ),
            (
                JsonObject::read("{\"test\": \"abc\\uD800\"}"),
                "Per \'\\uXXXX\' was an invalid code point specified",
            ),
            (
                JsonObject::read("{5: \"hgf\"}"),
                "Something different than a string was used \
as the key in an json object",
            ),
        ];

        for (val, s) in tests
        {
            assert!(val.is_err());
            assert_eq!(val.unwrap_err().to_string(), s);
        }
    }

    #[test]
    fn unique_tests()
    {
        let tests = vec![
            (Number(4.0), true),
            (JsonStr("test".to_string()), true),
            (Bool(true), true),
            (Bool(false), true),
            (Null, true),
            (
                Obj(vec![
                    ("abc".to_string(), Number(0.0)),
                    ("def".to_string(), Number(0.0)),
                    ("ghi".to_string(), Number(5.0)),
                ]),
                true,
            ),
            (
                Obj(vec![
                    ("abc".to_string(), Number(0.0)),
                    ("def".to_string(), Number(2.0)),
                    ("abc".to_string(), Number(5.0)),
                ]),
                false,
            ),
            (
                Array(vec![
                    Obj(vec![
                        ("qwe".to_string(), JsonStr("Hi!".to_string())),
                        ("asd".to_string(), Bool(true)),
                        ("yxc".to_string(), Null),
                    ]),
                    Obj(vec![
                        ("rtz".to_string(), Number(0.0)),
                        ("uio".to_string(), Number(2.0)),
                        ("lkj".to_string(), Number(5.0)),
                    ]),
                ]),
                true,
            ),
            (
                Array(vec![
                    Obj(vec![
                        ("qwe".to_string(), JsonStr("Hi!".to_string())),
                        ("asd".to_string(), Bool(true)),
                        ("yxc".to_string(), Null),
                    ]),
                    Obj(vec![
                        ("rtz".to_string(), Number(0.0)),
                        ("uio".to_string(), Number(2.0)),
                        ("uio".to_string(), Number(5.0)),
                    ]),
                ]),
                false,
            ),
            (
                Obj(vec![
                    (
                        "yse".to_string(),
                        Obj(vec![
                            ("qwe".to_string(), JsonStr("Hi!".to_string())),
                            ("asd".to_string(), Bool(true)),
                            ("yxc".to_string(), Null),
                        ]),
                    ),
                    (
                        "xdr".to_string(),
                        Obj(vec![
                            ("rtz".to_string(), Number(0.0)),
                            ("uio".to_string(), Number(2.0)),
                            ("lkj".to_string(), Number(5.0)),
                        ]),
                    ),
                ]),
                true,
            ),
            (
                Obj(vec![
                    (
                        "mju".to_string(),
                        Obj(vec![
                            ("qwe".to_string(), JsonStr("Hi!".to_string())),
                            ("asd".to_string(), Bool(true)),
                            ("yxc".to_string(), Null),
                        ]),
                    ),
                    (
                        "nhz".to_string(),
                        Obj(vec![
                            ("rtz".to_string(), Number(0.0)),
                            ("uio".to_string(), Number(2.0)),
                            ("uio".to_string(), Number(5.0)),
                        ]),
                    ),
                ]),
                false,
            ),
        ];

        for (input, output) in tests
        {
            assert_eq!(input.unique(), output);
            assert_eq!(JsonObject::read(&format!("{}", input)), Ok(input))
        }
    }
}
