#![warn(missing_docs)]

//! Encode and decode data with arbitrary bases. This coder supports multicharacter symbols, which
//! allows bases greater than 256.
//!
//! Symbols in the alphabet must have a uniform length or the encoded data must separate symbols
//! with a delimiter character.
//!
//! Currently only `u128` is supported as a data type.

use itertools::Itertools;
use std::collections::HashMap;
use std::mem;
use std::vec::Vec;

/// Error type returned by the [`Coder`](struct.Coder.html) factory methods `with_uniform_alphabet`
/// and `with_delimiter`.
#[derive(Debug, PartialEq)]
pub enum CoderFactoryError {
    /// The symbols in the alphabet differ in length.
    AlphabetNotUniform,
    /// The alphabet contains too few symbols.
    AlphabetTooSmall,
    /// The delimiter is part of a symbol.
    DelimiterOverlapping,
    /// There are duplicate symbols in the alphabet.
    SymbolsNotUnique,
}

/// Error type returned by the `decode` method of the [`Coder`](struct.Coder.html).
#[derive(Debug, PartialEq)]
pub enum DecoderError {
    /// The input string is empty.
    InputEmpty,
    /// The input length is not a multiple of the symbol length, when using a uniform alphabet.
    InputLengthUnmatched,
    /// An integer overflow occurred.
    Overflow,
    /// An invalid symbol has been encountered in the input data.
    SymbolInvalid,
}

/// Coder for a specific alphabet.
#[derive(Debug)]
pub struct Coder<'a> {
    alphabet: Vec<String>,
    symbols_map: HashMap<&'a str, u128>,
    delimiter: Option<char>,
}

impl<'a> Coder<'a> {
    fn new(alphabet: Vec<String>, delimiter: Option<char>) -> Result<Self, CoderFactoryError> {
        if alphabet.len() < 2 {
            return Err(CoderFactoryError::AlphabetTooSmall);
        }

        let mut symbols_map = HashMap::with_capacity(alphabet.len());
        let insert_and_check_dup = |(i, s): (usize, &String)| {
            let symbol = s.as_str();
            // The alphabet vec is not going to be changed and the symbols map won't live longer
            // than the alphabet vec. So we can safely point to the heap allocated Strings.
            let symbol = unsafe { mem::transmute(symbol) };
            symbols_map.insert(symbol, i as u128).is_some()
        };
        if alphabet
            .iter()
            .enumerate()
            .map(insert_and_check_dup)
            .any(|x| x)
        {
            return Err(CoderFactoryError::SymbolsNotUnique);
        }

        Ok(Self {
            alphabet,
            symbols_map,
            delimiter,
        })
    }

    /// Create a `Coder` with a uniform alphabet and no delimiter.
    pub fn with_uniform_alphabet(alphabet: Vec<String>) -> Result<Self, CoderFactoryError> {
        if alphabet.len() >= 2 {
            for symbol in &alphabet[1..] {
                if symbol.len() != alphabet[0].len() {
                    return Err(CoderFactoryError::AlphabetNotUniform);
                }
            }
        }
        Self::new(alphabet, None)
    }

    /// Create a `Coder` with a delimiter.
    pub fn with_delimiter(
        alphabet: Vec<String>,
        delimiter: char,
    ) -> Result<Self, CoderFactoryError> {
        for symbol in &alphabet {
            if symbol.contains(delimiter) {
                return Err(CoderFactoryError::DelimiterOverlapping);
            }
        }
        Self::new(alphabet, Some(delimiter))
    }

    fn base(&self) -> u128 {
        self.alphabet.len() as u128
    }

    /// Encode data to the `Coder`'s base.
    pub fn encode(&self, mut value: u128) -> String {
        let mut symbols = Vec::new();
        loop {
            symbols.push(&self.alphabet[(value % self.base()) as usize]);
            value /= self.base();
            if value == 0 {
                break;
            }
        }
        let delimiter = self.delimiter.map_or("".to_string(), |x| x.to_string());
        Itertools::join(&mut symbols.iter().rev(), &delimiter)
    }

    fn symbol_len(&self) -> Option<usize> {
        if self.delimiter.is_some() {
            return None;
        }
        Some(self.alphabet[0].len())
    }

    fn symbol_value(&self, symbol: &str) -> Result<u128, DecoderError> {
        self.symbols_map
            .get(symbol)
            .ok_or(DecoderError::SymbolInvalid)
            .and_then(|&x| Ok(x as u128))
    }

    /// Decode data from the `Coder`'s base.
    pub fn decode(&self, value: &str) -> Result<u128, DecoderError> {
        if value.is_empty() {
            return Err(DecoderError::InputEmpty);
        }
        if self.symbol_len().is_some() && value.len() % self.symbol_len().unwrap() != 0 {
            return Err(DecoderError::InputLengthUnmatched);
        }

        let rsymbols: Box<Iterator<Item = &str>> = if self.delimiter.is_some() {
            Box::new(value.rsplit(self.delimiter.unwrap()))
        } else {
            let slen = self.symbol_len().unwrap();
            Box::new(
                (0..(value.len() / slen))
                    .rev()
                    .map(move |i| &value[(i * slen)..((i + 1) * slen)]),
            )
        };

        let symbol_values = rsymbols.map(|x| self.symbol_value(x));
        let mut result: u128 = 0;
        let mut multiplier: u128 = 0;
        for v in symbol_values {
            if multiplier == 0 {
                multiplier = 1;
            } else {
                multiplier = multiplier
                    .checked_mul(self.base())
                    .ok_or(DecoderError::Overflow)?;
            }
            result = result
                .checked_add(v?.checked_mul(multiplier).ok_or(DecoderError::Overflow)?)
                .ok_or(DecoderError::Overflow)?;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_returns_ok() {
        let binary_alphabet = vec!["0".to_string(), "1".to_string()];

        let result = Coder::with_uniform_alphabet(binary_alphabet.clone());
        assert!(result.is_ok());
        let result = Coder::with_delimiter(binary_alphabet, '-');
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_returns_err() {
        let empty_alphabet = vec![];

        let result = Coder::with_uniform_alphabet(empty_alphabet.clone());
        assert_eq!(CoderFactoryError::AlphabetTooSmall, result.unwrap_err());
        let result = Coder::with_delimiter(empty_alphabet, '-');
        assert_eq!(CoderFactoryError::AlphabetTooSmall, result.unwrap_err());

        let singleton_alphabet = vec!["a".to_string()];
        let result = Coder::with_uniform_alphabet(singleton_alphabet.clone());
        assert_eq!(CoderFactoryError::AlphabetTooSmall, result.unwrap_err());
        let result = Coder::with_delimiter(singleton_alphabet, '-');
        assert_eq!(CoderFactoryError::AlphabetTooSmall, result.unwrap_err());

        let monotone_alphabet = vec!["x".to_string(), "x".to_string()];
        let result = Coder::with_uniform_alphabet(monotone_alphabet.clone());
        assert_eq!(CoderFactoryError::SymbolsNotUnique, result.unwrap_err());
        let result = Coder::with_delimiter(monotone_alphabet, '-');
        assert_eq!(CoderFactoryError::SymbolsNotUnique, result.unwrap_err());

        let non_uniform_alphabet = vec!["a".to_string(), "bc".to_string()];
        let result = Coder::with_uniform_alphabet(non_uniform_alphabet);
        assert_eq!(CoderFactoryError::AlphabetNotUniform, result.unwrap_err());

        let binary_alphabet = vec!["abc".to_string(), "def".to_string()];
        let result = Coder::with_delimiter(binary_alphabet, 'b');
        assert_eq!(CoderFactoryError::DelimiterOverlapping, result.unwrap_err());
    }

    #[test]
    fn test_encode_decode() {
        let binary_alphabet = vec!["0".to_string(), "1".to_string()];

        let coder = Coder::with_uniform_alphabet(binary_alphabet.clone()).unwrap();
        assert_eq!("10110111", coder.encode(0b10110111));
        assert_eq!(0b10110111, coder.decode(&"10110111".to_string()).unwrap());
        assert_eq!(
            DecoderError::InputEmpty,
            coder.decode(&"".to_string()).unwrap_err()
        );
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"10110121".to_string()).unwrap_err()
        );

        let decimal_alphabet: Vec<_> = (0..10).map(|i| i.to_string()).collect();
        let coder = Coder::with_uniform_alphabet(decimal_alphabet).unwrap();
        assert_eq!("5108631", coder.encode(5108631));
        assert_eq!(5108631, coder.decode(&"5108631".to_string()).unwrap());
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"51x8631".to_string()).unwrap_err()
        );

        let tertiary_alphabet = vec!["zero".to_string(), "oone".to_string(), "twoo".to_string()];
        let coder = Coder::with_uniform_alphabet(tertiary_alphabet).unwrap();
        assert_eq!("ooneoonetwoozero", coder.encode(42));
        assert_eq!(42, coder.decode(&"ooneoonetwoozero".to_string()).unwrap());
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"ooneoometwoozero".to_string()).unwrap_err()
        );
        assert_eq!(
            DecoderError::InputLengthUnmatched,
            coder.decode(&"ooneoonetwoozer".to_string()).unwrap_err()
        );

        let coder = Coder::with_delimiter(binary_alphabet, '-').unwrap();
        assert_eq!("1-1-0-1", coder.encode(13));
        assert_eq!(13, coder.decode(&"1-1-0-1".to_string()).unwrap());
        assert_eq!(
            DecoderError::InputEmpty,
            coder.decode(&"".to_string()).unwrap_err()
        );
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"1-1-0-1-".to_string()).unwrap_err()
        );
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"-1-1-0-1".to_string()).unwrap_err()
        );
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"1--1-0-1".to_string()).unwrap_err()
        );
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"1-10-1".to_string()).unwrap_err()
        );

        let binary_names_alphabet = vec!["zero".to_string(), "one".to_string()];
        let coder = Coder::with_delimiter(binary_names_alphabet, ' ').unwrap();
        assert_eq!("one zero one one", coder.encode(11));
        assert_eq!(11, coder.decode(&"one zero one one".to_string()).unwrap());
        assert_eq!(
            DecoderError::SymbolInvalid,
            coder.decode(&"one zer one one".to_string()).unwrap_err()
        );
    }

    #[test]
    fn test_decode_overflow() {
        let hex_alphabet: Vec<_> = "0123456789abcdef"
            .matches(|_| true)
            .map(|x| x.to_string())
            .collect();
        let coder = Coder::with_uniform_alphabet(hex_alphabet).unwrap();
        let ipv6addr: u128 = 0x20010db8000000420000cafffe001337;
        let ipv6addr_s = "20010db8000000420000cafffe001337".to_string();
        assert_eq!(ipv6addr_s, coder.encode(ipv6addr));
        assert_eq!(ipv6addr, coder.decode(&ipv6addr_s).unwrap());
        assert_eq!(
            DecoderError::Overflow,
            coder.decode(&(ipv6addr_s + "0")).unwrap_err()
        );
    }
}
