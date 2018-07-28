#[derive(Debug, PartialEq)]
pub enum ConverterError {
    AlphabetNotUniform,
    AlphabetTooSmall,
    DelimiterOverlapping,
    SymbolsNotUnique,
}

#[derive(Debug, PartialEq)]
pub enum DecodeError {
    InputEmpty,
    InputLengthUnmatched,
    InputSymbolInvalid,
}

#[derive(Debug)]
pub struct Converter<'a> {
    alphabet: &'a [String],
    delimiter: Option<char>,
}

impl<'a> Converter<'a> {
    fn new(alphabet: &'a [String], delimiter: Option<char>) -> Result<Self, ConverterError> {
        if alphabet.len() < 2 {
            return Err(ConverterError::AlphabetTooSmall);
        }

        for i in 1..alphabet.len() {
            if alphabet[i..].contains(&alphabet[i - 1]) {
                return Err(ConverterError::SymbolsNotUnique);
            }
        }

        Ok(Self { alphabet, delimiter })
    }

    pub fn with_uniform_alphabet(alphabet: &'a [String]) -> Result<Self, ConverterError> {
        if alphabet.len() >= 2 {
            for symbol in &alphabet[1..] {
                if symbol.len() != alphabet[0].len() {
                    return Err(ConverterError::AlphabetNotUniform);
                }
            }
        }
        Self::new(alphabet, None)
    }

    pub fn with_delimiter(alphabet: &'a [String], delimiter: char) -> Result<Self, ConverterError> {
        for symbol in alphabet {
            if symbol.contains(delimiter) {
                return Err(ConverterError::DelimiterOverlapping);
            }
        }
        Self::new(alphabet, Some(delimiter))
    }

    fn base(&self) -> u128 {
        self.alphabet.len() as u128
    }

    pub fn encode(&self, mut value: u128) -> String {
        let mut result = String::new();
        loop {
            if !result.is_empty() && self.delimiter.is_some() {
                result = self.delimiter.unwrap().to_string() + &result;
            }
            result = self.alphabet[(value % self.base()) as usize].clone() + &result;
            value /= self.base();
            if value == 0 {
                break;
            }
        }
        result
    }

    fn symbol_len(&self) -> Option<usize> {
        if self.delimiter.is_some() {
            return None;
        }
        Some(self.alphabet[0].len())
    }

    fn symbol_value(&self, symbol: String) -> Result<u128, DecodeError> {
        self.alphabet.iter()
            .position(|x| *x == symbol)
            .ok_or(DecodeError::InputSymbolInvalid)
            .and_then(|x| Ok(x as u128))
    }

    pub fn decode(&self, value: String) -> Result<u128, DecodeError> {
        if value.is_empty() {
            return Err(DecodeError::InputEmpty);
        }
        if self.symbol_len().is_some() && value.len() % self.symbol_len().unwrap() != 0 {
            return Err(DecodeError::InputLengthUnmatched);
        }

        // TODO: DRY this up, make it more functional
        if self.delimiter.is_some() {
            let symbol_values = value.rsplit(self.delimiter.unwrap())
                .map(|x| self.symbol_value(x.to_string()));
            let mut result: u128 = 0;
            let mut multiplier: u128 = 0;
            for v in symbol_values {
                if multiplier == 0 {
                    multiplier = 1;
                } else {
                    // TODO: catch overflow
                    multiplier *= self.base()
                }
                // TODO: catch overflow
                result += v? * multiplier;
            }
            Ok(result)
        } else {
            let mut result: u128 = 0;
            let mut multiplier: u128 = 0;
            let slen = self.symbol_len().unwrap();
            for i in (0..(value.len() / slen)).rev() {
                let symbol = &value[(i * slen)..((i + 1) * slen)];
                let v = self.symbol_value(symbol.to_string());
                if multiplier == 0 {
                    multiplier = 1;
                } else {
                    // TODO: catch overflow
                    multiplier *= self.base()
                }
                // TODO: catch overflow
                result += v? * multiplier;
            }
            Ok(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_returns_ok() {
        let binary_alphabet = vec!("0".to_string(), "1".to_string());

        let result = Converter::with_uniform_alphabet(&binary_alphabet);
        assert!(result.is_ok());

        let result = Converter::with_delimiter(&binary_alphabet, '-');
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_returns_err() {
        let empty_alphabet = vec!();
        let result = Converter::with_uniform_alphabet(&empty_alphabet);
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());
        let result = Converter::with_delimiter(&empty_alphabet, '-');
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());

        let singleton_alphabet = vec!("a".to_string());
        let result = Converter::with_uniform_alphabet(&singleton_alphabet);
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());
        let result = Converter::with_delimiter(&singleton_alphabet, '-');
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());

        let monotone_alphabet = vec!("x".to_string(), "x".to_string());
        let result = Converter::with_uniform_alphabet(&monotone_alphabet);
        assert_eq!(ConverterError::SymbolsNotUnique, result.unwrap_err());
        let result = Converter::with_delimiter(&monotone_alphabet, '-');
        assert_eq!(ConverterError::SymbolsNotUnique, result.unwrap_err());

        let non_uniform_alphabet = vec!("a".to_string(), "bc".to_string());
        let result = Converter::with_uniform_alphabet(&non_uniform_alphabet);
        assert_eq!(ConverterError::AlphabetNotUniform, result.unwrap_err());

        let binary_alphabet = vec!("abc".to_string(), "def".to_string());
        let result = Converter::with_delimiter(&binary_alphabet, 'b');
        assert_eq!(ConverterError::DelimiterOverlapping, result.unwrap_err());
    }

    #[test]
    fn test_encode_decode() {
        let binary_alphabet = vec!("0".to_string(), "1".to_string());
        let converter = Converter::with_uniform_alphabet(&binary_alphabet).unwrap();
        assert_eq!("10110111", converter.encode(0b10110111));
        assert_eq!(0b10110111, converter.decode("10110111".to_string()).unwrap());
        assert_eq!(DecodeError::InputEmpty, converter.decode("".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("10110121".to_string()).unwrap_err());

        let decimal_alphabet: Vec<_> = (0..10).map(|i| i.to_string()).collect();
        let converter = Converter::with_uniform_alphabet(&decimal_alphabet).unwrap();
        assert_eq!("5108631", converter.encode(5108631));
        assert_eq!(5108631, converter.decode("5108631".to_string()).unwrap());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("51x8631".to_string()).unwrap_err());

        let tertiary_alphabet: Vec<_> = ["zero", "oone", "twoo"].iter().map(|s| s.to_string()).collect();
        let converter = Converter::with_uniform_alphabet(&tertiary_alphabet).unwrap();
        assert_eq!("ooneoonetwoozero", converter.encode(42));
        assert_eq!(42, converter.decode("ooneoonetwoozero".to_string()).unwrap());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("ooneoometwoozero".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputLengthUnmatched, converter.decode("ooneoonetwoozer".to_string()).unwrap_err());

        let converter = Converter::with_delimiter(&binary_alphabet, '-').unwrap();
        assert_eq!("1-1-0-1", converter.encode(13));
        assert_eq!(13, converter.decode("1-1-0-1".to_string()).unwrap());
        assert_eq!(DecodeError::InputEmpty, converter.decode("".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("1-1-0-1-".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("-1-1-0-1".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("1--1-0-1".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("1-10-1".to_string()).unwrap_err());

        let binary_names_alphabet = vec!("zero".to_string(), "one".to_string());
        let converter = Converter::with_delimiter(&binary_names_alphabet, ' ').unwrap();
        assert_eq!("one zero one one", converter.encode(11));
        assert_eq!(11, converter.decode("one zero one one".to_string()).unwrap());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode("one zer one one".to_string()).unwrap_err());
        // TODO test overflow
    }
}
