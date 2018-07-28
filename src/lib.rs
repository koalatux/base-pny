#[derive(Debug, PartialEq)]
pub enum ConverterError {
    AlphabetNotUniform,
    AlphabetTooSmall,
    DelimiterOverlapping,
    SymbolsNotUnique,
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_returns_ok() {
        let binary_alphabet = vec!(String::from("0"), String::from("1"));

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

        let singleton_alphabet = vec!(String::from("a"));
        let result = Converter::with_uniform_alphabet(&singleton_alphabet);
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());
        let result = Converter::with_delimiter(&singleton_alphabet, '-');
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());

        let monotone_alphabet = vec!(String::from("x"), String::from("x"));
        let result = Converter::with_uniform_alphabet(&monotone_alphabet);
        assert_eq!(ConverterError::SymbolsNotUnique, result.unwrap_err());
        let result = Converter::with_delimiter(&monotone_alphabet, '-');
        assert_eq!(ConverterError::SymbolsNotUnique, result.unwrap_err());

        let non_uniform_alphabet = vec!(String::from("a"), String::from("bc"));
        let result = Converter::with_uniform_alphabet(&non_uniform_alphabet);
        assert_eq!(ConverterError::AlphabetNotUniform, result.unwrap_err());

        let binary_alphabet = vec!(String::from("abc"), String::from("def"));
        let result = Converter::with_delimiter(&binary_alphabet, 'b');
        assert_eq!(ConverterError::DelimiterOverlapping, result.unwrap_err());
    }

    #[test]
    fn test_encode() {
        let binary_alphabet = vec!(String::from("0"), String::from("1"));
        let converter = Converter::with_uniform_alphabet(&binary_alphabet).unwrap();
        assert_eq!("10110111", converter.encode(0b10110111));

        let decimal_alphabet = (0..10).map(|i| { i.to_string() }).collect::<Vec<String>>();
        let converter = Converter::with_uniform_alphabet(&decimal_alphabet).unwrap();
        assert_eq!("5108631", converter.encode(5108631));

        let binary_alphabet = vec!(String::from("zero"), String::from("one"));
        let converter = Converter::with_delimiter(&binary_alphabet, ' ').unwrap();
        assert_eq!("one zero one one", converter.encode(11));
    }
}
