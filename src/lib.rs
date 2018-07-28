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
    InputOverflow,
    InputSymbolInvalid,
}

#[derive(Debug)]
pub struct Converter<'a> {
    alphabet: &'a [&'a str],
    delimiter: Option<char>,
}

impl<'a> Converter<'a> {
    fn new(alphabet: &'a [&str], delimiter: Option<char>) -> Result<Self, ConverterError> {
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

    pub fn with_uniform_alphabet(alphabet: &'a [&str]) -> Result<Self, ConverterError> {
        if alphabet.len() >= 2 {
            for symbol in &alphabet[1..] {
                if symbol.len() != alphabet[0].len() {
                    return Err(ConverterError::AlphabetNotUniform);
                }
            }
        }
        Self::new(alphabet, None)
    }

    pub fn with_delimiter(alphabet: &'a [&str], delimiter: char) -> Result<Self, ConverterError> {
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
            result = self.alphabet[(value % self.base()) as usize].to_string() + &result;
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

    fn symbol_value(&self, symbol: &str) -> Result<u128, DecodeError> {
        self.alphabet.iter()
            .position(|x| *x == symbol)
            .ok_or(DecodeError::InputSymbolInvalid)
            .and_then(|x| Ok(x as u128))
    }

    pub fn decode(&self, value: &str) -> Result<u128, DecodeError> {
        if value.is_empty() {
            return Err(DecodeError::InputEmpty);
        }
        if self.symbol_len().is_some() && value.len() % self.symbol_len().unwrap() != 0 {
            return Err(DecodeError::InputLengthUnmatched);
        }

        let rsymbols: Box<Iterator<Item=&str>> = if self.delimiter.is_some() {
            Box::new(value.rsplit(self.delimiter.unwrap()))
        } else {
            let slen = self.symbol_len().unwrap();
            Box::new((0..(value.len() / slen)).rev()
                .map(move |i| &value[(i * slen)..((i + 1) * slen)]))
        };

        let symbol_values = rsymbols.map(|x| self.symbol_value(x));
        let mut result: u128 = 0;
        let mut multiplier: u128 = 0;
        for v in symbol_values {
            if multiplier == 0 {
                multiplier = 1;
            } else {
                multiplier = multiplier.checked_mul(self.base())
                    .ok_or(DecodeError::InputOverflow)?;
            }
            result = result.checked_add(
                v?.checked_mul(multiplier)
                    .ok_or(DecodeError::InputOverflow)?
            ).ok_or(DecodeError::InputOverflow)?;
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_returns_ok() {
        let binary_alphabet = ["0", "1"];

        let result = Converter::with_uniform_alphabet(&binary_alphabet);
        assert!(result.is_ok());

        let result = Converter::with_delimiter(&binary_alphabet, '-');
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_returns_err() {
        let empty_alphabet = [];
        let result = Converter::with_uniform_alphabet(&empty_alphabet);
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());
        let result = Converter::with_delimiter(&empty_alphabet, '-');
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());

        let singleton_alphabet = ["a"];
        let result = Converter::with_uniform_alphabet(&singleton_alphabet);
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());
        let result = Converter::with_delimiter(&singleton_alphabet, '-');
        assert_eq!(ConverterError::AlphabetTooSmall, result.unwrap_err());

        let monotone_alphabet = ["x", "x"];
        let result = Converter::with_uniform_alphabet(&monotone_alphabet);
        assert_eq!(ConverterError::SymbolsNotUnique, result.unwrap_err());
        let result = Converter::with_delimiter(&monotone_alphabet, '-');
        assert_eq!(ConverterError::SymbolsNotUnique, result.unwrap_err());

        let non_uniform_alphabet = ["a", "bc"];
        let result = Converter::with_uniform_alphabet(&non_uniform_alphabet);
        assert_eq!(ConverterError::AlphabetNotUniform, result.unwrap_err());

        let binary_alphabet = ["abc", "def"];
        let result = Converter::with_delimiter(&binary_alphabet, 'b');
        assert_eq!(ConverterError::DelimiterOverlapping, result.unwrap_err());
    }

    #[test]
    fn test_encode_decode() {
        let binary_alphabet = ["0", "1"];
        let converter = Converter::with_uniform_alphabet(&binary_alphabet).unwrap();
        assert_eq!("10110111", converter.encode(0b10110111));
        assert_eq!(0b10110111, converter.decode(&"10110111".to_string()).unwrap());
        assert_eq!(DecodeError::InputEmpty, converter.decode(&"".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"10110121".to_string()).unwrap_err());

        let decimal_alphabet_mem: Vec<_> = (0..10).map(|i| i.to_string()).collect();
        let decimal_alphabet: Vec<_> = decimal_alphabet_mem.iter().map(|x| &x[..]).collect();
        let converter = Converter::with_uniform_alphabet(&decimal_alphabet[..]).unwrap();
        assert_eq!("5108631", converter.encode(5108631));
        assert_eq!(5108631, converter.decode(&"5108631".to_string()).unwrap());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"51x8631".to_string()).unwrap_err());

        let tertiary_alphabet = ["zero", "oone", "twoo"];
        let converter = Converter::with_uniform_alphabet(&tertiary_alphabet).unwrap();
        assert_eq!("ooneoonetwoozero", converter.encode(42));
        assert_eq!(42, converter.decode(&"ooneoonetwoozero".to_string()).unwrap());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"ooneoometwoozero".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputLengthUnmatched, converter.decode(&"ooneoonetwoozer".to_string()).unwrap_err());

        let converter = Converter::with_delimiter(&binary_alphabet, '-').unwrap();
        assert_eq!("1-1-0-1", converter.encode(13));
        assert_eq!(13, converter.decode(&"1-1-0-1".to_string()).unwrap());
        assert_eq!(DecodeError::InputEmpty, converter.decode(&"".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"1-1-0-1-".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"-1-1-0-1".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"1--1-0-1".to_string()).unwrap_err());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"1-10-1".to_string()).unwrap_err());

        let binary_names_alphabet = ["zero", "one"];
        let converter = Converter::with_delimiter(&binary_names_alphabet, ' ').unwrap();
        assert_eq!("one zero one one", converter.encode(11));
        assert_eq!(11, converter.decode(&"one zero one one".to_string()).unwrap());
        assert_eq!(DecodeError::InputSymbolInvalid, converter.decode(&"one zer one one".to_string()).unwrap_err());
    }

    #[test]
    fn test_decode_overflow() {
        let hex_alphabet_mem: Vec<_> = "0123456789abcdef".chars().map(|x| x.to_string()).collect();
        let hex_alphabet: Vec<_> = hex_alphabet_mem.iter().map(|x| &x[..]).collect();
        let converter = Converter::with_uniform_alphabet(&hex_alphabet).unwrap();

        let ipv6addr: u128 = 0x20010db8000000420000cafffe001337;
        let ipv6addr_s = "20010db8000000420000cafffe001337".to_string();
        assert_eq!(ipv6addr_s, converter.encode(ipv6addr));
        assert_eq!(ipv6addr, converter.decode(&ipv6addr_s).unwrap());
        assert_eq!(DecodeError::InputOverflow, converter.decode(&(ipv6addr_s + "0")).unwrap_err());
    }
}
