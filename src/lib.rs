pub enum ConverterError {
    AlphabetTooSmall,
    SymbolsNotUnique,
    DelimiterOverlapping,
}

pub struct Converter {
    alphabet: Vec<String>,
    delimiter: char,
}

impl Converter {
    pub fn new(alphabet: Vec<String>, delimiter: char) -> Result<Self, ConverterError> {
        if alphabet.len() < 2 {
            return Err(ConverterError::AlphabetTooSmall);
        }

        for i in 1..alphabet.len() {
            if alphabet[i..].contains(&alphabet[i - 1]) {
                return Err(ConverterError::SymbolsNotUnique);
            }
        }

        for symbol in &alphabet {
            if symbol.contains(delimiter) {
                return Err(ConverterError::DelimiterOverlapping);
            }
        }

        Ok(Self { alphabet, delimiter })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_returns_ok() {
        let binary_alphabet = vec!(String::from("0"), String::from("1"));
        let result = Converter::new(binary_alphabet, '-');
        assert!(result.is_ok());
    }

    #[test]
    fn test_new_returns_err() {
        let empty_alphabet = vec!();
        let result = Converter::new(empty_alphabet, '-');
        assert!(match result {
            Err(ConverterError::AlphabetTooSmall) => true,
            _ => false
        });

        let singleton_alphabet = vec!(String::from("a"));
        let result = Converter::new(singleton_alphabet, '-');
        assert!(match result {
            Err(ConverterError::AlphabetTooSmall) => true,
            _ => false
        });

        let monotone_alphabet = vec!(String::from("x"), String::from("x"));
        let result = Converter::new(monotone_alphabet, '-');
        assert!(match result {
            Err(ConverterError::SymbolsNotUnique) => true,
            _ => false
        });

        let binary_alphabet = vec!(String::from("abc"), String::from("def"));
        let result = Converter::new(binary_alphabet, 'b');
        assert!(match result {
            Err(ConverterError::DelimiterOverlapping) => true,
            _ => false
        });
    }
}
