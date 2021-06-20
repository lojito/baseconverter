use colored::Colorize;
use std::collections::HashMap;
use std::convert::TryInto;

use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub struct BCError {
    details: String,
}

impl BCError {
    fn new(msg: &str) -> BCError {
        BCError {
            details: msg.to_string(),
        }
    }
}

impl fmt::Display for BCError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl Error for BCError {
    fn description(&self) -> &str {
        &self.details
    }
}

pub struct Config<'a> {
    pub number: &'a str,
    pub bf: &'a str,
    pub bt: &'a str,
}

impl<'a> Config<'a> {
    pub fn new(args: &[String]) -> Result<Config, BCError> {
        if args.len() < 4 {
            return Err(BCError::new("not enough arguments."));
        }

        let number = &args[1];
        let bf = &args[2];
        let bt = &args[3];

        Config::parse(&bf, &bt)?;

        Ok(Config { number, bf, bt })
    }

    fn parse(bf: &String, bt: &String) -> Result<(), BCError> {
        if (bf != Bin::BASE_IN && bf != Dec::BASE_IN && bf != Hex::BASE_IN && bf != Oct::BASE_IN)
            || (bt != Bin::BASE_IN
                && bt != Dec::BASE_IN
                && bt != Hex::BASE_IN
                && bt != Oct::BASE_IN)
        {
            return Err(BCError::new(&format!("enter {} for {} or {} for {} or {} for {} or {} for {} for the bases you are converting the number from and to.", Bin::BASE_IN, Bin::BASE_OUT, Dec::BASE_IN, Dec::BASE_OUT, Hex::BASE_IN, Hex::BASE_OUT, Oct::BASE_IN, Oct::BASE_OUT)));
        }

        if bf == bt {
            return Err(BCError::new(
                "the bases you are converting the number from and to must be different.",
            ));
        }

        Ok(())
    }
}

trait Base {
    const BASE_IN: &'static str;
    const BASE_OUT: &'static str;

    fn validate(number: &str) -> Result<(), BCError> {
        for c in number.to_uppercase().chars() {
            if !(Self::is_valid(c)) {
                return Err(BCError::new(Self::get_validation_msg()));
            }
        }

        Ok(())
    }

    fn is_valid(c: char) -> bool;

    fn get_validation_msg() -> &'static str;
}

#[derive(Debug, PartialEq)]
struct Bin(String);

impl Base for Bin {
    const BASE_IN: &'static str = "bin";
    const BASE_OUT: &'static str = "2(binary)";

    fn is_valid(c: char) -> bool {
        c == '0' || c == '1'
    }

    fn get_validation_msg() -> &'static str {
        "for base(bin) enter the digits 0 or 1."
    }
}

impl Bin {
    fn new(number: &str) -> Result<Self, BCError> {
        Self::validate(number)?;

        Ok(Self(number.to_string()))
    }
}

#[derive(Debug, PartialEq)]
struct Dec(String);

impl Base for Dec {
    const BASE_IN: &'static str = "dec";
    const BASE_OUT: &'static str = "10(decimal)";

    fn is_valid(c: char) -> bool {
        "0123456789-".contains(c)
    }

    fn get_validation_msg() -> &'static str {
        "for base(dec) enter digits in the range of 0 to 9."
    }
}

impl Dec {
    fn new(number: &str) -> Result<Self, BCError> {
        Self::validate(number)?;

        if let Err(_) = number.parse::<i32>() {
            return Err(BCError::new("decimal literal is too large."));
        };

        Ok(Self(number.to_string()))
    }
}

#[derive(Debug, PartialEq)]
struct Hex(String);

impl Base for Hex {
    const BASE_IN: &'static str = "hex";
    const BASE_OUT: &'static str = "16(hexadecimal)";

    fn is_valid(c: char) -> bool {
        "0123456789ABCDEF".contains(c)
    }

    fn get_validation_msg() -> &'static str {
        "for base(hex) enter digits in the range of 0 to 9 and a to f."
    }
}

impl Hex {
    fn new(number: &str) -> Result<Self, BCError> {
        Self::validate(number)?;

        Ok(Self(number.to_string()))
    }
}

#[derive(Debug, PartialEq)]
struct Oct(String);

impl Base for Oct {
    const BASE_IN: &'static str = "oct";
    const BASE_OUT: &'static str = "8(octal)";

    fn is_valid(c: char) -> bool {
        "01234567".contains(c)
    }

    fn get_validation_msg() -> &'static str {
        "for base(oct) enter digits in the range of 0 to 7."
    }
}

impl Oct {
    fn new(number: &str) -> Result<Self, BCError> {
        Self::validate(number)?;

        Ok(Self(number.to_string()))
    }
}

struct Bc {
    table: HashMap<char, u32>,
}

impl Bc {
    const DIGITS: &'static str = "0123456789ABCDEF";

    fn new() -> Self {
        let mut table = HashMap::new();

        for (i, c) in Self::DIGITS.chars().enumerate() {
            table.insert(c, i as u32);
        }
        Self { table }
    }

    fn to_decimal(&self, number: &String, base: u32, base_str: &str) -> Result<u32, BCError> {
        let mut dec: u32 = 0;

        for (i, c) in number.to_ascii_uppercase().chars().rev().enumerate() {
            let mut temp = u32::checked_pow(base, i.try_into().unwrap());
            if temp.is_none() {
                return Err(BCError::new(&format!("{} literal is too large.", base_str)));
            }
            temp = u32::checked_mul(*self.table.get(&c).unwrap(), temp.unwrap());
            if temp.is_none() {
                return Err(BCError::new(&format!("{} literal is too large.", base_str)));
            }
            dec += temp.unwrap();
            if dec > std::i32::MAX as u32 {
                return Err(BCError::new(&format!("{} literal is too large.", base_str)));
            }
        }
        Ok(dec)
    }
}

trait FromDec<B: Base> {
    fn from_dec(&self, d: &Dec) -> B;
}

impl FromDec<Bin> for Bc {
    fn from_dec(&self, d: &Dec) -> Bin {
        let n = d.0.parse::<i32>().unwrap();
        if n < 0 {
            Bin(format!("-{:b}", -n))
        } else {
            Bin(format!("{:b}", n))
        }
    }
}

impl FromDec<Dec> for Bc {
    fn from_dec(&self, d: &Dec) -> Dec {
        Dec(d.0.clone())
    }
}

impl FromDec<Hex> for Bc {
    fn from_dec(&self, d: &Dec) -> Hex {
        let n = d.0.parse::<i32>().unwrap();
        if n < 0 {
            Hex(format!("-{:x}", -n))
        } else {
            Hex(format!("{:x}", n))
        }
    }
}

impl FromDec<Oct> for Bc {
    fn from_dec(&self, d: &Dec) -> Oct {
        let n = d.0.parse::<i32>().unwrap();
        if n < 0 {
            Oct(format!("-{:o}", -n))
        } else {
            Oct(format!("{:o}", n))
        }
    }
}

trait ToDec<B: Base> {
    fn to_dec(&self, b: &B) -> Result<Dec, BCError>;
}

impl ToDec<Bin> for Bc {
    fn to_dec(&self, b: &Bin) -> Result<Dec, BCError> {
        let dec: u32 = self.to_decimal(&b.0, 2, "binary")?;
        Ok(Dec(dec.to_string()))
    }
}

impl ToDec<Dec> for Bc {
    fn to_dec(&self, d: &Dec) -> Result<Dec, BCError> {
        Ok(Dec(d.0.clone()))
    }
}

impl ToDec<Hex> for Bc {
    fn to_dec(&self, h: &Hex) -> Result<Dec, BCError> {
        let dec: u32 = self.to_decimal(&h.0, 16, "hexadecimal")?;
        Ok(Dec(dec.to_string()))
    }
}

impl ToDec<Oct> for Bc {
    fn to_dec(&self, o: &Oct) -> Result<Dec, BCError> {
        let dec: u32 = self.to_decimal(&o.0, 8, "octal")?;
        Ok(Dec(dec.to_string()))
    }
}

trait BaseConverter<F, T> {
    fn convert(&self, f: &F) -> Result<T, BCError>;
}

impl<B, F, T> BaseConverter<F, T> for B
where
    B: ToDec<F> + FromDec<T>,
    F: Base,
    T: Base,
{
    fn convert(&self, f: &F) -> Result<T, BCError> {
        Ok(self.from_dec(&self.to_dec(f)?))
    }
}

fn convert_from_base<F: Base>(f: &F, bt: &str) -> Result<(&'static str, String), BCError>
where
    Bc: ToDec<F>,
{
    let bc = Bc::new();

    match bt {
        Bin::BASE_IN => {
            let b: Bin = bc.convert(&f)?;
            Ok((Bin::BASE_OUT, b.0))
        }

        Dec::BASE_IN => {
            let d: Dec = bc.convert(&f)?;
            Ok((Dec::BASE_OUT, d.0))
        }

        Hex::BASE_IN => {
            let h: Hex = bc.convert(&f)?;
            Ok((Hex::BASE_OUT, h.0))
        }

        Oct::BASE_IN => {
            let o: Oct = bc.convert(&f)?;
            Ok((Oct::BASE_OUT, o.0))
        }

        _ => Err(BCError::new(&format!("enter {} for {} or {} for {} or {} for {} or {} for {} for the bases you are converting the number from and to.", Bin::BASE_IN, Bin::BASE_OUT, Dec::BASE_IN, Dec::BASE_OUT, Hex::BASE_IN, Hex::BASE_OUT, Oct::BASE_IN, Oct::BASE_OUT)))
    }
}

pub fn run(config: Config) -> Result<(), BCError> {
    let Config { number, bf, bt } = config;
    let mut result = ("", "".to_string());

    match bf {
        Bin::BASE_IN => {
            let b = Bin::new(&number)?;
            result = convert_from_base(&b, bt)?;
        }

        Dec::BASE_IN => {
            let d = Dec::new(&number)?;
            result = convert_from_base(&d, bt)?;
        }

        Hex::BASE_IN => {
            let h = Hex::new(&number)?;
            result = convert_from_base(&h, bt)?;
        }

        Oct::BASE_IN => {
            let o = Oct::new(&number)?;
            result = convert_from_base(&o, bt)?;
        }

        _ => (),
    }

    println!(
        "{}",
        format!(
            "\nThe number {} in base {} converted to base {} is {}.\n",
            number, bf, result.0, result.1
        )
        .green()
    );

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convert_bin_dec() {
        let bc = Bc::new();
        let config = Config {
            number: "11111111",
            bf: "bin",
            bt: "dec",
        };
        let b = Bin(config.number.to_string());
        let d: Dec = bc.convert(&b).unwrap();
        assert_eq!(d, Dec("255".to_string()));
    }

    #[test]
    fn convert_bin_hex() {
        let bc = Bc::new();
        let config = Config {
            number: "11111111",
            bf: "bin",
            bt: "hex",
        };
        let b = Bin(config.number.to_string());
        let h: Hex = bc.convert(&b).unwrap();
        assert_eq!(h, Hex("ff".to_string()));
    }

    #[test]
    fn convert_bin_oct() {
        let bc = Bc::new();
        let config = Config {
            number: "11111111",
            bf: "bin",
            bt: "oct",
        };
        let b = Bin(config.number.to_string());
        let o: Oct = bc.convert(&b).unwrap();
        assert_eq!(o, Oct("377".to_string()));
    }

    #[test]
    fn convert_dec_bin() {
        let bc = Bc::new();
        let config = Config {
            number: "255",
            bf: "dec",
            bt: "bin",
        };
        let d = Dec(config.number.to_string());
        let b: Bin = bc.convert(&d).unwrap();
        assert_eq!(b, Bin("11111111".to_string()));
    }

    #[test]
    fn convert_dec_hex() {
        let bc = Bc::new();
        let config = Config {
            number: "255",
            bf: "dec",
            bt: "hex",
        };
        let d = Dec(config.number.to_string());
        let h: Hex = bc.convert(&d).unwrap();
        assert_eq!(h, Hex("ff".to_string()));
    }

    #[test]
    fn convert_dec_oct() {
        let bc = Bc::new();
        let config = Config {
            number: "255",
            bf: "dec",
            bt: "oct",
        };
        let d = Dec(config.number.to_string());
        let o: Oct = bc.convert(&d).unwrap();
        assert_eq!(o, Oct("377".to_string()));
    }

    #[test]
    fn convert_hex_bin() {
        let bc = Bc::new();
        let config = Config {
            number: "ff",
            bf: "hex",
            bt: "bin",
        };
        let h = Hex(config.number.to_string());
        let b: Bin = bc.convert(&h).unwrap();
        assert_eq!(b, Bin("11111111".to_string()));
    }

    #[test]
    fn convert_hex_dec() {
        let bc = Bc::new();
        let config = Config {
            number: "ff",
            bf: "hex",
            bt: "dec",
        };
        let h = Hex(config.number.to_string());
        let d: Dec = bc.convert(&h).unwrap();
        assert_eq!(d, Dec("255".to_string()));
    }

    #[test]
    fn convert_hex_oct() {
        let bc = Bc::new();
        let config = Config {
            number: "ff",
            bf: "hex",
            bt: "oct",
        };
        let h = Hex(config.number.to_string());
        let o: Oct = bc.convert(&h).unwrap();
        assert_eq!(o, Oct("377".to_string()));
    }

    #[test]
    fn convert_oct_bin() {
        let bc = Bc::new();
        let config = Config {
            number: "377",
            bf: "oct",
            bt: "bin",
        };
        let o = Oct(config.number.to_string());
        let b: Bin = bc.convert(&o).unwrap();
        assert_eq!(b, Bin("11111111".to_string()));
    }

    #[test]
    fn convert_oct_dec() {
        let bc = Bc::new();
        let config = Config {
            number: "377",
            bf: "oct",
            bt: "dec",
        };
        let o = Oct(config.number.to_string());
        let d: Dec = bc.convert(&o).unwrap();
        assert_eq!(d, Dec("255".to_string()));
    }

    #[test]
    fn convert_oct_hex() {
        let bc = Bc::new();
        let config = Config {
            number: "377",
            bf: "oct",
            bt: "hex",
        };
        let o = Oct(config.number.to_string());
        let h: Hex = bc.convert(&o).unwrap();
        assert_eq!(h, Hex("ff".to_string()));
    }

    #[test]
    fn validate_err() {
        assert!(Config::parse(&String::from("unknown_base"), &String::from("bin")).is_err());
    }

    #[test]
    fn validate_ok() {
        assert!(Config::parse(&String::from("hex"), &String::from("bin")).is_ok());
    }
}
