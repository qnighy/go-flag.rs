use std::borrow::Cow;
use std::ffi::{OsStr, OsString};
use std::path::PathBuf;

use crate::error::{FlagParseError, FlagWarning};

pub trait FlagSetter {
    fn is_bool_flag(&self) -> bool;
    fn set(
        &mut self,
        value: Option<&OsStr>,
        warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError>;
}

impl<T: FlagValue> FlagSetter for T {
    fn is_bool_flag(&self) -> bool {
        T::is_bool_flag()
    }
    fn set(
        &mut self,
        value: Option<&OsStr>,
        warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError> {
        *self = T::parse(value, warnings)?;
        Ok(())
    }
}

pub trait FlagValue: Sized {
    fn is_bool_flag() -> bool {
        false
    }
    fn parse(
        value: Option<&OsStr>,
        warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<Self, FlagParseError>;
}

impl FlagValue for OsString {
    fn parse(
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<Self, FlagParseError> {
        Ok(value.unwrap().to_owned())
    }
}

impl FlagValue for PathBuf {
    fn parse(
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<Self, FlagParseError> {
        Ok(value.unwrap().to_owned().into())
    }
}

impl FlagValue for String {
    fn parse(
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<Self, FlagParseError> {
        let x = value
            .unwrap()
            .to_str()
            .ok_or_else(|| FlagParseError::StringParseError)?
            .to_owned();
        Ok(x)
    }
}

impl FlagValue for bool {
    fn is_bool_flag() -> bool {
        true
    }
    fn parse(
        value: Option<&OsStr>,
        warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<Self, FlagParseError> {
        let value = if let Some(value) = value {
            value
        } else {
            return Ok(true);
        };
        let value = value
            .to_str()
            .ok_or_else(|| FlagParseError::BoolParseError)?;
        Ok(match value {
            "true" => true,
            "false" => false,
            "1" | "t" | "T" | "TRUE" | "True" => {
                if let Some(warnings) = warnings {
                    warnings.push(FlagWarning::FlagValue {
                        value: value.to_owned(),
                    });
                }
                true
            }
            "0" | "f" | "F" | "FALSE" | "False" => {
                if let Some(warnings) = warnings {
                    warnings.push(FlagWarning::FlagValue {
                        value: value.to_owned(),
                    });
                }
                false
            }
            _ => return Err(FlagParseError::BoolParseError),
        })
    }
}

macro_rules! gen_int_impls {
    ($(($ty:ty, $allow_sign:expr),)*) => {
        $(
            impl FlagValue for $ty {
                fn parse(
                    value: Option<&OsStr>,
                    _warnings: Option<&mut Vec<FlagWarning>>,
                ) -> Result<Self, FlagParseError> {
                    let value = value
                        .unwrap()
                        .to_str()
                        .ok_or_else(|| FlagParseError::IntegerParseError)?;
                    let (value, radix) = cleanup_int(value, $allow_sign)?;
                    Self::from_str_radix(&value, radix)
                        .map_err(|_| FlagParseError::IntegerParseError)
                }
            }
        )*
    };
}
gen_int_impls!(
    (i8, true),
    (i16, true),
    (i32, true),
    (i64, true),
    (i128, true),
    (isize, true),
    (u8, false),
    (u16, false),
    (u32, false),
    (u64, false),
    (u128, false),
    (usize, false),
);

fn cleanup_int(s: &str, allow_sign: bool) -> Result<(Cow<'_, str>, u32), FlagParseError> {
    fn eat_radix(s: &str) -> (&str, u32) {
        if s.starts_with("0x") || s.starts_with("0X") {
            (&s[2..], 16)
        } else if s.starts_with("0o") || s.starts_with("0O") {
            (&s[2..], 8)
        } else if s.starts_with("0b") || s.starts_with("0B") {
            (&s[2..], 2)
        } else if s.starts_with("0") {
            (&s[1..], 8)
        } else {
            (s, 10)
        }
    }

    if !allow_sign && (s.starts_with("-") || s.starts_with("+")) {
        return Err(FlagParseError::IntegerParseError);
    }
    if s == "0" || s == "-0" || s == "+0" {
        return Ok((Cow::from(s), 10));
    }

    let has_underscore = s.contains('_');
    let has_radix_after_sign = s.starts_with("-0") || s.starts_with("+0");
    if !has_underscore && !has_radix_after_sign {
        let (s, radix) = eat_radix(s);
        if radix != 10 && (s.starts_with("-") || s.starts_with("+")) {
            return Err(FlagParseError::IntegerParseError);
        }
        return Ok((Cow::from(s), radix));
    }
    let mut ret = String::with_capacity(s.len());
    let s = if s.starts_with("-") {
        ret.push_str("-");
        &s[1..]
    } else if s.starts_with("+") {
        ret.push_str("+");
        &s[1..]
    } else {
        s
    };
    let (mut s, radix) = eat_radix(s);
    if radix != 10 && (s.starts_with("-") || s.starts_with("+")) {
        return Err(FlagParseError::IntegerParseError);
    }
    if radix != 10 && s.starts_with("_") {
        s = &s[1..];
    }
    while let Some(i) = s.find('_') {
        if i == 0 {
            return Err(FlagParseError::IntegerParseError);
        }
        ret.push_str(&s[..i]);
        s = &s[i + 1..];
    }
    if s.is_empty() {
        return Err(FlagParseError::IntegerParseError);
    }
    ret.push_str(s);
    Ok((Cow::from(ret), radix))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_bool() -> Result<(), FlagParseError> {
        assert_eq!(<bool as FlagValue>::is_bool_flag(), true);

        assert_eq!(bool::parse(None, None)?, true);

        let parse = |s: &str| bool::parse(Some(OsStr::new(s)), None);

        for &s in &["0", "f", "F", "false", "FALSE", "False"] {
            assert_eq!(parse(s).unwrap(), false);
        }

        for &s in &["1", "t", "T", "true", "TRUE", "True"] {
            assert_eq!(parse(s).unwrap(), true);
        }

        for &s in &["", "00", "2", "fALSE", "tRUE", "no", "yes", "off", "on"] {
            assert!(parse(s).is_err());
        }

        #[cfg(any(unix, target_os = "redox"))]
        for &s in &[b"true\xA0" as &[u8], b"\xE3"] {
            use std::os::unix::ffi::OsStrExt;

            assert!(bool::parse(Some(OsStr::from_bytes(s)), None).is_err());
        }

        Ok(())
    }

    #[test]
    fn test_parse_bool_warnings() -> Result<(), FlagParseError> {
        let parse = || {
            let mut warnings = Vec::new();
            let parsed = bool::parse(None, Some(&mut warnings)).unwrap();
            (parsed, warnings.len())
        };
        assert_eq!(parse(), (true, 0));

        let parse = |s: &str| {
            let mut warnings = Vec::new();
            let parsed = bool::parse(Some(OsStr::new(s)), Some(&mut warnings)).unwrap();
            (parsed, warnings.len())
        };

        for &s in &["false"] {
            assert_eq!(parse(s), (false, 0));
        }
        for &s in &["0", "f", "F", "FALSE", "False"] {
            assert_eq!(parse(s), (false, 1));
        }

        for &s in &["true"] {
            assert_eq!(parse(s), (true, 0));
        }
        for &s in &["1", "t", "T", "TRUE", "True"] {
            assert_eq!(parse(s), (true, 1));
        }

        Ok(())
    }

    #[test]
    fn test_parse_integer() {
        let parse = |s: &str| i32::parse(Some(OsStr::new(s)), None);

        assert_eq!(parse("0").unwrap(), 0);
        assert_eq!(parse("789").unwrap(), 789);
        assert_eq!(parse("+789").unwrap(), 789);
        assert_eq!(parse("-789").unwrap(), -789);
        assert_eq!(parse("12_345_6789").unwrap(), 123456789);
        assert_eq!(parse("0xABc").unwrap(), 0xABC);
        assert_eq!(parse("+0xABc").unwrap(), 0xABC);
        assert_eq!(parse("-0xABc").unwrap(), -0xABC);
        assert_eq!(parse("-0x_ABC_DEF").unwrap(), -0xABCDEF);
        assert_eq!(parse("0XABc").unwrap(), 0xABC);
        assert_eq!(parse("+0XABc").unwrap(), 0xABC);
        assert_eq!(parse("-0XABc").unwrap(), -0xABC);
        assert_eq!(parse("0o567").unwrap(), 0o567);
        assert_eq!(parse("+0o567").unwrap(), 0o567);
        assert_eq!(parse("-0o567").unwrap(), -0o567);
        assert_eq!(parse("+0o12_345_67").unwrap(), 0o1234567);
        assert_eq!(parse("0O567").unwrap(), 0o567);
        assert_eq!(parse("+0O567").unwrap(), 0o567);
        assert_eq!(parse("-0O567").unwrap(), -0o567);
        assert_eq!(parse("0b111").unwrap(), 0b111);
        assert_eq!(parse("+0b111").unwrap(), 0b111);
        assert_eq!(parse("-0b111").unwrap(), -0b111);
        assert_eq!(parse("0B111").unwrap(), 0b111);
        assert_eq!(parse("+0B111").unwrap(), 0b111);
        assert_eq!(parse("-0B111").unwrap(), -0b111);
        assert_eq!(parse("0x_ABC").unwrap(), 0xABC);
        assert_eq!(parse("0o_567").unwrap(), 0o567);
        assert_eq!(parse("0b_111").unwrap(), 0b111);
        assert_eq!(parse("0_567").unwrap(), 0o567);
        assert_eq!(parse("2147483647").unwrap(), 2147483647);
        assert_eq!(parse("-2147483648").unwrap(), -2147483648);
        assert_eq!(parse("0x000000007FFFFFFF").unwrap(), 0x7FFFFFFF);
        assert_eq!(parse("-0x0000000080000000").unwrap(), -0x80000000);

        assert!(parse("").is_err());
        assert!(parse("-").is_err());
        assert!(parse("+").is_err());
        assert!(parse("--1").is_err());
        assert!(parse("-+1").is_err());
        assert!(parse("+-1").is_err());
        assert!(parse("++1").is_err());
        assert!(parse("ABC").is_err());
        assert!(parse("-ABC").is_err());
        assert!(parse("0789").is_err());
        assert!(parse("-0789").is_err());
        assert!(parse("0o789").is_err());
        assert!(parse("-0o789").is_err());
        assert!(parse("0xGHI").is_err());
        assert!(parse("-0xGHI").is_err());
        assert!(parse("0b222").is_err());
        assert!(parse("-0b222").is_err());
        assert!(parse("0-111").is_err());
        assert!(parse("0x-111").is_err());
        assert!(parse("0b-111").is_err());
        assert!(parse("0o-111").is_err());
        assert!(parse("0+111").is_err());
        assert!(parse("0x+111").is_err());
        assert!(parse("0b+111").is_err());
        assert!(parse("0o+111").is_err());
        assert!(parse("_").is_err());
        assert!(parse("0_").is_err());
        assert!(parse("0x_").is_err());
        assert!(parse("_1").is_err());
        assert!(parse("_01").is_err());
        assert!(parse("1_").is_err());
        assert!(parse("0x1_").is_err());
        assert!(parse("1__2").is_err());
        assert!(parse("0x1__2").is_err());
        assert!(parse("0x__1").is_err());
        assert!(parse("2147483648").is_err());
        assert!(parse("-2147483649").is_err());

        #[cfg(any(unix, target_os = "redox"))]
        {
            use std::os::unix::ffi::OsStrExt;
            let parse = |s: &[u8]| i32::parse(Some(OsStr::from_bytes(s)), None);
            assert!(parse(b"\xA0").is_err());
        }
    }

    #[test]
    fn test_parse_integer_unsigned() {
        let parse = |s: &str| u32::parse(Some(OsStr::new(s)), None);

        assert_eq!(parse("0").unwrap(), 0);
        assert_eq!(parse("789").unwrap(), 789);
        assert_eq!(parse("12_345_6789").unwrap(), 123456789);
        assert_eq!(parse("0xABc").unwrap(), 0xABC);
        assert_eq!(parse("0XABc").unwrap(), 0xABC);
        assert_eq!(parse("0o567").unwrap(), 0o567);
        assert_eq!(parse("0O567").unwrap(), 0o567);
        assert_eq!(parse("0b111").unwrap(), 0b111);
        assert_eq!(parse("0B111").unwrap(), 0b111);
        assert_eq!(parse("0x_ABC").unwrap(), 0xABC);
        assert_eq!(parse("0o_567").unwrap(), 0o567);
        assert_eq!(parse("0b_111").unwrap(), 0b111);
        assert_eq!(parse("0_567").unwrap(), 0o567);
        assert_eq!(parse("4294967295").unwrap(), 4294967295);
        assert_eq!(parse("0x00000000FFFFFFFF").unwrap(), 0xFFFFFFFF);

        assert!(parse("").is_err());
        assert!(parse("-").is_err());
        assert!(parse("+").is_err());
        assert!(parse("--1").is_err());
        assert!(parse("-+1").is_err());
        assert!(parse("+-1").is_err());
        assert!(parse("++1").is_err());
        assert!(parse("ABC").is_err());
        assert!(parse("-ABC").is_err());
        assert!(parse("0789").is_err());
        assert!(parse("-0789").is_err());
        assert!(parse("0o789").is_err());
        assert!(parse("-0o789").is_err());
        assert!(parse("0xGHI").is_err());
        assert!(parse("-0xGHI").is_err());
        assert!(parse("0b222").is_err());
        assert!(parse("-0b222").is_err());
        assert!(parse("0-111").is_err());
        assert!(parse("0x-111").is_err());
        assert!(parse("0b-111").is_err());
        assert!(parse("0o-111").is_err());
        assert!(parse("0+111").is_err());
        assert!(parse("0x+111").is_err());
        assert!(parse("0b+111").is_err());
        assert!(parse("0o+111").is_err());
        assert!(parse("_").is_err());
        assert!(parse("0_").is_err());
        assert!(parse("0x_").is_err());
        assert!(parse("_1").is_err());
        assert!(parse("_01").is_err());
        assert!(parse("1_").is_err());
        assert!(parse("0x1_").is_err());
        assert!(parse("1__2").is_err());
        assert!(parse("0x1__2").is_err());
        assert!(parse("0x__1").is_err());
        assert!(parse("4294967296").is_err());

        assert!(parse("+789").is_err());
        assert!(parse("-789").is_err());
        assert!(parse("+0xABc").is_err());
        assert!(parse("-0xABc").is_err());
        assert!(parse("-0x_ABC_DEF").is_err());
        assert!(parse("+0XABc").is_err());
        assert!(parse("-0XABc").is_err());
        assert!(parse("+0o567").is_err());
        assert!(parse("-0o567").is_err());
        assert!(parse("+0o12_345_67").is_err());
        assert!(parse("+0O567").is_err());
        assert!(parse("-0O567").is_err());
        assert!(parse("+0b111").is_err());
        assert!(parse("-0b111").is_err());
        assert!(parse("+0B111").is_err());
        assert!(parse("-0B111").is_err());

        #[cfg(any(unix, target_os = "redox"))]
        {
            use std::os::unix::ffi::OsStrExt;
            let parse = |s: &[u8]| u32::parse(Some(OsStr::from_bytes(s)), None);
            assert!(parse(b"\xA0").is_err());
        }
    }
}
