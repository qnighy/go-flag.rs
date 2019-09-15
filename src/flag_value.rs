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

        for &s in &["0", "f", "F", "false", "FALSE", "False"] {
            assert_eq!(bool::parse(Some(OsStr::new(s)), None)?, false);
        }

        for &s in &["1", "t", "T", "true", "TRUE", "True"] {
            assert_eq!(bool::parse(Some(OsStr::new(s)), None)?, true);
        }

        for &s in &["", "00", "2", "fALSE", "tRUE", "no", "yes", "off", "on"] {
            assert!(bool::parse(Some(OsStr::new(s)), None).is_err());
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
        let mut warnings = Vec::new();
        assert_eq!(bool::parse(None, Some(&mut warnings))?, true);
        assert_eq!(warnings.len(), 0);

        for &s in &["false"] {
            warnings.clear();
            assert_eq!(bool::parse(Some(OsStr::new(s)), None)?, false);
            assert_eq!(warnings.len(), 0);
        }
        for &s in &["0", "f", "F", "FALSE", "False"] {
            warnings.clear();
            assert_eq!(
                bool::parse(Some(OsStr::new(s)), Some(&mut warnings))?,
                false
            );
            assert_eq!(warnings.len(), 1);
        }

        for &s in &["true"] {
            warnings.clear();
            assert_eq!(bool::parse(Some(OsStr::new(s)), Some(&mut warnings))?, true);
            assert_eq!(warnings.len(), 0);
        }
        for &s in &["1", "t", "T", "TRUE", "True"] {
            warnings.clear();
            assert_eq!(bool::parse(Some(OsStr::new(s)), Some(&mut warnings))?, true);
            assert_eq!(warnings.len(), 1);
        }

        Ok(())
    }

    #[test]
    fn test_parse_integer() {
        assert_eq!(i32::parse(Some(OsStr::new("0")), None).unwrap(), 0);
        assert_eq!(i32::parse(Some(OsStr::new("789")), None).unwrap(), 789);
        assert_eq!(i32::parse(Some(OsStr::new("+789")), None).unwrap(), 789);
        assert_eq!(i32::parse(Some(OsStr::new("-789")), None).unwrap(), -789);
        assert_eq!(
            i32::parse(Some(OsStr::new("12_345_6789")), None).unwrap(),
            123456789
        );
        assert_eq!(i32::parse(Some(OsStr::new("0xABc")), None).unwrap(), 0xABC);
        assert_eq!(i32::parse(Some(OsStr::new("+0xABc")), None).unwrap(), 0xABC);
        assert_eq!(
            i32::parse(Some(OsStr::new("-0xABc")), None).unwrap(),
            -0xABC
        );
        assert_eq!(
            i32::parse(Some(OsStr::new("-0x_ABC_DEF")), None).unwrap(),
            -0xABCDEF
        );
        assert_eq!(i32::parse(Some(OsStr::new("0XABc")), None).unwrap(), 0xABC);
        assert_eq!(i32::parse(Some(OsStr::new("+0XABc")), None).unwrap(), 0xABC);
        assert_eq!(
            i32::parse(Some(OsStr::new("-0XABc")), None).unwrap(),
            -0xABC
        );
        assert_eq!(i32::parse(Some(OsStr::new("0o567")), None).unwrap(), 0o567);
        assert_eq!(i32::parse(Some(OsStr::new("+0o567")), None).unwrap(), 0o567);
        assert_eq!(
            i32::parse(Some(OsStr::new("-0o567")), None).unwrap(),
            -0o567
        );
        assert_eq!(
            i32::parse(Some(OsStr::new("+0o12_345_67")), None).unwrap(),
            0o1234567
        );
        assert_eq!(i32::parse(Some(OsStr::new("0O567")), None).unwrap(), 0o567);
        assert_eq!(i32::parse(Some(OsStr::new("+0O567")), None).unwrap(), 0o567);
        assert_eq!(
            i32::parse(Some(OsStr::new("-0O567")), None).unwrap(),
            -0o567
        );
        assert_eq!(i32::parse(Some(OsStr::new("0b111")), None).unwrap(), 0b111);
        assert_eq!(i32::parse(Some(OsStr::new("+0b111")), None).unwrap(), 0b111);
        assert_eq!(
            i32::parse(Some(OsStr::new("-0b111")), None).unwrap(),
            -0b111
        );
        assert_eq!(i32::parse(Some(OsStr::new("0B111")), None).unwrap(), 0b111);
        assert_eq!(i32::parse(Some(OsStr::new("+0B111")), None).unwrap(), 0b111);
        assert_eq!(
            i32::parse(Some(OsStr::new("-0B111")), None).unwrap(),
            -0b111
        );
        assert_eq!(i32::parse(Some(OsStr::new("0x_ABC")), None).unwrap(), 0xABC);
        assert_eq!(i32::parse(Some(OsStr::new("0o_567")), None).unwrap(), 0o567);
        assert_eq!(i32::parse(Some(OsStr::new("0b_111")), None).unwrap(), 0b111);
        assert_eq!(i32::parse(Some(OsStr::new("0_567")), None).unwrap(), 0o567);
        assert_eq!(
            i32::parse(Some(OsStr::new("2147483647")), None).unwrap(),
            2147483647
        );
        assert_eq!(
            i32::parse(Some(OsStr::new("-2147483648")), None).unwrap(),
            -2147483648
        );
        assert_eq!(
            i32::parse(Some(OsStr::new("0x000000007FFFFFFF")), None).unwrap(),
            0x7FFFFFFF
        );
        assert_eq!(
            i32::parse(Some(OsStr::new("-0x0000000080000000")), None).unwrap(),
            -0x80000000
        );

        assert!(i32::parse(Some(OsStr::new("")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("+")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("--1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-+1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("+-1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("++1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("ABC")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-ABC")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0789")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-0789")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0o789")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-0o789")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0xGHI")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-0xGHI")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0b222")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-0b222")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0-111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0x-111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0b-111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0o-111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0+111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0x+111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0b+111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0o+111")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("_")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0_")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0x_")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("_1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("_01")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("1_")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0x1_")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("1__2")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0x1__2")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("0x__1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("2147483648")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("-2147483649")), None).is_err());

        #[cfg(any(unix, target_os = "redox"))]
        {
            use std::os::unix::ffi::OsStrExt;
            assert!(i32::parse(Some(OsStr::from_bytes(b"\xA0")), None).is_err());
        }
    }

    #[test]
    fn test_parse_integer_unsigned() {
        assert_eq!(u32::parse(Some(OsStr::new("0")), None).unwrap(), 0);
        assert_eq!(u32::parse(Some(OsStr::new("789")), None).unwrap(), 789);
        assert_eq!(
            u32::parse(Some(OsStr::new("12_345_6789")), None).unwrap(),
            123456789
        );
        assert_eq!(u32::parse(Some(OsStr::new("0xABc")), None).unwrap(), 0xABC);
        assert_eq!(u32::parse(Some(OsStr::new("0XABc")), None).unwrap(), 0xABC);
        assert_eq!(u32::parse(Some(OsStr::new("0o567")), None).unwrap(), 0o567);
        assert_eq!(u32::parse(Some(OsStr::new("0O567")), None).unwrap(), 0o567);
        assert_eq!(u32::parse(Some(OsStr::new("0b111")), None).unwrap(), 0b111);
        assert_eq!(u32::parse(Some(OsStr::new("0B111")), None).unwrap(), 0b111);
        assert_eq!(u32::parse(Some(OsStr::new("0x_ABC")), None).unwrap(), 0xABC);
        assert_eq!(u32::parse(Some(OsStr::new("0o_567")), None).unwrap(), 0o567);
        assert_eq!(u32::parse(Some(OsStr::new("0b_111")), None).unwrap(), 0b111);
        assert_eq!(u32::parse(Some(OsStr::new("0_567")), None).unwrap(), 0o567);
        assert_eq!(
            u32::parse(Some(OsStr::new("4294967295")), None).unwrap(),
            4294967295
        );
        assert_eq!(
            u32::parse(Some(OsStr::new("0x00000000FFFFFFFF")), None).unwrap(),
            0xFFFFFFFF
        );

        assert!(u32::parse(Some(OsStr::new("")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("--1")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-+1")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+-1")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("++1")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("ABC")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-ABC")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0789")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0789")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0o789")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0o789")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0xGHI")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0xGHI")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0b222")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0b222")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0-111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0x-111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0b-111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0o-111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0+111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0x+111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0b+111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0o+111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("_")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0_")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0x_")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("_1")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("_01")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("1_")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0x1_")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("1__2")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0x1__2")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("0x__1")), None).is_err());
        assert!(i32::parse(Some(OsStr::new("4294967296")), None).is_err());

        assert!(u32::parse(Some(OsStr::new("+789")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-789")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0xABc")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0xABc")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0x_ABC_DEF")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0XABc")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0XABc")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0o567")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0o567")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0o12_345_67")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0O567")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0O567")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0b111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0b111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("+0B111")), None).is_err());
        assert!(u32::parse(Some(OsStr::new("-0B111")), None).is_err());

        #[cfg(any(unix, target_os = "redox"))]
        {
            use std::os::unix::ffi::OsStrExt;
            assert!(u32::parse(Some(OsStr::from_bytes(b"\xA0")), None).is_err());
        }
    }
}
