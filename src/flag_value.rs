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
        _warnings: Option<&mut Vec<FlagWarning>>,
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
            "1" | "t" | "T" | "true" | "TRUE" | "True" => true,
            "0" | "f" | "F" | "false" | "FALSE" | "False" => false,
            _ => return Err(FlagParseError::BoolParseError),
        })
    }
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
}
