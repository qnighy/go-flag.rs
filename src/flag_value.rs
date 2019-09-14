use std::ffi::{OsStr, OsString};
use std::path::PathBuf;

use crate::error::{FlagParseError, FlagWarning};

pub trait FlagValue {
    fn is_bool_flag(&self) -> bool {
        false
    }
    fn set(
        &mut self,
        value: Option<&OsStr>,
        warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError>;
}

impl FlagValue for OsString {
    fn set(
        &mut self,
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError> {
        *self = value.unwrap().to_owned();
        Ok(())
    }
}

impl FlagValue for PathBuf {
    fn set(
        &mut self,
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError> {
        *self = value.unwrap().to_owned().into();
        Ok(())
    }
}

impl FlagValue for String {
    fn set(
        &mut self,
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError> {
        *self = value
            .unwrap()
            .to_str()
            .ok_or_else(|| FlagParseError::StringParseError)?
            .to_owned();
        Ok(())
    }
}

impl FlagValue for bool {
    fn is_bool_flag(&self) -> bool {
        true
    }
    fn set(
        &mut self,
        value: Option<&OsStr>,
        _warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<(), FlagParseError> {
        let value = if let Some(value) = value {
            value
        } else {
            *self = true;
            return Ok(());
        };
        let value = value
            .to_str()
            .ok_or_else(|| FlagParseError::BoolParseError)?;
        *self = match value {
            "1" | "t" | "T" | "true" | "TRUE" | "True" => true,
            "0" | "f" | "F" | "false" | "FALSE" | "False" => false,
            _ => return Err(FlagParseError::BoolParseError),
        };
        Ok(())
    }
}
