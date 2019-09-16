use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt;

pub use error::{FlagError, FlagParseError, FlagWarning};
pub use flag_value::{FlagSetter, FlagValue};
use unit_parsing::{parse_one, FlagResult};

mod error;
mod flag_value;
mod unit_parsing;

#[derive(Debug)]
pub struct FlagSet<'a> {
    flag_specs: HashMap<&'a str, FlagSpec<'a>>,
}

impl<'a> FlagSet<'a> {
    pub fn new() -> Self {
        Self {
            flag_specs: HashMap::new(),
        }
    }

    pub fn add_flag(&mut self, name: &'a str, value: &'a mut dyn FlagSetter) {
        let value = FlagSpec { r: value };
        let old = self.flag_specs.insert(name, value);
        if old.is_some() {
            panic!("multiple flags with same name: {}", name);
        }
    }

    pub fn parse<'b, T: FlagValue, S: AsRef<OsStr>>(
        &mut self,
        args: &'b [S],
    ) -> Result<Vec<T>, FlagError> {
        self.parse_with_warnings(args, None)
    }

    pub fn parse_with_warnings<'b, T: FlagValue, S: AsRef<OsStr>>(
        &mut self,
        mut args: &'b [S],
        mut warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<Vec<T>, FlagError> {
        loop {
            let seen = self.process_one(&mut args, reborrow_option_mut(&mut warnings))?;
            if !seen {
                break;
            }
        }
        let args = args
            .iter()
            .map(|x| {
                T::parse(Some(x.as_ref()), reborrow_option_mut(&mut warnings))
                    .map_err(|error| FlagError::ParseError { error })
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(args)
    }

    fn process_one<S: AsRef<OsStr>>(
        &mut self,
        args: &mut &[S],
        mut warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<bool, FlagError> {
        if args.is_empty() {
            return Ok(false);
        }
        let arg0: &OsStr = args[0].as_ref();
        let (num_minuses, name, value) = match parse_one(arg0) {
            FlagResult::Argument => return Ok(false),
            FlagResult::EndFlags => {
                *args = &args[1..];
                return Ok(false);
            }
            FlagResult::BadFlag => {
                return Err(FlagError::BadFlag {
                    flag: arg0.to_string_lossy().into_owned(),
                })
            }
            FlagResult::Flag {
                num_minuses,
                name,
                value,
            } => (num_minuses, name, value),
        };
        *args = &args[1..];
        if let Some(warnings) = reborrow_option_mut(&mut warnings) {
            if name.len() > 1 && num_minuses == 1 {
                warnings.push(FlagWarning::ShortLong {
                    flag: arg0.to_string_lossy().into_owned(),
                });
            }
            if name.len() == 1 && num_minuses == 2 {
                warnings.push(FlagWarning::LongShort {
                    flag: arg0.to_string_lossy().into_owned(),
                });
            }
        }
        let name = name.to_str().ok_or_else(|| FlagError::UnknownFlag {
            name: name.to_string_lossy().into_owned(),
        })?;
        let flag_spec = if let Some(flag_spec) = self.flag_specs.get_mut(name) {
            flag_spec
        } else {
            return Err(FlagError::UnknownFlag {
                name: name.to_owned(),
            });
        };
        let value = if !flag_spec.r.is_bool_flag() && value.is_none() {
            if args.is_empty() {
                return Err(FlagError::ArgumentNeeded {
                    name: name.to_owned(),
                });
            }
            let arg1 = args[0].as_ref();
            *args = &args[1..];
            Some(arg1)
        } else {
            value.as_ref().map(|x| x.as_ref())
        };
        flag_spec
            .r
            .set(value, reborrow_option_mut(&mut warnings))
            .map_err(|error| FlagError::ParseError { error })?;
        Ok(true)
    }
}

fn reborrow_option_mut<'a, T>(x: &'a mut Option<&mut T>) -> Option<&'a mut T> {
    if let Some(x) = x {
        Some(x)
    } else {
        None
    }
}

struct FlagSpec<'a> {
    r: &'a mut dyn FlagSetter,
}

impl<'a> fmt::Debug for FlagSpec<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct FlagSetterPlaceholder<'a>(&'a dyn FlagSetter);
        impl<'a> fmt::Debug for FlagSetterPlaceholder<'a> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "<mutable reference {:p}>", self.0)
            }
        }

        f.debug_struct("FlagSpec")
            .field("r", &FlagSetterPlaceholder(self.r))
            .finish()
    }
}

pub fn parse_args<'a, T, S: AsRef<OsStr>, F>(args: &[S], f: F) -> Result<Vec<T>, FlagError>
where
    T: FlagValue,
    F: FnOnce(&mut FlagSet<'a>),
{
    parse_args_with_warnings(args, None, f)
}

pub fn parse_args_with_warnings<'a, T, S: AsRef<OsStr>, F>(
    args: &[S],
    mut warnings: Option<&mut Vec<FlagWarning>>,
    f: F,
) -> Result<Vec<T>, FlagError>
where
    T: FlagValue,
    F: FnOnce(&mut FlagSet<'a>),
{
    let mut flag_set = FlagSet::new();
    f(&mut flag_set);
    let remain = flag_set.parse_with_warnings(args, reborrow_option_mut(&mut warnings))?;
    Ok(remain)
}

pub fn parse<'a, T, F>(f: F) -> Vec<T>
where
    T: FlagValue,
    F: FnOnce(&mut FlagSet<'a>),
{
    parse_with_warnings(WarningMode::Report, f)
}

pub fn parse_with_warnings<'a, T, F>(mode: WarningMode, f: F) -> Vec<T>
where
    T: FlagValue,
    F: FnOnce(&mut FlagSet<'a>),
{
    let mut warnings = if mode == WarningMode::Ignore {
        None
    } else {
        Some(Vec::new())
    };
    let args = std::env::args_os().collect::<Vec<_>>();
    match parse_args_with_warnings(&args[1..], warnings.as_mut(), f) {
        Ok(x) => {
            if let Some(warnings) = &warnings {
                for w in warnings {
                    eprintln!("{}", w);
                }
                if !warnings.is_empty() && mode == WarningMode::Error {
                    std::process::exit(1);
                }
            }
            x
        }
        Err(e) => {
            eprintln!("{}", e);
            std::process::exit(1);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum WarningMode {
    Ignore,
    Report,
    Error,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_args() {
        let parse = |args: &[&str]| -> Result<(bool, i32, Vec<String>), FlagError> {
            let mut force = false;
            let mut lines = 10_i32;
            let args = parse_args(args, |flags| {
                flags.add_flag("f", &mut force);
                flags.add_flag("lines", &mut lines);
            })?;
            Ok((force, lines, args))
        };
        assert_eq!(parse(&[]).unwrap(), (false, 10, vec![]));
        assert_eq!(parse(&["-f"]).unwrap(), (true, 10, vec![]));
        assert_eq!(parse(&["-f", "--lines=20"]).unwrap(), (true, 20, vec![]));
    }
}
