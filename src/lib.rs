use cfg_if::cfg_if;
use std::borrow::Cow;
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fmt;

pub use error::{FlagError, FlagParseError, FlagWarning};
pub use flag_value::FlagValue;

mod error;
mod flag_value;

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

    pub fn add_flag(&mut self, name: &'a str, value: &'a mut dyn FlagValue) {
        let value = FlagSpec {
            r: value,
        };
        let old = self.flag_specs.insert(name, value);
        if old.is_some() {
            panic!("multiple flags with same name: {}", name);
        }
    }

    pub fn parse<'b, S: AsRef<OsStr>>(
        &mut self,
        args: &'b [S],
    ) -> Result<&'b [S], FlagError> {
        self.parse_with_warnings(args).map(|(remain, _)| remain)
    }

    pub fn parse_with_warnings<'b, S: AsRef<OsStr>>(
        &mut self,
        mut args: &'b [S],
    ) -> Result<(&'b [S], Vec<FlagWarning>), FlagError> {
        let mut warnings = Vec::new();
        loop {
            let seen = self.process_one(&mut args, Some(&mut warnings))?;
            if !seen {
                break;
            }
        }
        Ok((args, warnings))
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
        Ok(false)
    }
}

fn reborrow_option_mut<'a, T>(x: &'a mut Option<&mut T>) -> Option<&'a mut T> {
    if let Some(x) = x {
        Some(x)
    } else {
        None
    }
}

#[derive(Debug)]
enum FlagResult<'a> {
    Argument,
    EndFlags,
    BadFlag,
    Flag {
        num_minuses: usize,
        name: &'a OsStr,
        value: Option<Cow<'a, OsStr>>,
    },
}
cfg_if! {
    if #[cfg(any(unix, target_os = "redox"))] {
        fn parse_one(s: &OsStr) -> FlagResult<'_> {
            use std::os::unix::ffi::OsStrExt;

            let sb = s.as_bytes();
            if sb.len() < 2 || !sb[0] != b'-' {
                // Empty string, `-` and something other than `/-.*/` is a non-flag.
                return FlagResult::Argument;
            }
            if sb == b"--" {
                // `--` terminates flags.
                return FlagResult::EndFlags;
            }
            let (num_minuses, nv) = if sb.len() >= 2 && &sb[..2] == b"--" {
                (2, &sb[2..])
            } else {
                (1, &sb[1..])
            };
            if nv.len() == 0 || nv[0] == b'-' || nv[0] == b'-' {
                return FlagResult::BadFlag;
            }
            let equal_pos = nv.iter().position(|&c| c == b'=');
            let (name, value) = if let Some(equal_pos) = equal_pos {
                (&nv[..equal_pos], Some(&nv[equal_pos + 1..]))
            } else {
                (nv, None)
            };
            FlagResult::Flag {
                num_minuses,
                name: OsStr::from_bytes(name),
                value: value.map(|value| Cow::from(OsStr::from_bytes(value))),
            }
        }
    } else if #[cfg(windows)] {
        copile_error!("TODO: implement for cfg(windows) case");
    } else {
        copile_error!("TODO: implement for cfg(not(any(unix, target_os = \"redox\", windows))) case");
    }
}

struct FlagSpec<'a> {
    r: &'a mut dyn FlagValue,
}

impl<'a> fmt::Debug for FlagSpec<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        struct FlagValuePlaceholder<'a>(&'a dyn FlagValue);
        impl<'a> fmt::Debug for FlagValuePlaceholder<'a> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "<mutable reference {:p}>", self.0)
            }
        }

        f.debug_struct("FlagSpec")
            .field("r", &FlagValuePlaceholder(self.r))
            .finish()
    }
}

pub fn parse_args<S: AsRef<OsStr>, F>(
    args: &[S],
    f: F,
) -> Result<Vec<OsString>, FlagError>
where
    F: FnOnce(&mut FlagSet<'_>),
{
    parse_args_with_warnings(args, f).map(|(remain, _)| remain)
}

pub fn parse_args_with_warnings<S: AsRef<OsStr>, F>(
    args: &[S],
    f: F,
) -> Result<(Vec<OsString>, Vec<FlagWarning>), FlagError>
where
    F: FnOnce(&mut FlagSet<'_>),
{
    let mut flag_set = FlagSet::new();
    f(&mut flag_set);
    let (remain, warnings) = flag_set.parse_with_warnings(args)?;
    let remain = remain.iter().map(|x| x.as_ref().to_owned()).collect::<Vec<_>>();
    Ok((remain, warnings))
}

pub fn parse_os<'a, F>(
    f: F,
) -> Result<Vec<OsString>, FlagError>
where
    F: FnOnce(&mut FlagSet<'_>),
{
    parse_os_with_warnings(f).map(|(remain, _)| remain)
}

pub fn parse_os_with_warnings<'a, F>(
    f: F,
) -> Result<(Vec<OsString>, Vec<FlagWarning>), FlagError>
where
    F: FnOnce(&mut FlagSet<'_>),
{
    let args = std::env::args_os().collect::<Vec<_>>();
    parse_args_with_warnings(&args, f)
}

pub fn parse<'a, F>(
    f: F,
) -> Result<Vec<String>, FlagError>
where
    F: FnOnce(&mut FlagSet<'_>),
{
    parse_with_warnings(f).map(|(remain, _)| remain)
}

pub fn parse_with_warnings<'a, F>(
    f: F,
) -> Result<(Vec<String>, Vec<FlagWarning>), FlagError>
where
    F: FnOnce(&mut FlagSet<'_>),
{
    parse_os_with_warnings(f).map(|(remain, warnings)| {
        // TODO: handle Err
        let remain = remain.into_iter().map(|x| x.into_string().unwrap()).collect::<Vec<_>>();
        (remain, warnings)
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
