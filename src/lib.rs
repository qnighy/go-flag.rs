use cfg_if::cfg_if;
use std::borrow::Cow;
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fmt;

pub use error::{FlagError, FlagParseError, FlagWarning};
pub use flag_value::{FlagSetter, FlagValue};

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

    pub fn add_flag(&mut self, name: &'a str, value: &'a mut dyn FlagSetter) {
        let value = FlagSpec { r: value };
        let old = self.flag_specs.insert(name, value);
        if old.is_some() {
            panic!("multiple flags with same name: {}", name);
        }
    }

    pub fn parse<'b, S: AsRef<OsStr>>(&mut self, args: &'b [S]) -> Result<&'b [S], FlagError> {
        self.parse_with_warnings(args, None)
    }

    pub fn parse_with_warnings<'b, S: AsRef<OsStr>>(
        &mut self,
        mut args: &'b [S],
        mut warnings: Option<&mut Vec<FlagWarning>>,
    ) -> Result<&'b [S], FlagError> {
        loop {
            let seen = self.process_one(&mut args, reborrow_option_mut(&mut warnings))?;
            if !seen {
                break;
            }
        }
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

#[derive(Debug, PartialEq)]
enum FlagResult<'a> {
    Argument,
    EndFlags,
    BadFlag,
    Flag {
        num_minuses: usize,
        name: Cow<'a, OsStr>,
        value: Option<Cow<'a, OsStr>>,
    },
}

fn parse_one(s: &OsStr) -> FlagResult<'_> {
    let s = if let Some(s) = s.to_str() {
        s
    } else {
        return parse_one_fallback(s);
    };

    if s.len() < 2 || !s.starts_with("-") {
        // Empty string, `-` and something other than `/-.*/` is a non-flag.
        return FlagResult::Argument;
    }
    if s == "--" {
        // `--` terminates flags.
        return FlagResult::EndFlags;
    }
    let (num_minuses, nv) = if s.len() >= 2 && s.starts_with("--") {
        (2, &s[2..])
    } else {
        (1, &s[1..])
    };
    if nv.len() == 0 || nv.starts_with("-") || nv.starts_with("=") {
        return FlagResult::BadFlag;
    }
    let equal_pos = nv.find('=');
    let (name, value) = if let Some(equal_pos) = equal_pos {
        (&nv[..equal_pos], Some(&nv[equal_pos + 1..]))
    } else {
        (nv, None)
    };
    FlagResult::Flag {
        num_minuses,
        name: Cow::from(OsStr::new(name)),
        value: value.map(|value| Cow::from(OsStr::new(value))),
    }
}

cfg_if! {
    if #[cfg(any(unix, target_os = "redox"))] {
        fn parse_one_fallback(s: &OsStr) -> FlagResult<'_> {
            use std::os::unix::ffi::OsStrExt;

            let sb = s.as_bytes();
            if sb.len() < 2 || sb[0] != b'-' {
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
            if nv.len() == 0 || nv[0] == b'-' || nv[0] == b'=' {
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
                name: Cow::from(OsStr::from_bytes(name)),
                value: value.map(|value| Cow::from(OsStr::from_bytes(value))),
            }
        }
    } else if #[cfg(windows)] {
        fn parse_one_fallback(s: &OsStr) -> FlagResult<'_> {
            use std::ffi::OsString;
            use std::os::windows::ffi::{OsStrExt, OsStringExt};

            let sb = s.encode_wide().collect::<Vec<_>>();
            if sb.len() < 2 || sb[0] != b'-' as u16 {
                // Empty string, `-` and something other than `/-.*/` is a non-flag.
                return FlagResult::Argument;
            }
            if sb == [b'-' as u16, b'-' as u16] {
                // `--` terminates flags.
                return FlagResult::EndFlags;
            }
            let (num_minuses, nv) = if sb.len() >= 2 && &sb[..2] == [b'-' as u16, b'-' as u16] {
                (2, &sb[2..])
            } else {
                (1, &sb[1..])
            };
            if nv.len() == 0 || nv[0] == b'-' as u16 || nv[0] == b'=' as u16 {
                return FlagResult::BadFlag;
            }
            let equal_pos = nv.iter().position(|&c| c == b'=' as u16);
            let (name, value) = if let Some(equal_pos) = equal_pos {
                (&nv[..equal_pos], Some(&nv[equal_pos + 1..]))
            } else {
                (nv, None)
            };
            FlagResult::Flag {
                num_minuses,
                name: Cow::from(OsString::from_wide(name)),
                value: value.map(|value| Cow::from(OsString::from_wide(value))),
            }
        }
    } else {
        compile_error!("TODO: implement for cfg(not(any(unix, target_os = \"redox\", windows))) case");
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
    T: FlagValue + Default,
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
    T: FlagValue + Default,
    F: FnOnce(&mut FlagSet<'a>),
{
    let mut flag_set = FlagSet::new();
    f(&mut flag_set);
    let remain = flag_set.parse_with_warnings(args, reborrow_option_mut(&mut warnings))?;
    let remain = remain
        .iter()
        .map(|x| {
            let mut val = T::default();
            val.set(Some(x.as_ref()), reborrow_option_mut(&mut warnings))
                .map_err(|error| FlagError::ParseError { error })?;
            Ok(val)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(remain)
}

pub fn parse<'a, T, F>(f: F) -> Vec<T>
where
    T: FlagValue + Default,
    F: FnOnce(&mut FlagSet<'a>),
{
    parse_with_warnings(WarningMode::Report, f)
}

pub fn parse_with_warnings<'a, T, F>(mode: WarningMode, f: F) -> Vec<T>
where
    T: FlagValue + Default,
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
    }

    #[test]
    fn test_parse_one() {
        assert_eq!(parse_one("".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z-y".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("=".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("=x".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z=".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z=x".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z-y=".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z-y=x".as_ref()), FlagResult::Argument);

        assert_eq!(parse_one("-".as_ref()), FlagResult::Argument);
        assert_eq!(
            parse_one("-z".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z")),
                value: None,
            }
        );
        assert_eq!(
            parse_one("-z-y".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z-y")),
                value: None,
            }
        );
        assert_eq!(parse_one("-=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("-=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(
            parse_one("-z=".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("-z=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );
        assert_eq!(
            parse_one("-z-y=".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("-z-y=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );

        assert_eq!(parse_one("--".as_ref()), FlagResult::EndFlags);
        assert_eq!(
            parse_one("--z".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z")),
                value: None,
            }
        );
        assert_eq!(
            parse_one("--z-y".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z-y")),
                value: None,
            }
        );
        assert_eq!(parse_one("--=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("--=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(
            parse_one("--z=".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("--z=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );
        assert_eq!(
            parse_one("--z-y=".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("--z-y=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );

        assert_eq!(parse_one("---".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z-y".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z-y=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z-y=x".as_ref()), FlagResult::BadFlag);
    }

    #[test]
    #[cfg(any(unix, target_os = "redox", windows))]
    fn test_parse_one_fallback() {
        use parse_one_fallback as parse_one;

        assert_eq!(parse_one("".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z-y".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("=".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("=x".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z=".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z=x".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z-y=".as_ref()), FlagResult::Argument);
        assert_eq!(parse_one("z-y=x".as_ref()), FlagResult::Argument);

        assert_eq!(parse_one("-".as_ref()), FlagResult::Argument);
        assert_eq!(
            parse_one("-z".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z")),
                value: None,
            }
        );
        assert_eq!(
            parse_one("-z-y".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z-y")),
                value: None,
            }
        );
        assert_eq!(parse_one("-=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("-=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(
            parse_one("-z=".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("-z=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );
        assert_eq!(
            parse_one("-z-y=".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("-z-y=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );

        assert_eq!(parse_one("--".as_ref()), FlagResult::EndFlags);
        assert_eq!(
            parse_one("--z".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z")),
                value: None,
            }
        );
        assert_eq!(
            parse_one("--z-y".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z-y")),
                value: None,
            }
        );
        assert_eq!(parse_one("--=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("--=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(
            parse_one("--z=".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("--z=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );
        assert_eq!(
            parse_one("--z-y=".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("")))
            }
        );
        assert_eq!(
            parse_one("--z-y=x".as_ref()),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::new("z-y")),
                value: Some(Cow::from(OsStr::new("x")))
            }
        );

        assert_eq!(parse_one("---".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z-y".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z=x".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z-y=".as_ref()), FlagResult::BadFlag);
        assert_eq!(parse_one("---z-y=x".as_ref()), FlagResult::BadFlag);
    }

    #[test]
    #[cfg(any(unix, target_os = "redox"))]
    fn test_parse_one_unix() {
        use std::os::unix::ffi::OsStrExt;

        assert_eq!(parse_one(OsStr::from_bytes(b"")), FlagResult::Argument);
        assert_eq!(parse_one(OsStr::from_bytes(b"z\xA0")), FlagResult::Argument);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"z\xA0-y\xB0")),
            FlagResult::Argument
        );
        assert_eq!(parse_one(OsStr::from_bytes(b"=")), FlagResult::Argument);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"=x\xC0")),
            FlagResult::Argument
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"z\xA0=")),
            FlagResult::Argument
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"z\xA0=x\xC0")),
            FlagResult::Argument
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"z\xA0-y\xB0=")),
            FlagResult::Argument
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"z\xA0-y\xB0=x\xC0")),
            FlagResult::Argument
        );

        assert_eq!(parse_one(OsStr::from_bytes(b"-")), FlagResult::Argument);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-z\xA0")),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::from_bytes(b"z\xA0")),
                value: None,
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-z\xA0-y\xB0")),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::from_bytes(b"z\xA0-y\xB0")),
                value: None,
            }
        );
        assert_eq!(parse_one(OsStr::from_bytes(b"-=")), FlagResult::BadFlag);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-=x\xC0")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-z\xA0=")),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::from_bytes(b"z\xA0")),
                value: Some(Cow::from(OsStr::from_bytes(b"")))
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-z\xA0=x\xC0")),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::from_bytes(b"z\xA0")),
                value: Some(Cow::from(OsStr::from_bytes(b"x\xC0")))
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-z\xA0-y\xB0=")),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::from_bytes(b"z\xA0-y\xB0")),
                value: Some(Cow::from(OsStr::from_bytes(b"")))
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"-z\xA0-y\xB0=x\xC0")),
            FlagResult::Flag {
                num_minuses: 1,
                name: Cow::from(OsStr::from_bytes(b"z\xA0-y\xB0")),
                value: Some(Cow::from(OsStr::from_bytes(b"x\xC0")))
            }
        );

        assert_eq!(parse_one(OsStr::from_bytes(b"--")), FlagResult::EndFlags);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--z\xA0")),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::from_bytes(b"z\xA0")),
                value: None,
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--z\xA0-y\xB0")),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::from_bytes(b"z\xA0-y\xB0")),
                value: None,
            }
        );
        assert_eq!(parse_one(OsStr::from_bytes(b"--=")), FlagResult::BadFlag);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--=x\xC0")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--z\xA0=")),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::from_bytes(b"z\xA0")),
                value: Some(Cow::from(OsStr::from_bytes(b"")))
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--z\xA0=x\xC0")),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::from_bytes(b"z\xA0")),
                value: Some(Cow::from(OsStr::from_bytes(b"x\xC0")))
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--z\xA0-y\xB0=")),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::from_bytes(b"z\xA0-y\xB0")),
                value: Some(Cow::from(OsStr::from_bytes(b"")))
            }
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"--z\xA0-y\xB0=x\xC0")),
            FlagResult::Flag {
                num_minuses: 2,
                name: Cow::from(OsStr::from_bytes(b"z\xA0-y\xB0")),
                value: Some(Cow::from(OsStr::from_bytes(b"x\xC0")))
            }
        );

        assert_eq!(parse_one(OsStr::from_bytes(b"---")), FlagResult::BadFlag);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---z\xA0")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---z\xA0-y\xB0")),
            FlagResult::BadFlag
        );
        assert_eq!(parse_one(OsStr::from_bytes(b"---=")), FlagResult::BadFlag);
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---=x\xC0")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---z\xA0=")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---z\xA0=x\xC0")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---z\xA0-y\xB0=")),
            FlagResult::BadFlag
        );
        assert_eq!(
            parse_one(OsStr::from_bytes(b"---z\xA0-y\xB0=x\xC0")),
            FlagResult::BadFlag
        );
    }
}
