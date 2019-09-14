use std::fmt;

#[derive(Debug)]
pub enum FlagError {
    BadFlag { flag: String },
    UnknownFlag { name: String },
    ArgumentNeeded { name: String },
    ParseError { error: FlagParseError },
}

impl fmt::Display for FlagError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use FlagError::*;
        match self {
            BadFlag { flag } => write!(f, "bad flag syntax: {}", flag),
            UnknownFlag { name } => write!(f, "flag provided but not defined: -{}", name),
            ArgumentNeeded { name } => write!(f, "flag needs an argument: -{}", name),
            ParseError { .. } => write!(f, "parse error"),
        }
    }
}

impl std::error::Error for FlagError {
    fn description(&self) -> &str {
        use FlagError::*;
        match self {
            BadFlag { .. } => "bad flag syntax",
            UnknownFlag { .. } => "flag provided but not defined",
            ArgumentNeeded { .. } => "flag needs an argument",
            ParseError { .. } => "parse error",
        }
    }

    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use FlagError::*;
        match self {
            BadFlag { .. } => None,
            UnknownFlag { .. } => None,
            ArgumentNeeded { .. } => None,
            ParseError { error } => Some(error),
        }
    }
}

#[derive(Debug)]
pub enum FlagWarning {
    FlagAfterArg { flag: String },
    ShortLong { flag: String },
    LongShort { flag: String },
}

impl fmt::Display for FlagWarning {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use FlagWarning::*;
        match self {
            FlagAfterArg { flag } => {
                write!(f, "flag-like syntax appearing after argument: {}", flag)
            }
            ShortLong { flag } => write!(f, "long flag with single minus: {}", flag),
            LongShort { flag } => write!(f, "short flag with double minuses: {}", flag),
        }
    }
}

impl std::error::Error for FlagWarning {
    fn description(&self) -> &str {
        use FlagWarning::*;
        match self {
            FlagAfterArg { .. } => "flag-like syntax appearing after argument",
            ShortLong { .. } => "long flag with single minus",
            LongShort { .. } => "short flag with double minuses",
        }
    }
}

#[derive(Debug)]
pub enum FlagParseError {
    BoolParseError,
}

impl fmt::Display for FlagParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use FlagParseError::*;
        match self {
            BoolParseError => write!(f, "invalid bool"),
        }
    }
}

impl std::error::Error for FlagParseError {
    fn description(&self) -> &str {
        use FlagParseError::*;
        match self {
            BoolParseError => "invalid bool",
        }
    }
}
