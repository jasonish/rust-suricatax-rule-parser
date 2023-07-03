// SPDX-FileCopyrightText: (C) 2021 Jason Ish <jason@codemonkey.net>
// SPDX-License-Identifier: MIT OR Apache-2.0

pub mod byte_jump;
pub mod byte_math;
pub mod byte_test;

use crate::common::{parse_number, parse_tag, parse_token};
use crate::types;
use crate::types::*;
use crate::RuleParseError;
use nom::branch::alt;
use nom::bytes::complete::escaped_transform;
use nom::bytes::complete::{is_not, tag, take_until, take_while};
use nom::character::complete::none_of;
use nom::character::complete::one_of;
use nom::character::complete::{alphanumeric1, multispace0};
use nom::combinator::map;
use nom::combinator::{eof, opt, rest};
use nom::multi::separated_list0;
use nom::sequence::delimited;
use nom::sequence::{preceded, terminated, tuple};
use nom::Err::Error;
use nom::IResult;
use serde::Deserialize;
use serde::Serialize;
use std::str::FromStr;

static WHITESPACE: &str = " \t\r\n";

//
// Utility parsers.
//

/// Parse all characters up until the next whitespace character.
pub(crate) fn take_until_whitespace(input: &str) -> IResult<&str, &str, RuleParseError<&str>> {
    nom::bytes::complete::is_not(WHITESPACE)(input)
}

pub(crate) fn parse_u64<'a>(
    input: &'a str,
    context: &str,
) -> IResult<&'a str, u64, RuleParseError<&'a str>> {
    let (_, input) = preceded(multispace0, take_until_whitespace)(input)?;
    let val = input.parse().map_err(|_| {
        nom::Err::Error(RuleParseError::IntegerParseError(format!(
            "{}: {}",
            context, input
        )))
    })?;
    Ok((input, val))
}

#[cfg_attr(
    feature = "serde_support",
    derive(Serialize, Deserialize),
    serde(rename_all = "snake_case"),
    serde(untagged)
)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArrayElement {
    String(String),
    NotElement(String),
    Array(Vec<ArrayElement>),
    NotArray(Vec<ArrayElement>),
}

pub fn parse_array(input: &str) -> IResult<&str, Vec<ArrayElement>, RuleParseError<&str>> {
    // Use a stack to avoid recursion. Should probably still set a
    // size bound on it.
    let mut stack: Vec<Vec<ArrayElement>> = vec![Vec::new()];
    let mut token = String::new();
    let mut depth = 0;
    let mut offset = 0;
    let mut neg = false;

    // We might not always have an array, if not, parse a scalar and
    // return it as an array.
    if !input.starts_with('[') {
        let (input, scalar) = parse_token(input)?;
        return Ok((input, vec![ArrayElement::String(scalar.to_string())]));
    }

    for ch in input.chars() {
        offset += 1;
        match ch {
            '[' => {
                depth += 1;
                stack.push(Vec::new())
            }
            ']' => {
                if !token.is_empty() {
                    if let Some(top) = stack.last_mut() {
                        if neg {
                            top.push(ArrayElement::NotElement(token.clone()));
                        } else {
                            top.push(ArrayElement::String(token.clone()));
                        }
                        neg = false;
                        token.clear();
                    } else {
                        return Err(nom::Err::Error(RuleParseError::UnbalancedArray));
                    }
                }
                let last = stack
                    .pop()
                    .ok_or(nom::Err::Error(RuleParseError::UnbalancedArray))?;
                if let Some(top) = stack.last_mut() {
                    top.push(ArrayElement::Array(last));
                } else {
                    return Err(nom::Err::Error(RuleParseError::UnbalancedArray));
                }

                depth -= 1;

                if depth == 0 {
                    break;
                }
            }
            ',' => {
                if !token.is_empty() {
                    if let Some(top) = stack.last_mut() {
                        if neg {
                            top.push(ArrayElement::NotElement(token.clone()));
                        } else {
                            top.push(ArrayElement::String(token.clone()));
                        }
                        neg = false;
                        token.clear();
                    } else {
                        return Err(nom::Err::Error(RuleParseError::UnbalancedArray));
                    }
                }
            }
            '!' => {
                neg = true;
            }
            _ => token.push(ch),
        }
    }

    if !token.is_empty() {
        if let Some(top) = stack.last_mut() {
            top.push(ArrayElement::String(token.clone()));
        } else {
            return Err(nom::Err::Error(RuleParseError::UnbalancedArray));
        }
    }

    // Double unwrap as we used a stack to avoid recursion.
    if let Some(mut stack) = stack.pop() {
        if let Some(ArrayElement::Array(stack)) = stack.pop() {
            return Ok((&input[offset..], stack));
        }
    }

    Err(nom::Err::Error(RuleParseError::UnbalancedArray))
}

/// Parse a quote string as often seen in Suricata rules.
///
/// This handles escaped quotes and semicolons (however semicolons do not need
/// to be escaped like most parsers enforce).
///
/// The input string must start with a quote and will parse up to the next
/// unescaped quote.
///
/// The return value is a String with escapes removed and no leading or trailing
/// double quotes.
fn parse_quoted_string(input: &str) -> IResult<&str, String, RuleParseError<&str>> {
    let escaped_parser = escaped_transform(none_of("\\\""), '\\', one_of("\"\\;\\:"));
    let empty = map(tag(""), |s: &str| s.to_string());
    let escaped_or_empty = alt((escaped_parser, empty));
    delimited(tag("\""), escaped_or_empty, tag("\""))(input)
}

//
// Element parsers.
//
// Try to keep in alphabetical order.
//

pub fn parse_content(input: &str) -> IResult<&str, types::Content, RuleParseError<&str>> {
    let (input, negate) = preceded(multispace0, opt(tag("!")))(input)?;
    let (input, pattern) = parse_quoted_string(input)?;
    Ok((
        input,
        types::Content {
            pattern,
            negate: negate.is_some(),
            ..Default::default()
        },
    ))
}

pub(crate) fn parse_direction(
    input: &str,
) -> IResult<&str, types::Direction, RuleParseError<&str>> {
    let (input, direction) = alt((tag("->"), tag("<>")))(input)?;
    match direction {
        "->" => Ok((input, types::Direction::Single)),
        "<>" => Ok((input, types::Direction::Both)),
        _ => Err(nom::Err::Error(RuleParseError::InvalidDirection(
            direction.to_string(),
        ))),
    }
}

pub(crate) fn parse_count_or_name(
    input: &str,
) -> IResult<&str, types::CountOrName, RuleParseError<&str>> {
    let (_, input) = preceded(multispace0, take_until_whitespace)(input)?;
    if let Ok(distance) = input.parse() {
        Ok((input, types::CountOrName::Value(distance)))
    } else {
        Ok((input, types::CountOrName::Var(input.to_string())))
    }
}

pub(crate) fn parse_flowbits(input: &str) -> IResult<&str, Flowbits, RuleParseError<&str>> {
    let command_parser = preceded(multispace0, alphanumeric1);
    let name_parser = preceded(tag(","), preceded(multispace0, rest));
    let (input, (command, names)) = tuple((command_parser, opt(name_parser)))(input)?;
    let command = FlowbitCommand::from_str(command)?;

    fn make_error<S: AsRef<str>>(reason: S) -> nom::Err<RuleParseError<&'static str>> {
        Error(RuleParseError::Flowbit(reason.as_ref().to_string()))
    }

    match command {
        FlowbitCommand::IsNotSet
        | FlowbitCommand::Unset
        | FlowbitCommand::Toggle
        | FlowbitCommand::IsSet
        | FlowbitCommand::Set => {
            let names = names
                .ok_or_else(|| make_error(format!("{} requires argument", command)))?
                .split('|')
                .map(|s| s.trim().to_string())
                .collect();
            Ok((input, Flowbits { command, names }))
        }
        FlowbitCommand::NoAlert => {
            if names.is_some() {
                Err(make_error("noalert takes no arguments"))
            } else {
                Ok((
                    input,
                    Flowbits {
                        command,
                        names: vec![],
                    },
                ))
            }
        }
    }
}

pub(crate) fn parse_isdataat(input: &str) -> IResult<&str, IsDataAt, RuleParseError<&str>> {
    // Look for a possible negation flag.
    let (input, negate) = preceded(multispace0, opt(tag("!")))(input)?;
    let (input, position) = parse_token(input)?;
    let position = if let Ok((_, number)) = parse_number::<u64>(position) {
        IsDataAtPosition::Position(number)
    } else {
        IsDataAtPosition::Identifier(position.to_string())
    };
    let mut relative = false;
    let mut rawbytes = false;

    for option in input.split(',').map(|s| s.trim()) {
        match option {
            "relative" => {
                relative = true;
            }
            "rawbytes" => {
                rawbytes = true;
            }
            "" => {}
            _ => {
                return Err(Error(RuleParseError::Other(format!(
                    "invalid isdataat option: {}",
                    option
                ))));
            }
        }
    }
    Ok((
        "",
        IsDataAt {
            negate: negate.is_some(),
            position,
            relative,
            rawbytes,
        },
    ))
}

pub(crate) fn parse_xbits(input: &str) -> IResult<&str, XBits, RuleParseError<&str>> {
    let (input, command) = parse_token(input)?;
    let command = XbitCommand::from_str(command)?;
    let (input, _) = parse_tag(",")(input)?;
    let (input, name) = parse_token(input)?;
    let (input, _) = parse_tag(",")(input)?;
    let track_parser = preceded(multispace0, tuple((tag("track"), multispace0, is_not(","))));
    let (input, (_, _, track)) = preceded(multispace0, track_parser)(input)?;

    fn parse_expire(input: &str) -> IResult<&str, &str, RuleParseError<&str>> {
        let (input, _) = parse_tag(",")(input)?;
        let (input, _) = parse_tag("expire")(input)?;
        let (input, expires) = parse_token(input)?;
        Ok((input, expires))
    }

    let end = preceded(multispace0, alt((eof, tag(";"))));
    let (input, expire) = alt((parse_expire, end))(input)?;
    let expire = if expire.is_empty() {
        None
    } else {
        let expire: u64 = expire
            .parse()
            .map_err(|_| Error(RuleParseError::Other("invalid expire".to_string())))?;
        Some(expire)
    };
    let (input, _) = preceded(multispace0, alt((eof, tag(";"))))(input)?;

    Ok((
        input,
        XBits {
            command,
            name: name.trim().to_string(),
            track: track.trim().to_string(),
            expire,
        },
    ))
}

pub(crate) fn parse_flow(input: &str) -> IResult<&str, Vec<Flow>, RuleParseError<&str>> {
    let (input, values) = separated_list0(tag(","), preceded(multispace0, is_not(",")))(input)?;
    let mut options = vec![];
    for option in values {
        options.push(Flow::from_str(option.trim())?);
    }
    Ok((input, options))
}

/// Parse the metadata into a list of the comma separated values.
pub(crate) fn parse_metadata(input: &str) -> IResult<&str, Vec<String>, RuleParseError<&str>> {
    let sep = terminated(multispace0, preceded(multispace0, tag(",")));
    let (input, parts) = separated_list0(
        sep,
        preceded(multispace0, take_while(|c| c != ',' && c != ';')),
    )(input)?;
    let parts: Vec<String> = parts.iter().map(|p| p.trim().to_string()).collect();
    Ok((input, parts))
}

pub(crate) fn parse_pcre(input: &str) -> IResult<&str, Pcre, RuleParseError<&str>> {
    let (input, negate) = opt(tag("!"))(input)?;
    let (input, _open_quote) = preceded(multispace0, tag("\""))(input)?;
    let (input, _open_pcre) = tag("/")(input)?;
    let pattern_end = input.rfind('/').ok_or_else(|| {
        nom::Err::Error(RuleParseError::Other("pcre: no terminating /".to_string()))
    })?;
    let pattern = &input[0..pattern_end];
    let input = &input[pattern_end..];
    let (input, _close_re) = tag("/")(input)?;

    // Return what we have if we're at the end of the quoted section.
    if let Ok((input, _)) = parse_end_quote(input) {
        let pcre = Pcre {
            negate: negate.is_some(),
            pattern: pattern.to_string(),
            modifiers: "".to_string(),
            vars: vec![],
        };
        return Ok((input, pcre));
    }

    // Now parse the modifiers.
    let (input, modifiers) = alphanumeric1(input)?;

    // There might also be some variable captures.
    let parse_start_of_vars = preceded(multispace0, tag(","));
    let parse_vars = preceded(parse_start_of_vars, take_until("\""));
    let (input, vars) = opt(parse_vars)(input)?;
    let (input, _) = parse_end_quote(input)?;

    let vars: Vec<String> = if let Some(vars) = vars {
        vars.split(',').map(|s| s.trim().to_string()).collect()
    } else {
        vec![]
    };

    let pcre = Pcre {
        negate: negate.is_some(),
        pattern: pattern.to_string(),
        modifiers: modifiers.to_string(),
        vars,
    };
    Ok((input, pcre))
}

/// Parse an end quote. Probably not the best name for thie parser but it parses up to and
/// including a quote that is only prefixed by optional whitespace.
fn parse_end_quote(input: &str) -> IResult<&str, &str, RuleParseError<&str>> {
    preceded(multispace0, tag("\""))(input)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parse_array() {
        let input = "[a]xxx";
        let (rem, array) = parse_array(input).unwrap();
        assert_eq!(rem, "xxx");
        assert_eq!(array, vec![ArrayElement::String("a".to_string())]);

        let input = "[a,bbb]xxx";
        let (rem, array) = parse_array(input).unwrap();
        assert_eq!(rem, "xxx");
        assert_eq!(
            array,
            vec![
                ArrayElement::String("a".to_string()),
                ArrayElement::String("bbb".to_string())
            ]
        );

        let input = "[a,[bbb,ccc,[xxx]],ddd,[eee,fff]]aaa";
        let (rem, array) = parse_array(input).unwrap();
        assert_eq!(rem, "aaa");
        assert_eq!(
            array,
            vec![
                ArrayElement::String("a".to_string()),
                ArrayElement::Array(vec![
                    ArrayElement::String("bbb".to_string()),
                    ArrayElement::String("ccc".to_string()),
                    ArrayElement::Array(vec![ArrayElement::String("xxx".to_string())]),
                ]),
                ArrayElement::String("ddd".to_string()),
                ArrayElement::Array(vec![
                    ArrayElement::String("eee".to_string()),
                    ArrayElement::String("fff".to_string()),
                ]),
            ]
        );
    }

    #[test]
    fn test_parse_array_neg() {
        let input = "[!aaa,bbb]";
        let (_rem, array) = parse_array(input).unwrap();
        dbg!(array);
        panic!();
    }

    #[test]
    fn test_parse_pcre() {
        let input0 = r#""/[0-9]{6}/""#;
        let (rem, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(rem, "");
        assert_eq!(
            pcre,
            Pcre {
                negate: false,
                pattern: r#"[0-9]{6}"#.to_string(),
                modifiers: "".to_string(),
                vars: vec![],
            }
        );

        let input0 = r#""/[0-9]{6}/UR""#;
        let (rem, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(rem, "");
        assert_eq!(
            pcre,
            Pcre {
                negate: false,
                pattern: r#"[0-9]{6}"#.to_string(),
                modifiers: "UR".to_string(),
                vars: vec![],
            }
        );

        let input0 = "\"/([^:/$]+)/R,flow:rce_server\"";
        let (_, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(
            pcre,
            Pcre {
                negate: false,
                pattern: r#"([^:/$]+)"#.to_string(),
                modifiers: "R".to_string(),
                vars: vec!["flow:rce_server".to_string()],
            }
        );

        let input0 = "\"/([^:/$]+)/Ri, flow:rce_server\"";
        let (_, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(
            pcre,
            Pcre {
                negate: false,
                pattern: r#"([^:/$]+)"#.to_string(),
                modifiers: "Ri".to_string(),
                vars: vec!["flow:rce_server".to_string()],
            }
        );

        let input0 = r#""/\/winhost(?:32|64)\.(exe|pack)$/i""#;
        let (_, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(
            pcre,
            Pcre {
                negate: false,
                pattern: r#"\/winhost(?:32|64)\.(exe|pack)$"#.to_string(),
                modifiers: "i".to_string(),
                vars: vec![],
            }
        );

        let input0 = r#""/\/(?=[0-9]*?[a-z]*?[a-z0-9)(?=[a-z0-9]*[0-9][a-z]*[0-9][a-z0-9]*\.exe)(?!setup\d+\.exe)[a-z0-9]{5,15}\.exe/""#;
        let (_, _pcre) = parse_pcre(input0).unwrap();

        let input0 = r#""/passwd/main\x2Ephp\x3F[^\x0A\x0D]*backend\x3D[^\x0A\x0D\x26]*\x22/i""#;
        let (_, _pcre) = parse_pcre(input0).unwrap();

        let input0 = r#""/^(?:d(?:(?:ocu|uco)sign|ropbox)|o(?:ffice365|nedrive)|adobe|gdoc)/""#;
        let (_, _pcre) = parse_pcre(input0).unwrap();

        let input0 = r#"!"/^onedrivecl[a-z]{2}prod[a-z]{2}[0-9]{5}\./""#;
        let (_, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(rem, "");
        assert!(pcre.negate);

        let input0 = r#"! "/^\w+\s+\w+:\/\/([^\/\s:#]+)[\/\s:#]\S*.+?Host:[ \t]*\1\S*\b/is""#;
        let (rem, pcre) = parse_pcre(input0).unwrap();
        assert_eq!(rem, "");
        assert_eq!(pcre.modifiers, "is");
        assert_eq!(
            pcre.pattern,
            r#"^\w+\s+\w+:\/\/([^\/\s:#]+)[\/\s:#]\S*.+?Host:[ \t]*\1\S*\b"#
        );
    }

    #[test]
    fn test_parse_metadata() {
        let (_, metadata) = parse_metadata("oneword").unwrap();
        assert_eq!(&metadata, &["oneword"]);

        let (_, metadata) = parse_metadata("one,two").unwrap();
        assert_eq!(&metadata, &["one", "two"]);

        let (_, metadata) = parse_metadata("one ,two").unwrap();
        assert_eq!(&metadata, &["one", "two"]);

        let (_, metadata) = parse_metadata("one , two").unwrap();
        assert_eq!(&metadata, &["one", "two"]);

        let (_, metadata) = parse_metadata("key val , key val").unwrap();
        assert_eq!(&metadata, &["key val", "key val"]);

        let (rem, metadata) = parse_metadata("key val , key val;").unwrap();
        assert_eq!(&metadata, &["key val", "key val"]);
        assert_eq!(rem, ";");
    }

    #[test]
    fn test_parse_flow() {
        let flow = parse_flow("to_client,established").unwrap();
        assert_eq!(flow.1, vec![Flow::ToClient, Flow::Established]);

        let flow = parse_flow("to_client, established").unwrap();
        assert_eq!(flow.1, vec![Flow::ToClient, Flow::Established]);

        let flow = parse_flow("to_client").unwrap();
        assert_eq!(flow.1, vec![Flow::ToClient]);

        let flow = parse_flow(" to_client").unwrap();
        assert_eq!(flow.1, vec![Flow::ToClient]);

        let flow = parse_flow(" to_client  ,    established   ").unwrap();
        assert_eq!(flow.1, vec![Flow::ToClient, Flow::Established]);
    }

    #[test]
    fn test_parse_xbits() {
        let (_, xbits) = parse_xbits("set,ET.dropsite,track ip_src").unwrap();
        assert_eq!(
            xbits,
            XBits {
                command: XbitCommand::Set,
                name: "ET.dropsite".to_string(),
                track: "ip_src".to_string(),
                expire: None,
            }
        );

        let (_, xbits) = parse_xbits("set  ,  ET.dropsite  ,  track ip_src").unwrap();
        assert_eq!(
            xbits,
            XBits {
                command: XbitCommand::Set,
                name: "ET.dropsite".to_string(),
                track: "ip_src".to_string(),
                expire: None,
            }
        );

        let (_, xbits) = parse_xbits("set,ET.dropsite,track ip_src,expire 5000").unwrap();
        assert_eq!(
            xbits,
            XBits {
                command: XbitCommand::Set,
                name: "ET.dropsite".to_string(),
                track: "ip_src".to_string(),
                expire: Some(5000),
            }
        );

        let (_, xbits) = parse_xbits("set,ET.dropsite,track ip_src  , expire 5000  ").unwrap();
        assert_eq!(
            xbits,
            XBits {
                command: XbitCommand::Set,
                name: "ET.dropsite".to_string(),
                track: "ip_src".to_string(),
                expire: Some(5000),
            }
        );

        // Test some invalid input.
        assert!(parse_xbits("set,ET.dropsite,track ip_src,a").is_err());
        assert!(parse_xbits("set,ET.dropsite,track ip_src, expire a").is_err());
        assert!(parse_xbits("set,ET.dropsite,track ip_src, expire 5000 a").is_err());
    }

    #[test]
    pub fn test_parse_flowbits() {
        assert!(parse_flowbits("set,foo.bar").is_ok());
        assert!(parse_flowbits("set,foo | bar").is_ok());
        assert!(parse_flowbits("noalert").is_ok());

        let (_, flowbits) = parse_flowbits("set,myflow2").unwrap();
        assert_eq!(flowbits.command, FlowbitCommand::Set);
        assert_eq!(flowbits.names, vec!["myflow2"]);

        let (_, flowbits) = parse_flowbits("toggle, myflow2").unwrap();
        assert_eq!(flowbits.command, FlowbitCommand::Toggle);
        assert_eq!(flowbits.names, vec!["myflow2"]);
    }

    #[test]
    fn test_parse_isdataat() {
        let (_, isdataat) = parse_isdataat("100").unwrap();
        assert_eq!(
            isdataat,
            IsDataAt {
                position: IsDataAtPosition::Position(100),
                negate: false,
                relative: false,
                rawbytes: false,
            }
        );

        let (_, isdataat) = parse_isdataat("!100").unwrap();
        assert_eq!(
            isdataat,
            IsDataAt {
                position: IsDataAtPosition::Position(100),
                negate: true,
                relative: false,
                rawbytes: false,
            }
        );

        let (_, isdataat) = parse_isdataat("!100,relative").unwrap();
        assert_eq!(
            isdataat,
            IsDataAt {
                position: IsDataAtPosition::Position(100),
                negate: true,
                relative: true,
                rawbytes: false,
            }
        );

        let (_, isdataat) = parse_isdataat("!100,rawbytes").unwrap();
        assert_eq!(
            isdataat,
            IsDataAt {
                position: IsDataAtPosition::Position(100),
                negate: true,
                relative: false,
                rawbytes: true,
            }
        );

        let (_, isdataat) = parse_isdataat("!100, relative, rawbytes").unwrap();
        assert_eq!(
            isdataat,
            IsDataAt {
                position: IsDataAtPosition::Position(100),
                negate: true,
                relative: true,
                rawbytes: true,
            }
        );

        assert!(parse_isdataat("!100, absolute").is_err());

        let (_, isdataat) = parse_isdataat("!length,relative").unwrap();
        assert_eq!(
            isdataat,
            IsDataAt {
                position: IsDataAtPosition::Identifier("length".to_string()),
                negate: true,
                relative: true,
                rawbytes: false,
            }
        );
    }

    #[test]
    fn test_parse_str() {
        let (i, a) = parse_quoted_string(r#""""#).unwrap();
        assert_eq!(i, "");
        assert_eq!(a, "");

        let (i, a) = parse_quoted_string(r#""simple string""#).unwrap();
        assert_eq!(i, "");
        assert_eq!(a, "simple string");

        let (i, a) = parse_quoted_string(r#""with; semicolons.""#).unwrap();
        assert_eq!(i, "");
        assert_eq!(a, "with; semicolons.");

        let (i, a) = parse_quoted_string(r#""with escaped\; semicolons.""#).unwrap();
        assert_eq!(i, "");
        assert_eq!(a, "with escaped; semicolons.");

        let (i, a) =
            parse_quoted_string(r#""with escaped\; semicolons and \" inner quote""#).unwrap();
        assert_eq!(i, "");
        assert_eq!(a, "with escaped; semicolons and \" inner quote");
    }

    #[test]
    fn test_parse_content() {
        let (i, content) = parse_content(r#""|be ef|""#).unwrap();
        assert_eq!(
            content,
            types::Content {
                pattern: "|be ef|".to_string(),
                negate: false,
                ..Default::default()
            }
        );
        assert_eq!(i, "");

        let (i, content) = parse_content(r#"!"|be ef|""#).unwrap();
        assert_eq!(
            content,
            types::Content {
                pattern: "|be ef|".to_string(),
                negate: true,
                ..Default::default()
            }
        );
        assert_eq!(i, "");

        // Snort 3 style...
        let (i, content) = parse_content(r#"!"|be ef|", within 5"#).unwrap();
        assert_eq!(
            content,
            types::Content {
                pattern: "|be ef|".to_string(),
                negate: true,
                ..Default::default()
            }
        );
        assert_eq!(i, ", within 5");

        let (rem, content) = parse_content(r#""/pda_projects.php?offset=http\:""#).unwrap();
        assert_eq!(rem, "");
        assert_eq!(
            content,
            types::Content {
                negate: false,
                pattern: r#"/pda_projects.php?offset=http:"#.to_string(),
                ..Default::default()
            }
        )
    }
}
