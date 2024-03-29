// SPDX-FileCopyrightText: (C) 2022 Jason Ish <jason@codemonkey.net>
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::common::{parse_number, parse_number_or_name, parse_tag, parse_token};
use crate::{ByteTest, ByteTestOperator, Endian, RuleParseError};
use nom::bytes::complete::tag;
use nom::combinator::opt;
use nom::Err::Error;
use nom::IResult;

fn parse_op(input: &str) -> IResult<&str, ByteTestOperator, RuleParseError<&str>> {
    let (input, op) = parse_token(input)?;
    let op = match op {
        "<" => ByteTestOperator::Lt,
        ">" => ByteTestOperator::Gt,
        "<=" => ByteTestOperator::Lte,
        ">=" => ByteTestOperator::Gte,
        "=" => ByteTestOperator::Eq,
        "&" => ByteTestOperator::And,
        "^" => ByteTestOperator::Or,
        _ => {
            return Err(nom::Err::Error(RuleParseError::Other(format!(
                "invalid byte test operator: {}",
                op
            ))));
        }
    };
    Ok((input, op))
}

pub fn parse_byte_test(input: &str) -> IResult<&str, ByteTest, RuleParseError<&str>> {
    let (input, bytes) = parse_number::<usize>(input)?;
    let (input, _) = parse_tag(",")(input)?;
    let (input, negate) = opt(tag("!"))(input)?;
    let (input, op) = parse_op(input)?;
    let (input, _) = parse_tag(",")(input)?;
    let (input, value) = parse_number_or_name::<u64>(input)?;
    let (input, _) = parse_tag(",")(input)?;
    let (input, offset) = parse_number_or_name::<i32>(input)?;

    let mut relative = false;
    let mut endian = Endian::Big;
    let mut string = false;
    let mut hex = false;
    let mut dec = false;
    let mut oct = false;
    let mut dce = false;
    let mut bitmask = 0;

    let mut input = input;
    while let Ok((i, _)) = parse_tag(",")(input) {
        let (mut i, opt) = parse_token(i)?;
        match opt {
            "relative" => relative = true,
            "dce" => dce = true,
            "bitmask" => {
                let (_i, _bitmask) = parse_number(i)?;
                i = _i;
                bitmask = _bitmask;
            }
            "string" => {
                string = true;
            }
            "hex" => {
                hex = true;
            }
            "dec" => {
                dec = true;
            }
            "oct" => {
                oct = true;
            }
            "big" => {
                endian = Endian::Big;
            }
            "little" => {
                endian = Endian::Little;
            }
            _ => {
                return Err(Error(RuleParseError::UnknownOption(opt.to_string())));
            }
        }
        input = i;
    }

    Ok((
        input,
        ByteTest {
            bytes,
            negate: negate.is_some(),
            op,
            value,
            offset,
            relative,
            endian,
            string,
            hex,
            dec,
            oct,
            dce,
            bitmask,
        },
    ))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::NumberOrName;

    #[test]
    fn test_parse_byte_test() {
        parse_byte_test("1,=,1,OFFSET,relative").unwrap();
        parse_byte_test("2,=,1,1").unwrap();
        parse_byte_test("2,=,1,0x1").unwrap();

        let (_, bt) = parse_byte_test("4,=,1337,1,relative,string,dec").unwrap();
        assert_eq!(
            bt,
            ByteTest {
                bytes: 4,
                negate: false,
                op: ByteTestOperator::Eq,
                value: NumberOrName::Number(1337),
                offset: NumberOrName::Number(1),
                relative: true,
                endian: Endian::Big,
                string: true,
                hex: false,
                dec: true,
                oct: false,
                dce: false,
                bitmask: 0,
            }
        );

        let (_, bt) = parse_byte_test("8, =, 0xdeadbeef, 0, string, hex").unwrap();
        assert_eq!(
            bt,
            ByteTest {
                bytes: 8,
                negate: false,
                op: ByteTestOperator::Eq,
                value: NumberOrName::Number(0xdeadbeef),
                offset: NumberOrName::Number(0),
                relative: false,
                endian: Endian::Big,
                string: true,
                hex: true,
                dec: false,
                oct: false,
                dce: false,
                bitmask: 0,
            }
        );

        let (_, bt) = parse_byte_test("1,!=,0x20,0,string,hex,relative").unwrap();
        assert_eq!(
            bt,
            ByteTest {
                bytes: 1,
                negate: true,
                op: ByteTestOperator::Eq,
                value: NumberOrName::Number(0x20),
                offset: NumberOrName::Number(0),
                relative: true,
                endian: Endian::Big,
                string: true,
                hex: true,
                dec: false,
                oct: false,
                dce: false,
                bitmask: 0,
            }
        );

        let (_, bt) = parse_byte_test("1,!&,0x40,2").unwrap();
        assert_eq!(
            bt,
            ByteTest {
                bytes: 1,
                negate: true,
                op: ByteTestOperator::And,
                value: NumberOrName::Number(0x40),
                offset: NumberOrName::Number(2),
                relative: false,
                endian: Endian::Big,
                string: false,
                hex: false,
                dec: false,
                oct: false,
                dce: false,
                bitmask: 0,
            }
        );

        let (_, bt) = parse_byte_test("4,>,128,20,relative,little").unwrap();
        assert_eq!(
            bt,
            ByteTest {
                bytes: 4,
                negate: false,
                op: ByteTestOperator::Gt,
                value: NumberOrName::Number(128),
                offset: NumberOrName::Number(20),
                relative: true,
                endian: Endian::Little,
                string: false,
                hex: false,
                dec: false,
                oct: false,
                dce: false,
                bitmask: 0,
            }
        );
    }
}
