/*!
`base62` is a `no_std` crate (requires [`alloc`](alloc)) that has six functions for
encoding to and decoding from [base62](https://en.wikipedia.org/wiki/Base62).

[![Build status](https://github.com/fbernier/base62/workflows/ci/badge.svg)](https://github.com/fbernier/base62/actions)
[![Crates.io](https://img.shields.io/crates/v/base62.svg)](https://crates.io/crates/base62)
[![Docs](https://docs.rs/base62/badge.svg)](https://docs.rs/base62)
*/

#![no_std]
extern crate alloc;
use alloc::string::String;

const BASE: u64 = 62;
const BASE_TO_2: u64 = BASE * BASE;
const BASE_TO_3: u64 = BASE_TO_2 * BASE;
const BASE_TO_6: u64 = BASE_TO_3 * BASE_TO_3;
const BASE_TO_10: u128 = BASE_TO_6 as u128 * BASE_TO_2 as u128 * BASE_TO_2 as u128;
const BASE_TO_11: u128 = BASE_TO_10 * BASE as u128;

const BASE_POWERS: [(u128, u128); 22] = {
    let mut result: [(u128, u128); 22] = [(1, 1); 22];

    let mut a = 1;
    let mut b = 1;

    let mut i = 10;
    while i < 20 {
        a *= 62;
        result[i] = (a, b);
        i += 1;
    }

    while i < 22 {
        a *= 62;
        b *= 62;
        result[i] = (a, b);
        i += 1;
    }

    result
};

/// Indicates the cause of a decoding failure in [`decode`](crate::decode) or
/// [`decode_alternative`](crate::decode_alternative).
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DecodeError {
    /// The decoded number cannot fit into a [`u128`](core::primitive::u128).
    ArithmeticOverflow,

    /// The encoded input is an empty string.
    EmptyInput,

    /// The encoded input contains the given invalid byte at the given index.
    InvalidBase62Byte(u8, usize),
}

impl core::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            DecodeError::ArithmeticOverflow => {
                f.write_str("Decoded number cannot fit into a `u128`")
            }
            DecodeError::EmptyInput => f.write_str("Encoded input is an empty string"),
            DecodeError::InvalidBase62Byte(ch, idx) => {
                use core::fmt::Write;

                f.write_str("Encoded input contains the invalid byte b'")?;
                for char_in_escape in core::ascii::escape_default(ch) {
                    f.write_char(char::from(char_in_escape))?;
                }
                write!(f, "' at index {}", idx)
            }
        }
    }
}

macro_rules! internal_decoder_loop_body {
    ($block_start_values:expr, $result:ident, $ch:ident, $i:ident) => {
        let mut ch: u8 = $ch;

        // The 32-character block number is which of the following blocks `$ch` starts
        // in:
        //     0: characters 0..=31        4: characters 128..=159
        //     1: characters 32..=63       5: characters 160..=191
        //     2: characters 64..=95       6: characters 192..=223
        //     3: characters 96..=127      7: characters 224..=255
        let block_number = (ch >> 5) as usize;

        // The first valid base 62 character in each block
        const BLOCK_START_CHARACTERS: [u8; 8] = [0, b'0', b'A', b'a', 0, 0, 0, 0];
        // Subtract to make the first valid base 62 character in this block zero
        ch = ch.wrapping_sub(BLOCK_START_CHARACTERS[block_number]);

        // The count of valid base 62 characters in each block
        const BLOCK_CHARACTER_COUNTS: [u8; 8] = [0, 10, 26, 26, 0, 0, 0, 0];
        // Valid base 62 characters will now be in
        // `0..BLOCK_CHARACTER_COUNTS[block_number]`, so return an error if this
        // character isn't in that range
        if ch >= BLOCK_CHARACTER_COUNTS[block_number] {
            return Err(DecodeError::InvalidBase62Byte($ch, $i));
        }

        // The base 62 value of the first valid base 62 character in each block
        const BLOCK_START_VALUES: [u8; 8] = $block_start_values;
        // Add the base 62 value of the first valid base 62 character in this block to
        // get the actual base 62 value of this character
        ch = ch.wrapping_add(BLOCK_START_VALUES[block_number]);

        $result = $result.wrapping_mul(BASE).wrapping_add(ch as u64);
    };
}

macro_rules! internal_decoder_fn {
    ($fn_name:ident, $block_start_values:expr) => {
        fn $fn_name(input: &[u8]) -> Result<u128, DecodeError> {
            if input.is_empty() {
                return Result::Err(DecodeError::EmptyInput);
            }

            let &(a_power, b_power) = unsafe { BASE_POWERS.get_unchecked(input.len() - 1) };

            let mut iter = input.iter().map(|&ch| ch).enumerate();

            let mut result_a = 0_u64;
            for (i, ch) in iter.by_ref().take(10) {
                internal_decoder_loop_body!($block_start_values, result_a, ch, i);
            }
            let result_a = (result_a as u128)
                .checked_mul(a_power)
                .ok_or(DecodeError::ArithmeticOverflow)?;

            let mut result_b = 0_u64;
            for (i, ch) in iter.by_ref().take(10) {
                internal_decoder_loop_body!($block_start_values, result_b, ch, i);
            }
            let result_b = (result_b as u128).wrapping_mul(b_power);

            let mut result_c = 0_u64;
            for (i, ch) in iter {
                internal_decoder_loop_body!($block_start_values, result_c, ch, i);
            }
            let result_c = result_c as u128;

            Ok(result_a
                .checked_add(result_b.wrapping_add(result_c))
                .ok_or(DecodeError::ArithmeticOverflow)?)
        }
    };
}

internal_decoder_fn!(_decode, [0, 0, 10, 36, 0, 0, 0, 0]);
internal_decoder_fn!(_decode_alternative, [0, 0, 36, 10, 0, 0, 0, 0]);

/// Decodes a base62 byte slice or an equivalent, like a [`String`](alloc::string::String),
/// using the standard digit ordering (0 to 9, then A to Z, then a to z).
///
/// Returns a [`Result`](core::result::Result) containing the decoded
/// [`u128`](core::primitive::u128) or a [`DecodeError`](crate::DecodeError).
///
/// # Examples
///
/// ```rust
/// extern crate base62;
///
/// let value = base62::decode("rustlang").unwrap();
/// assert_eq!(value, 189876682536016);
/// ```
#[must_use = "this returns the decoded result without modifying the original"]
pub fn decode<T: AsRef<[u8]>>(input: T) -> Result<u128, DecodeError> {
    _decode(input.as_ref())
}

/// Decodes a base62 byte slice or an equivalent, like a [`String`](alloc::string::String),
/// using the alternative digit ordering (0 to 9, then a to z, then A to Z) with lowercase
/// letters before uppercase letters.
///
/// Returns a [`Result`](core::result::Result) containing the decoded
/// [`u128`](core::primitive::u128) or a [`DecodeError`](crate::DecodeError).
///
/// # Examples
///
/// ```rust
/// extern crate base62;
///
/// let value = base62::decode_alternative("rustlang").unwrap();
/// assert_eq!(value, 96813686712946);
/// ```
#[must_use = "this returns the decoded result without modifying the original"]
pub fn decode_alternative<T: AsRef<[u8]>>(input: T) -> Result<u128, DecodeError> {
    _decode_alternative(input.as_ref())
}

// Finds out how many base62 digits a value encodes into.
pub(crate) fn digit_count(mut n: u128) -> usize {
    let mut result = 1;

    if n >= BASE_TO_11 {
        result += 11;
        n /= BASE_TO_11;
    }
    if n >= BASE_TO_10 {
        return result + 10;
    }
    let mut n = n as u64;
    if n >= BASE_TO_6 {
        result += 6;
        n /= BASE_TO_6;
    }
    if n >= BASE_TO_3 {
        result += 3;
        n /= BASE_TO_3;
    }
    if n >= BASE_TO_2 {
        return result + 2;
    }
    if n >= BASE {
        return result + 1;
    }

    result
}

macro_rules! internal_encoder_fn {
    ($fn_name:ident, $numeric_offset:expr, $first_letters_offset:expr, $last_letters_offset:expr) => {
        /// # Safety
        ///
        /// With this function, `buf` MUST ALREADY have its capacity extended
        /// to hold all the new base62 characters that will be added
        unsafe fn $fn_name(mut num: u128, digits: usize, buf: &mut String) {
            const NUMERIC_OFFSET: u8 = $numeric_offset;
            const FIRST_LETTERS_OFFSET: u8 = $first_letters_offset - 10;
            const LAST_LETTERS_OFFSET: u8 = $last_letters_offset - 10 - 26;

            let buf_vec = buf.as_mut_vec();
            let new_len = buf_vec.len().wrapping_add(digits);
            let mut ptr = buf_vec.as_mut_ptr().add(new_len).sub(1);

            let mut digit_index = 0_usize;
            let mut u64_num = (num % BASE_TO_10) as u64;
            num /= BASE_TO_10;
            loop {
                core::ptr::write(ptr, {
                    let digit = (u64_num % BASE) as u8;
                    match digit {
                        0..=9 => digit.wrapping_add(NUMERIC_OFFSET),
                        10..=35 => digit.wrapping_add(FIRST_LETTERS_OFFSET),
                        _ => digit.wrapping_add(LAST_LETTERS_OFFSET),
                    }
                });
                ptr = ptr.sub(1);

                digit_index = digit_index.wrapping_add(1);
                match digit_index {
                    _ if digit_index == digits => break,
                    10 => {
                        u64_num = (num % BASE_TO_10) as u64;
                        num /= BASE_TO_10;
                    }
                    20 => u64_num = num as u64,
                    _ => u64_num /= BASE,
                }
            }

            buf_vec.set_len(new_len);
        }
    };
}

// # Safety
//
// With these functions, `buf` MUST ALREADY have its capacity extended
// to hold all the new base62 characters that will be added
internal_encoder_fn!(_encode_buf, b'0', b'A', b'a');
internal_encoder_fn!(_encode_alternative_buf, b'0', b'a', b'A');

/// Encodes an unsigned integer into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), and returns the resulting
/// [`String`](alloc::string::String).
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let b62 = base62::encode(1337_u32);
/// assert_eq!(b62, "LZ");
/// ```
#[must_use = "this allocates a new `String`"]
pub fn encode<T: Into<u128>>(num: T) -> String {
    let num = num.into();
    let digits = digit_count(num);
    let mut buf = String::with_capacity(digits);
    unsafe {
        _encode_buf(num, digits, &mut buf);
    }
    buf
}

/// Encodes an unsigned integer into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), and then appends it onto the end of the given
/// [`String`](alloc::string::String).
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let mut buf = String::from("1337 in base62: ");
/// base62::encode_buf(1337_u32, &mut buf);
/// assert_eq!(buf, "1337 in base62: LZ");
/// ```
pub fn encode_buf<T: Into<u128>>(num: T, buf: &mut String) {
    let num = num.into();
    let digits = digit_count(num);
    buf.reserve(digits);
    unsafe {
        _encode_buf(num, digits, buf);
    }
}

/// Encodes an unsigned integer into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z) with lowercase letters before uppercase letters,
/// and returns the resulting [`String`](alloc::string::String).
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let b62 = base62::encode_alternative(1337_u32);
/// assert_eq!(b62, "lz");
/// ```
#[must_use = "this allocates a new `String`"]
pub fn encode_alternative<T: Into<u128>>(num: T) -> String {
    let num = num.into();
    let digits = digit_count(num);
    let mut buf = String::with_capacity(digits);
    unsafe {
        _encode_alternative_buf(num, digits, &mut buf);
    }
    buf
}

/// Encodes an unsigned integer into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z) with lowercase letters before uppercase letters, and
/// then appends it onto the end of the given [`String`](alloc::string::String).
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let mut buf = String::from("1337 in base62 alternative: ");
/// base62::encode_alternative_buf(1337_u32, &mut buf);
/// assert_eq!(buf, "1337 in base62 alternative: lz");
/// ```
pub fn encode_alternative_buf<T: Into<u128>>(num: T, buf: &mut String) {
    let num = num.into();
    let digits = digit_count(num);
    buf.reserve(digits);
    unsafe {
        _encode_alternative_buf(num, digits, buf);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;
    use quickcheck::{quickcheck, TestResult};

    quickcheck! {
        fn encode_decode(num: u128) -> bool {
            decode(encode(num)) == Ok(num)
        }
    }

    quickcheck! {
        fn decode_bad(input: Vec<u8>) -> TestResult {
            if !input.is_empty() && input.iter().all(|ch| ch.is_ascii_alphanumeric()) {
                TestResult::discard()
            } else {
                TestResult::from_bool(decode(&input).is_err())
            }
        }
    }

    quickcheck! {
        fn decode_good(input: Vec<u8>) -> TestResult {
            if !input.is_empty() && input.iter().all(|ch| ch.is_ascii_alphanumeric()) {
                TestResult::from_bool(decode(&input).is_ok())
            } else {
                TestResult::discard()
            }
        }
    }

    #[test]
    fn test_encode() {
        // Test numeric type boundaries
        assert_eq!(encode(u128::MAX), "7n42DGM5Tflk9n8mt7Fhc7");
        assert_eq!(encode(u64::MAX as u128 + 1), "LygHa16AHYG");
        assert_eq!(encode(u64::MAX), "LygHa16AHYF");
        assert_eq!(encode(0_u8), "0");

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('z');
            power_str.push('0');

            assert_eq!(encode(power - 1), power_minus_one_str);
            assert_eq!(encode(power), power_str);
        }

        // Test cases that failed due te earlier bugs
        assert_eq!(encode(691337691337_u64), "CAcoUun");
        assert_eq!(
            encode(92202686130861137968548313400401640448_u128),
            "26tF05fvSIgh0000000000"
        );
    }

    #[test]
    fn test_encode_buf() {
        let mut buf = String::with_capacity(22);

        // Test append functionality
        buf.push_str("Base62: ");
        encode_buf(10622433094_u64, &mut buf);
        assert_eq!(buf, "Base62: Base62");
        buf.clear();

        // Test numeric type boundaries
        encode_buf(u128::MAX, &mut buf);
        assert_eq!(buf, "7n42DGM5Tflk9n8mt7Fhc7");
        buf.clear();

        encode_buf(u64::MAX as u128 + 1, &mut buf);
        assert_eq!(buf, "LygHa16AHYG");
        buf.clear();

        encode_buf(u64::MAX, &mut buf);
        assert_eq!(buf, "LygHa16AHYF");
        buf.clear();

        encode_buf(0_u8, &mut buf);
        assert_eq!(buf, "0");
        buf.clear();

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('z');
            power_str.push('0');

            encode_buf(power - 1, &mut buf);
            assert_eq!(buf, power_minus_one_str);
            buf.clear();

            encode_buf(power, &mut buf);
            assert_eq!(buf, power_str);
            buf.clear();
        }

        // Test cases that failed due to earlier bugs
        encode_buf(691337691337_u64, &mut buf);
        assert_eq!(buf, "CAcoUun");
        buf.clear();

        encode_buf(92202686130861137968548313400401640448_u128, &mut buf);
        assert_eq!(buf, "26tF05fvSIgh0000000000");
        // buf.clear();
    }

    #[test]
    fn test_encode_alternative() {
        // Test numeric type boundaries
        assert_eq!(encode_alternative(u128::MAX), "7N42dgm5tFLK9N8MT7fHC7");
        assert_eq!(encode_alternative(u64::MAX as u128 + 1), "lYGhA16ahyg");
        assert_eq!(encode_alternative(u64::MAX), "lYGhA16ahyf");
        assert_eq!(encode_alternative(0_u8), "0");

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('Z');
            power_str.push('0');

            assert_eq!(encode_alternative(power - 1), power_minus_one_str);
            assert_eq!(encode_alternative(power), power_str);
        }

        // Test cases that failed due to earlier bugs
        assert_eq!(
            encode(92202686130861137968548313400401640448_u128),
            "26tF05fvSIgh0000000000"
        );
        assert_eq!(encode_alternative(691337691337_u64), "caCOuUN");
    }

    #[test]
    fn test_encode_alternative_buf() {
        let mut buf = String::with_capacity(22);

        // Test append functionality
        buf.push_str("Base62: ");
        encode_alternative_buf(34051405518_u64, &mut buf);
        assert_eq!(buf, "Base62: Base62");
        buf.clear();

        // Test numeric type boundaries
        encode_alternative_buf(u128::MAX, &mut buf);
        assert_eq!(buf, "7N42dgm5tFLK9N8MT7fHC7");
        buf.clear();

        encode_alternative_buf(u64::MAX as u128 + 1, &mut buf);
        assert_eq!(buf, "lYGhA16ahyg");
        buf.clear();

        encode_alternative_buf(u64::MAX, &mut buf);
        assert_eq!(buf, "lYGhA16ahyf");
        buf.clear();

        encode_alternative_buf(0_u8, &mut buf);
        assert_eq!(buf, "0");
        buf.clear();

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('Z');
            power_str.push('0');

            encode_alternative_buf(power - 1, &mut buf);
            assert_eq!(buf, power_minus_one_str);
            buf.clear();

            encode_alternative_buf(power, &mut buf);
            assert_eq!(buf, power_str);
            buf.clear();
        }

        // Test cases that failed due to earlier bugs
        encode_alternative_buf(691337691337_u64, &mut buf);
        assert_eq!(buf, "caCOuUN");
        buf.clear();

        encode_alternative_buf(92202686130861137968548313400401640448_u128, &mut buf);
        assert_eq!(buf, "26Tf05FVsiGH0000000000");
        // buf.clear();
    }

    #[test]
    fn test_decode() {
        // Test numeric type boundaries
        assert_eq!(decode("7n42DGM5Tflk9n8mt7Fhc7"), Ok(u128::MAX));
        assert_eq!(decode("LygHa16AHYG"), Ok(u64::MAX as u128 + 1));
        assert_eq!(decode("LygHa16AHYF"), Ok(u64::MAX as u128));
        assert_eq!(decode("0"), Ok(0));

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('z');
            power_str.push('0');

            assert_eq!(decode(&power_minus_one_str), Ok(power - 1));
            assert_eq!(decode(&power_str), Ok(power));
        }

        // Test cases that failed due te earlier bugs
        assert_eq!(decode("CAcoUun"), Ok(691337691337));
        assert_eq!(
            decode("26tF05fvSIgh0000000000"),
            Ok(92202686130861137968548313400401640448)
        );
    }

    #[test]
    fn test_decode_overflow() {
        assert_eq!(
            decode("7n42DGM5Tflk9n8mt7Fhc78"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_decode_empty_input() {
        assert_eq!(decode(""), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn test_decode_invalid_char() {
        assert_eq!(
            decode("ds{Z455f"),
            Err(DecodeError::InvalidBase62Byte(b'{', 2))
        );
    }

    #[test]
    fn test_decode_alternative() {
        // Test numeric type boundaries
        assert_eq!(decode_alternative("7N42dgm5tFLK9N8MT7fHC7"), Ok(u128::MAX));
        assert_eq!(decode_alternative("lYGhA16ahyg"), Ok(u64::MAX as u128 + 1));
        assert_eq!(decode_alternative("lYGhA16ahyf"), Ok(u64::MAX as u128));
        assert_eq!(decode_alternative("0"), Ok(0));

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('Z');
            power_str.push('0');

            assert_eq!(decode_alternative(&power_minus_one_str), Ok(power - 1));
            assert_eq!(decode_alternative(&power_str), Ok(power));
        }

        // Test cases that failed due te earlier bugs
        assert_eq!(decode_alternative("caCOuUN"), Ok(691337691337));
        assert_eq!(
            decode_alternative("26Tf05FVsiGH0000000000"),
            Ok(92202686130861137968548313400401640448)
        );
    }

    #[test]
    fn test_decode_alternative_overflow() {
        assert_eq!(
            decode_alternative("7N42dgm5tFLK9N8MT7fHC8"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_decode_alternative_empty_input() {
        assert_eq!(decode_alternative(""), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn test_decode_alternative_invalid_char() {
        assert_eq!(
            decode_alternative("ds{Z455f"),
            Err(DecodeError::InvalidBase62Byte(b'{', 2))
        );
    }

    #[test]
    fn test_digit_count() {
        // Assume that `digit_count` is a monotonically increasing function and
        // check that the boundary outputs have the right values
        for pow in 1..22 {
            let this_power = (BASE as u128).pow(pow as u32);

            assert_eq!(digit_count(this_power - 1), pow);
            assert_eq!(digit_count(this_power), pow + 1);
        }

        // Check that boundary inputs have the right values
        assert_eq!(digit_count(0), 1);
        assert_eq!(digit_count(1), 1);
        assert_eq!(digit_count(u64::MAX as u128), 11);
        assert_eq!(digit_count(u64::MAX as u128 + 1), 11);
        assert_eq!(digit_count(u128::MAX), 22);
    }
}
