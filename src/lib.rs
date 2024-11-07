/*!
`base62` is a `no_std` crate (requires [`alloc`]) that has six functions for
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
const BASE_TO_4: u64 = BASE_TO_3 * BASE;
const BASE_TO_5: u64 = BASE_TO_4 * BASE;
const BASE_TO_6: u64 = BASE_TO_5 * BASE;
const BASE_TO_7: u64 = BASE_TO_6 * BASE;
const BASE_TO_8: u64 = BASE_TO_7 * BASE;
const BASE_TO_9: u64 = BASE_TO_8 * BASE;
const BASE_TO_10: u128 = (BASE_TO_9 * BASE) as u128;
const BASE_TO_11: u128 = BASE_TO_10 * BASE as u128;
const BASE_TO_12: u128 = BASE_TO_11 * BASE as u128;
const BASE_TO_13: u128 = BASE_TO_12 * BASE as u128;
const BASE_TO_14: u128 = BASE_TO_13 * BASE as u128;
const BASE_TO_15: u128 = BASE_TO_14 * BASE as u128;
const BASE_TO_16: u128 = BASE_TO_15 * BASE as u128;
const BASE_TO_17: u128 = BASE_TO_16 * BASE as u128;
const BASE_TO_18: u128 = BASE_TO_17 * BASE as u128;
const BASE_TO_19: u128 = BASE_TO_18 * BASE as u128;
const BASE_TO_20: u128 = BASE_TO_19 * BASE as u128;
const BASE_TO_21: u128 = BASE_TO_20 * BASE as u128;

/// Indicates the cause of a decoding failure in [`decode`] or
/// [`decode_alternative`].
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DecodeError {
    /// The decoded number cannot fit into a [`u128`].
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
                write!(f, "' at index {idx}")
            }
        }
    }
}

/// Indicates the cause of an encoding failure in [`encode`](crate::encode_bytes).
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EncodeError {
    BufferTooSmall,
}

macro_rules! internal_decoder_loop_body {
    ($result:ident, $ch:ident, $i:ident, $numeric_start_value:expr, $uppercase_start_value:expr, $lowercase_start_value:expr) => {
        const CHARACTER_VALUES: [u8; 256] = [
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            $numeric_start_value + 0,
            $numeric_start_value + 1,
            $numeric_start_value + 2,
            $numeric_start_value + 3,
            $numeric_start_value + 4,
            $numeric_start_value + 5,
            $numeric_start_value + 6,
            $numeric_start_value + 7,
            $numeric_start_value + 8,
            $numeric_start_value + 9,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            $uppercase_start_value + 0,
            $uppercase_start_value + 1,
            $uppercase_start_value + 2,
            $uppercase_start_value + 3,
            $uppercase_start_value + 4,
            $uppercase_start_value + 5,
            $uppercase_start_value + 6,
            $uppercase_start_value + 7,
            $uppercase_start_value + 8,
            $uppercase_start_value + 9,
            $uppercase_start_value + 10,
            $uppercase_start_value + 11,
            $uppercase_start_value + 12,
            $uppercase_start_value + 13,
            $uppercase_start_value + 14,
            $uppercase_start_value + 15,
            $uppercase_start_value + 16,
            $uppercase_start_value + 17,
            $uppercase_start_value + 18,
            $uppercase_start_value + 19,
            $uppercase_start_value + 20,
            $uppercase_start_value + 21,
            $uppercase_start_value + 22,
            $uppercase_start_value + 23,
            $uppercase_start_value + 24,
            $uppercase_start_value + 25,
            255,
            255,
            255,
            255,
            255,
            255,
            $lowercase_start_value + 0,
            $lowercase_start_value + 1,
            $lowercase_start_value + 2,
            $lowercase_start_value + 3,
            $lowercase_start_value + 4,
            $lowercase_start_value + 5,
            $lowercase_start_value + 6,
            $lowercase_start_value + 7,
            $lowercase_start_value + 8,
            $lowercase_start_value + 9,
            $lowercase_start_value + 10,
            $lowercase_start_value + 11,
            $lowercase_start_value + 12,
            $lowercase_start_value + 13,
            $lowercase_start_value + 14,
            $lowercase_start_value + 15,
            $lowercase_start_value + 16,
            $lowercase_start_value + 17,
            $lowercase_start_value + 18,
            $lowercase_start_value + 19,
            $lowercase_start_value + 20,
            $lowercase_start_value + 21,
            $lowercase_start_value + 22,
            $lowercase_start_value + 23,
            $lowercase_start_value + 24,
            $lowercase_start_value + 25,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
            255,
        ];

        let char_value = *unsafe { CHARACTER_VALUES.get_unchecked($ch as usize) };
        if char_value == 255 {
            return Err(DecodeError::InvalidBase62Byte($ch, $i));
        }
        $result = $result.wrapping_mul(BASE).wrapping_add(char_value as u64);
    };
}

macro_rules! internal_decoder_fn {
    ($fn_name:ident, $numeric_start_value:expr, $uppercase_start_value:expr, $lowercase_start_value:expr) => {
        fn $fn_name(mut input: &[u8]) -> Result<u128, DecodeError> {
            if input.is_empty() {
                return Err(DecodeError::EmptyInput);
            }

            // Remove leading zeroes
            let mut chopped_count = 0_usize;
            while let Option::Some(b'0') = input.first() {
                input = &input[1..];
                chopped_count += 1;
            }
            let input_len = input.len();
            if input_len <= 22 {
                const MULTIPLIERS: [(u128, u64); 23] = [
                    (0, 0),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (1, 1),
                    (BASE as u128, 1),
                    (BASE_TO_2 as u128, 1),
                    (BASE_TO_3 as u128, 1),
                    (BASE_TO_4 as u128, 1),
                    (BASE_TO_5 as u128, 1),
                    (BASE_TO_6 as u128, 1),
                    (BASE_TO_7 as u128, 1),
                    (BASE_TO_8 as u128, 1),
                    (BASE_TO_9 as u128, 1),
                    (BASE_TO_10, 1),
                    (BASE_TO_11, BASE),
                    (BASE_TO_12, BASE_TO_2),
                ];

                let (a_power, b_power) = MULTIPLIERS[input_len];

                let mut iter = (chopped_count..).zip(input.iter().map(|&ch| ch));

                let mut result_a = 0_u64;
                for (i, ch) in iter.by_ref().take(10) {
                    internal_decoder_loop_body!(
                        result_a,
                        ch,
                        i,
                        $numeric_start_value,
                        $uppercase_start_value,
                        $lowercase_start_value
                    );
                }
                let result_a = (result_a as u128)
                    .checked_mul(a_power)
                    .ok_or(DecodeError::ArithmeticOverflow)?;

                let mut result_b = 0_u64;
                for (i, ch) in iter.by_ref().take(10) {
                    internal_decoder_loop_body!(
                        result_b,
                        ch,
                        i,
                        $numeric_start_value,
                        $uppercase_start_value,
                        $lowercase_start_value
                    );
                }
                let result_b = (result_b as u128).wrapping_mul(b_power as u128);

                let mut result_c = 0_u64;
                for (i, ch) in iter {
                    internal_decoder_loop_body!(
                        result_c,
                        ch,
                        i,
                        $numeric_start_value,
                        $uppercase_start_value,
                        $lowercase_start_value
                    );
                }
                let result_c = result_c as u128;

                let result = result_a
                    .checked_add(result_b.wrapping_add(result_c))
                    .ok_or(DecodeError::ArithmeticOverflow)?;
                Ok(result)
            } else {
                Err(input
                    .iter()
                    .position(|b| !b.is_ascii_alphanumeric())
                    .map(|i| {
                        DecodeError::InvalidBase62Byte(input[i], chopped_count.wrapping_add(i))
                    })
                    .unwrap_or(DecodeError::ArithmeticOverflow))
            }
        }
    };
}

internal_decoder_fn!(_decode, 0, 10, 36);
internal_decoder_fn!(_decode_alternative, 0, 36, 10);

/// Decodes a base62 byte slice or an equivalent, like a [`String`],
/// using the standard digit ordering (0 to 9, then A to Z, then a to z).
///
/// Returns a [`Result`] containing the decoded
/// [`u128`] or a [`DecodeError`].
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

/// Decodes a base62 byte slice or an equivalent, like a [`String`],
/// using the alternative digit ordering (0 to 9, then a to z, then A to Z) with lowercase
/// letters before uppercase letters.
///
/// Returns a [`Result`] containing the decoded
/// [`u128`] or a [`DecodeError`].
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
pub(crate) fn digit_count(n: u128) -> usize {
    const POWERS: [u128; 22] = [
        0,
        BASE as u128,
        BASE_TO_2 as u128,
        BASE_TO_3 as u128,
        BASE_TO_4 as u128,
        BASE_TO_5 as u128,
        BASE_TO_6 as u128,
        BASE_TO_7 as u128,
        BASE_TO_8 as u128,
        BASE_TO_9 as u128,
        BASE_TO_10,
        BASE_TO_11,
        BASE_TO_12,
        BASE_TO_13,
        BASE_TO_14,
        BASE_TO_15,
        BASE_TO_16,
        BASE_TO_17,
        BASE_TO_18,
        BASE_TO_19,
        BASE_TO_20,
        BASE_TO_21,
    ];

    match POWERS.binary_search(&n) {
        Ok(n) => n.wrapping_add(1),
        Err(n) => n,
    }
}

macro_rules! internal_encoder_fn {
    ($fn_name:ident, $numeric_offset:expr, $first_letters_offset:expr, $last_letters_offset:expr) => {
        unsafe fn $fn_name(mut num: u128, digits: usize, buf: &mut [u8]) -> usize {
            let mut write_idx = digits;

            let mut digit_index = 0_usize;
            let mut u64_num = (num % BASE_TO_10) as u64;
            num /= BASE_TO_10;
            loop {
                const VALUE_CHARACTERS: [u8; 62] = [
                    $numeric_offset,
                    $numeric_offset + 1,
                    $numeric_offset + 2,
                    $numeric_offset + 3,
                    $numeric_offset + 4,
                    $numeric_offset + 5,
                    $numeric_offset + 6,
                    $numeric_offset + 7,
                    $numeric_offset + 8,
                    $numeric_offset + 9,
                    $first_letters_offset,
                    $first_letters_offset + 1,
                    $first_letters_offset + 2,
                    $first_letters_offset + 3,
                    $first_letters_offset + 4,
                    $first_letters_offset + 5,
                    $first_letters_offset + 6,
                    $first_letters_offset + 7,
                    $first_letters_offset + 8,
                    $first_letters_offset + 9,
                    $first_letters_offset + 10,
                    $first_letters_offset + 11,
                    $first_letters_offset + 12,
                    $first_letters_offset + 13,
                    $first_letters_offset + 14,
                    $first_letters_offset + 15,
                    $first_letters_offset + 16,
                    $first_letters_offset + 17,
                    $first_letters_offset + 18,
                    $first_letters_offset + 19,
                    $first_letters_offset + 20,
                    $first_letters_offset + 21,
                    $first_letters_offset + 22,
                    $first_letters_offset + 23,
                    $first_letters_offset + 24,
                    $first_letters_offset + 25,
                    $last_letters_offset,
                    $last_letters_offset + 1,
                    $last_letters_offset + 2,
                    $last_letters_offset + 3,
                    $last_letters_offset + 4,
                    $last_letters_offset + 5,
                    $last_letters_offset + 6,
                    $last_letters_offset + 7,
                    $last_letters_offset + 8,
                    $last_letters_offset + 9,
                    $last_letters_offset + 10,
                    $last_letters_offset + 11,
                    $last_letters_offset + 12,
                    $last_letters_offset + 13,
                    $last_letters_offset + 14,
                    $last_letters_offset + 15,
                    $last_letters_offset + 16,
                    $last_letters_offset + 17,
                    $last_letters_offset + 18,
                    $last_letters_offset + 19,
                    $last_letters_offset + 20,
                    $last_letters_offset + 21,
                    $last_letters_offset + 22,
                    $last_letters_offset + 23,
                    $last_letters_offset + 24,
                    $last_letters_offset + 25,
                ];

                write_idx = write_idx.wrapping_sub(1);
                let ch = *VALUE_CHARACTERS.get_unchecked((u64_num % BASE) as usize);
                *buf.get_unchecked_mut(write_idx) = ch;

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

            digits
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
/// [`String`].
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
        buf.as_mut_vec().set_len(digits);
        let len = _encode_buf(num, digits, buf.as_bytes_mut());
        debug_assert_eq!(len, digits);
    }
    buf
}

/// Encodes an unsigned integer into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), and then appends it onto the end of the given
/// [`String`].
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
    let old_len = buf.len();
    buf.reserve(digits);
    unsafe {
        buf.as_mut_vec().set_len(old_len + digits);
        let len = _encode_buf(num, digits, &mut buf.as_bytes_mut()[old_len..]);
        debug_assert_eq!(len, digits);
    }
}

/// Encodes an unsigned integer into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), and writes it to the passed buffer.
///
/// The return value is the number of bytes written to the buffer.
///
/// # Safety
/// - To encode all possible values of u128, the buffer must be at least 22 bytes long. However
///   a smaller buffer may be used if the value to be encoded is known to be smaller.
///   Base62 encoding adds 37.5% overhead to the size of the input.
/// - The remaining end of the buffer is left untouched. It's up to the caller to zero it using
///   the returned len if they want to.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let mut buf = [0; 22];
/// base62::encode_bytes(1337_u32, &mut buf);
/// assert_eq!(&buf[..2], b"LZ");
/// ```
pub fn encode_bytes<T: Into<u128>>(num: T, buf: &mut [u8]) -> Result<usize, EncodeError> {
    let num = num.into();
    let digits = digit_count(num);

    if buf.len() < digits {
        return Err(EncodeError::BufferTooSmall);
    }

    unsafe {
        let len = _encode_buf(num, digits, &mut buf[..digits]);
        debug_assert_eq!(len, digits);
    }

    Ok(digits)
}

/// Encodes an unsigned integer into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z), and writes it to the passed buffer.
///
/// The return value is the number of bytes written to the buffer.
///
/// # Safety
/// - To encode all possible values of u128, the buffer must be at least 22 bytes long. However
///   a smaller buffer may be used if the value to be encoded is known to be smaller.
///   Base62 encoding adds 37.5% overhead to the size of the input.
/// - The remaining end of the buffer is left untouched. It's up to the caller to zero it using
///   the returned len if they want to.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let mut buf = [0; 22];
/// base62::encode_bytes(1337_u32, &mut buf);
/// assert_eq!(&buf[..2], b"LZ");
/// ```
pub fn encode_alternative_bytes<T: Into<u128>>(
    num: T,
    buf: &mut [u8],
) -> Result<usize, EncodeError> {
    let num = num.into();
    let digits = digit_count(num);

    if buf.len() < digits {
        return Err(EncodeError::BufferTooSmall);
    }

    unsafe {
        let len = _encode_alternative_buf(num, digits, &mut buf[..digits]);
        debug_assert_eq!(len, digits);
    }

    Ok(digits)
}

/// Encodes an unsigned integer into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z) with lowercase letters before uppercase letters,
/// and returns the resulting [`String`].
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
        buf.as_mut_vec().set_len(digits);
        let len = _encode_alternative_buf(num, digits, buf.as_bytes_mut());
        debug_assert_eq!(len, digits);
    }
    buf
}

/// Encodes an unsigned integer into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z) with lowercase letters before uppercase letters, and
/// then appends it onto the end of the given [`String`].
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
    let old_len = buf.len();
    buf.reserve(digits);
    unsafe {
        buf.as_mut_vec().set_len(old_len + digits);
        let len = _encode_alternative_buf(num, digits, &mut buf.as_bytes_mut()[old_len..]);
        debug_assert_eq!(len, digits);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    // Don't run quickcheck tests under miri because that's infinitely slow
    #[cfg(not(miri))]
    mod quickcheck_tests {
        use super::*;
        use quickcheck::{quickcheck, TestResult};
        quickcheck! {
            fn encode_decode(num: u128) -> bool {
                decode(encode(num)) == Ok(num)
            }
        }

        quickcheck! {
            fn encode_decode_alternative(num: u128) -> bool {
                decode_alternative(encode_alternative(num)) == Ok(num)
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
    }

    #[test]
    fn test_decode() {
        // Test leading zeroes handling
        assert_eq!(
            decode("00001000000000000000000000"),
            Ok((BASE as u128).pow(21))
        );

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
    fn test_decode_empty_input() {
        assert_eq!(decode(""), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn test_decode_invalid_char() {
        let mut input = Vec::with_capacity(40);
        let mut invalid_chars = (0..b'0')
            .chain(b'0' + 10..b'A')
            .chain(b'A' + 26..b'a')
            .chain(b'a' + 26..=255)
            .cycle();

        for size in [10, 22, 23, 40].iter().copied() {
            input.clear();
            input.resize(size, b'0');

            for i in 0..size {
                input[i] = b'1';
                for j in 0..size {
                    let invalid_char = invalid_chars.next().unwrap();
                    input[j] = invalid_char;

                    assert_eq!(
                        decode(&input),
                        Err(DecodeError::InvalidBase62Byte(invalid_char, j))
                    );

                    input[j] = b'0';
                    input[i] = b'1';
                }
                input[i] = b'0';
            }
        }
    }

    #[test]
    fn test_decode_overflow() {
        assert_eq!(
            decode("10000000000000000000000"),
            Err(DecodeError::ArithmeticOverflow)
        );
        assert_eq!(
            decode("7n42DGM5Tflk9n8mt7Fhc78"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_decode_alternative() {
        // Test leading zeroes handling
        assert_eq!(
            decode_alternative("00001000000000000000000000"),
            Ok((BASE as u128).pow(21))
        );

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
    fn test_decode_alternative_empty_input() {
        assert_eq!(decode_alternative(""), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn test_decode_altenative_invalid_char() {
        let mut input = Vec::with_capacity(40);
        let mut invalid_chars = (0..b'0')
            .chain(b'0' + 10..b'A')
            .chain(b'A' + 26..b'a')
            .chain(b'a' + 26..=255)
            .cycle();

        for size in [10, 22, 23, 40].iter().copied() {
            input.clear();
            input.resize(size, b'0');

            for i in 0..size {
                input[i] = b'1';
                for j in 0..size {
                    let invalid_char = invalid_chars.next().unwrap();
                    input[j] = invalid_char;

                    assert_eq!(
                        decode_alternative(&input),
                        Err(DecodeError::InvalidBase62Byte(invalid_char, j))
                    );

                    input[j] = b'0';
                    input[i] = b'1';
                }
                input[i] = b'0';
            }
        }
    }

    #[test]
    fn test_decode_alternative_overflow() {
        assert_eq!(
            decode_alternative("10000000000000000000000"),
            Err(DecodeError::ArithmeticOverflow)
        );
        assert_eq!(
            decode_alternative("7N42dgm5tFLK9N8MT7fHC8"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_encode_bytes_buffer_too_small() {
        let mut buf = [0; 1];
        assert_eq!(
            encode_bytes(1337_u16, &mut buf),
            Err(EncodeError::BufferTooSmall)
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
    fn test_encode_bytes() {
        let mut buf = [0; 22];

        // Test numeric type boundaries
        assert!(encode_bytes(u128::MAX, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"7n42DGM5Tflk9n8mt7Fhc7"));
        buf.fill(0);

        assert!(encode_bytes(u64::MAX as u128 + 1, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"LygHa16AHYG"));
        buf.fill(0);

        assert!(encode_bytes(u64::MAX, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"LygHa16AHYF"));
        buf.fill(0);

        assert!(encode_bytes(0_u8, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"0"));
        buf.fill(0);

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('z');
            power_str.push('0');

            assert!(encode_bytes(power - 1, &mut buf).is_ok());
            assert!(&buf[..].starts_with(power_minus_one_str.as_bytes()));
            buf.fill(0);

            assert!(encode_bytes(power, &mut buf).is_ok());
            assert!(&buf[..].starts_with(power_str.as_bytes()));
            buf.fill(0);
        }

        // Test cases that failed due to earlier bugs
        assert!(encode_bytes(691337691337_u64, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"CAcoUun"));
        buf.fill(0);

        assert!(encode_bytes(92202686130861137968548313400401640448_u128, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"26tF05fvSIgh0000000000"));
        // buf.fill(0);
    }

    #[test]
    fn test_encode_bytes_alternative() {
        let mut buf = [0; 22];

        // Test numeric type boundaries
        assert!(encode_alternative_bytes(u128::MAX, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"7N42dgm5tFLK9N8MT7fHC7"));
        buf.fill(0);

        assert!(encode_alternative_bytes(u64::MAX as u128 + 1, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"lYGhA16ahyg"));
        buf.fill(0);

        assert!(encode_alternative_bytes(u64::MAX, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"lYGhA16ahyf"));
        buf.fill(0);

        assert!(encode_alternative_bytes(0_u8, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"0"));
        buf.fill(0);

        // Test base62 length-change boundaries
        let mut power = 1_u128;
        let mut power_minus_one_str = String::with_capacity(21);
        let mut power_str = String::with_capacity(22);
        power_str.push('1');
        for _ in 1..22 {
            power *= BASE as u128;
            power_minus_one_str.push('Z');
            power_str.push('0');

            assert!(encode_alternative_bytes(power - 1, &mut buf).is_ok());
            assert!(&buf[..].starts_with(power_minus_one_str.as_bytes()));
            buf.fill(0);

            assert!(encode_alternative_bytes(power, &mut buf).is_ok());
            assert!(&buf[..].starts_with(power_str.as_bytes()));
            buf.fill(0);
        }

        // Test cases that failed due to earlier bugs
        assert!(encode_alternative_bytes(691337691337_u64, &mut buf).is_ok());
        assert!(&buf[..].starts_with(b"caCOuUN"));
        buf.fill(0);

        assert!(
            encode_alternative_bytes(92202686130861137968548313400401640448_u128, &mut buf).is_ok()
        );
        assert!(&buf[..].starts_with(b"26Tf05FVsiGH0000000000"));
        // buf.fill(0);
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
}
