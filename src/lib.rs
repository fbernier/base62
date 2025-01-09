/*!
`base62` is a `no_std` crate (requires [`alloc`]) that has six functions for
encoding to and decoding from [base62](https://en.wikipedia.org/wiki/Base62).

[![Build status](https://github.com/fbernier/base62/workflows/ci/badge.svg)](https://github.com/fbernier/base62/actions)
[![Crates.io](https://img.shields.io/crates/v/base62.svg)](https://crates.io/crates/base62)
[![Docs](https://docs.rs/base62/badge.svg)](https://docs.rs/base62)
*/

#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

use core::fmt;

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

/// Indicates the cause of an encoding failure in [`encode`](crate::encode_bytes).
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EncodeError {
    BufferTooSmall,
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            DecodeError::ArithmeticOverflow => {
                f.write_str("Decoded number cannot fit into a `u128`")
            }
            DecodeError::EmptyInput => f.write_str("Encoded input is an empty string"),
            DecodeError::InvalidBase62Byte(ch, idx) => {
                use fmt::Write;
                f.write_str("Encoded input contains the invalid byte b'")?;
                for char_in_escape in core::ascii::escape_default(ch) {
                    f.write_char(char::from(char_in_escape))?;
                }
                write!(f, "' at index {idx}")
            }
        }
    }
}

// For DecodeError
#[rustversion::since(1.81)]
impl core::error::Error for DecodeError {}

#[rustversion::before(1.81)]
#[cfg(feature = "std")]
impl std::error::Error for DecodeError {}

// For EncodeError
#[rustversion::since(1.81)]
impl core::error::Error for EncodeError {}

#[rustversion::before(1.81)]
#[cfg(feature = "std")]
impl std::error::Error for EncodeError {}

// You'll also need to implement std::fmt::Display for EncodeError since it's required for Error
impl fmt::Display for EncodeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EncodeError::BufferTooSmall => write!(f, "Buffer too small to encode the number"),
        }
    }
}

/// Writes the base62 representation of a number using the standard alphabet to any fmt::Write destination.
///
/// # Example
/// ```rust
/// let mut output = String::new();
/// base62::encode_fmt(1337_u32, &mut output).unwrap();
/// assert_eq!(output, "LZ");
/// ```
pub fn encode_fmt<T: Into<u128>, W: fmt::Write + ?Sized>(num: T, f: &mut W) -> fmt::Result {
    let num = num.into();
    let digits = digit_count(num);
    let mut buf = [0u8; 22]; // Maximum possible size for u128

    // SAFETY: We know buf is 22 bytes which is enough for any u128
    unsafe {
        let len = _encode_buf(num, digits, &mut buf[..digits]);
        // SAFETY: The encoded bytes are guaranteed to be valid ASCII
        for &b in &buf[..len] {
            f.write_char(char::from_u32_unchecked(b as u32))?;
        }
        Ok(())
    }
}

/// Wraps a number to [`Display`] it via [`encode_fmt()`].
///
/// # Example
/// ```rust
/// assert_eq!(format!("{}", base62::fmt(1337_u32)), "LZ");
/// assert_eq!(base62::fmt(1337_u32).to_string(), "LZ");
/// ```
///
/// [`Display`]: fmt::Display
pub fn fmt<T: Into<u128>>(num: T) -> impl fmt::Display {
    Fmt(num.into())
}

struct Fmt(u128);

impl fmt::Display for Fmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        encode_fmt(self.0, f)
    }
}

/// Writes the base62 representation of a number using the alternative alphabet (0 to 9, then a to z, then A to Z)
/// to any fmt::Write destination.
///
/// # Example
/// ```rust
/// let mut output = String::new();
/// base62::encode_alternative_fmt(1337_u32, &mut output).unwrap();
/// assert_eq!(output, "lz");
/// ```
pub fn encode_alternative_fmt<T: Into<u128>, W: fmt::Write + ?Sized>(
    num: T,
    f: &mut W,
) -> fmt::Result {
    let num = num.into();
    let digits = digit_count(num);
    let mut buf = [0u8; 22]; // Maximum possible size for u128

    // SAFETY: We know buf is 22 bytes which is enough for any u128
    unsafe {
        let len = _encode_alternative_buf(num, digits, &mut buf[..digits]);
        // SAFETY: The encoded bytes are guaranteed to be valid ASCII
        for &b in &buf[..len] {
            f.write_char(char::from_u32_unchecked(b as u32))?;
        }
        Ok(())
    }
}

/// Wraps a number to [`Display`] it via [`encode_alternative_fmt()`].
///
/// # Example
/// ```rust
/// assert_eq!(format!("{}", base62::fmt_alt(1337_u32)), "lz");
/// assert_eq!(base62::fmt_alt(1337_u32).to_string(), "lz");
/// ```
///
/// [`Display`]: fmt::Display
pub fn fmt_alt<T: Into<u128>>(num: T) -> impl fmt::Display {
    FmtAlternative(num.into())
}

struct FmtAlternative(u128);

impl fmt::Display for FmtAlternative {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        encode_alternative_fmt(self.0, f)
    }
}

/// Writes the base62 representation of a number using the standard alphabet to any io::Write destination.
///
/// This function is only available when the `std` feature is enabled.
///
/// # Example
/// ```rust
/// # use std::io::Write;
/// let mut output = Vec::new();
/// base62::encode_io(1337_u32, &mut output).unwrap();
/// assert_eq!(output, b"LZ");
/// ```
#[cfg(feature = "std")]
pub fn encode_io<T: Into<u128>, W: std::io::Write + ?Sized>(
    num: T,
    w: &mut W,
) -> std::io::Result<()> {
    let num = num.into();
    let digits = digit_count(num);
    let mut buf = [0u8; 22]; // Maximum possible size for u128

    // SAFETY: We know buf is 22 bytes which is enough for any u128
    unsafe {
        let len = _encode_buf(num, digits, &mut buf[..digits]);
        w.write_all(&buf[..len])
    }
}

/// Writes the base62 representation of a number using the alternative alphabet (0 to 9, then a to z, then A to Z)
/// to any io::Write destination.
///
/// This function is only available when the `std` feature is enabled.
///
/// # Example
/// ```rust
/// # use std::io::Write;
/// let mut output = Vec::new();
/// base62::encode_alternative_io(1337_u32, &mut output).unwrap();
/// assert_eq!(output, b"lz");
/// ```
#[cfg(feature = "std")]
pub fn encode_alternative_io<T: Into<u128>, W: std::io::Write + ?Sized>(
    num: T,
    w: &mut W,
) -> std::io::Result<()> {
    let num = num.into();
    let digits = digit_count(num);
    let mut buf = [0u8; 22]; // Maximum possible size for u128

    // SAFETY: We know buf is 22 bytes which is enough for any u128
    unsafe {
        let len = _encode_alternative_buf(num, digits, &mut buf[..digits]);
        w.write_all(&buf[..len])
    }
}

// Internal functions used by both no_std and alloc features
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

macro_rules! internal_decoder_loop_body {
    ($result:ident, $ch:ident, $i:ident, $numeric_start_value:literal, $uppercase_start_value:literal, $lowercase_start_value:literal) => {
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
    ($fn_name:ident, $numeric_start_value:literal, $uppercase_start_value:literal, $lowercase_start_value:literal) => {
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

macro_rules! internal_encoder_fn {
    ($fn_name:ident, $numeric_offset:literal, $first_letters_offset:literal, $last_letters_offset:literal) => {
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
                unsafe {
                    let ch = *VALUE_CHARACTERS.get_unchecked((u64_num % BASE) as usize);
                    *buf.get_unchecked_mut(write_idx) = ch;
                }

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

unsafe fn _encode_buf(num: u128, digits: usize, buf: &mut [u8]) -> usize {
    internal_encoder_fn!(_encode_bytes_impl, b'0', b'A', b'a');
    _encode_bytes_impl(num, digits, buf)
}

unsafe fn _encode_alternative_buf(num: u128, digits: usize, buf: &mut [u8]) -> usize {
    internal_encoder_fn!(_encode_alternative_bytes_impl, b'0', b'a', b'A');
    _encode_alternative_bytes_impl(num, digits, buf)
}

#[cfg(feature = "alloc")]
mod alloc_support {
    use super::*;
    use alloc::string::String;

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
    pub fn decode_alternative<T: AsRef<[u8]>>(input: T) -> Result<u128, DecodeError> {
        _decode_alternative(input.as_ref())
    }
}

#[cfg(feature = "alloc")]
pub use alloc_support::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "alloc")]
    use alloc::string::String;
    #[cfg(feature = "alloc")]
    use alloc::vec::Vec;

    // Don't run quickcheck tests under miri because that's infinitely slow
    #[cfg(all(test, feature = "alloc", not(miri)))]
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

        quickcheck! {
            fn encode_fmt_decode(num: u128) -> bool {
                let mut s = String::new();
                encode_fmt(num, &mut s).unwrap();
                decode(&s) == Ok(num)
            }
        }

        quickcheck! {
            fn encode_alternative_fmt_decode(num: u128) -> bool {
                let mut s = String::new();
                encode_alternative_fmt(num, &mut s).unwrap();
                decode_alternative(&s) == Ok(num)
            }
        }

        #[cfg(feature = "std")]
        quickcheck! {
            fn encode_io_decode(num: u128) -> bool {
                let mut v = Vec::new();
                encode_io(num, &mut v).unwrap();
                decode(&v) == Ok(num)
            }
        }

        #[cfg(feature = "std")]
        quickcheck! {
            fn encode_alternative_io_decode(num: u128) -> bool {
                let mut v = Vec::new();
                encode_alternative_io(num, &mut v).unwrap();
                decode_alternative(&v) == Ok(num)
            }
        }

        quickcheck! {
            fn encode_buf_decode(num: u128) -> bool {
                let mut s = String::new();
                encode_buf(num, &mut s);
                decode(&s) == Ok(num)
            }
        }

        quickcheck! {
            fn encode_alternative_buf_decode(num: u128) -> bool {
                let mut s = String::new();
                encode_alternative_buf(num, &mut s);
                decode_alternative(&s) == Ok(num)
            }
        }

        quickcheck! {
            fn encode_bytes_decode(num: u128) -> bool {
                let mut buf = [0u8; 22];  // Max size needed for u128
                if let Ok(len) = encode_bytes(num, &mut buf) {
                    decode(&buf[..len]) == Ok(num)
                } else {
                    false
                }
            }
        }

        quickcheck! {
            fn encode_alternative_bytes_decode(num: u128) -> bool {
                let mut buf = [0u8; 22];  // Max size needed for u128
                if let Ok(len) = encode_alternative_bytes(num, &mut buf) {
                    decode_alternative(&buf[..len]) == Ok(num)
                } else {
                    false
                }
            }
        }
    }

    // Pure computation tests that don't need allocation
    #[test]
    fn test_digit_count() {
        for pow in 1..22 {
            let this_power = (BASE as u128).pow(pow as u32);
            assert_eq!(digit_count(this_power - 1), pow);
            assert_eq!(digit_count(this_power), pow + 1);
        }
        assert_eq!(digit_count(0), 1);
        assert_eq!(digit_count(1), 1);
        assert_eq!(digit_count(u64::MAX as u128), 11);
        assert_eq!(digit_count(u64::MAX as u128 + 1), 11);
        assert_eq!(digit_count(u128::MAX), 22);
    }

    #[test]
    fn test_decode_empty_input() {
        assert_eq!(_decode(&[]), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn test_decode_overflow() {
        let long_input = [b'1'; 23];
        assert_eq!(_decode(&long_input), Err(DecodeError::ArithmeticOverflow));
    }

    #[test]
    fn test_decode_invalid_char() {
        assert_eq!(_decode(b"!"), Err(DecodeError::InvalidBase62Byte(b'!', 0)));
    }

    #[test]
    fn test_decode_alternative_empty_input() {
        assert_eq!(_decode_alternative(&[]), Err(DecodeError::EmptyInput));
    }

    #[test]
    fn test_decode_alternative_overflow() {
        let long_input = [b'1'; 23];
        assert_eq!(
            _decode_alternative(&long_input),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_decode_alternative_invalid_char() {
        assert_eq!(
            _decode_alternative(b"!"),
            Err(DecodeError::InvalidBase62Byte(b'!', 0))
        );
    }

    // Tests requiring alloc
    #[cfg(feature = "alloc")]
    mod alloc_tests {
        use alloc::{format, string::ToString};

        use super::*;

        #[test]
        fn test_encode() {
            assert_eq!(encode(u128::MAX), "7n42DGM5Tflk9n8mt7Fhc7");
            assert_eq!(encode(u64::MAX as u128 + 1), "LygHa16AHYG");
            assert_eq!(encode(u64::MAX), "LygHa16AHYF");
            assert_eq!(encode(0_u8), "0");

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
        }

        #[test]
        fn test_encode_buf() {
            let mut buf = String::new();

            buf.push_str("Base62: ");
            encode_buf(10622433094_u64, &mut buf);
            assert_eq!(buf, "Base62: Base62");
            buf.clear();

            encode_buf(u128::MAX, &mut buf);
            assert_eq!(buf, "7n42DGM5Tflk9n8mt7Fhc7");
            buf.clear();
        }

        #[test]
        fn test_encode_fmt() {
            let mut s = String::new();
            encode_fmt(1337_u32, &mut s).unwrap();
            assert_eq!(s, "LZ");
            s.clear();

            encode_fmt(0_u8, &mut s).unwrap();
            assert_eq!(s, "0");
        }

        #[test]
        fn test_encode_alternative() {
            assert_eq!(encode_alternative(u128::MAX), "7N42dgm5tFLK9N8MT7fHC7");
            assert_eq!(encode_alternative(u64::MAX as u128 + 1), "lYGhA16ahyg");
            assert_eq!(encode_alternative(u64::MAX), "lYGhA16ahyf");
            assert_eq!(encode_alternative(0_u8), "0");
        }

        #[test]
        fn test_encode_alternative_buf() {
            let mut buf = String::new();
            buf.push_str("Base62: ");
            encode_alternative_buf(34051405518_u64, &mut buf);
            assert_eq!(buf, "Base62: Base62");
        }

        #[test]
        fn test_encode_alternative_fmt() {
            let mut s = String::new();
            encode_alternative_fmt(1337_u32, &mut s).unwrap();
            assert_eq!(s, "lz");
        }

        #[test]
        fn test_decode() {
            assert_eq!(
                decode("00001000000000000000000000"),
                Ok((BASE as u128).pow(21))
            );
            assert_eq!(decode("7n42DGM5Tflk9n8mt7Fhc7"), Ok(u128::MAX));
            assert_eq!(decode("0"), Ok(0));
            assert_eq!(decode("CAcoUun"), Ok(691337691337));
        }

        #[test]
        fn test_decode_alternative() {
            assert_eq!(decode_alternative("7N42dgm5tFLK9N8MT7fHC7"), Ok(u128::MAX));
            assert_eq!(decode_alternative("0"), Ok(0));
            assert_eq!(decode_alternative("caCOuUN"), Ok(691337691337));
        }
    }

    // Tests requiring std
    #[cfg(feature = "std")]
    mod std_tests {
        use super::*;
        use std::io::Write;

        #[test]
        fn test_encode_io() {
            let mut output = Vec::new();
            encode_io(1337_u32, &mut output).unwrap();
            assert_eq!(output, b"LZ");
            output.clear();

            encode_io(0_u8, &mut output).unwrap();
            assert_eq!(output, b"0");
        }

        #[test]
        fn test_encode_alternative_io() {
            let mut output = Vec::new();
            encode_alternative_io(1337_u32, &mut output).unwrap();
            assert_eq!(output, b"lz");
            output.clear();

            encode_alternative_io(0_u8, &mut output).unwrap();
            assert_eq!(output, b"0");
        }
    }
}
