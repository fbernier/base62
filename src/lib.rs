const BASE: u128 = 62;

// How much to add to the least-significant five bits of a byte to get the digit's
// value.
//
// Index 1: decimal digits
// Index 2: uppercase letters
// Index 3: lowercase letters
const STANDARD_OFFSETS: u32 = u32::from_le_bytes([0, -16_i8 as u8, 9, 35]);
const ALTERNATIVE_OFFSETS: u32 = u32::from_le_bytes([0, -16_i8 as u8, 35, 9]);

#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DecodeError {
    InvalidBase62Byte(u8, usize),
    ArithmeticOverflow,
}

impl core::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        match *self {
            DecodeError::InvalidBase62Byte(ch, idx) => {
                use core::fmt::Write;

                f.write_str("Invalid byte b'")?;
                for char_in_escape in core::ascii::escape_default(ch) {
                    f.write_char(char::from(char_in_escape))?;
                }
                write!(f, "' at position {}", idx)
            }
            DecodeError::ArithmeticOverflow => write!(f, "Decoded number is too large"),
        }
    }
}

// Finds out how many base62 digits a value encodes into.
pub(crate) fn digit_count(mut n: u128) -> usize {
    const BASE_TO_2: u128 = BASE.pow(2);
    const BASE_TO_3: u128 = BASE.pow(3);
    const BASE_TO_6: u128 = BASE.pow(6);
    const BASE_TO_11: u128 = BASE.pow(11);

    let mut result = 1;

    if n >= BASE_TO_11 {
        result += 11;
        n /= BASE_TO_11;
    }
    if n >= BASE_TO_6 {
        result += 6;
        n /= BASE_TO_6;
    }
    if n >= BASE_TO_3 {
        result += 3;
        n /= BASE_TO_3;
    }
    if n >= BASE_TO_2 {
        result += 2;
        n /= BASE_TO_2;
    }
    if n >= BASE {
        result += 1;
    }

    result
}

macro_rules! internal_encoder_fn {
    ($fn_name:ident, $numeric_offset:literal, $first_letters_offset:literal, $last_letters_offset:literal) => {
        // # Safety
        //
        // With this function, `buf` MUST ALREADY have its capacity extended
        // to hold all the new base62 characters that will be added
        unsafe fn $fn_name(mut num: u128, digits: usize, buf: &mut String) {
            let buf_vec = buf.as_mut_vec();
            let new_len = buf_vec.len().wrapping_add(digits);
            let mut ptr = buf_vec.as_mut_ptr().add(new_len.wrapping_sub(1));

            for _ in 0..digits {
                ::core::ptr::write(ptr, {
                    let digit = (num % $crate::BASE) as u8;
                    match digit {
                        0..=9 => digit.wrapping_add($numeric_offset),
                        10..=35 => digit.wrapping_add($first_letters_offset),
                        _ => digit.wrapping_add($last_letters_offset),
                    }
                });
                ptr = ptr.sub(1);

                num /= $crate::BASE;
            }

            buf_vec.set_len(new_len);
        }
    };
}

// # Safety
//
// With these functions, `buf` MUST ALREADY have its capacity extended
// to hold all the new base62 characters that will be added
internal_encoder_fn!(_encode_buf, 48, 55, 61);
internal_encoder_fn!(_encode_alternative_buf, 48, 87, 29);

/// Encodes a uint into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), and returns the resulting `String`.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let b62 = base62::encode(1337_u32);
///     assert_eq!(b62, "LZ");
/// }
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

/// Appends a uint encoded into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), onto the end of a `String`.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let mut buf = String::new();
///     base62::encode_buf(1337_u32, &mut buf);
///     assert_eq!(buf, "LZ");
/// }
/// ```
pub fn encode_buf<T: Into<u128>>(num: T, buf: &mut String) {
    let num = num.into();
    let digits = digit_count(num);
    buf.reserve(digits);
    unsafe {
        _encode_buf(num, digits, buf);
    }
}

/// Encodes a uint into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z) with lowercase letters before uppercase letters,
/// and returns the resulting `String`.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let b62 = base62::encode(1337_u32);
///     assert_eq!(b62, "LZ");
/// }
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

/// Appends a uint encoded into base62, using the alternative digit ordering
/// (0 to 9, then a to z, then A to Z) with lowercase letters before uppercase letters,
/// onto the end of a `String`.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let mut buf = String::new();
///     base62::encode_alternative_buf(1337_u32, &mut buf);
///     assert_eq!(buf, "lz");
/// }
/// ```
pub fn encode_alternative_buf<T: Into<u128>>(num: T, buf: &mut String) {
    let num = num.into();
    let digits = digit_count(num);
    buf.reserve(digits);
    unsafe {
        _encode_alternative_buf(num, digits, buf);
    }
}

macro_rules! internal_decoder_fn {
    ($fn_name:ident, $offsets:ident) => {
        fn $fn_name(input: &[u8]) -> Result<u128, DecodeError> {
            let mut result = 0_u128;
            for (i, &ch) in input.iter().enumerate() {
                if ch.is_ascii_alphanumeric() {
                    result = result
                        .checked_mul(BASE)
                        .and_then(|x| {
                            x.checked_add((ch & 0b0001_1111).wrapping_add(
                                $offsets.wrapping_shr((ch.wrapping_shr(2) & 0b0001_1000) as u32)
                                    as u8,
                            ) as u128)
                        })
                        .ok_or($crate::DecodeError::ArithmeticOverflow)?
                } else {
                    return Err($crate::DecodeError::InvalidBase62Byte(ch, i));
                }
            }

            Ok(result)
        }
    };
}

internal_decoder_fn!(_decode, STANDARD_OFFSETS);
internal_decoder_fn!(_decode_alternative, ALTERNATIVE_OFFSETS);

/// Decodes a base62 byte slice or an equivalent like a `String` using the standard
/// digit ordering (0 to 9, then A to Z, then a to z).
///
/// Returns a Result containing a `u128`, which can be downcasted to any other uint.
///
/// # Examples
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let value = base62::decode("rustlang").unwrap();
///     assert_eq!(value, 189876682536016);
/// }
/// ```
#[must_use = "this returns the decoded result without modifying the original"]
pub fn decode<T: AsRef<[u8]>>(input: T) -> Result<u128, DecodeError> {
    _decode(input.as_ref())
}

/// Decodes a base62 byte slice or an equivalent like a `String` using the alternative
/// digit ordering (0 to 9, then a to z, then A to Z) with lowercase letters before
/// uppercase letters.
///
/// Returns a Result containing a `u128`, which can be downcasted to any other uint.
///
/// # Examples
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let value = base62::decode_alternative("rustlang").unwrap();
///     assert_eq!(value, 96813686712946);
/// }
/// ```
#[must_use = "this returns the decoded result without modifying the original"]
pub fn decode_alternative<T: AsRef<[u8]>>(input: T) -> Result<u128, DecodeError> {
    _decode_alternative(input.as_ref())
}

#[cfg(test)]
mod tests {
    use super::*;
    use quickcheck::{quickcheck, TestResult};

    quickcheck! {
        fn encode_decode(xs: u128) -> bool {
            let encoded = encode(xs);
            xs == decode(&encoded).unwrap()
        }
    }

    quickcheck! {
        fn decode_good(xs: String) -> TestResult {
            if xs.chars().all(|ch| ch.is_ascii_alphanumeric()) && !xs.is_empty() {
                TestResult::from_bool(decode(&xs).is_ok())
            } else {
                TestResult::discard()
            }
        }
    }

    quickcheck! {
        fn decode_bad(xs: String) -> TestResult {
            if xs.chars().all(|ch| ch.is_ascii_alphanumeric()) {
                TestResult::discard()
            } else {
                TestResult::from_bool(decode(&xs).is_err())
            }
        }
    }

    #[test]
    fn test_encode() {
        assert_eq!(encode(u128::MAX), "7n42DGM5Tflk9n8mt7Fhc7");
        assert_eq!(encode(0_u8), "0");
    }

    #[test]
    fn test_encode_buf() {
        let mut buf = String::new();
        encode_buf(u128::MAX, &mut buf);
        assert_eq!(buf, "7n42DGM5Tflk9n8mt7Fhc7");
    }

    #[test]
    fn test_encode_alternative() {
        assert_eq!(encode_alternative(691337691337_u128), "caCOuUN");
        assert_eq!(encode_alternative(0_u8), "0");
    }

    #[test]
    fn test_encode_alternative_buf() {
        let mut buf = String::new();
        encode_alternative_buf(691337691337_u128, &mut buf);
        assert_eq!(buf, "caCOuUN");
    }

    #[test]
    fn test_decode() {
        assert_eq!(decode("7n42DGM5Tflk9n8mt7Fhc7").unwrap(), u128::MAX);
        assert_eq!(decode("").unwrap(), 0);
    }

    #[test]
    fn test_decode_invalid_char() {
        assert_eq!(
            decode("ds{Z455f"),
            Err(DecodeError::InvalidBase62Byte(b'{', 2))
        );
    }

    #[test]
    fn test_decode_long_string() {
        assert_eq!(
            decode("7n42DGM5Tflk9n8mt7Fhc78"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_decode_alternative() {
        assert_eq!(
            decode_alternative("7N42dgm5tFLK9N8MT7fHC7").unwrap(),
            u128::MAX
        );
        assert_eq!(decode_alternative("").unwrap(), 0);
    }

    #[test]
    fn test_decode_alternative_invalid_char() {
        assert_eq!(
            decode_alternative("ds{Z455f"),
            Err(DecodeError::InvalidBase62Byte(b'{', 2))
        );
    }

    #[test]
    fn test_decode_alternative_long_string() {
        assert_eq!(
            decode_alternative("7N42dgm5tFLK9N8MT7fHC8"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }

    #[test]
    fn test_digit_count() {
        // The maximum length of a base62-encoded `u128`.
        let max_encoded_len: usize = core::iter::successors(Some(u128::MAX), |&n| Some(n / BASE))
            .take_while(|&n| n != 0)
            .count();

        // Assume that `digit_count` is a monotonically increasing function and
        // check that the boundaries have the right values.
        assert_eq!(digit_count(0), 1);
        assert_eq!(digit_count(BASE.pow(0)), 1);
        for pow in 1..max_encoded_len {
            let this_power = BASE.pow(pow as u32);

            assert_eq!(digit_count(this_power - 1), pow);
            assert_eq!(digit_count(this_power), pow + 1);
        }
        assert_eq!(digit_count(u128::MAX), 22);
    }
}
