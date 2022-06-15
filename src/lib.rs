const BASE: u64 = 62;
const BASE_TO_2: u64 = BASE.pow(2);
const BASE_TO_3: u64 = BASE.pow(3);
const BASE_TO_6: u128 = (BASE as u128).pow(6);
const BASE_TO_10: u64 = BASE.pow(10);
const BASE_TO_11: u128 = (BASE as u128).pow(11);

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
    let mut result = 1;

    if n >= BASE_TO_11 {
        result += 11;
        n /= BASE_TO_11;
    }
    if n >= BASE_TO_6 {
        result += 6;
        n /= BASE_TO_6;
    }
    let mut n = n as u64;
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

            let mut digit_index = 0_usize;
            let mut u64_num = (num % ($crate::BASE_TO_10 as u128)) as u64;
            num /= $crate::BASE_TO_10 as u128;
            loop {
                ::core::ptr::write(ptr, {
                    let digit = (u64_num % $crate::BASE) as u8;
                    match digit {
                        0..=9 => digit.wrapping_add($numeric_offset),
                        10..=35 => digit.wrapping_add($first_letters_offset),
                        _ => digit.wrapping_add($last_letters_offset),
                    }
                });
                ptr = ptr.sub(1);

                digit_index = digit_index.wrapping_add(1);
                match digit_index {
                    _ if digit_index == digits => break,
                    10 => {
                        u64_num = (num % ($crate::BASE_TO_10 as u128)) as u64;
                        num /= $crate::BASE_TO_10 as u128;
                    }
                    20 => u64_num = num as u64,
                    _ => u64_num /= $crate::BASE,
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

/// Appends a uint encoded into base62, using the standard digit ordering
/// (0 to 9, then A to Z, then a to z), onto the end of a `String`.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// let mut buf = String::new();
/// base62::encode_buf(1337_u32, &mut buf);
/// assert_eq!(buf, "LZ");
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
/// let b62 = base62::encode(1337_u32);
/// assert_eq!(b62, "LZ");
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
/// let mut buf = String::new();
/// base62::encode_alternative_buf(1337_u32, &mut buf);
/// assert_eq!(buf, "lz");
/// ```
pub fn encode_alternative_buf<T: Into<u128>>(num: T, buf: &mut String) {
    let num = num.into();
    let digits = digit_count(num);
    buf.reserve(digits);
    unsafe {
        _encode_alternative_buf(num, digits, buf);
    }
}

macro_rules! internal_decoder_loop_body {
    ($offsets:ident, $uint:ty, $result:ident, $ch:ident, $i:ident) => {
        if $ch.is_ascii_alphanumeric() {
            $result = $result
                .checked_mul(BASE as $uint)
                .and_then(|x| {
                    x.checked_add(($ch & 0b0001_1111).wrapping_add(
                        $offsets.wrapping_shr(($ch.wrapping_shr(2) & 0b0001_1000) as u32) as u8,
                    ) as $uint)
                })
                .ok_or($crate::DecodeError::ArithmeticOverflow)?
        } else {
            return Err($crate::DecodeError::InvalidBase62Byte($ch, $i));
        }
    };
}

macro_rules! internal_decoder_fn {
    ($fn_name:ident, $offsets:ident) => {
        fn $fn_name(input: &[u8]) -> Result<u128, DecodeError> {
            let mut result = 0_u64;
            let mut iter = input.iter().copied().enumerate();
            for (i, ch) in iter.by_ref().take(10) {
                internal_decoder_loop_body!($offsets, u64, result, ch, i);
            }

            let mut result = result as u128;
            for (i, ch) in iter {
                internal_decoder_loop_body!($offsets, u128, result, ch, i)
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
/// let value = base62::decode("rustlang").unwrap();
/// assert_eq!(value, 189876682536016);
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
/// let value = base62::decode_alternative("rustlang").unwrap();
/// assert_eq!(value, 96813686712946);
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
            Ok(xs) == decode(&encoded)
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
            power *= 62;
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
            power *= 62;
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
            power *= 62;
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
            power *= 62;
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
        // Test empty base62 string
        assert_eq!(decode(""), Ok(0));

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
            power *= 62;
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
        // Test empty base62 string
        assert_eq!(decode_alternative(""), Ok(0));

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
            power *= 62;
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
