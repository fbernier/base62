pub use self::DecodeError::*;
use std::fmt;

pub const ORDERED: Flavor = Flavor::Ordered(Ordered {});
pub const REVERSED: Flavor = Flavor::Reversed(Reversed {});

const BASE: u128 = 62;
const MAX_DECODED_LEN: usize = 111;

pub struct Ordered {}
pub struct Reversed {}
pub enum Flavor {
    Ordered(Ordered),
    Reversed(Reversed),
}

impl Flavor {
    fn alphabet(&self) -> [u8; BASE as usize] {
        match self {
            Flavor::Ordered(f) => f.alphabet(),
            Flavor::Reversed(f) => f.alphabet(),
        }
    }
}

trait Alphabet {
    fn alphabet(&self) -> [u8; BASE as usize];
}

impl Alphabet for Ordered {
    fn alphabet(&self) -> [u8; BASE as usize] {
        [
            b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'A', b'B', b'C', b'D',
            b'E', b'F', b'G', b'H', b'I', b'J', b'K', b'L', b'M', b'N', b'O', b'P', b'Q', b'R',
            b'S', b'T', b'U', b'V', b'W', b'X', b'Y', b'Z', b'a', b'b', b'c', b'd', b'e', b'f',
            b'g', b'h', b'i', b'j', b'k', b'l', b'm', b'n', b'o', b'p', b'q', b'r', b's', b't',
            b'u', b'v', b'w', b'x', b'y', b'z',
        ]
    }
}

impl Alphabet for Reversed {
    fn alphabet(&self) -> [u8; BASE as usize] {
        [
            b'0', b'1', b'2', b'3', b'4', b'5', b'6', b'7', b'8', b'9', b'a', b'b', b'c', b'd',
            b'e', b'f', b'g', b'h', b'i', b'j', b'k', b'l', b'm', b'n', b'o', b'p', b'q', b'r',
            b's', b't', b'u', b'v', b'w', b'x', b'y', b'z', b'A', b'B', b'C', b'D', b'E', b'F',
            b'G', b'H', b'I', b'J', b'K', b'L', b'M', b'N', b'O', b'P', b'Q', b'R', b'S', b'T',
            b'U', b'V', b'W', b'X', b'Y', b'Z',
        ]
    }
}

#[derive(PartialEq)]
pub enum DecodeError {
    InvalidBase62Byte(char, usize),
    ArithmeticOverflow,
}

impl fmt::Debug for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            InvalidBase62Byte(ch, idx) => {
                write!(f, "Invalid character '{}' at position {}", ch, idx)
            }
            ArithmeticOverflow => write!(f, "Decode result is too large"),
        }
    }
}

impl fmt::Display for DecodeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self, f)
    }
}

/// Encode any uint as base64.
/// Returns a String.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let b62 = base62::encode(1337u32);
///     println!("{}", b62);
/// }
/// ```
#[must_use]
pub fn encode<T: Into<u128>>(num: T) -> String {
    _encode(num.into(), Flavor::Ordered(Ordered {}))
}

#[must_use]
pub fn encode_config<T: Into<u128>>(num: T, flavor: Flavor) -> String {
    _encode(num.into(), flavor)
}

#[inline]
fn _encode(num: u128, flavor: Flavor) -> String {
    let mut buf = String::with_capacity(MAX_DECODED_LEN);
    encode_config_buf(num, flavor, &mut buf);
    buf
}

/// Encode any uint as base64.
/// Writes into the supplied output buffer, which will grow the buffer if needed.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let mut buf = String::new();
///     base62::encode_buf(1337u32, &mut buf);
///     println!("{}", buf);
/// }
/// ```
pub fn encode_buf<T: Into<u128>>(num: T, buf: &mut String) {
    _encode_buf(num.into(), ORDERED, buf)
}

pub fn encode_config_buf<T: Into<u128>>(num: T, flavor: Flavor, buf: &mut String) {
    _encode_buf(num.into(), flavor, buf)
}

#[inline(always)]
fn _encode_buf(mut num: u128, flavor: Flavor, buf: &mut String) {
    if num == 0 {
        *buf = "0".to_owned();
        return;
    }
    let mut bytes: [u8; MAX_DECODED_LEN] = [0; MAX_DECODED_LEN];

    let mut i: usize = MAX_DECODED_LEN;
    loop {
        if num == 0 {
            break;
        }
        i -= 1;

        bytes[i] = flavor.alphabet()[(num % BASE) as usize];
        num /= BASE;
    }

    unsafe {
        *buf = std::str::from_utf8_unchecked(&bytes[i..MAX_DECODED_LEN]).to_owned();
    }
}

/// Decode from string reference as octets.
/// Returns a Result containing a u128 which can be downcasted to any other uint.
///
/// # Example
///
/// ```rust
/// extern crate base62;
///
/// fn main() {
///     let bytes = base62::decode("rustlang").unwrap();
///     println!("{:?}", bytes);
/// }
/// ```
pub fn decode<T: AsRef<[u8]>>(input: T) -> Result<u128, DecodeError> {
    _decode(input.as_ref(), ORDERED)
}

pub fn decode_config<T: AsRef<[u8]>>(input: T, flavor: Flavor) -> Result<u128, DecodeError> {
    _decode(input.as_ref(), flavor)
}

#[inline(always)]
fn _decode(input: &[u8], flavor: Flavor) -> Result<u128, DecodeError> {
    let mut result = 0u128;

    for (i, c) in input.iter().rev().enumerate() {
        let num = BASE.checked_pow(i as u32).ok_or(ArithmeticOverflow)?;
        match flavor.alphabet().iter().position(|x| x == c) {
            Some(v) => match (v as u128).checked_mul(num) {
                Some(z) => result = result.checked_add(z as u128).ok_or(ArithmeticOverflow)?,
                None => return Err(ArithmeticOverflow),
            },
            None => {
                return Err(InvalidBase62Byte(c.to_owned() as char, input.len() - i));
            }
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use crate::base62::*;
    use quickcheck::{quickcheck, TestResult};

    quickcheck! {
        fn encode_decode(xs: u128) -> bool {
            let encoded = encode(xs);
            xs == decode(&encoded).unwrap()
        }
    }

    quickcheck! {
        fn decode_good(xs: String) -> TestResult {
            if xs.chars().all(|c| c.is_ascii() && Flavor::alphabet(&ORDERED).iter().position(|x| *x == c as u8).is_some()) && !xs.is_empty() {
                return TestResult::from_bool(decode(&xs).is_ok());
            } else {
                TestResult::discard()
            }
        }
    }

    quickcheck! {
        fn decode_bad(xs: String) -> TestResult {
            if xs.chars().all(|c| c.is_ascii() && Flavor::alphabet(&ORDERED).iter().position(|x| *x == c as u8).is_some()) {
                TestResult::discard()
            } else {
                return TestResult::from_bool(decode(&xs).is_err());
            }
        }
    }

    #[test]
    fn test_encode() {
        assert_eq!(encode(u128::MAX), "7n42DGM5Tflk9n8mt7Fhc7");
        assert_eq!(encode(0u8), "0");
    }

    #[test]
    fn test_encode_config() {
        assert_eq!(encode_config(691337691337u128, REVERSED), "caCOuUN");
        assert_eq!(encode_config(0u8, REVERSED), "0");
    }

    #[test]
    fn test_encode_buf() {
        let mut buf = String::new();
        encode_buf(u128::MAX, &mut buf);
        assert_eq!(buf, "7n42DGM5Tflk9n8mt7Fhc7");
    }

    #[test]
    fn test_encode_config_buf() {
        let mut buf = String::new();
        encode_config_buf(691337691337u128, REVERSED, &mut buf);
        assert_eq!(buf, "caCOuUN");
    }

    #[test]
    fn test_decode() {
        assert_eq!(decode("7n42DGM5Tflk9n8mt7Fhc7").unwrap(), u128::MAX);
        assert_eq!(decode("").unwrap(), 0);
    }

    #[test]
    fn test_decode_config() {
        assert_eq!(
            decode_config("7N42dgm5tFLK9N8MT7fHC7", REVERSED).unwrap(),
            u128::MAX
        );
        assert_eq!(decode_config("", REVERSED).unwrap(), 0);
    }

    #[test]
    fn test_decode_invalid_char() {
        assert_eq!(
            decode("ds{Z455f"),
            Err(DecodeError::InvalidBase62Byte('{', 3))
        );
    }

    #[test]
    fn test_decode_long_string() {
        assert_eq!(
            decode("7n42DGM5Tflk9n8mt7Fhc7B"),
            Err(DecodeError::ArithmeticOverflow)
        );
    }
}
