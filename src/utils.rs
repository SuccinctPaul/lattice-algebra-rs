// Example:
// (11)10 -> (1101 0000)2
pub fn bytes_to_le_bits(bytes: &[u8]) -> Vec<bool> {
    let mut bits = Vec::new();
    for &byte in bytes {
        for i in 0..8 {
            bits.push((byte & (1 << i)) != 0);
        }
    }
    bits
}

// Example:
// (11)10 -> (1101)2 -> (1101 0000)2
pub fn bits_formalize(bits: &[bool]) -> Vec<bool> {
    let mut bits = bits.to_vec();
    while bits.len() % 8 != 0 {
        bits.push(false);
    }
    bits
}

// Example:
// (11)10 -> (1101 0000)2 -> (1101)2
pub fn bits_normalize(bits: &[bool]) -> Vec<bool> {
    let mut bits = bits.to_vec();
    while !bits.last().unwrap_or(&false) {
        bits.pop();
    }
    bits
}

// Example:
//  (1011 0000)2 -> (11)10
pub fn le_bits_to_bytes(bits: &[bool]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for chunk in bits.chunks(8) {
        let mut byte = 0u8;
        for (i, &bit) in chunk.iter().enumerate() {
            if bit {
                byte |= 1 << i;
            }
        }
        bytes.push(byte);
    }
    bytes
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes_to_bits() {
        let bytes = vec![0b01001011, 0b10001110];
        let expected = vec![
            true, true, false, true, false, false, true, false, false, true, true, true, false,
            false, false, true,
        ];
        assert_eq!(bytes_to_le_bits(&bytes), expected);
        let expected = vec![true, true, false, true];
        assert_eq!(bytes_to_le_bits(&vec![11]), bits_formalize(&expected));
        assert_eq!(bits_normalize(&bytes_to_le_bits(&vec![11])), expected);
    }

    #[test]
    fn test_bits_to_bytes() {
        let bits = vec![
            true, true, false, true, false, false, true, false, false, true, true, true, false,
            false, false, true,
        ];
        let expected = vec![0b01001011, 0b10001110];
        assert_eq!(le_bits_to_bytes(&bits), expected);
    }

    #[test]
    fn test_roundtrip_bytes_to_bits_to_bytes() {
        let original_bytes = vec![0xA5, 0x3C, 0xF0];
        let bits = bytes_to_le_bits(&original_bytes);
        let reconstructed_bytes = le_bits_to_bytes(&bits);
        assert_eq!(original_bytes, reconstructed_bytes);
    }

    #[test]
    fn test_roundtrip_bits_to_bytes_to_bits() {
        let original_bits = vec![
            true, false, true, true, false, false, true, false, true, true, true, false, false,
            false, false, true,
        ];
        let bytes = le_bits_to_bytes(&original_bits);
        let reconstructed_bits = bytes_to_le_bits(&bytes);
        assert_eq!(original_bits, reconstructed_bits);
    }
}
