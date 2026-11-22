//! Nonrecursive transport profile for the pinned SDK's bincode receipts.
//! The ASK guest uses no receipt assumptions. Reject those before the SDK's
//! recursive deserializer can allocate or recurse into attacker input.
//! All proof verification still belongs to the unmodified RISC Zero SDK.
use bincode::Options;
use risc0_zkvm::{Receipt, SegmentReceipt};
use std::io::Cursor;

pub const MAX_RECEIPT: u64 = 512 * 1024 * 1024;
const MAX_SEGMENTS: u64 = 1024;

fn error(message: &str) -> bincode::Error {
    Box::new(bincode::ErrorKind::Custom(message.to_owned()))
}

fn options() -> impl Options {
    bincode::DefaultOptions::new().with_fixint_encoding()
        .with_limit(MAX_RECEIPT).reject_trailing_bytes()
}

pub fn decode_receipt(bytes: &[u8]) -> Result<Receipt, bincode::Error> {
    if bytes.len() as u64 > MAX_RECEIPT {
        return Err(error("receipt exceeds byte limit"));
    }
    let mut input = Cursor::new(bytes);
    // These discriminants and field order are pinned by risc0-zkvm 3.1.0
    // and bincode 1.3.3. An SDK update requires reviewing this envelope.
    let variant: u32 = options().deserialize_from(&mut input)?;
    match variant {
        0 => {
            let count: u64 = options().deserialize_from(&mut input)?;
            if count == 0 || count > MAX_SEGMENTS {
                return Err(error("composite segment count outside the supported profile"));
            }
            for _ in 0..count {
                // The SDK SegmentReceipt and its ReceiptClaim contain no
                // nested receipt types. Decode one at a time, then release it.
                let _: SegmentReceipt = options().deserialize_from(&mut input)?;
            }
            let assumptions: u64 = options().deserialize_from(&mut input)?;
            if assumptions != 0 {
                return Err(error("receipt assumptions are outside the ASK profile"));
            }
        }
        1 | 2 => {}, // Succinct and Groth16 receipt structures are nonrecursive.
        3 => return Err(error("development receipts are refused")),
        _ => return Err(error("unsupported receipt variant")),
    }
    options().deserialize(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{sha::Digest, ReceiptClaim};

    fn segment() -> Vec<u8> {
        bincode::serialize(&(Vec::<u32>::new(), 0u32, String::new(), Digest::ZERO,
            ReceiptClaim::ok(Digest::ZERO, Vec::new()))).unwrap()
    }

    fn composite(assumptions: u64) -> Vec<u8> {
        let mut bytes = bincode::serialize(&(0u32, 1u64)).unwrap();
        bytes.extend(segment());
        bytes.extend(assumptions.to_le_bytes());
        bytes
    }

    #[test]
    fn flat_sdk_wire_roundtrip_and_trailing_byte_refusal() {
        let mut bytes = composite(0);
        bytes.extend(bincode::serialize(&(Digest::ZERO, Vec::<u8>::new(), Digest::ZERO)).unwrap());
        let receipt = decode_receipt(&bytes).unwrap();
        assert_eq!(receipt.inner.composite().unwrap().segments.len(), 1);
        assert_eq!(bincode::serialize(&receipt).unwrap(), bytes);
        // This is a wire fixture with an empty seal, not a cryptographic proof.
        assert!(receipt.verify(Digest::ZERO).is_err());
        bytes.push(0);
        assert!(decode_receipt(&bytes).is_err());
    }

    #[test]
    fn recursive_assumptions_refused_before_decoding() {
        let mut bytes = composite(1);
        for _ in 0..20_000 {
            bytes.extend(bincode::serialize(&(0u32, 0u64, 1u64)).unwrap());
        }
        let message = decode_receipt(&bytes).unwrap_err().to_string();
        assert!(message.contains("assumptions are outside"));
    }

    #[test]
    fn empty_or_excessive_segment_lists_refused() {
        for count in [0, MAX_SEGMENTS + 1, u64::MAX] {
            assert!(decode_receipt(&bincode::serialize(&(0u32, count)).unwrap()).is_err());
        }
    }

    #[test]
    fn fake_unknown_and_truncated_variants_refused() {
        for tag in [3u32, 4, u32::MAX] {
            assert!(decode_receipt(&tag.to_le_bytes()).is_err());
        }
        assert!(decode_receipt(&[]).is_err());
        assert!(decode_receipt(&[0; 3]).is_err());
    }
}
