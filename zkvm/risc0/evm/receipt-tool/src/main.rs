//! Local byte transport around the unmodified pinned RISC Zero SDK.
//! No RDF/query semantics, alternative crypto primitive or remote proving client.
//! Final receipts are verified before publication; development receipts are refused.
use anyhow::{bail, ensure, Context, Result};
#[path = "../../../receipt_format.rs"]
mod receipt_format;
use hex::FromHex;
use risc0_groth16::{ProofJson, Seal};
use risc0_zkp::core::hash::poseidon_254::Poseidon254HashSuite;
use risc0_zkvm::{
    sha::{Digest, Digestible}, ApiClient, AssetRequest, ExternalProver, Groth16Receipt,
    Groth16ReceiptVerifierParameters, InnerReceipt, Prover, ProverOpts, Receipt,
    SuccinctReceiptVerifierParameters, VerifierContext,
};
use serde_json::json;
use std::{env, fs, io::{Read, Write}, path::Path, process::Command};

use receipt_format::MAX_RECEIPT;
const PARAMS_HEX: &str = "e71e6620a834f4d8dc1998476b865a9a6437a14474f9442cf8664f9ec22a5eee";

fn bounded_read(path: &Path, max: u64) -> Result<Vec<u8>> {
    let file = fs::File::open(path).with_context(|| format!("open {}", path.display()))?;
    ensure!(file.metadata()?.len() <= max, "file exceeds size limit");
    let mut bytes = Vec::new();
    file.take(max + 1).read_to_end(&mut bytes)?;
    ensure!(bytes.len() as u64 <= max, "file grew past size limit");
    Ok(bytes)
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)] {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    let mut file = options.open(path).with_context(|| format!("create {}", path.display()))?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

fn read_receipt(path: &Path) -> Result<Receipt> {
    Ok(receipt_format::decode_receipt(&bounded_read(path, MAX_RECEIPT)?)?)
}

fn verify_binding(receipt: &Receipt, image: Digest, expected: &[u8]) -> Result<()> {
    ensure!(!matches!(receipt.inner, InnerReceipt::Fake(_)), "development receipt refused");
    receipt.verify(image).context("cryptographic receipt/image/journal verification failed")?;
    ensure!(receipt.journal.bytes == expected, "receipt journal differs from authorised bytes");
    Ok(())
}

fn require_ask_true(journal: &[u8]) -> Result<()> {
    ensure!(journal.len() == 128, "ASK v1 journal must be exactly 128 bytes");
    ensure!(journal[96..127].iter().all(|byte| *byte == 0), "noncanonical ABI Boolean padding");
    ensure!(journal[127] <= 1, "noncanonical ABI Boolean value");
    ensure!(journal[127] == 1, "authorised ASK result must be true");
    Ok(())
}

fn encode_verified_seal(receipt: &Receipt) -> Result<Vec<u8>> {
    let InnerReceipt::Groth16(inner) = &receipt.inner else { bail!("only real Groth16 receipts can be exported") };
    ensure!(inner.verifier_parameters == Groth16ReceiptVerifierParameters::default().digest(),
        "receipt does not use the patched 3.1 verifier parameters");
    ensure!(inner.seal.len() == 256, "unexpected Groth16 seal length");
    // Exact byte transport from official risc0-ethereum v3.1.0 encode_seal:
    // first four bytes of the parameter digest, then the SDK's 256-byte seal.
    // Verification happens before this function; no curve arithmetic is implemented here.
    let mut seal = inner.verifier_parameters.as_bytes()[..4].to_vec();
    seal.extend_from_slice(&inner.seal);
    ensure!(seal[..4] == [0xe7, 0x1e, 0x66, 0x20], "wrong verifier selector");
    Ok(seal)
}

fn identity_verifier_parameters() -> SuccinctReceiptVerifierParameters {
    let groth_params = Groth16ReceiptVerifierParameters::default();
    let suite = Poseidon254HashSuite::new_suite();
    // SDK 3.1.0 host/api/tests.rs verifies identity_p254 against
    // MerkleGroup([BN254_IDENTITY_CONTROL_ID]).calc_root(Poseidon254).
    // receipt/merkle.rs fixes that tree at depth eight, padding missing
    // leaves with Digest::ZERO. MerkleGroup is only publicly exported with
    // the prover feature; derive this fixed root using the SDK's hash_pair.
    // All inputs are pinned SDK constants, never returned receipt metadata.
    let mut root = groth_params.bn254_control_id;
    let mut empty = Digest::ZERO;
    for _ in 0..8 {
        root = *suite.hashfn.hash_pair(&root, &empty);
        empty = *suite.hashfn.hash_pair(&empty, &empty);
    }
    SuccinctReceiptVerifierParameters {
        control_root: root,
        inner_control_root: Some(groth_params.control_root),
        ..Default::default()
    }
}

fn prepare(image: Digest, receipt: &Receipt, expected: &[u8], r0vm: &Path, output: &Path) -> Result<()> {
    ensure!(!output.exists(), "prepare output directory already exists");
    let version = Command::new(r0vm).arg("--version").output()?;
    ensure!(version.status.success() && String::from_utf8(version.stdout)?.trim() == "risc0-r0vm 3.1.0",
        "local r0vm must be exactly version 3.1.0");
    verify_binding(receipt, image, expected)?;
    ensure!(!matches!(receipt.inner, InnerReceipt::Groth16(_)), "receipt is already Groth16");
    // std::fs::File::lock uses flock on this Linux host, sharing the same lock
    // as the standalone CPU prover runner and the parent guest proof process.
    let proof_lock = fs::OpenOptions::new().create(true).append(true)
        .open("/tmp/factoidal-zk-prove.lock")?;
    println!("Waiting for shared local proving lock: /tmp/factoidal-zk-prove.lock");
    proof_lock.lock()?;
    println!("Acquired shared proving lock; starting local succinct compression");
    let local = ExternalProver::new("pinned-local-r0vm", r0vm);
    let succinct = local.compress(&ProverOpts::succinct(), receipt)?;
    verify_binding(&succinct, image, expected)?;
    let InnerReceipt::Succinct(inner) = &succinct.inner else { bail!("expected real succinct receipt") };
    fs::create_dir(output)?;
    #[cfg(unix)] {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(output, fs::Permissions::from_mode(0o700))?;
    }
    write_new(&output.join("succinct.receipt"), &bincode::serialize(&succinct)?)?;
    println!("Checkpointed verified succinct receipt at {}", output.join("succinct.receipt").display());
    println!("Starting local identity_p254 conversion");
    let client = ApiClient::new_sub_process(r0vm)?;
    let identity = client.identity_p254(&ProverOpts::succinct(), inner.clone().try_into()?, AssetRequest::Inline)?;

    // identity_p254 has its own one-program control root and retains the trusted
    // inner recursion root. Derive both from pinned SDK constants, never receipt metadata.
    let mut context = VerifierContext::empty()
        .with_succinct_verifier_parameters(identity_verifier_parameters());
    // identity_p254 serialises the wire name "poseidon_254". The suite's
    // descriptive .name is "poseidon254", which is not this lookup key.
    context.suites.insert("poseidon_254".into(), Poseidon254HashSuite::new_suite());
    identity.verify_integrity_with_context(&context).context("identity_p254 verification failed")?;
    ensure!(identity.claim.digest() == receipt.claim()?.digest(), "identity_p254 changed the claim");

    let identity_bytes = identity.get_seal_bytes();
    write_new(&output.join("identity.seal"), &identity_bytes)?;
    write_new(&output.join("identity.receipt"), &bincode::serialize(&identity)?)?;
    println!("Checkpointed verified identity_p254 receipt at {}", output.join("identity.receipt").display());
    let inputs = risc0_groth16::prove::to_json(&identity_bytes)?;
    write_new(&output.join("input.json"), inputs.as_bytes())?;
    println!("Verified succinct and identity_p254 proofs; official CPU prover input prepared");
    Ok(())
}

fn main() -> Result<()> {
    ensure!(risc0_zkvm::VERSION == "3.1.0", "wrong SDK version");
    ensure!(Groth16ReceiptVerifierParameters::default().digest().to_string() == PARAMS_HEX,
        "unexpected verifier parameters in SDK");
    let args: Vec<_> = env::args().collect();
    let action = args.get(1).map(String::as_str).unwrap_or("");
    if action == "parameters" && args.len() == 2 {
        println!("sdk=3.1.0 groth16=3.0.6 parameters={PARAMS_HEX}");
        return Ok(());
    }
    if action == "statement" && args.len() == 5 {
        let image = Digest::from_hex(args[2].trim_start_matches("0x"))?;
        let journal = bounded_read(Path::new(&args[3]), 128)?;
        require_ask_true(&journal)?;
        let statement = json!({"imageId":format!("0x{image}"), "journal":format!("0x{}",hex::encode(journal))});
        write_new(Path::new(&args[4]), serde_json::to_string_pretty(&statement)?.as_bytes())?;
        return Ok(());
    }
    ensure!(args.len() >= 5, "usage: parameters | statement IMAGE EXPECTED_JOURNAL OUT.json | prepare IMAGE RECEIPT EXPECTED_JOURNAL R0VM NEW_DIRECTORY | finish IMAGE RECEIPT EXPECTED_JOURNAL PROOF.json OUT.receipt | export IMAGE RECEIPT EXPECTED_JOURNAL OUT.json");
    let image = Digest::from_hex(args[2].trim_start_matches("0x"))?;
    let receipt = read_receipt(Path::new(&args[3]))?;
    let expected = bounded_read(Path::new(&args[4]), 65536)?;
    verify_binding(&receipt, image, &expected)?;
    match action {
        "prepare" if args.len() == 7 => prepare(image, &receipt, &expected, Path::new(&args[5]), Path::new(&args[6])),
        "finish" if args.len() == 7 => {
            let proof: ProofJson = serde_json::from_slice(&bounded_read(Path::new(&args[5]), 1024 * 1024)?)?;
            let seal: Seal = proof.try_into()?;
            let inner = Groth16Receipt::new(seal.to_vec(), receipt.claim()?, Groth16ReceiptVerifierParameters::default().digest());
            let finished = Receipt::new(InnerReceipt::Groth16(inner), receipt.journal.bytes.clone());
            verify_binding(&finished, image, &expected).context("refusing unverified Groth16 output")?;
            encode_verified_seal(&finished)?;
            write_new(Path::new(&args[6]), &bincode::serialize(&finished)?)?;
            println!("Verified genuine Groth16 receipt for image={image}");
            Ok(())
        }
        "export" if args.len() == 6 => {
            require_ask_true(&expected)?;
            let seal = encode_verified_seal(&receipt)?;
            let exported = json!({
                "schema":"factoidal.ask.evm.v1", "sdk":"3.1.0", "receiptKind":"groth16",
                "imageId":format!("0x{image}"), "journal":format!("0x{}",hex::encode(expected)),
                "seal":format!("0x{}",hex::encode(seal)), "verifierParameters":format!("0x{PARAMS_HEX}")
            });
            write_new(Path::new(&args[5]), serde_json::to_string_pretty(&exported)?.as_bytes())?;
            println!("Exported verified ASK v1 Groth16 seal and journal");
            Ok(())
        }
        _ => bail!("invalid action or arguments"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};

    #[test]
    fn identity_context_uses_the_pinned_merkle_root_not_its_leaf() {
        let params = identity_verifier_parameters();
        assert_ne!(params.control_root, Groth16ReceiptVerifierParameters::default().bn254_control_id);
        // Independently observed from the official 3.1.0 identity producer.
        // The previous direct-leaf construction produced df670d44... and
        // correctly failed integrity verification on the first real ASK run.
        assert_eq!(params.digest().to_string(),
            "8dfe5a6be7860f94a46ad4dd69483b3d2b11ea9bae656e86027e893879586b6b");
    }

    #[test]
    fn true_gate_requires_exact_canonical_abi() {
        let mut journal = vec![0; 128];
        assert!(require_ask_true(&journal).is_err());
        journal[127] = 1;
        assert!(require_ask_true(&journal).is_ok());
        journal[96] = 1;
        assert!(require_ask_true(&journal).is_err());
        journal[96] = 0;
        journal[127] = 2;
        assert!(require_ask_true(&journal).is_err());
        assert!(require_ask_true(&[0;127]).is_err());
        assert!(require_ask_true(&[0;129]).is_err());
    }

    #[test]
    fn development_receipt_is_rejected() {
        let image = Digest::ZERO;
        let receipt = Receipt::new(InnerReceipt::Fake(FakeReceipt::new(ReceiptClaim::ok(image, vec![]))), vec![]);
        assert!(verify_binding(&receipt, image, &[]).is_err());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn shared_proving_lock_interoperates_with_flock() {
        let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let path = env::temp_dir().join(format!("factoidal-lock-check-{}-{stamp}", std::process::id()));
        let lock = fs::OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
        lock.lock().unwrap();
        let blocked = Command::new("flock").arg("-n").arg(&path).arg("true").status().unwrap();
        assert_eq!(blocked.code(), Some(1), "another flock user must be excluded");
        drop(lock);
        let available = Command::new("flock").arg("-n").arg(&path).arg("true").status().unwrap();
        fs::remove_file(path).unwrap();
        assert!(available.success(), "the lock must be released when its file is dropped");
    }

    #[test]
    fn official_v31_fixture_verifies_and_tampering_fails() {
        // Read the clean pinned checkout installed by ../bootstrap.py; this is
        // the official real Groth16 fixture, whose journal is not an ASK journal.
        let source = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../lib/risc0-ethereum/contracts/test/TestReceiptV3_1.sol")).unwrap();
        let field = |name: &str| -> Vec<u8> {
            let rest = source.split_once(&format!("{name} =")).unwrap().1;
            let encoded = rest.split_once("hex\"").unwrap().1.split_once('"').unwrap().0;
            hex::decode(encoded).unwrap()
        };
        let image = Digest::from_hex(hex::encode(field("IMAGE_ID"))).unwrap();
        let journal = field("JOURNAL");
        let evm_seal = field("SEAL");
        let inner = Groth16Receipt::new(evm_seal[4..].to_vec(), ReceiptClaim::ok(image, journal.clone()).into(),
            Groth16ReceiptVerifierParameters::default().digest());
        let receipt = Receipt::new(InnerReceipt::Groth16(inner), journal.clone());
        let receipt = receipt_format::decode_receipt(&bincode::serialize(&receipt).unwrap()).unwrap();
        verify_binding(&receipt, image, &journal).unwrap();
        assert_eq!(encode_verified_seal(&receipt).unwrap(), evm_seal);
        assert!(require_ask_true(&journal).is_err());
        assert!(verify_binding(&receipt, Digest::ZERO, &journal).is_err());
        let mut changed = receipt.clone();
        changed.journal.bytes[0] ^= 1;
        assert!(verify_binding(&changed, image, &changed.journal.bytes).is_err());
    }
}
