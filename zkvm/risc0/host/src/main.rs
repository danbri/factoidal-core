//! Byte packaging and offline receipt verification only. RDF, policy admission,
//! closure, ASK evaluation and the journal encoding are implemented in Lean.
use anyhow::{bail, ensure, Context, Result};
#[path = "../../receipt_format.rs"]
mod receipt_format;
use hex::FromHex;
use risc0_binfmt::ProgramBinary;
use risc0_zkvm::{sha::Digest, Executor, ExecutorEnv, ExitCode, ExternalProver,
    InnerReceipt, Prover, ProverOpts, Receipt};
use std::{env, fs, path::Path, process::Command, time::Instant};

fn bounded_read(path: &str, max: u64) -> Result<Vec<u8>> {
    let file = fs::File::open(path).with_context(|| format!("open {path}"))?;
    ensure!(file.metadata()?.len() <= max, "file exceeds input limit: {path}");
    use std::io::Read;
    let mut bytes = Vec::new();
    file.take(max + 1).read_to_end(&mut bytes)?;
    ensure!(bytes.len() as u64 <= max, "file grew beyond input limit: {path}");
    Ok(bytes)
}

fn journal_boolean(bytes: &[u8]) -> Result<bool> {
    ensure!(bytes.len() == 128, "expected exactly 128 journal bytes");
    ensure!(bytes[96..127].iter().all(|b| *b == 0), "noncanonical ABI boolean");
    match bytes[127] {
        0 => Ok(false),
        1 => Ok(true),
        _ => bail!("noncanonical ABI boolean"),
    }
}

fn segment_limit(value: Option<&str>) -> Result<u32> {
    let limit: u32 = value.unwrap_or("18").parse().context("invalid FACTOIDAL_ZK_SEGMENT_PO2")?;
    ensure!((18..=20).contains(&limit), "FACTOIDAL_ZK_SEGMENT_PO2 must be 18, 19 or 20");
    Ok(limit)
}

fn verify(receipt: &Receipt, image_id: Digest, expected: &[u8]) -> Result<bool> {
    let satisfied = journal_boolean(expected)?;
    ensure!(!matches!(receipt.inner, InnerReceipt::Fake(_)), "development receipts are refused");
    // disable-dev-mode is also compiled into the SDK, independently of the
    // explicit variant check and any process environment variables.
    receipt.verify(image_id).context("receipt proof/image/journal verification failed")?;
    ensure!(receipt.journal.bytes == expected, "journal differs from the authorised statement");
    Ok(satisfied)
}

fn write_new(path: &str, bytes: &[u8]) -> Result<()> {
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)] {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    use std::io::Write;
    let mut file = options.open(path)?;
    file.write_all(bytes)?;
    file.sync_all()?;
    Ok(())
}

fn run_local(args: &[String], prove: bool) -> Result<()> {
    ensure!(env::var_os("RISC0_DEV_MODE").is_none(), "unset RISC0_DEV_MODE; development mode is refused");
    let version = Command::new(&args[2]).arg("--version").output()?;
    ensure!(version.status.success() && String::from_utf8(version.stdout)?.trim() == "risc0-r0vm 3.1.0",
        "the explicit local r0vm must be version 3.1.0");
    let program = bounded_read(&args[3], 128 * 1024 * 1024)?;
    let image = ProgramBinary::decode(&program)?.compute_image_id()?;
    let frame = bounded_read(&args[4], 102453)?;
    let expected = bounded_read(&args[5], 128)?;
    let satisfied = journal_boolean(&expected)?;
    let mut builder = ExecutorEnv::builder();
    // Segment size trades prover memory for continuation overhead. It changes
    // neither the guest image nor the verified statement or session ceiling.
    let setting = env::var_os("FACTOIDAL_ZK_SEGMENT_PO2");
    let setting = setting.as_ref().map(|s| s.to_str().context("non-UTF-8 segment setting")).transpose()?;
    builder.write_slice(&frame).segment_limit_po2(segment_limit(setting)?).session_limit(Some(64 * 1024 * 1024));
    let guest_env = builder.build()?;
    // An explicit local subprocess avoids the SDK's default prover selection.
    // The Bonsai feature is not compiled in.
    let local = ExternalProver::new("factoidal-pinned-local-r0vm", &args[2]);
    let started = Instant::now();
    if prove {
        ensure!(!Path::new(&args[6]).exists(), "receipt output already exists");
        let lock = fs::OpenOptions::new().create(true).append(true)
            .open("/tmp/factoidal-zk-prove.lock")?;
        lock.lock()?;
        let result = local.prove_with_opts(guest_env, &program, &ProverOpts::composite())?;
        verify(&result.receipt, image, &expected)?;
        let encoded = bincode::serialize(&result.receipt)?;
        // Check that the same bounded public decoder accepts what we publish.
        verify(&receipt_format::decode_receipt(&encoded)?, image, &expected)?;
        write_new(&args[6], &encoded)?;
        println!("{{\"kind\":\"verified-composite\",\"imageId\":\"{image}\",\"satisfied\":{satisfied},\"userCycles\":{},\"totalCycles\":{},\"segments\":{},\"receiptBytes\":{},\"seconds\":{:.3}}}",
            result.stats.user_cycles, result.stats.total_cycles, result.stats.segments,
            encoded.len(), started.elapsed().as_secs_f64());
    } else {
        let result = local.execute(guest_env, &program)?;
        ensure!(result.exit_code == ExitCode::Halted(0), "guest did not halt successfully");
        ensure!(result.journal.bytes == expected, "execution journal differs from authorised bytes");
        println!("{{\"kind\":\"execution-only\",\"imageId\":\"{image}\",\"satisfied\":{satisfied},\"userCycles\":{},\"segments\":{},\"seconds\":{:.3}}}",
            result.cycles(), result.segments.len(), started.elapsed().as_secs_f64());
    }
    Ok(())
}

fn main() -> Result<()> {
    let args: Vec<_> = env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("execute") if args.len() == 6 => run_local(&args, false)?,
        Some("prove") if args.len() == 7 => run_local(&args, true)?,
        Some("pack") if args.len() == 4 => {
            let user = bounded_read(&args[2], 128 * 1024 * 1024)?;
            let binary = ProgramBinary::new(&user, risc0_zkos_v1compat::V1COMPAT_ELF);
            let id = binary.compute_image_id()?;
            fs::write(&args[3], binary.encode())?;
            println!("{id}");
        }
        Some("verify") if args.len() == 5 => {
            let image_id = Digest::from_hex(&args[2]).context("invalid image ID")?;
            let encoded = bounded_read(&args[3], receipt_format::MAX_RECEIPT)?;
            let receipt = receipt_format::decode_receipt(&encoded).context("invalid receipt encoding")?;
            let expected = bounded_read(&args[4], 128)?;
            let satisfied = verify(&receipt, image_id, &expected)?;
            println!("verified image={image_id} satisfied={satisfied} journal={}", hex::encode(expected));
        }
        Some("frame") if args.len() == 9 => {
            let regime: u8 = args[2].parse().context("invalid regime byte")?;
            ensure!(regime <= 1, "unknown regime");
            // Strict length framing only; Lean independently validates these
            // limits, all text, policy admission and computation semantics.
            let limits = [65536, 32, 16384, 16384, 4096];
            let mut frame = vec![regime];
            for (path, max) in args[3..8].iter().zip(limits) {
                let bytes = bounded_read(path, max)?;
                frame.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
                frame.extend_from_slice(&bytes);
            }
            ensure!(!Path::new(&args[8]).exists(), "refusing to replace an existing witness frame");
            write_new(&args[8], &frame)?;
        }
        _ => bail!("usage: factoidal-ask-receipt pack USER_ELF PROGRAM.bin\n       factoidal-ask-receipt verify IMAGE_ID RECEIPT EXPECTED_JOURNAL\n       factoidal-ask-receipt frame REGIME INPUT SALT QUERY RULES CONTEXT OUT\n       factoidal-ask-receipt execute R0VM PROGRAM FRAME EXPECTED_JOURNAL\n       factoidal-ask-receipt prove R0VM PROGRAM FRAME EXPECTED_JOURNAL RECEIPT"),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn segment_setting_preserves_the_bounded_profiles() {
        assert_eq!(segment_limit(None).unwrap(), 18);
        for value in ["18", "19", "20"] {
            assert_eq!(segment_limit(Some(value)).unwrap().to_string(), value);
        }
        for value in ["", "17", "21", "-1", "18.0", "unbounded"] {
            assert!(segment_limit(Some(value)).is_err());
        }
    }

    #[test]
    fn journal_requires_exact_length_and_canonical_boolean() {
        let mut b = [0u8; 128];
        assert!(!journal_boolean(&b).unwrap());
        b[127] = 1;
        assert!(journal_boolean(&b).unwrap());
        b[96] = 1;
        assert!(journal_boolean(&b).is_err());
        b[96] = 0;
        b[127] = 2;
        assert!(journal_boolean(&b).is_err());
        assert!(journal_boolean(&b[..127]).is_err());
        assert!(journal_boolean(&[0; 129]).is_err());
    }
}
