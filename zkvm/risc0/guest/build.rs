use sha2::{Digest, Sha256};
use std::{env, fs, path::PathBuf};
mod runtime_snapshot;
fn main() {
    println!("cargo:rerun-if-env-changed=FACTOIDAL_ZK_RUNTIME");
    println!("cargo:rerun-if-env-changed=RISC0_HOME");
    let runtime = PathBuf::from(env::var("FACTOIDAL_ZK_RUNTIME").expect("set FACTOIDAL_ZK_RUNTIME"));
    let root = PathBuf::from(env::var("RISC0_HOME").expect("set RISC0_HOME"));
    let archive = runtime.join("libfactoidal_ask.a");
    assert!(archive.is_file(), "build the pinned Lean runtime first");
    let manifest: serde_json::Value = serde_json::from_slice(
        &fs::read(runtime.join("manifest.json")).expect("runtime manifest missing"))
        .expect("invalid runtime manifest");
    assert_eq!(manifest["leanRuntime"]["commit"].as_str(),
        Some("819816b2e0a3bf405af45ae5c7af2491d8f5bee6"), "unexpected Lean runtime");
    let archive_bytes = fs::read(&archive).expect("read runtime archive");
    let actual = format!("{:x}", Sha256::digest(&archive_bytes));
    assert_eq!(manifest["archiveSha256"].as_str(), Some(actual.as_str()),
        "runtime archive differs from its build manifest");
    println!("cargo:rerun-if-changed={}", archive.display());
    println!("cargo:rerun-if-changed={}", runtime.join("manifest.json").display());
    println!("cargo:rerun-if-changed=runtime_snapshot.rs");
    let output = PathBuf::from(env::var_os("OUT_DIR").expect("Cargo OUT_DIR missing"));
    let snapshot = runtime_snapshot::snapshot_verified_archive(&output, &actual, &archive_bytes)
        .expect("create verified runtime snapshot");
    // The linker reopens only this private, content-named copy, never the
    // mutable build-runtime output whose bytes we checked above.
    println!("cargo:rustc-link-search=native={}", snapshot.display());
    println!("cargo:rustc-link-lib=static=factoidal_ask");
    println!("cargo:rustc-link-search=native={}", root.join("cpp/riscv32-unknown-elf/lib").display());
    println!("cargo:rustc-link-search=native={}", root.join("cpp/lib/gcc/riscv32-unknown-elf/13.2.0").display());
    for lib in ["stdc++", "c", "m", "gcc"] {
        println!("cargo:rustc-link-lib=static={lib}");
    }
    println!("cargo:rustc-link-arg=-Map={}", runtime.join("guest.map").display());
}
