#![no_main]
//! Bounded framing and ABI ownership only. No RDF, policy, hash or query logic.
use risc0_zkvm::guest::env;
use std::io::{Read, Write};

risc0_zkvm::guest::entry!(main);

extern "C" {
    fn l4zk_attest(input: *const u8, input_n: usize, salt: *const u8, salt_n: usize,
        query: *const u8, query_n: usize, rules: *const u8, rules_n: usize,
        context: *const u8, context_n: usize, regime: u8, journal: *mut u8) -> u8;
}

fn field(reader: &mut impl Read, max: usize) -> Vec<u8> {
    let mut length = [0; 4];
    reader.read_exact(&mut length).expect("truncated input length");
    let n = u32::from_le_bytes(length) as usize;
    assert!(n <= max, "input frame exceeds allocation limit");
    let mut bytes = vec![0; n];
    reader.read_exact(&mut bytes).expect("truncated input field");
    bytes
}

fn main() {
    let mut stdin = env::stdin();
    let mut regime = [0];
    stdin.read_exact(&mut regime).expect("missing regime");
    let input = field(&mut stdin, 65536);
    let salt = field(&mut stdin, 32);
    let query = field(&mut stdin, 16384);
    let rules = field(&mut stdin, 16384);
    let context = field(&mut stdin, 4096);
    assert_eq!(stdin.read(&mut [0]).expect("input read failed"), 0, "trailing input bytes");
    let mut journal = [0u8; 128];
    // Each slice stays alive throughout the synchronous call. C copies it to
    // owned Lean ByteArrays and consumes the returned managed pair.
    let status = unsafe {
        l4zk_attest(input.as_ptr(), input.len(), salt.as_ptr(), salt.len(),
            query.as_ptr(), query.len(), rules.as_ptr(), rules.len(),
            context.as_ptr(), context.len(), regime[0], journal.as_mut_ptr())
    };
    assert!(status <= 1, "checked Lean computation refused: status {status}");
    assert_eq!(journal[127], status, "journal/status ABI mismatch");
    env::commit_slice(&journal);
}

#[no_mangle]
pub unsafe extern "C" fn l4zk_heap_allocate(n: usize) -> *mut u8 {
    // A single disjoint arena for newlib; newlib supplies real malloc/free.
    std::alloc::alloc(std::alloc::Layout::from_size_align(n, 16).expect("heap layout"))
}

#[no_mangle]
pub unsafe extern "C" fn l4zk_private_write(fd: i32, p: *const u8, n: usize) {
    let bytes = std::slice::from_raw_parts(p, n);
    if fd == 1 { env::stdout().write_all(bytes).expect("diagnostic write"); }
    else { env::stderr().write_all(bytes).expect("diagnostic write"); }
}

#[no_mangle]
pub extern "C" fn l4zk_fail() -> ! {
    panic!("restricted C/Lean runtime refused")
}

#[no_mangle]
pub unsafe extern "C" fn l4zk_seed_random(p: *mut u8) {
    // Init.Data.Random seeds its standard-library generator once. The SDK
    // supplies these bytes as host advice; no entropy or authority is proved.
    // This is independent of the private salt supplied to the ASK protocol.
    let mut words = [0u32; 2];
    risc0_zkvm_platform::syscall::sys_rand(words.as_mut_ptr(), words.len());
    std::ptr::copy_nonoverlapping(words.as_ptr().cast::<u8>(), p, 8);
}
