//! fx-driver-static: the benchmark loop of ../driver-rs over direct calls
//! to the C entry points of ../baseline-emcc/fx_emcc.c (the char* ABI).
//! Usage (wasmtime): fx-static.wasm <document> <format> <query.rq> [n]

use std::ffi::{c_char, CStr, CString};
use std::time::Instant;

extern "C" {
    fn fx_parse_c(text: *const c_char, format: *const c_char, base: *const c_char) -> *mut c_char;
    fn fx_query_c(nquads: *const c_char, sparql: *const c_char) -> *mut c_char;
    fn free(p: *mut c_char);
}

/// Copy a malloc'd C string out and free it.
fn take(p: *mut c_char) -> String {
    let s = unsafe { CStr::from_ptr(p) }.to_string_lossy().into_owned();
    unsafe { free(p) };
    s
}

fn median(mut v: Vec<u128>) -> u128 {
    v.sort_unstable();
    v[v.len() / 2]
}

#[no_mangle]
pub extern "C" fn fx_driver_main() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: fx-static <document> <format> <query.rq> [n]");
        return 2;
    }
    let doc = CString::new(std::fs::read_to_string(&args[1]).expect("read document")).unwrap();
    let fmt = CString::new(args[2].as_str()).unwrap();
    let query = CString::new(std::fs::read_to_string(&args[3]).expect("read query")).unwrap();
    let base = CString::new("").unwrap();
    let n: usize = args.get(4).map(|s| s.parse().expect("n")).unwrap_or(5);
    let (mut parse_us, mut query_us) = (Vec::new(), Vec::new());
    let (mut nq, mut answer) = (String::new(), String::new());
    for _ in 0..n {
        let t = Instant::now();
        let r = take(unsafe { fx_parse_c(doc.as_ptr(), fmt.as_ptr(), base.as_ptr()) });
        if !r.starts_with('O') {
            eprintln!("parse error: {}", &r[1..]);
            return 1;
        }
        nq = r[1..].to_string();
        parse_us.push(t.elapsed().as_micros());
        let c = CString::new(nq.as_str()).unwrap();
        let t = Instant::now();
        answer = take(unsafe { fx_query_c(c.as_ptr(), query.as_ptr()) });
        query_us.push(t.elapsed().as_micros());
    }
    println!(
        "{{\"nquadsBytes\":{},\"parseUs\":{},\"queryUs\":{},\"answerBytes\":{},\"answerHead\":{:?}}}",
        nq.len(), median(parse_us), median(query_us), answer.len(),
        answer.chars().take(120).collect::<String>()
    );
    0
}
