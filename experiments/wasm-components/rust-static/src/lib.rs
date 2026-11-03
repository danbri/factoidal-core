//! wc-static: the same driver as wc-client (`bench.rs`), calling the Lean
//! shim (`c/wc_shim.c`) directly instead of through a component import.
#[path = "../../rust-client/src/bench.rs"]
mod bench;

extern "C" {
    fn wc_turtle_to_nquads_n(t: *const u8, tl: usize, b: *const u8, bl: usize, out: *mut usize) -> *mut u8;
    fn wc_query_turtle_n(t: *const u8, tl: usize, q: *const u8, ql: usize, out: *mut usize) -> *mut u8;
    fn wc_free(p: *mut u8);
}

/// Copy the shim's malloc'd answer into a String and free it.
unsafe fn take(p: *mut u8, n: usize) -> String {
    assert!(!p.is_null(), "engine initialisation failed");
    let s = String::from_utf8_lossy(std::slice::from_raw_parts(p, n)).into_owned();
    wc_free(p);
    s
}

struct Static;
impl bench::Engine for Static {
    fn turtle_to_nquads(&self, ttl: &str) -> Result<String, String> {
        let mut n = 0;
        let s = unsafe { take(wc_turtle_to_nquads_n(ttl.as_ptr(), ttl.len(), "".as_ptr(), 0, &mut n), n) };
        match s.strip_prefix('!') { Some(e) => Err(e.to_string()), None => Ok(s) }
    }
    fn query(&self, ttl: &str, rq: &str) -> String {
        let mut n = 0;
        unsafe { take(wc_query_turtle_n(ttl.as_ptr(), ttl.len(), rq.as_ptr(), rq.len(), &mut n), n) }
    }
}

/// Called by the C `main` of build.sh's static link.
#[no_mangle]
pub extern "C" fn wc_static_main() -> i32 {
    let args: Vec<String> = std::env::args().skip(1).collect();
    bench::run(&Static, &args);
    0
}
