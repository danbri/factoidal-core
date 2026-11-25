// Tor component probe for the built-in WebAssembly engine (BubblePopWASM).
// Runs parts of Arti 0.48.0 that need no network: onion v3 address parsing and key blinding
// (tor-hscrypto), microdescriptor consensus parsing (tor-netdoc), and the primitive costs of
// circuit set-up (x25519) and relay cell crypto (AES-128-CTR, 3 hops). Not a Tor client.
// Record: docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md, section 8.
// `run` returns one JSON object per line and also logs each line to the console.
// Page clocks are virtual in Foafnaut, so the caller passes the real time in `now_ms`.
use std::time::Duration;
use wasm_bindgen::prelude::*;

struct Instant(f64);
impl Instant {
    fn now() -> Self { Instant(js_sys::Date::now()) }
    fn elapsed_ms(&self) -> f64 { perf_now() - self.0 }
}
fn perf_now() -> f64 { js_sys::Date::now() }
use cipher::{KeyIvInit, StreamCipher};
use digest::Digest;
use tor_checkable::{ExternallySigned, TimeBound};
use tor_hscrypto::pk::{HsId, HsIdKey};
use tor_hscrypto::time::TimePeriod;
use tor_llcrypto::cipher::aes::Aes128Ctr;
use tor_llcrypto::d::{Sha1, Sha3_256};
use x25519_dalek::{PublicKey, StaticSecret};

fn ms(t: Instant) -> f64 { t.elapsed_ms() }
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn rnd32() -> [u8; 32] { let mut b = [0u8; 32]; getrandom::getrandom(&mut b).expect("random_get"); b }

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

#[wasm_bindgen]
pub fn step(msg: &str) { log(&format!("tor step {msg}")); }

#[wasm_bindgen]
pub fn run(cells: usize, dh: usize, now_ms: f64) -> String {
    std::panic::set_hook(Box::new(|p| log(&format!("tor panic {p}"))));
    let mut out = String::new();
    macro_rules! println { ($($a:tt)*) => {{ out.push_str(&format!($($a)*)); out.push('\n'); log(&format!("tor line {}", out.lines().last().unwrap_or(""))); }} }
    let total = Instant::now();

    // 1. Onion service v3: parse and check an address, blind its key for the current period.
    let t = Instant::now();
    let addr = "2gzyxa5ihm7nsggfxnu52rck2vv4rvmdlkiu3zzui5du4xyclen53wid.onion";
    match addr.parse::<HsId>() {
        Ok(id) => {
            let key = HsIdKey::try_from(id).expect("valid ed25519 point");
            let now = std::time::UNIX_EPOCH + Duration::from_millis(now_ms as u64);
            let tp = TimePeriod::new(Duration::from_secs(1440 * 60), now, Duration::from_secs(12 * 3600)).expect("period");
            let (blind, _sub) = key.compute_blinded_key(tp).expect("blind");
            let blind_id = blind.id();
            println!("{{\"step\":\"onion\",\"ok\":true,\"address\":\"{addr}\",\"period\":{},\"blindedId\":\"{}\",\"ms\":{:.1}}}",
                tp.interval_num(), hex(blind_id.as_ref()), ms(t));
        }
        Err(e) => println!("{{\"step\":\"onion\",\"ok\":false,\"error\":\"{e}\"}}"),
    }
    // A corrupted address must be refused (checksum, SHA3-256).
    let bad = addr.replacen('2', "3", 1);
    println!("{{\"step\":\"onion-bad-checksum\",\"refused\":{}}}", bad.parse::<HsId>().is_err());

    // 2. Microdescriptor consensus (Arti test data, a few relays; the live one has about 8000).
    let t = Instant::now();
    let text = include_str!("../.work/mdconsensus1.txt");
    match tor_netdoc::doc::netstatus::MdConsensus::parse(text) {
        Ok((_signed, _rest, unchecked)) => {
            let c = unchecked.dangerously_assume_timely().dangerously_assume_wellsigned();
            println!("{{\"step\":\"consensus\",\"ok\":true,\"bytes\":{},\"relays\":{},\"ms\":{:.1}}}",
                text.len(), c.relays().len(), ms(t));
        }
        Err(e) => println!("{{\"step\":\"consensus\",\"ok\":false,\"error\":\"{e}\"}}"),
    }

    // 3. x25519, the costly part of an ntor handshake (2 DH per hop on the client).
    let t = Instant::now();
    let server = StaticSecret::from(rnd32());
    let server_pub = PublicKey::from(&server);
    let mut agree = true;
    for _ in 0..dh {
        let c = StaticSecret::from(rnd32());
        let cp = PublicKey::from(&c);
        agree &= c.diffie_hellman(&server_pub).as_bytes() == server.diffie_hellman(&cp).as_bytes();
    }
    let x = ms(t);
    let per = if dh == 0 { "null".to_string() } else { format!("{:.2}", x / dh as f64) };
    println!("{{\"step\":\"x25519\",\"ok\":{agree},\"pairs\":{dh},\"ms\":{x:.1},\"msPerPair\":{per}}}");

    // 4. Relay cells through a 3-hop circuit: client encrypts 3 layers, each relay removes one.
    let keys: Vec<([u8; 16], [u8; 16])> = (0..3).map(|_| { let r = rnd32(); (r[..16].try_into().unwrap(), [0u8; 16]) }).collect();
    let mut client: Vec<Aes128Ctr> = keys.iter().map(|(k, iv)| Aes128Ctr::new(k.into(), iv.into())).collect();
    let mut relays: Vec<Aes128Ctr> = keys.iter().map(|(k, iv)| Aes128Ctr::new(k.into(), iv.into())).collect();
    let mut digests: Vec<Sha1> = (0..3).map(|_| Sha1::new()).collect();
    let t = Instant::now();
    let mut ok = true;
    for n in 0..cells {
        let mut body = [0u8; 509];
        body[0] = (n % 251) as u8;
        let plain = body;
        digests[2].update(&body); // running digest of the last hop
        for c in client.iter_mut().rev() { c.apply_keystream(&mut body); }
        for r in relays.iter_mut() { r.apply_keystream(&mut body); }
        ok &= body == plain;
    }
    let r = ms(t);
    let mut h = Sha3_256::new(); h.update(b"probe"); let _ = h.finalize();
    println!("{{\"step\":\"relay-cells\",\"ok\":{ok},\"cells\":{cells},\"hops\":3,\"ms\":{r:.1},\"kBps\":{:.1}}}",
        (cells * 509) as f64 / 1024.0 / (r / 1000.0).max(1e-9));
    println!("{{\"step\":\"done\",\"ms\":{:.1}}}", ms(total));
    out
}
