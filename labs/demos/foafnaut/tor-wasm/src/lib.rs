//! Arti 2.8.0 (the Tor Project's Rust Tor client) built for wasm32-unknown-unknown, with the
//! smallest runtime that lets `arti-client` start in a Foafnaut page.
//!
//! Record: docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md, section 10.
//!
//! What this runtime gives Arti, and what it refuses:
//! - Tasks: `wasm_bindgen_futures::spawn_local` (one thread; the page event loop runs them).
//! - Timers: `setTimeout` through gloo-timers.
//! - Wall clock: the page's `Date.now()`, which Arti also reads directly in several places.
//!   A Foafnaut page clock is virtual and starts near 1970, so the embedding page must give
//!   `Date.now()` the real time (see `pages.py`). `bootstrap` refuses to start when the clock
//!   reads earlier than 2024.
//! - Network: TCP to IP literals through the host (`globalThis.torHost`, given by the Deno
//!   worker `deno/tor-worker.ts`), and only after `enable_unreviewed_transport` with the exact
//!   acknowledgement string. Without both, every connection is refused. Unix sockets, UDP and
//!   listening are always refused. There is no fallback path.
//! - TLS: rustls (ring provider) inside the module, with Arti's own link verifier.
//!
//! EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
//! WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW. The transport is not trusted for real users.
//! - Blocking work: run at once on the calling thread (there are no threads).
//! - State (guards, circuit build times): Arti's in-memory state manager on wasm, which the host
//!   can read out (`state_snapshot`) and load back (`state_load`). Keys: ephemeral keystore.

use std::io::{Error as IoError, ErrorKind, Result as IoResult};
use std::net::SocketAddr;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use async_trait::async_trait;
use futures::future::FutureObj;
use futures::task::{Spawn, SpawnError};
use send_wrapper::SendWrapper;
use tor_general_addr::unix;
use tor_rtcompat::unimpl::{FakeListener, FakeStream};
use tor_rtcompat::tls::{CertifiedConn, RustlsProvider, TlsAcceptorSettings, TlsConnector};
use tor_rtcompat::StreamOps;
use tor_rtcompat::{
    Blocking, CoarseTimeProvider, JoinSetProvider, NetStreamProvider, RealCoarseTimeProvider,
    SleepProvider, TlsProvider, UdpProvider, UdpSocket,
};
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);
}

/// Arti's memory quota in this build: 256 MiB (reclamation starts above it).
const MEMORY_QUOTA_BYTES: usize = 256 * 1024 * 1024;

/// 2024-01-01T00:00:00Z. A wall clock earlier than this is not a real clock (a Foafnaut page
/// clock starts near 1970), and Tor must not run on it: consensus validity, certificate
/// lifetimes and onion service time periods all depend on the real date.
const EARLIEST_REAL_TIME: u64 = 1_704_067_200;

/// The wall clock Arti reads (`SystemTime::get()`, from the page's `Date.now()`), if it is real.
fn real_wallclock() -> Option<SystemTime> {
    use web_time::web::SystemTimeExt as _;
    let now = web_time::SystemTime::now().to_std();
    let secs = now.duration_since(UNIX_EPOCH).ok()?.as_secs();
    (secs >= EARLIEST_REAL_TIME).then_some(now)
}

/// Connection, listen and bind requests refused (all of them: there is no transport).
static REFUSED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn no_transport() -> IoError {
    REFUSED.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
    IoError::new(
        ErrorKind::Unsupported,
        "no transport: this host gives the Tor client no network connection",
    )
}

/// The runtime. It holds no state of its own.
#[derive(Clone)]
pub struct WasmRuntime {
    coarse: RealCoarseTimeProvider,
    tls: std::sync::Arc<RustlsProvider>,
}

impl std::fmt::Debug for WasmRuntime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("WasmRuntime")
    }
}

impl Default for WasmRuntime {
    fn default() -> Self {
        // rustls needs a process-wide crypto provider; installing it twice is harmless.
        let _ = rustls::crypto::ring::default_provider().install_default();
        WasmRuntime { coarse: RealCoarseTimeProvider::default(), tls: std::sync::Arc::new(RustlsProvider::default()) }
    }
}

impl Spawn for WasmRuntime {
    fn spawn_obj(&self, future: FutureObj<'static, ()>) -> Result<(), SpawnError> {
        wasm_bindgen_futures::spawn_local(future);
        Ok(())
    }
}

impl Blocking for WasmRuntime {
    type ThreadHandle<T: Send + 'static> = std::future::Ready<T>;

    fn spawn_blocking<F, T>(&self, f: F) -> Self::ThreadHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        std::future::ready(f())
    }

    fn reenter_block_on<F>(&self, _future: F) -> F::Output
    where
        F: std::future::Future,
        F::Output: Send + 'static,
    {
        panic!("reenter_block_on is not possible on wasm32 with one thread")
    }
}

impl JoinSetProvider for WasmRuntime {
    type JoinSet<T: Send + Sync + 'static> = tor_rtcompat::join_set::FuturesJoinSet<T, Self>;
    fn new_join_set<T: Send + Sync + 'static>(&self) -> Self::JoinSet<T> {
        tor_rtcompat::join_set::FuturesJoinSet::new(self.clone())
    }
}

/// A `setTimeout` future. The page has one thread, so the wrapper never moves between threads.
pub struct Sleep(SendWrapper<gloo_timers::future::TimeoutFuture>);
impl std::future::Future for Sleep {
    type Output = ();
    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<()> {
        std::pin::Pin::new(&mut *self.0).poll(cx)
    }
}

impl SleepProvider for WasmRuntime {
    type SleepFuture = Sleep;
    fn sleep(&self, d: Duration) -> Sleep {
        let ms = d.as_millis().min(u32::MAX as u128) as u32;
        Sleep(SendWrapper::new(gloo_timers::future::TimeoutFuture::new(ms)))
    }
}

impl CoarseTimeProvider for WasmRuntime {
    fn now_coarse(&self) -> tor_rtcompat::CoarseInstant {
        self.coarse.now_coarse()
    }
}

#[async_trait]
impl NetStreamProvider<SocketAddr> for WasmRuntime {
    type Stream = HostStream;
    type Listener = HostListener;
    type ConnectOptions = tor_rtcompat::TcpConnectOptions;
    type ListenOptions = tor_rtcompat::TcpListenOptions;
    async fn connect(&self, a: &SocketAddr, _o: &Self::ConnectOptions) -> IoResult<HostStream> {
        HostStream::connect(a).await
    }
    async fn listen(&self, _a: &SocketAddr, _o: &Self::ListenOptions) -> IoResult<Self::Listener> {
        Err(no_transport())
    }
}

#[async_trait]
impl NetStreamProvider<unix::SocketAddr> for WasmRuntime {
    type Stream = FakeStream;
    type Listener = FakeListener<unix::SocketAddr>;
    type ConnectOptions = tor_rtcompat::UnixConnectOptions;
    type ListenOptions = tor_rtcompat::UnixListenOptions;
    async fn connect(&self, _a: &unix::SocketAddr, _o: &Self::ConnectOptions) -> IoResult<FakeStream> {
        Err(no_transport())
    }
    async fn listen(&self, _a: &unix::SocketAddr, _o: &Self::ListenOptions) -> IoResult<Self::Listener> {
        Err(no_transport())
    }
}

/// The acknowledgement a caller must pass to `enable_unreviewed_transport`.
pub const TRANSPORT_ACK: &str = "dangerously-use-unreviewed-tor-transport";
static TRANSPORT_ON: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Allow connections through the host's `torHost`. Returns false (and stays off) unless `ack`
/// is exactly `TRANSPORT_ACK`. The transport is unreviewed and not for real users.
#[wasm_bindgen]
pub fn enable_unreviewed_transport(ack: &str) -> bool {
    let on = ack == TRANSPORT_ACK;
    if on {
        log("tor WARNING: unreviewed Tor transport enabled. EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.");
    }
    TRANSPORT_ON.store(on, std::sync::atomic::Ordering::SeqCst);
    on
}

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = torHost, js_name = connect, catch)]
    fn host_connect(ip: &str, port: u16) -> Result<js_sys::Promise, JsValue>;
    #[wasm_bindgen(js_namespace = torHost, js_name = read, catch)]
    fn host_read(h: u32, max: u32) -> Result<js_sys::Promise, JsValue>;
    #[wasm_bindgen(js_namespace = torHost, js_name = write, catch)]
    fn host_write(h: u32, data: &[u8]) -> Result<js_sys::Promise, JsValue>;
    #[wasm_bindgen(js_namespace = torHost, js_name = close, catch)]
    fn host_close(h: u32) -> Result<(), JsValue>;
}

/// The message of a host error, without its stack (a stack names local file paths).
fn js_err(e: JsValue) -> IoError {
    let msg = e
        .as_string()
        .or_else(|| js_sys::Reflect::get(&e, &"message".into()).ok().and_then(|m| m.as_string()))
        .unwrap_or_else(|| "host error".into());
    IoError::new(ErrorKind::Other, format!("host: {msg}"))
}

type HostFuture = SendWrapper<wasm_bindgen_futures::JsFuture>;

/// A host promise as a `Send` future (the module has one thread).
struct HostFut(HostFuture);
impl std::future::Future for HostFut {
    type Output = Result<JsValue, JsValue>;
    fn poll(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<Self::Output> {
        std::pin::Pin::new(&mut *self.0).poll(cx)
    }
}

/// A TCP connection held by the host. The module has one thread, so the wrappers never move.
pub struct HostStream {
    h: u32,
    rd: Option<HostFuture>,
    buf: Vec<u8>,
    pos: usize,
    wr: Option<(HostFuture, usize)>,
    closed: bool,
}

impl HostStream {
    async fn connect(a: &SocketAddr) -> IoResult<HostStream> {
        if !TRANSPORT_ON.load(std::sync::atomic::Ordering::SeqCst) {
            return Err(no_transport());
        }
        // Only IP literals reach this point: Arti connects to relays by address, so no name
        // is ever resolved, here or in the host.
        let p = host_connect(&a.ip().to_string(), a.port()).map_err(|_| no_transport())?;
        let v = HostFut(SendWrapper::new(wasm_bindgen_futures::JsFuture::from(p))).await.map_err(js_err)?;
        let h = v.as_f64().ok_or_else(|| IoError::new(ErrorKind::Other, "host: bad handle"))? as u32;
        Ok(HostStream { h, rd: None, buf: Vec::new(), pos: 0, wr: None, closed: false })
    }
}

impl futures::io::AsyncRead for HostStream {
    fn poll_read(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>, out: &mut [u8]) -> std::task::Poll<IoResult<usize>> {
        use std::task::Poll;
        let this = &mut *self;
        loop {
            if this.pos < this.buf.len() {
                let n = out.len().min(this.buf.len() - this.pos);
                out[..n].copy_from_slice(&this.buf[this.pos..this.pos + n]);
                this.pos += n;
                return Poll::Ready(Ok(n));
            }
            if this.closed {
                return Poll::Ready(Ok(0));
            }
            if this.rd.is_none() {
                match host_read(this.h, 16384) {
                    Ok(p) => this.rd = Some(SendWrapper::new(wasm_bindgen_futures::JsFuture::from(p))),
                    Err(e) => return Poll::Ready(Err(js_err(e))),
                }
            }
            let f = this.rd.as_mut().expect("read future");
            match std::pin::Pin::new(&mut **f).poll(cx) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(r) => {
                    this.rd = None;
                    let v = r.map_err(js_err)?;
                    let a = js_sys::Uint8Array::new(&v);
                    if a.length() == 0 {
                        return Poll::Ready(Ok(0));
                    }
                    this.buf = a.to_vec();
                    this.pos = 0;
                }
            }
        }
    }
}

impl futures::io::AsyncWrite for HostStream {
    fn poll_write(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>, data: &[u8]) -> std::task::Poll<IoResult<usize>> {
        use std::task::Poll;
        let this = &mut *self;
        if this.wr.is_none() {
            let n = data.len().min(16384);
            match host_write(this.h, &data[..n]) {
                Ok(p) => this.wr = Some((SendWrapper::new(wasm_bindgen_futures::JsFuture::from(p)), n)),
                Err(e) => return Poll::Ready(Err(js_err(e))),
            }
        }
        let (f, n) = this.wr.as_mut().expect("write future");
        let n = *n;
        match std::pin::Pin::new(&mut **f).poll(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(r) => {
                this.wr = None;
                r.map_err(js_err)?;
                Poll::Ready(Ok(n))
            }
        }
    }
    fn poll_flush(mut self: std::pin::Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> std::task::Poll<IoResult<()>> {
        use std::task::Poll;
        let this = &mut *self;
        if let Some((f, _)) = this.wr.as_mut() {
            match std::pin::Pin::new(&mut **f).poll(cx) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(r) => {
                    this.wr = None;
                    r.map_err(js_err)?;
                }
            }
        }
        Poll::Ready(Ok(()))
    }
    fn poll_close(mut self: std::pin::Pin<&mut Self>, _cx: &mut std::task::Context<'_>) -> std::task::Poll<IoResult<()>> {
        if !self.closed {
            self.closed = true;
            let _ = host_close(self.h);
        }
        std::task::Poll::Ready(Ok(()))
    }
}

impl Drop for HostStream {
    fn drop(&mut self) {
        if !self.closed {
            self.closed = true;
            let _ = host_close(self.h);
        }
    }
}

impl StreamOps for HostStream {}

/// Listening is refused, so this type is never made.
pub struct HostListener(void::Void);
impl tor_rtcompat::NetStreamListener<SocketAddr> for HostListener {
    type Stream = HostStream;
    type Incoming = futures::stream::Empty<IoResult<(HostStream, SocketAddr)>>;
    fn incoming(self) -> Self::Incoming {
        void::unreachable(self.0)
    }
    fn local_addr(&self) -> IoResult<SocketAddr> {
        void::unreachable(self.0)
    }
}

/// A TLS connection that cannot exist (there is no stream for TLS to run over).
pub struct NoTlsConn(void::Void);
impl futures::io::AsyncRead for NoTlsConn {
    fn poll_read(self: std::pin::Pin<&mut Self>, _c: &mut std::task::Context<'_>, _b: &mut [u8]) -> std::task::Poll<IoResult<usize>> {
        void::unreachable(self.0)
    }
}
impl futures::io::AsyncWrite for NoTlsConn {
    fn poll_write(self: std::pin::Pin<&mut Self>, _c: &mut std::task::Context<'_>, _b: &[u8]) -> std::task::Poll<IoResult<usize>> {
        void::unreachable(self.0)
    }
    fn poll_flush(self: std::pin::Pin<&mut Self>, _c: &mut std::task::Context<'_>) -> std::task::Poll<IoResult<()>> {
        void::unreachable(self.0)
    }
    fn poll_close(self: std::pin::Pin<&mut Self>, _c: &mut std::task::Context<'_>) -> std::task::Poll<IoResult<()>> {
        void::unreachable(self.0)
    }
}
impl StreamOps for NoTlsConn {
    fn set_tcp_notsent_lowat(&self, _n: u32) -> IoResult<()> {
        void::unreachable(self.0)
    }
    fn new_handle(&self) -> Box<dyn StreamOps + Send + Unpin> {
        void::unreachable(self.0)
    }
}
impl CertifiedConn for NoTlsConn {
    fn export_keying_material(&self, _l: usize, _label: &[u8], _c: Option<&[u8]>) -> IoResult<Vec<u8>> {
        void::unreachable(self.0)
    }
    fn peer_certificate(&self) -> IoResult<Option<std::borrow::Cow<'_, [u8]>>> {
        void::unreachable(self.0)
    }
    fn own_certificate(&self) -> IoResult<Option<std::borrow::Cow<'_, [u8]>>> {
        void::unreachable(self.0)
    }
}

/// A TLS connector that refuses. It is never reached, because no stream can be made.
#[derive(Clone, Debug, Default)]
pub struct NoTls;

#[async_trait]
impl<S: Send + 'static> TlsConnector<S> for NoTls {
    type Conn = NoTlsConn;
    async fn negotiate_unvalidated(&self, _s: S, _sni: &str) -> IoResult<NoTlsConn> {
        Err(no_transport())
    }
}

impl TlsProvider<HostStream> for WasmRuntime {
    type Connector = <RustlsProvider as TlsProvider<HostStream>>::Connector;
    type TlsStream = <RustlsProvider as TlsProvider<HostStream>>::TlsStream;
    type Acceptor = NoTls;
    type TlsServerStream = NoTlsConn;
    fn tls_connector(&self) -> Self::Connector {
        TlsProvider::<HostStream>::tls_connector(&*self.tls)
    }
    fn tls_acceptor(&self, _s: TlsAcceptorSettings) -> IoResult<NoTls> {
        Err(no_transport())
    }
    fn supports_keying_material_export(&self) -> bool {
        TlsProvider::<HostStream>::supports_keying_material_export(&*self.tls)
    }
}

/// A UDP socket that cannot exist.
pub struct NoUdp(void::Void);
#[async_trait]
impl UdpSocket for NoUdp {
    async fn recv(&self, _b: &mut [u8]) -> IoResult<(usize, SocketAddr)> {
        void::unreachable(self.0)
    }
    async fn send(&self, _b: &[u8], _t: &SocketAddr) -> IoResult<usize> {
        void::unreachable(self.0)
    }
    fn local_addr(&self) -> IoResult<SocketAddr> {
        void::unreachable(self.0)
    }
}

#[async_trait]
impl UdpProvider for WasmRuntime {
    type UdpSocket = NoUdp;
    async fn bind(&self, _a: &SocketAddr) -> IoResult<NoUdp> {
        Err(no_transport())
    }
}

/// Where the host keeps Arti's state between runs: "none" until the host reports a store with
/// `set_state_store`. Only "lws-sealed" (a local, encrypted LWS storage) is accepted.
/// Expected-failure test: xfail.test.cjs (https://github.com/danbri/factoidal-core/issues/1058).
static STATE_STORE: std::sync::Mutex<&'static str> = std::sync::Mutex::new("none");

#[wasm_bindgen]
pub fn state_backend() -> String {
    STATE_STORE.lock().map(|s| s.to_string()).unwrap_or_else(|_| "none".into())
}

/// The host says where it keeps the state. Only "lws-sealed" is accepted.
#[wasm_bindgen]
pub fn set_state_store(kind: &str) -> bool {
    let ok = kind == "lws-sealed";
    if ok {
        if let Ok(mut s) = STATE_STORE.lock() {
            *s = "lws-sealed";
        }
    }
    ok
}

/// Arti's state (guards, circuit build times, ...) as one JSON object: key to JSON text.
/// Sensitive: it names this client's guards. The host must keep it sealed and local.
#[wasm_bindgen]
pub fn state_snapshot() -> String {
    serde_json::to_string(&tor_persist::wasm_shared_state().snapshot()).unwrap_or_else(|_| "{}".into())
}

/// Put back state saved by `state_snapshot`, before `bootstrap`. Returns the number of keys.
#[wasm_bindgen]
pub fn state_load(json: &str) -> i32 {
    match serde_json::from_str::<std::collections::HashMap<String, String>>(json) {
        Ok(m) => {
            let n = m.len() as i32;
            tor_persist::wasm_shared_state().preload(m);
            n
        }
        Err(_) => -1,
    }
}

/// True when this module runs in a dedicated worker, where no other page script can read its
/// memory. Expected-failure test: xfail.test.cjs.
#[wasm_bindgen]
pub fn isolated_context() -> bool {
    let g = js_sys::global();
    js_sys::Reflect::has(&g, &"WorkerGlobalScope".into()).unwrap_or(false)
        && js_sys::Reflect::has(&g, &"importScripts".into()).unwrap_or(false)
}

/// Start an Arti client and try to bootstrap it for at most `timeout_ms`. Returns one JSON
/// object per line: each bootstrap status Arti reports, then the result.
#[wasm_bindgen]
pub async fn bootstrap(timeout_ms: u32, config_toml: Option<String>) -> String {
    use futures::StreamExt;
    use tor_rtcompat::SleepProviderExt;
    let mut out = String::new();
    let mut say = |s: String| {
        log(&format!("tor {s}"));
        out.push_str(&s);
        out.push('\n');
    };
    let Some(now) = real_wallclock() else {
        say(r#"{"step":"refused","why":"the wall clock is not real (earlier than 2024): Tor needs the real date"}"#.into());
        return out;
    };
    say(format!(
        r#"{{"step":"start","arti":"2.8.0","wallclockUnix":{}}}"#,
        now.duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
    ));
    let rt = WasmRuntime::default();
    // Arti keeps its state in memory on wasm (TestingStateMgr), so these paths are never opened;
    // they only replace the defaults, which need a home directory to resolve.
    // A TOML configuration (for example a private test network's `[tor_network]`) replaces the
    // defaults; storage paths and the keystore kind below are always set by this module.
    let mut b = match config_toml.as_deref() {
        None => arti_client::config::TorClientConfigBuilder::default(),
        Some(t) => match toml::from_str::<arti_client::config::TorClientConfigBuilder>(t) {
            Ok(b) => b,
            Err(e) => {
                say(format!(r#"{{"step":"config","ok":false,"error":{:?}}}"#, e.to_string()));
                return out;
            }
        },
    };
    b.storage()
        .cache_dir(arti_client::config::CfgPath::new_literal("/arti-wasm/cache"))
        .state_dir(arti_client::config::CfgPath::new_literal("/arti-wasm/state"));
    // Memory quota: on wasm Arti cannot read the machine's memory size and uses 1 GiB. Set a
    // fixed limit unless the configuration gave one, so a hostile peer cannot grow buffers to it.
    if config_toml.as_deref().is_none_or(|t| !t.contains("[system.memory]")) {
        b.system().memory().max(MEMORY_QUOTA_BYTES);
    }
    // Keys (onion service client keys included) stay in memory: nothing is written anywhere.
    b.storage()
        .keystore()
        .primary()
        .kind(tor_config::ExplicitOrAuto::Explicit(tor_keymgr::config::ArtiKeystoreKind::Ephemeral));
    let config = match b.build() {
        Ok(c) => c,
        Err(e) => {
            say(format!(r#"{{"step":"config","ok":false,"error":{:?}}}"#, format!("{e:?}")));
            return out;
        }
    };
    let client = match arti_client::TorClient::with_runtime(rt.clone())
        .config(config)
        .create_unbootstrapped()
    {
        Ok(c) => c,
        Err(e) => {
            say(format!(r#"{{"step":"create","ok":false,"error":{:?}}}"#, format!("{e:?}")));
            return out;
        }
    };
    say(r#"{"step":"create","ok":true}"#.into());
    let mut events = client.bootstrap_events();
    let watch = async move {
        let mut seen = Vec::new();
        while let Some(st) = events.next().await {
            let line = format!(r#"{{"step":"status","fraction":{:.2},"text":{:?}}}"#, st.as_frac(), st.to_string());
            log(&format!("tor {line}"));
            seen.push(line);
        }
        seen
    };
    wasm_bindgen_futures::spawn_local(async move {
        let _ = watch.await;
    });
    let res = rt.timeout(Duration::from_millis(timeout_ms as u64), client.bootstrap()).await;
    match res {
        Ok(Ok(())) => say(r#"{"step":"bootstrap","ok":true}"#.into()),
        Ok(Err(e)) => say(format!(r#"{{"step":"bootstrap","ok":false,"error":{:?}}}"#, e.to_string())),
        Err(_) => say(format!(r#"{{"step":"bootstrap","ok":false,"error":"timeout after {timeout_ms} ms"}}"#)),
    }
    CLIENT.with(|c| *c.borrow_mut() = Some(client.clone()));
    let st = client.bootstrap_status();
    say(format!(
        r#"{{"step":"end","fraction":{:.2},"text":{:?},"refusedConnections":{}}}"#,
        st.as_frac(),
        st.to_string(),
        REFUSED.load(std::sync::atomic::Ordering::SeqCst)
    ));
    out
}

thread_local! {
    static CLIENT: std::cell::RefCell<Option<std::sync::Arc<arti_client::TorClient<WasmRuntime>>>> = const { std::cell::RefCell::new(None) };
    /// One isolated client per network partition (for a browser: the top-level site). Streams of
    /// two partitions never share a circuit (Arti `isolated_client`).
    static PARTITIONS: std::cell::RefCell<std::collections::HashMap<String, std::sync::Arc<arti_client::TorClient<WasmRuntime>>>> =
        std::cell::RefCell::new(std::collections::HashMap::new());
}

/// The client for `partition`: a new isolated client the first time a partition is seen.
/// An empty partition name is refused, so no caller can share a circuit by accident.
fn client_for(partition: &str) -> Result<std::sync::Arc<arti_client::TorClient<WasmRuntime>>, String> {
    if partition.is_empty() {
        return Err("no partition: every stream must name its partition (for a browser, the top-level site)".into());
    }
    let base = CLIENT.with(|c| c.borrow().clone()).ok_or("no client: run bootstrap first")?;
    Ok(PARTITIONS.with(|m| m.borrow_mut().entry(partition.to_string()).or_insert_with(|| base.isolated_client()).clone()))
}

/// New identity: forget every partition's isolation, so later streams use new circuits that no
/// earlier stream used. Returns the number of partitions forgotten.
#[wasm_bindgen]
pub fn new_identity() -> u32 {
    PARTITIONS.with(|m| {
        let mut m = m.borrow_mut();
        let n = m.len() as u32;
        m.clear();
        n
    })
}

/// Drop the client of the last `bootstrap`. Arti flushes its state when its circuit manager
/// is dropped, so call this before `state_snapshot` at the end of a session.
#[wasm_bindgen]
pub fn close() -> bool {
    CLIENT.with(|c| c.borrow_mut().take()).is_some()
}

/// Through the isolated client of `partition`, open a stream to `host:port` (the exit resolves
/// the name; nothing is resolved here), send `request` and return up to `max` bytes of reply.
#[wasm_bindgen]
pub async fn stream_request(partition: String, host: String, port: u16, request: String, max: u32, timeout_ms: u32) -> String {
    use futures::{AsyncReadExt, AsyncWriteExt};
    use tor_rtcompat::SleepProviderExt;
    let client = match client_for(&partition) {
        Ok(c) => c,
        Err(e) => return format!(r#"{{"step":"stream","ok":false,"error":{e:?}}}"#),
    };
    let rt = WasmRuntime::default();
    let work = async {
        let mut s = client.connect((host.as_str(), port)).await.map_err(|e| format!("{e:?}"))?;
        s.write_all(request.as_bytes()).await.map_err(|e| e.to_string())?;
        s.flush().await.map_err(|e| e.to_string())?;
        let mut buf = vec![0u8; max as usize];
        let mut got = 0;
        while got < buf.len() {
            let n = s.read(&mut buf[got..]).await.map_err(|e| e.to_string())?;
            if n == 0 { break; }
            got += n;
        }
        buf.truncate(got);
        Ok::<Vec<u8>, String>(buf)
    };
    let line = match rt.timeout(Duration::from_millis(timeout_ms as u64), work).await {
        Ok(Ok(b)) => format!(r#"{{"step":"stream","ok":true,"bytes":{},"reply":{:?}}}"#, b.len(), String::from_utf8_lossy(&b)),
        Ok(Err(e)) => format!(r#"{{"step":"stream","ok":false,"error":{:?}}}"#, e),
        Err(_) => format!(r#"{{"step":"stream","ok":false,"error":"timeout after {timeout_ms} ms"}}"#),
    };
    log(&format!("tor {line}"));
    line
}

static LOG_DEBUG: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Show Arti's debug lines too (safe logging stays on).
#[wasm_bindgen]
pub fn log_debug(on: bool) {
    LOG_DEBUG.store(on, std::sync::atomic::Ordering::SeqCst);
}

/// Send Arti's log lines (safe logging stays on: addresses are redacted) to the console.
#[wasm_bindgen(start)]
pub fn start() {
    struct Console;
    impl std::io::Write for Console {
        fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
            let s = String::from_utf8_lossy(b);
            let s = s.trim_end();
            // The level is the first word of the line (no timestamp is written).
            let t = s.trim_start();
            let debug = t.starts_with("DEBUG") || t.starts_with("TRACE");
            if !s.is_empty() && (!debug || LOG_DEBUG.load(std::sync::atomic::Ordering::SeqCst)) {
                log(&format!("arti {s}"));
            }
            Ok(b.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    std::panic::set_hook(Box::new(|p| log(&format!("tor panic {p}"))));
    let _ = tracing_subscriber::fmt()
        .with_writer(|| Console)
        .with_ansi(false)
        .without_time()
        .with_max_level(tracing::Level::DEBUG)
        .try_init();
}
