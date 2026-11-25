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
//! - Network: none. TCP, Unix sockets, UDP and listening all fail with an error that names the
//!   cause. There is no fallback to any other path: a request either goes through Tor or fails.
//! - TLS: none, because there is no stream for it to run over.
//! - Blocking work: run at once on the calling thread (there are no threads).
//! - State (guards, keys): Arti's in-memory state manager on wasm (`TestingStateMgr`), so it is
//!   lost when the page closes. See the record for the risk.

use std::io::{Error as IoError, ErrorKind, Result as IoResult};
use std::net::SocketAddr;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use async_trait::async_trait;
use futures::future::FutureObj;
use futures::task::{Spawn, SpawnError};
use send_wrapper::SendWrapper;
use tor_general_addr::unix;
use tor_rtcompat::unimpl::{FakeListener, FakeStream};
use tor_rtcompat::tls::{CertifiedConn, TlsAcceptorSettings, TlsConnector};
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
#[derive(Clone, Debug, Default)]
pub struct WasmRuntime {
    coarse: RealCoarseTimeProvider,
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
    type Stream = FakeStream;
    type Listener = FakeListener<SocketAddr>;
    type ConnectOptions = tor_rtcompat::TcpConnectOptions;
    type ListenOptions = tor_rtcompat::TcpListenOptions;
    async fn connect(&self, _a: &SocketAddr, _o: &Self::ConnectOptions) -> IoResult<FakeStream> {
        Err(no_transport())
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

impl TlsProvider<FakeStream> for WasmRuntime {
    type Connector = NoTls;
    type TlsStream = NoTlsConn;
    type Acceptor = NoTls;
    type TlsServerStream = NoTlsConn;
    fn tls_connector(&self) -> NoTls {
        NoTls
    }
    fn tls_acceptor(&self, _s: TlsAcceptorSettings) -> IoResult<NoTls> {
        Err(no_transport())
    }
    fn supports_keying_material_export(&self) -> bool {
        false
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

/// Where Arti keeps its state (guards, circuit build times, keys, directory cache) in this
/// build: "memory". A page reload loses it. Expected-failure test: xfail.test.cjs.
#[wasm_bindgen]
pub fn state_backend() -> String {
    "memory".into()
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
pub async fn bootstrap(timeout_ms: u32) -> String {
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
    let mut b = arti_client::config::TorClientConfigBuilder::from_directories("/arti-wasm/state", "/arti-wasm/cache");
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
    let st = client.bootstrap_status();
    say(format!(
        r#"{{"step":"end","fraction":{:.2},"text":{:?},"refusedConnections":{}}}"#,
        st.as_frac(),
        st.to_string(),
        REFUSED.load(std::sync::atomic::Ordering::SeqCst)
    ));
    out
}

/// Send Arti's log lines (safe logging stays on: addresses are redacted) to the console.
#[wasm_bindgen(start)]
pub fn start() {
    struct Console;
    impl std::io::Write for Console {
        fn write(&mut self, b: &[u8]) -> std::io::Result<usize> {
            let s = String::from_utf8_lossy(b);
            let s = s.trim_end();
            if !s.is_empty() {
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
        .with_max_level(tracing::Level::INFO)
        .try_init();
}
