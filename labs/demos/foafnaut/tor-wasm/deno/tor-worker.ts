// Deno worker that runs the Arti (Tor) wasm module and gives it TCP through Deno.connect.
// Started by tor-host.ts with narrow permissions (network, and read of the module only).
//
// EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
// WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW. Not trusted for real users.
//
// Rules held here:
// - Only IP literals are dialled. A host name is refused, so this worker never resolves a name
//   (Arti dials relays by address; exits resolve the names a client asks for).
// - Bytes from the module are copied before any await: the module's memory can grow and move.
// - There is no other network path in this worker.
// Record: docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md, section 12.
import init, * as tor from "../.build/web/foafnaut_tor_wasm.js";

import { isIpLiteral } from "./ip-literal.ts";
import { startSocks5, type Socks5Event } from "./socks5.ts";

const conns = new Map<number, Deno.TcpConn>();
let next = 1;
let dialled = 0;
// Per-connection trace (op "trace"): times in ms from the worker's start, byte counts, and
// connect errors. Addresses are not recorded. Used to find where channels stall.
const t0 = performance.now();
const ms = () => Math.round(performance.now() - t0);
type ConnTrace = { h: number; dial: number; open?: number; firstIn?: number; inB: number; outB: number; reads: number; closed?: number; err?: string };
const traces: ConnTrace[] = [];
const traceOf = new Map<number, ConnTrace>();
let tracing = false;
// Event-loop lag: the module has one thread, so CPU work in it (parsing a consensus, checking
// signatures) delays every socket read and timer. A tick every 50 ms records how late it ran;
// runs of more than 1 s are kept with their start time.
let lagMax = 0;
const stalls: { at: number; ms: number }[] = [];
let lastTick = performance.now();
setInterval(() => {
  const now = performance.now();
  const late = now - lastTick - 50;
  lastTick = now;
  if (late > lagMax) lagMax = late;
  if (late > 1000) stalls.push({ at: Math.round(now - t0 - late), ms: Math.round(late) });
}, 50);

(globalThis as unknown as { torHost: unknown }).torHost = {
  async connect(ip: string, port: number): Promise<number> {
    if (!isIpLiteral(ip)) throw new Error("refused: not an IP literal");
    if (!(port > 0 && port < 65536)) throw new Error("refused: bad port");
    dialled++;
    const tr: ConnTrace = { h: 0, dial: ms(), inB: 0, outB: 0, reads: 0 };
    traces.push(tr);
    let c: Deno.TcpConn;
    try {
      c = await Deno.connect({ hostname: ip, port, transport: "tcp" });
    } catch (e) {
      tr.err = String((e as Error).name ?? e);
      tr.closed = ms();
      throw e;
    }
    const h = next++;
    tr.h = h; tr.open = ms();
    traceOf.set(h, tr);
    conns.set(h, c);
    return h;
  },
  async read(h: number, max: number): Promise<Uint8Array> {
    const c = conns.get(h);
    if (!c) return new Uint8Array(0);
    const b = new Uint8Array(Math.min(max, 65536));
    const n = await c.read(b);
    const tr = traceOf.get(h);
    if (tr) { tr.reads++; if (n && tr.firstIn === undefined) tr.firstIn = ms(); tr.inB += n ?? 0; }
    return n === null ? new Uint8Array(0) : b.subarray(0, n);
  },
  async write(h: number, view: Uint8Array): Promise<number> {
    const data = view.slice(); // copy now: the view points into module memory
    const c = conns.get(h);
    if (!c) throw new Error("closed");
    let off = 0;
    while (off < data.length) off += await c.write(data.subarray(off));
    const tr = traceOf.get(h);
    if (tr) tr.outB += data.length;
    return data.length;
  },
  close(h: number): void {
    const c = conns.get(h);
    if (!c) return;
    conns.delete(h);
    const tr = traceOf.get(h);
    if (tr) tr.closed = ms();
    try { c.close(); } catch { /* already closed */ }
  },
};

await init({ module_or_path: await Deno.readFile(new URL("../.build/web/foafnaut_tor_wasm_bg.wasm", import.meta.url)) });

type Msg =
  | { id: number; op: "enable"; ack: string }
  | { id: number; op: "debug"; on: boolean }
  | { id: number; op: "snapshot" }
  | { id: number; op: "close" }
  | { id: number; op: "store"; kind: string }
  | { id: number; op: "load"; state: string }
  | { id: number; op: "bootstrap"; timeoutMs: number; config?: string }
  | { id: number; op: "stream"; partition: string; host: string; port: number; request: string; max: number; timeoutMs: number }
  | { id: number; op: "new-identity" }
  | { id: number; op: "isolated" }
  | { id: number; op: "trace"; on: boolean }
  | { id: number; op: "socks"; timeoutMs: number };

// The SOCKS5 server, started once by op "socks". The port and password go only to the thread
// that started this worker. Events keep no host names.
let socks: { port: number; password: string } | undefined;
const socksEvents: Socks5Event[] = [];

self.onmessage = async (e: MessageEvent<Msg>) => {
  const m = e.data;
  let result: unknown;
  if (m.op === "enable") result = tor.enable_unreviewed_transport(m.ack);
  else if (m.op === "debug") result = tor.log_debug(m.on);
  else if (m.op === "snapshot") result = tor.state_snapshot();
  else if (m.op === "close") result = tor.close();
  else if (m.op === "store") result = tor.set_state_store(m.kind);
  else if (m.op === "load") result = tor.state_load(m.state);
  else if (m.op === "bootstrap") result = await tor.bootstrap(m.timeoutMs, m.config);
  else if (m.op === "stream") result = await tor.stream_request(m.partition, m.host, m.port, m.request, m.max, m.timeoutMs);
  else if (m.op === "new-identity") result = tor.new_identity();
  else if (m.op === "isolated") result = tor.isolated_context();
  else if (m.op === "trace") { tracing = m.on; result = tracing; }
  else if (m.op === "socks") {
    if (!socks) {
      const t = m.timeoutMs;
      const s = startSocks5({
        open: (p, host, port) => tor.stream_open(p, host, port, t),
        read: (h, max) => tor.stream_read(h, max),
        write: (h, d) => tor.stream_write(h, d),
        close: (h) => { tor.stream_close(h); },
      }, (e) => { if (socksEvents.length < 1000) socksEvents.push(e); });
      socks = { port: s.port, password: s.password };
    }
    result = socks;
  }
  const conn = tracing ? traces.splice(0, traces.length) : undefined;
  const socksSeen = socks ? { socks: socksEvents.splice(0, socksEvents.length), streamsOpen: tor.streams_open() } : {};
  const loop = tracing ? { maxLagMs: Math.round(lagMax), stalls: stalls.splice(0, stalls.length) } : undefined;
  if (tracing) lagMax = 0;
  (self as unknown as Worker).postMessage({ id: m.id, result, dialled, open: conns.size, ...socksSeen, ...(conn ? { conns: conn, at: ms(), loop } : {}) });
};
(self as unknown as Worker).postMessage({ ready: true });
