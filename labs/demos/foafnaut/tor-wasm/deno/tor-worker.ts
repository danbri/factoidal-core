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

const IPV4 = /^(25[0-5]|2[0-4]\d|1?\d?\d)(\.(25[0-5]|2[0-4]\d|1?\d?\d)){3}$/;
const isIpLiteral = (s: string) => IPV4.test(s) || (/^[0-9a-fA-F:.]+$/.test(s) && s.includes(":"));

const conns = new Map<number, Deno.TcpConn>();
let next = 1;
let dialled = 0;

(globalThis as unknown as { torHost: unknown }).torHost = {
  async connect(ip: string, port: number): Promise<number> {
    if (!isIpLiteral(ip)) throw new Error("refused: not an IP literal");
    if (!(port > 0 && port < 65536)) throw new Error("refused: bad port");
    dialled++;
    const c = await Deno.connect({ hostname: ip, port, transport: "tcp" });
    const h = next++;
    conns.set(h, c);
    return h;
  },
  async read(h: number, max: number): Promise<Uint8Array> {
    const c = conns.get(h);
    if (!c) return new Uint8Array(0);
    const b = new Uint8Array(Math.min(max, 65536));
    const n = await c.read(b);
    return n === null ? new Uint8Array(0) : b.subarray(0, n);
  },
  async write(h: number, view: Uint8Array): Promise<number> {
    const data = view.slice(); // copy now: the view points into module memory
    const c = conns.get(h);
    if (!c) throw new Error("closed");
    let off = 0;
    while (off < data.length) off += await c.write(data.subarray(off));
    return data.length;
  },
  close(h: number): void {
    const c = conns.get(h);
    if (!c) return;
    conns.delete(h);
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
  | { id: number; op: "stream"; host: string; port: number; request: string; max: number; timeoutMs: number };

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
  else if (m.op === "stream") result = await tor.stream_request(m.host, m.port, m.request, m.max, m.timeoutMs);
  (self as unknown as Worker).postMessage({ id: m.id, result, dialled, open: conns.size });
};
(self as unknown as Worker).postMessage({ ready: true });
