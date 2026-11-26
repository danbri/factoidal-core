// Start the Arti wasm worker with narrow permissions and run one bootstrap (and optionally one
// stream request) through it. Prints JSON lines.
//
// EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
// WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW. Not trusted for real users.
//
// deno run --unstable-worker-options --allow-net --allow-read [--allow-write --allow-run --allow-env] deno/tor-host.ts \
//   --dangerously-use-unreviewed-tor-transport [--config arti.toml] [--timeout 60000] \
//   [--request [PARTITION@]HOST:PORT | NEWID | PAR | END ...] [--fetch PARTITION@URL ...] [--debug] [--trace-conns] [--restart-check] [--hold MS] [--state-dir DIR]
// --trace-conns: after each step, one JSON line per TCP connection of that step and one "loop"
// line (worst event-loop lag, and every stall over 1 s: CPU work blocks reads and timers) (times in ms
// from the worker's start, bytes in and out, connect errors; no addresses), and a summary.
const args = Deno.args;
const flag = (n: string) => args.includes(n);
const opt = (n: string) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : undefined; };
const ack = flag("--dangerously-use-unreviewed-tor-transport") ? "dangerously-use-unreviewed-tor-transport" : "";
const config = opt("--config") ? await Deno.readTextFile(opt("--config")!) : undefined;
const timeoutMs = Number(opt("--timeout") ?? 60000);
const requests = args.flatMap((a, i) => (a === "--request" ? [args[i + 1]] : []));
// --fetch PARTITION@URL: fetch from this (main) thread through the worker's SOCKS5 server, as
// the browser's network pool will (socks5h: names go to the exit). All --fetch run at once.
const fetches = args.flatMap((a, i) => (a === "--fetch" ? [args[i + 1]] : []));

console.error("EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.");
const dir = new URL("./", import.meta.url);
import { proxyCheck, type Socks5Event, torHttpClient } from "./socks5.ts";
import { openTorState, type TorStateStore } from "./tor-state.ts";
// --state-dir DIR: keep Arti's state in a sealed local LWS storage in DIR (needs
// FOAFNAUT_TOR_STATE_KEY). Without it, or when the store cannot be opened, state is in memory only.
const stateDir = opt("--state-dir");
let store: TorStateStore | undefined;
if (stateDir) {
  const opened = await openTorState(stateDir, (l) => console.log(JSON.stringify(l)));
  if (typeof opened === "string") console.log(JSON.stringify({ step: "tor-state", saved: false, why: opened }));
  else store = opened;
}
type ConnTrace = { h: number; dial: number; open?: number; firstIn?: number; inB: number; outB: number; reads: number; closed?: number; err?: string; msg?: string; v6?: boolean; writes?: number; firstOut?: number; firstOutB?: number; eof?: number; closedBy?: string };
type Reply = { result: unknown; dialled: number; open: number; socks?: unknown[]; streamsOpen?: number; conns?: ConnTrace[]; at?: number; loop?: { maxLagMs: number; stalls: { at: number; ms: number }[] } };
/** --trace-conns: print the connections a step made, and a summary of where they stopped. */
function printConns(step: string, r: Reply) {
  if (!r.conns) return;
  for (const c of r.conns) console.log(JSON.stringify({ step: "conn", during: step, ...c }));
  const cs = r.conns;
  const n = (f: (c: ConnTrace) => boolean) => cs.filter(f).length;
  console.log(JSON.stringify({ step: "conns", during: step, at: r.at, made: cs.length,
    connectFailed: n((c) => c.err !== undefined), connectTimedOut: n((c) => c.err === "TimedOut"),
    stillConnecting: n((c) => c.err === undefined && c.open === undefined), ipv6Dials: n((c) => c.v6 === true),
    ipv6Failed: n((c) => c.v6 === true && c.err !== undefined), opened: n((c) => c.open !== undefined),
    sentNothing: n((c) => c.open !== undefined && c.outB === 0),
    sentButNoReply: n((c) => c.outB > 0 && c.inB === 0),
    // inB 0 after a write: no ServerHello came, so the stop is in the TLS handshake, before the
    // Tor link handshake (VERSIONS, CERTS). A reply then a stop is later.
    noReplyThenPeerClosed: n((c) => c.outB > 0 && c.inB === 0 && c.eof !== undefined),
    noReplyClosedByArti: n((c) => c.outB > 0 && c.inB === 0 && c.eof === undefined && c.closed !== undefined),
    replied: n((c) => c.inB > 0) }));
  if (r.loop) console.log(JSON.stringify({ step: "loop", during: step, ...r.loop }));
}

/** Start the worker with narrow permissions; return a call function and the worker. */
async function startWorker() {
  const worker = new Worker(new URL("tor-worker.ts", dir), {
    type: "module",
    deno: {
      permissions: {
        net: true,
        read: [new URL("../.build/web/", dir)],
        write: false, env: false, run: false, ffi: false, sys: false, import: false,
      },
    },
  } as WorkerOptions);
  let nextId = 1;
  const pending = new Map<number, (v: Reply) => void>();
  await new Promise<void>((res) => {
    worker.onmessage = (e) => {
      if (e.data.ready) return res();
      pending.get(e.data.id)?.(e.data);
      pending.delete(e.data.id);
    };
  });
  const call = (m: Record<string, unknown>) => new Promise<Reply>((res) => {
    const id = nextId++;
    pending.set(id, res);
    worker.postMessage({ id, ...m });
  });
  return { worker, call };
}

/** One client run: optional saved state in, bootstrap, requests; returns the state out. */
async function runOnce(label: string, saved?: string): Promise<string> {
  const { worker, call } = await startWorker();
  if (flag("--debug")) await call({ op: "debug", on: true });
  if (flag("--trace-conns")) await call({ op: "trace", on: true });
  if (store) {
    const fromStore = await store.load();
    if (fromStore !== undefined) saved = fromStore;
    await call({ op: "store", kind: "lws-sealed" });
  }
  if (saved !== undefined) {
    const n = await call({ op: "load", state: saved });
    console.log(JSON.stringify({ step: "state-load", run: label, keys: n.result }));
  }
  const en = await call({ op: "enable", ack });
  console.log(JSON.stringify({ step: "transport", run: label, enabled: en.result }));
  // Save the state every 60 s while the client runs (Arti stores its own state every 60 s), so a
  // crash loses at most about two minutes of it.
  let saving = false;
  const saver = store ? setInterval(async () => {
    if (saving) return;
    saving = true;
    try {
      const snap = String((await call({ op: "snapshot" })).result);
      if (snap !== "{}") await store!.save(snap);
      console.log(JSON.stringify({ step: "tor-state", run: label, periodicSave: true }));
    } catch (e) {
      console.log(JSON.stringify({ step: "tor-state", run: label, periodicSave: false, error: String((e as Error).message) }));
    } finally { saving = false; }
  }, 60000) : undefined;
  const b = await call({ op: "bootstrap", timeoutMs, config });
  for (const l of String(b.result).trim().split("\n")) console.log(l);
  console.log(JSON.stringify({ step: "host", run: label, dialled: b.dialled, open: b.open }));
  printConns("bootstrap", b);
  // --request [PARTITION@]HOST:PORT. Streams of different partitions use different circuits.
  // --request PAR ... --request END: the requests between run at the same time (one promise
  // each), so several circuits and channels are built at once.
  const one = async (spec: string) => {
    const atSign = spec.indexOf("@");
    const partition = atSign >= 0 ? spec.slice(0, atSign) : "default";
    const request = atSign >= 0 ? spec.slice(atSign + 1) : spec;
    const at = request.lastIndexOf(":");
    const host = request.slice(0, at), port = Number(request.slice(at + 1));
    const r = await call({ op: "stream", partition, host, port, request: `GET / HTTP/1.0\r\nHost: ${host}\r\n\r\n`, max: 2048, timeoutMs });
    console.log(String(r.result));
    printConns(`stream ${partition}`, r);
    return String(r.result);
  };
  for (let i = 0; i < requests.length; i++) {
    const spec = requests[i];
    if (spec === "NEWID") {
      // New identity: later streams of every partition use circuits no earlier stream used.
      const n = await call({ op: "new-identity" });
      console.log(JSON.stringify({ step: "new-identity", partitionsForgotten: n.result }));
      continue;
    }
    if (spec === "PAR") {
      const group: string[] = [];
      while (++i < requests.length && requests[i] !== "END") group.push(requests[i]);
      const t = performance.now();
      const out = await Promise.all(group.map(one));
      const ok = out.filter((o) => /"ok":true/.test(o)).length;
      console.log(JSON.stringify({ step: "parallel", run: label, streams: group.length, ok, ms: Math.round(performance.now() - t) }));
      continue;
    }
    await one(spec);
  }
  if (fetches.length) {
    const sp = await call({ op: "socks", timeoutMs });
    const { port, password } = sp.result as { port: number; password: string };
    // Start-up check: loopback, private and reserved names must all reach the proxy.
    const missed = await proxyCheck(port, password, async () =>
      ((await call({ op: "isolated" })).socks as Socks5Event[] ?? []).flatMap((e) => (e.ev === "proxy-check" ? [e.target] : [])));
    console.log(JSON.stringify({ step: "proxy-check", run: label, ok: missed.length === 0, missed }));
    if (missed.length) throw new Error("refused: some requests would go around Tor; no fetch is made");
    const t = performance.now();
    const out = await Promise.all(fetches.map(async (spec) => {
      const atSign = spec.indexOf("@");
      const partition = spec.slice(0, atSign), url = spec.slice(atSign + 1);
      const client = torHttpClient(port, partition, password);
      const t1 = performance.now();
      try {
        const res = await fetch(url, { client, signal: AbortSignal.timeout(timeoutMs) });
        const body = await res.text();
        return { partition, ok: res.ok, status: res.status, bytes: body.length, body: body.slice(0, 60), ms: Math.round(performance.now() - t1) };
      } catch (e) {
        return { partition, ok: false, error: String((e as Error).message).slice(0, 200), ms: Math.round(performance.now() - t1) };
      } finally { client.close(); }
    }));
    for (const o of out) console.log(JSON.stringify({ step: "socks-fetch", run: label, ...o }));
    const after = await call({ op: "isolated" });
    console.log(JSON.stringify({ step: "socks", run: label, fetches: out.length, ok: out.filter((o) => o.ok).length, ms: Math.round(performance.now() - t), streamsOpenAfter: after.streamsOpen, events: after.socks?.length }));
  }
  // Arti stores its state every 60 s and when its circuit manager is dropped. --hold waits for
  // the periodic store before the snapshot.
  const hold = Number(opt("--hold") ?? 0);
  if (hold > 0) await new Promise((r) => setTimeout(r, hold));
  if (saver !== undefined) clearInterval(saver);
  while (saving) await new Promise((r) => setTimeout(r, 50));
  await call({ op: "close" });
  await new Promise((r) => setTimeout(r, 200));
  const snap = String((await call({ op: "snapshot" })).result);
  if (store) {
    await store.save(snap);
    console.log(JSON.stringify({ step: "tor-state", run: label, saved: true, keys: Object.keys(JSON.parse(snap)) }));
  }
  worker.terminate();
  return snap;
}

/** The guard identities in a state snapshot (key "guards"), sorted; empty when absent. */
function guardIds(snap: string): string[] {
  try {
    const g = JSON.parse(JSON.parse(snap).guards ?? "null");
    const ids = new Set<string>();
    JSON.stringify(g, (k, v) => { if ((k === "ed25519" || k === "rsa") && typeof v === "string") ids.add(v); return v; });
    return [...ids].sort();
  } catch { return []; }
}

const first = await runOnce("1");
console.log(JSON.stringify({ step: "state", run: "1", keys: Object.keys(JSON.parse(first)) }));
if (flag("--restart-check")) {
  // The saved state stays in this process: this check does not write it anywhere.
  const second = await runOnce("2", store ? undefined : first);
  const a = guardIds(first), b = guardIds(second);
  const same = a.length > 0 && a.every((x) => b.includes(x));
  console.log(JSON.stringify({ step: "restart-check", via: store ? "sealed LWS storage" : "host memory", guardsBefore: a.length, guardsAfter: b.length, sameGuards: same }));
  if (store && stateDir) {
    // The state on disk must not show any guard identity in clear text.
    let clear = 0;
    for await (const f of walkFiles(`${stateDir}/pod`)) {
      const text = new TextDecoder("utf-8", { fatal: false }).decode(await Deno.readFile(f));
      if (a.some((id) => text.includes(id))) clear++;
    }
    console.log(JSON.stringify({ step: "at-rest-check", filesWithGuardIdsInClearText: clear }));
  }
}
await store?.close();

async function* walkFiles(d: string): AsyncGenerator<string> {
  for await (const e of Deno.readDir(d)) {
    const p = `${d}/${e.name}`;
    if (e.isDirectory) yield* walkFiles(p); else if (e.isFile) yield p;
  }
}

