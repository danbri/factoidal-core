// Start the Arti wasm worker with narrow permissions and run one bootstrap (and optionally one
// stream request) through it. Prints JSON lines.
//
// EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
// WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW. Not trusted for real users.
//
// deno run --unstable-worker-options --allow-net --allow-read [--allow-write --allow-run --allow-env] deno/tor-host.ts \
//   --dangerously-use-unreviewed-tor-transport [--config arti.toml] [--timeout 60000] \
//   [--request HOST:PORT ...] [--debug] [--restart-check] [--hold MS] [--state-dir DIR]
const args = Deno.args;
const flag = (n: string) => args.includes(n);
const opt = (n: string) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : undefined; };
const ack = flag("--dangerously-use-unreviewed-tor-transport") ? "dangerously-use-unreviewed-tor-transport" : "";
const config = opt("--config") ? await Deno.readTextFile(opt("--config")!) : undefined;
const timeoutMs = Number(opt("--timeout") ?? 60000);
const requests = args.flatMap((a, i) => (a === "--request" ? [args[i + 1]] : []));

console.error("EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.");
const dir = new URL("./", import.meta.url);
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
type Reply = { result: unknown; dialled: number; open: number };

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
  const b = await call({ op: "bootstrap", timeoutMs, config });
  for (const l of String(b.result).trim().split("\n")) console.log(l);
  console.log(JSON.stringify({ step: "host", run: label, dialled: b.dialled, open: b.open }));
  for (const request of requests) {
    const at = request.lastIndexOf(":");
    const host = request.slice(0, at), port = Number(request.slice(at + 1));
    const r = await call({ op: "stream", host, port, request: `GET / HTTP/1.0\r\nHost: ${host}\r\n\r\n`, max: 2048, timeoutMs });
    console.log(String(r.result));
  }
  // Arti stores its state every 60 s and when its circuit manager is dropped. --hold waits for
  // the periodic store before the snapshot.
  const hold = Number(opt("--hold") ?? 0);
  if (hold > 0) await new Promise((r) => setTimeout(r, hold));
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

