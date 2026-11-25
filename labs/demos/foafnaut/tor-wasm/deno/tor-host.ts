// Start the Arti wasm worker with narrow permissions and run one bootstrap (and optionally one
// stream request) through it. Prints JSON lines.
//
// EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
// WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW. Not trusted for real users.
//
// deno run --unstable-worker-options --allow-net --allow-read deno/tor-host.ts \
//   --dangerously-use-unreviewed-tor-transport [--config arti.toml] [--timeout 60000] \
//   [--request HOST:PORT ...] [--debug]
const args = Deno.args;
const flag = (n: string) => args.includes(n);
const opt = (n: string) => { const i = args.indexOf(n); return i >= 0 ? args[i + 1] : undefined; };
const ack = flag("--dangerously-use-unreviewed-tor-transport") ? "dangerously-use-unreviewed-tor-transport" : "";
const config = opt("--config") ? await Deno.readTextFile(opt("--config")!) : undefined;
const timeoutMs = Number(opt("--timeout") ?? 60000);
const requests = args.flatMap((a, i) => (a === "--request" ? [args[i + 1]] : []));

console.error("EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.");
const dir = new URL("./", import.meta.url);
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
const pending = new Map<number, (v: { result: unknown; dialled: number; open: number }) => void>();
const ready = new Promise<void>((res) => {
  worker.onmessage = (e) => {
    if (e.data.ready) return res();
    pending.get(e.data.id)?.(e.data);
    pending.delete(e.data.id);
  };
});
const call = (m: Record<string, unknown>) => new Promise<{ result: unknown; dialled: number; open: number }>((res) => {
  const id = nextId++;
  pending.set(id, res);
  worker.postMessage({ id, ...m });
});
await ready;
if (flag("--debug")) await call({ op: "debug", on: true });
const en = await call({ op: "enable", ack });
console.log(JSON.stringify({ step: "transport", enabled: en.result }));
const b = await call({ op: "bootstrap", timeoutMs, config });
for (const l of String(b.result).trim().split("\n")) console.log(l);
console.log(JSON.stringify({ step: "host", dialled: b.dialled, open: b.open }));
for (const request of requests) {
  const at = request.lastIndexOf(":");
  const host = request.slice(0, at), port = Number(request.slice(at + 1));
  const r = await call({ op: "stream", host, port, request: `GET / HTTP/1.0\r\nHost: ${host}\r\n\r\n`, max: 2048, timeoutMs });
  console.log(String(r.result));
}
worker.terminate();
