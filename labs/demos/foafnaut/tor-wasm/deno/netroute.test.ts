// The page host's Tor route (native_net.ts `wireRoute`, `netAnswer`, `socketOpen`) with a fake
// Tor side and a local server that counts what reaches it. Every refused path must give status 0
// and reach the server zero times (no direct connection). Run:
// deno test -A labs/demos/foafnaut/tor-wasm/deno/netroute.test.ts
import { netAnswer, socketOpen, wireRoute, type NetWire } from "../../native_net.ts";
import { startSocks5, torRoute, type TorStreams } from "./socks5.ts";

function fakeTor() {
  const opened: { partition: string; host: string; port: number }[] = [];
  const queued = new Map<number, Uint8Array[]>();
  let next = 1;
  const tor: TorStreams = {
    open(partition, host, port) {
      opened.push({ partition, host, port });
      const h = next++;
      queued.set(h, []);
      return Promise.resolve(h);
    },
    async write(h) {
      const q = queued.get(h)!;
      if (q.length === 0) q.push(new TextEncoder().encode("HTTP/1.1 200 OK\r\nContent-Length: 3\r\nConnection: close\r\n\r\ntor"));
      return 0;
    },
    async read(h) {
      for (let i = 0; i < 100; i++) {
        const q = queued.get(h);
        if (!q) return new Uint8Array(0);
        if (q.length) return q.shift()!;
        await new Promise((r) => setTimeout(r, 5));
      }
      return new Uint8Array(0);
    },
    close(h) { queued.delete(h); },
  };
  return { tor, opened };
}

/** A local server that counts requests and TCP connections. */
function counter() {
  let hits = 0;
  const server = Deno.serve({ hostname: "127.0.0.1", port: 0, onListen() {} }, () => { hits++; return new Response("direct"); });
  return { url: `http://127.0.0.1:${server.addr.port}/`, port: server.addr.port, hits: () => hits, stop: () => server.shutdown() };
}

const wire = (url: string, extra: Partial<NetWire> = {}): NetWire => ({ id: 7, method: "GET", url, headers: [], ...extra });

Deno.test("a tor wire goes through SOCKS5 in its partition; the server is not reached directly", async () => {
  const { tor, opened } = fakeTor();
  const s = startSocks5(tor);
  const route = torRoute(s.port, s.password);
  const srv = counter();
  try {
    const a = await netAnswer(wire(srv.url, { tor: true, partition: "https://site-a.example" }), { tor: route, torOnly: true });
    if (a.status !== 200 || atob(a.bodyBase64 ?? "") !== "tor") throw new Error(JSON.stringify(a));
    if (opened.length !== 1 || opened[0].partition !== "https://site-a.example" || opened[0].host !== "127.0.0.1") throw new Error(JSON.stringify(opened));
    if (srv.hits() !== 0) throw new Error("direct request");
  } finally { route.close(); s.stop(); await srv.stop(); }
});

Deno.test("fail closed: no direct request on any refused path", async () => {
  const { tor, opened } = fakeTor();
  const s = startSocks5(tor);
  const route = torRoute(s.port, s.password);
  const srv = counter();
  try {
    const cases: [string, NetWire, Parameters<typeof netAnswer>[1]][] = [
      ["tor wire, no Tor route", wire(srv.url, { tor: true, partition: "https://a.example" }), {}],
      ["tor wire with an address", wire(srv.url, { tor: true, partition: "https://a.example", address: "127.0.0.1", port: srv.port }), { tor: route }],
      ["tor wire asking to resolve", wire(srv.url, { tor: true, partition: "https://a.example", resolve: true }), { tor: route }],
      ["tor wire with no partition", wire(srv.url, { tor: true }), { tor: route }],
      ["tor wire in partition null", wire(srv.url, { tor: true, partition: "null" }), { tor: route }],
      ["direct wire in Tor mode", wire(srv.url), { tor: route, torOnly: true }],
      ["direct resolve in Tor mode", wire(srv.url, { resolve: true }), { tor: route, torOnly: true }],
      ["direct address in Tor mode", wire(srv.url, { address: "127.0.0.1", port: srv.port }), { tor: route, torOnly: true }],
    ];
    for (const [name, w, o] of cases) {
      const a = await netAnswer(w, o);
      if (a.status !== 0 || a.addresses) throw new Error(`${name}: ${JSON.stringify(a)}`);
    }
    const ws = await socketOpen(wire(`ws://127.0.0.1:${srv.port}/`, { method: "WEBSOCKET" }), { torOnly: true });
    if (ws.answer.status !== 0 || ws.socket) throw new Error("WebSocket in Tor mode opened");
    if (srv.hits() !== 0 || opened.length !== 0) throw new Error(`hits ${srv.hits()} opened ${opened.length}`);
    // Control: the same direct wire outside Tor mode does reach the server.
    const c = await netAnswer(wire(srv.url), {});
    if (c.status !== 200 || srv.hits() !== 1) throw new Error("control: direct wire did not reach the server");
  } finally { route.close(); s.stop(); await srv.stop(); }
});

Deno.test("wireRoute table", () => {
  const r = { client: () => { throw new Error("unused"); } } as never;
  const t = (w: Partial<NetWire>, o: object) => wireRoute(wire("http://x.example/", w), o);
  const want: [string, string][] = [
    [t({ tor: true, partition: "https://a" }, { tor: r }), "tor"],
    [t({ tor: true, partition: "https://a" }, {}), "refuse"],
    [t({}, {}), "direct"],
    [t({}, { torOnly: true }), "refuse"],
  ];
  for (const [got, exp] of want) if (got !== exp) throw new Error(`${got} != ${exp}`);
});
