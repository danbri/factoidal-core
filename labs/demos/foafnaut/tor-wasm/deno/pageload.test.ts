// The page loader in Tor mode (native_html_document.ts `setTorNet`, issue 1060, record
// 2026-11-25-foafnaut-tor-onion-routing.md section 21a). A fake engine stands for the ops
// `navigation` and `subresource` (the Lean decisions are proved in Net.NavigationTheorems and
// built in the native engine); a fake Tor side and a local server that counts requests check the
// host: every request goes through the Tor route, and no path reaches the server directly. Run:
// deno test -A labs/demos/foafnaut/tor-wasm/deno/pageload.test.ts
import { readSource, readSubresource, setTorNet } from "../../native_html_document.ts";
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
      if (q.length === 0) {
        q.push(new TextEncoder().encode("HTTP/1.1 200 OK\r\nContent-Type: text/html\r\nContent-Length: 10\r\nConnection: close\r\n\r\n<p>tor</p>"));
      }
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

function counter() {
  let hits = 0;
  const server = Deno.serve({ hostname: "127.0.0.1", port: 0, onListen() {} }, () => { hits++; return new Response("direct"); });
  return { url: `http://127.0.0.1:${server.addr.port}/`, hits: () => hits, stop: () => server.shutdown() };
}

/** A fake of the engine's two ops in Tor mode: one tor wire in the origin's partition, then done. */
function fakeEngine(seen: Record<string, unknown>[]) {
  const op = (request: Record<string, unknown>) => {
    seen.push(request);
    if (request.action === "cancel") return {};
    if (request.action === "start") {
      const url = String(request.url);
      return { id: 1, wire: { id: 1, method: "GET", url, headers: [], tor: request.tor === true, partition: new URL(url).origin } };
    }
    const a = request.answer as { status?: number; headers?: [string, string][] };
    if (!a?.status) return { id: 1, fail: "network error" };
    const type = (a.headers ?? []).find(([k]) => k.toLowerCase() === "content-type")?.[1] ?? "";
    return { id: 1, done: { status: a.status, type, url: String(seen.find((r) => r.action === "start")!.url) } };
  };
  return { navigation: op, subresource: op };
}

Deno.test("Tor mode: the document and a subresource go through the Tor route; no direct request", async () => {
  const { tor, opened } = fakeTor();
  const s = startSocks5(tor);
  const route = torRoute(s.port, s.password);
  const srv = counter();
  setTorNet(route);
  try {
    const seen: Record<string, unknown>[] = [];
    const engine = fakeEngine(seen);
    const doc = await readSource(srv.url, undefined, undefined, { navigate: engine.navigation });
    if (!doc.source.includes("tor")) throw new Error(`document: ${doc.source}`);
    if (!seen.some((r) => r.action === "start" && r.tor === true)) throw new Error("navigation not started in Tor mode");
    const seenSub: Record<string, unknown>[] = [];
    const sub = await readSubresource(fakeEngine(seenSub), "image", srv.url + "i.png", srv.url, 1 << 20);
    if (sub.bytes.length === 0) throw new Error("subresource: no bytes");
    if (!seenSub.some((r) => r.action === "start" && r.tor === true)) throw new Error("subresource not started in Tor mode");
    if (opened.length !== 2 || opened.some((o) => o.partition !== new URL(srv.url).origin)) throw new Error(JSON.stringify(opened));
    if (srv.hits() !== 0) throw new Error("direct request");
  } finally { setTorNet(undefined); route.close(); s.stop(); await srv.stop(); }
});

Deno.test("Tor mode fails closed: no engine route means no fetch", async () => {
  const { tor, opened } = fakeTor();
  const s = startSocks5(tor);
  const route = torRoute(s.port, s.password);
  const srv = counter();
  setTorNet(route);
  try {
    const refused = async (name: string, f: () => Promise<unknown>) => {
      let ok = false;
      try { await f(); } catch (e) { ok = /Tor mode|refused|network error/.test(String(e)); }
      if (!ok) throw new Error(`${name}: not refused`);
    };
    await refused("document with no navigation op", () => readSource(srv.url));
    await refused("sheet with the before path", () =>
      readSubresource(undefined, "style", srv.url + "a.css", srv.url, 1 << 20, undefined,
        () => fetch(srv.url).then(async (r) => ({ url: srv.url, bytes: new Uint8Array(await r.arrayBuffer()), contentType: "" }))));
    await refused("image with no subresource op", () => readSubresource({}, "image", srv.url + "i.png", srv.url, 1 << 20));
    // An engine that answers a wire not marked tor: the host refuses it (torOnly).
    const direct = fakeEngine([]);
    const plain = (r: Record<string, unknown>) => direct.navigation({ ...r, tor: false });
    await refused("a wire not marked tor", () => readSource(srv.url, undefined, undefined, { navigate: plain }));
    if (srv.hits() !== 0 || opened.length !== 0) throw new Error(`hits ${srv.hits()} opened ${opened.length}`);
  } finally { setTorNet(undefined); route.close(); s.stop(); await srv.stop(); }
  // Control: outside Tor mode the same document is read directly.
  const srv2 = counter();
  try {
    const d = await readSource(srv2.url);
    if (d.source !== "direct" || srv2.hits() !== 1) throw new Error("control: direct read failed");
  } finally { await srv2.stop(); }
});
