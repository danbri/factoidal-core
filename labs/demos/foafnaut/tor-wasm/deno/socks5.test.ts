// Tests of the SOCKS5 server with a fake Tor side (no network). Run:
// deno test --allow-net labs/demos/foafnaut/tor-wasm/deno/socks5.test.ts
import { proxyCheck, REP, replyFor, startSocks5, type Socks5Event, type TorStreams } from "./socks5.ts";

/** A fake Tor side: answers every stream with a fixed HTTP reply; records what was opened. */
function fakeTor() {
  const opened: { partition: string; host: string; port: number }[] = [];
  const sent = new Map<number, string>();
  const queued = new Map<number, Uint8Array[]>();
  let next = 1;
  const tor: TorStreams = {
    open(partition, host, port) {
      if (host === "fail.example") return Promise.reject(new Error("tor: remote hostname not found"));
      opened.push({ partition, host, port });
      const h = next++;
      sent.set(h, "");
      queued.set(h, []);
      return Promise.resolve(h);
    },
    async write(h, data) {
      sent.set(h, sent.get(h)! + new TextDecoder().decode(data));
      if (sent.get(h)!.includes("\r\n\r\n") && queued.get(h)!.length === 0) {
        const body = `from ${opened[h - 1].partition}!`;
        queued.get(h)!.push(new TextEncoder().encode(`HTTP/1.1 200 OK\r\nContent-Length: ${body.length}\r\nConnection: close\r\n\r\n${body}`));
      }
      return data.length;
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
  return { tor, opened, sent };
}

async function handshake(port: number, user: string, pass: string, methods = [2]) {
  const c = await Deno.connect({ hostname: "127.0.0.1", port });
  const read = async (n: number) => {
    const b = new Uint8Array(n); let got = 0;
    while (got < n) { const k = await c.read(b.subarray(got)); if (k === null) break; got += k; }
    return Array.from(b.subarray(0, got));
  };
  await c.write(new Uint8Array([5, methods.length, ...methods]));
  const greet = await read(2);
  if (greet[1] !== 2) return { c, greet, auth: [] as number[], read };
  const u = new TextEncoder().encode(user), p = new TextEncoder().encode(pass);
  await c.write(new Uint8Array([1, u.length, ...u, p.length, ...p]));
  return { c, greet, auth: await read(2), read };
}

Deno.test("Deno's fetch through socks5h sends the name and the partition; the reply comes back", async () => {
  const { tor, opened } = fakeTor();
  const s = startSocks5(tor);
  try {
    for (const site of ["siteA.example", "siteB.example"]) {
      const client = Deno.createHttpClient({ proxy: { transport: "socks5", url: `socks5h://127.0.0.1:${s.port}`, basicAuth: { username: site, password: s.password } } } as Deno.CreateHttpClientOptions);
      const res = await fetch("http://exampleonionaddressxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx.onion/", { client });
      const body = await res.text();
      client.close();
      if (body !== `from ${site}!`) throw new Error(`body ${JSON.stringify(body)}`);
    }
    const want = "exampleonionaddressxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx.onion";
    if (opened.length !== 2 || opened[0].host !== want || opened[0].port !== 80 || opened[0].partition !== "siteA.example" || opened[1].partition !== "siteB.example") {
      throw new Error(JSON.stringify(opened));
    }
  } finally { s.stop(); }
});

Deno.test("a wrong password is refused and no stream is opened", async () => {
  const { tor, opened } = fakeTor();
  const events: Socks5Event[] = [];
  const s = startSocks5(tor, (e) => events.push(e));
  try {
    const { c, auth } = await handshake(s.port, "siteA", "not-the-password");
    c.close();
    if (auth.join() !== "1,1") throw new Error(`auth reply ${auth}`);
    const client = Deno.createHttpClient({ proxy: { transport: "socks5", url: `socks5h://127.0.0.1:${s.port}`, basicAuth: { username: "x", password: "wrong" } } } as Deno.CreateHttpClientOptions);
    let failed = false;
    try { await (await fetch("http://a.example/", { client })).text(); } catch { failed = true; }
    client.close();
    if (!failed || opened.length !== 0) throw new Error("fetch with a wrong password got through");
  } finally { s.stop(); }
});

Deno.test("no username/password method: refused with 0xFF", async () => {
  const s = startSocks5(fakeTor().tor);
  try {
    const { c, greet } = await handshake(s.port, "", "", [0]);
    c.close();
    if (greet.join() !== "5,255") throw new Error(`greeting reply ${greet}`);
  } finally { s.stop(); }
});

Deno.test("BIND and UDP ASSOCIATE are refused (command not supported)", async () => {
  const s = startSocks5(fakeTor().tor);
  try {
    for (const cmd of [2, 3]) {
      const { c, auth, read } = await handshake(s.port, "siteA", s.password);
      if (auth.join() !== "1,0") throw new Error(`auth ${auth}`);
      await c.write(new Uint8Array([5, cmd, 0, 1, 127, 0, 0, 1, 0, 80]));
      const rep = await read(10);
      c.close();
      if (rep[1] !== REP.commandNotSupported) throw new Error(`cmd ${cmd} reply ${rep}`);
    }
  } finally { s.stop(); }
});

Deno.test("a Tor error is given to the client as a SOCKS reply code", async () => {
  const s = startSocks5(fakeTor().tor);
  try {
    const { c, read } = await handshake(s.port, "siteA", s.password);
    const name = new TextEncoder().encode("fail.example");
    await c.write(new Uint8Array([5, 1, 0, 3, name.length, ...name, 0, 80]));
    const rep = await read(10);
    c.close();
    if (rep[1] !== REP.hostUnreachable) throw new Error(`reply ${rep}`);
  } finally { s.stop(); }
  if (replyFor("timeout") !== REP.ttlExpired || replyFor("refused: x") !== REP.notAllowed) throw new Error("replyFor");
});

Deno.test("start-up check: with NO_PROXY set, every request still reaches the proxy; without the fix, the check sees the bypass", async () => {
  const before = Deno.env.get("NO_PROXY");
  const events: Socks5Event[] = [];
  const s = startSocks5(fakeTor().tor, (e) => events.push(e));
  const seen = () => events.flatMap((e) => (e.ev === "proxy-check" ? [e.target] : []));
  try {
    // Control: a client made with NO_PROXY in force. Loopback and 10/8 go direct.
    Deno.env.set("NO_PROXY", "localhost,127.0.0.1,::1,10.0.0.0/8");
    const plain = (port: number, username: string, password: string) =>
      Deno.createHttpClient({ proxy: { transport: "socks5", url: `socks5h://127.0.0.1:${port}`, basicAuth: { username, password } } } as Deno.CreateHttpClientOptions);
    const missed = await proxyCheck(s.port, s.password, seen, plain);
    if (missed.length === 0) throw new Error("control: expected the bypass to be seen");
    events.length = 0;
    // torHttpClient clears NO_PROXY: nothing is missed.
    Deno.env.set("NO_PROXY", "localhost,127.0.0.1,::1,10.0.0.0/8");
    const missed2 = await proxyCheck(s.port, s.password, seen);
    if (missed2.length !== 0) throw new Error(`requests around the proxy: ${missed2}`);
  } finally {
    s.stop();
    if (before === undefined) Deno.env.delete("NO_PROXY"); else Deno.env.set("NO_PROXY", before);
  }
});
