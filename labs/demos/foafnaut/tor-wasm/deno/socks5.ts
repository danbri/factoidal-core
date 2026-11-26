// SOCKS5 server (RFC 1928) with username/password authentication (RFC 1929) in front of the Tor
// streams of the worker. Only CONNECT is served. The user name is the partition (the top-level
// site): streams of different user names use different circuits. The password is a secret made
// per session, so no other local process can use the port. A domain name is passed to Tor as it
// is and resolved by the exit; nothing is resolved here.
//
// EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
// WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.

/** The Tor side: the stream exports of the wasm module, or a fake in tests. */
export interface TorStreams {
  open(partition: string, host: string, port: number): Promise<number>;
  read(h: number, max: number): Promise<Uint8Array>;
  write(h: number, data: Uint8Array): Promise<number>;
  close(h: number): void;
}

// RFC 1928 section 6 reply codes.
export const REP = {
  ok: 0, general: 1, notAllowed: 2, hostUnreachable: 4, refused: 5, ttlExpired: 6,
  commandNotSupported: 7, addressNotSupported: 8,
} as const;

/** Reads exact byte counts from a connection; keeps bytes that arrived early. */
class Reader {
  private buf = new Uint8Array(0);
  constructor(private conn: Deno.Conn) {}
  async exact(n: number): Promise<Uint8Array> {
    while (this.buf.length < n) {
      const chunk = new Uint8Array(4096);
      const got = await this.conn.read(chunk);
      if (got === null) throw new Error("closed during handshake");
      const next = new Uint8Array(this.buf.length + got);
      next.set(this.buf);
      next.set(chunk.subarray(0, got), this.buf.length);
      this.buf = next;
    }
    const out = this.buf.slice(0, n);
    this.buf = this.buf.slice(n);
    return out;
  }
  /** Bytes read past the handshake (a client may send data before our reply). */
  rest(): Uint8Array {
    const r = this.buf;
    this.buf = new Uint8Array(0);
    return r;
  }
}

function sameBytes(a: Uint8Array, b: Uint8Array): boolean {
  // Time does not depend on where the bytes differ.
  let d = a.length ^ b.length;
  for (let i = 0; i < Math.max(a.length, b.length); i++) d |= (a[i] ?? 0) ^ (b[i] ?? 0);
  return d === 0;
}

function ipv6Text(b: Uint8Array): string {
  const g: string[] = [];
  for (let i = 0; i < 16; i += 2) g.push(((b[i] << 8) | b[i + 1]).toString(16));
  return g.join(":");
}

/** Map an error of `TorStreams.open` to a reply code. */
export function replyFor(err: string): number {
  if (err.startsWith("timeout")) return REP.ttlExpired;
  if (err.startsWith("refused")) return REP.notAllowed;
  if (/not found|unreachable|resolve/i.test(err)) return REP.hostUnreachable;
  if (/refused/i.test(err)) return REP.refused;
  return REP.general;
}

/** User name of the start-up check: such a request is recorded and refused, never sent to Tor.
 *  The host fetches loopback and reserved names with it and requires every one to arrive here:
 *  Deno's fetch sends a host on the NO_PROXY list directly, around the proxy (measured with
 *  Deno 2.9.8: http://127.0.0.1/ went direct while NO_PROXY listed 127.0.0.1). */
export const PROXY_CHECK_USER = "foafnaut-proxy-check";

export type Socks5Event = { ev: "refused"; why: string } | { ev: "proxy-check"; target: string } | { ev: "stream"; partition: string; ok: boolean; rep: number };

/** Serve one client connection to the end. */
export async function serveOne(conn: Deno.Conn, password: Uint8Array, tor: TorStreams, note: (e: Socks5Event) => void = () => {}): Promise<void> {
  const r = new Reader(conn);
  const send = (b: number[]) => conn.write(new Uint8Array(b));
  const reply = (rep: number) => send([5, rep, 0, 1, 0, 0, 0, 0, 0, 0]);
  try {
    // Greeting: VER NMETHODS METHODS. Only method 2 (username/password) is accepted.
    const [ver, nm] = await r.exact(2);
    if (ver !== 5) { note({ ev: "refused", why: "not SOCKS5" }); return; }
    const methods = await r.exact(nm);
    if (!methods.includes(2)) { await send([5, 0xff]); note({ ev: "refused", why: "no username/password method" }); return; }
    await send([5, 2]);
    // RFC 1929: VER ULEN UNAME PLEN PASSWD.
    const [aver, ulen] = await r.exact(2);
    const uname = await r.exact(ulen);
    const [plen] = await r.exact(1);
    const pass = await r.exact(plen);
    const partition = new TextDecoder("utf-8", { ignoreBOM: true }).decode(uname);
    if (aver !== 1 || !sameBytes(pass, password) || ulen === 0 || !/^[\x21-\x7e]+$/.test(partition)) {
      await send([1, 1]);
      note({ ev: "refused", why: "authentication failed" });
      return;
    }
    await send([1, 0]);
    // Request: VER CMD RSV ATYP DST.ADDR DST.PORT.
    const [rver, cmd, , atyp] = await r.exact(4);
    if (rver !== 5) { note({ ev: "refused", why: "bad request version" }); return; }
    let host: string;
    if (atyp === 1) host = Array.from(await r.exact(4)).join(".");
    else if (atyp === 3) { const [n] = await r.exact(1); host = new TextDecoder("utf-8", { ignoreBOM: true }).decode(await r.exact(n)); }
    else if (atyp === 4) host = ipv6Text(await r.exact(16));
    else { await reply(REP.addressNotSupported); note({ ev: "refused", why: "address type" }); return; }
    const pb = await r.exact(2);
    const port = (pb[0] << 8) | pb[1];
    if (cmd !== 1) { await reply(REP.commandNotSupported); note({ ev: "refused", why: "only CONNECT" }); return; }
    if (partition === PROXY_CHECK_USER) { await reply(REP.notAllowed); note({ ev: "proxy-check", target: `${host}:${port}` }); return; }
    if (host.length === 0 || port === 0) { await reply(REP.notAllowed); note({ ev: "refused", why: "empty host or port 0" }); return; }
    let h: number;
    try {
      h = await tor.open(partition, host, port);
    } catch (e) {
      const rep = replyFor(String((e as Error)?.message ?? e));
      await reply(rep);
      note({ ev: "stream", partition, ok: false, rep });
      return;
    }
    await reply(REP.ok);
    note({ ev: "stream", partition, ok: true, rep: REP.ok });
    await pump(conn, r.rest(), h, tor);
  } catch {
    // The client went away or sent too little: nothing more to do.
  } finally {
    try { conn.close(); } catch { /* already closed */ }
  }
}

/** Copy bytes both ways until either side ends; then close both. */
async function pump(conn: Deno.Conn, early: Uint8Array, h: number, tor: TorStreams): Promise<void> {
  let done = false;
  const finish = () => {
    if (done) return;
    done = true;
    tor.close(h);
    try { conn.close(); } catch { /* already closed */ }
  };
  const up = (async () => {
    if (early.length) await tor.write(h, early);
    const b = new Uint8Array(16384);
    while (!done) {
      const n = await conn.read(b);
      if (n === null) break;
      await tor.write(h, b.slice(0, n));
    }
  })().catch(() => {}).finally(finish);
  const down = (async () => {
    while (!done) {
      const d = await tor.read(h, 16384);
      if (d.length === 0) break;
      let off = 0;
      while (off < d.length) off += await conn.write(d.subarray(off));
    }
  })().catch(() => {}).finally(finish);
  await Promise.all([up, down]);
}

/** Listen on 127.0.0.1 (a port the system picks). Returns the port and the session password. */
export function startSocks5(tor: TorStreams, note?: (e: Socks5Event) => void): { port: number; password: string; stop: () => void } {
  const secret = new Uint8Array(32);
  crypto.getRandomValues(secret);
  const password = Array.from(secret, (b) => b.toString(16).padStart(2, "0")).join("");
  const pw = new TextEncoder().encode(password);
  const listener = Deno.listen({ hostname: "127.0.0.1", port: 0, transport: "tcp" });
  (async () => {
    for await (const c of listener) serveOne(c, pw, tor, note);
  })().catch(() => {});
  return { port: (listener.addr as Deno.NetAddr).port, password, stop: () => listener.close() };
}

/** Names the start-up check fetches. Each must reach the server through the proxy. */
export const PROXY_CHECK_URLS = ["http://127.0.0.1:80/", "http://localhost:80/", "http://[::1]:80/", "http://10.255.255.1:80/", "http://proxy-check.invalid:80/"];

/** Make an HTTP client for Deno's fetch that sends every request through the SOCKS5 server
 *  (socks5h: names go to the exit). Clears NO_PROXY and no_proxy first: Deno reads them when a
 *  client is made and sends listed hosts directly. Needs --allow-env. */
export function torHttpClient(port: number, username: string, password: string): Deno.HttpClient {
  for (const k of ["NO_PROXY", "no_proxy"]) Deno.env.delete(k);
  return Deno.createHttpClient({ proxy: { transport: "socks5", url: `socks5h://127.0.0.1:${port}`, basicAuth: { username, password } } } as Deno.CreateHttpClientOptions);
}

/** The start-up check: fetch each PROXY_CHECK_URLS entry with user PROXY_CHECK_USER and return
 *  the ones that did NOT reach the server (empty means every request went through the proxy). */
export async function proxyCheck(port: number, password: string, seen: () => string[] | Promise<string[]>, make = torHttpClient): Promise<string[]> {
  const client = make(port, PROXY_CHECK_USER, password);
  try {
    for (const u of PROXY_CHECK_URLS) {
      try { await (await fetch(u, { client, signal: AbortSignal.timeout(3000) })).body?.cancel(); } catch { /* refused: expected */ }
    }
  } finally { client.close(); }
  const got = new Set(await seen());
  return PROXY_CHECK_URLS.filter((u) => {
    const x = new URL(u);
    const h = x.hostname.replace(/^\[|\]$/g, "");
    const forms = h === "::1" ? ["::1", "0:0:0:0:0:0:0:1"] : [h];
    return !forms.some((f) => got.has(`${f}:${x.port || "80"}`));
  });
}
