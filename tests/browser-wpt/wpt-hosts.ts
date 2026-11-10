// wpt-hosts.ts: the WPT test-mode host fetch for testharness-run.ts --wptserve.
//
// WPT's tests name their servers by WPT's own hostnames (web-platform.test, its
// subdomains www, www1, www2, the two IDN ones, and not-web-platform.test), which
// a real browser run reaches through /etc/hosts. This runner changes nothing on the
// system: in WPT test mode, and only there, a fetch to one of those names on one of
// the ports the local wptserve listens on is sent to 127.0.0.1 on that port, and an
// HTTPS fetch trusts WPT's own test CA (tools/certs/cacert.pem in the checkout),
// for this client only. Every other URL is refused: this is not a proxy, and no fetch
// in this mode reaches a real network host. `.test` is a reserved TLD (RFC 2606), so
// these names have no real host anyway.
//
// HTTP goes through Deno's fetch with a `tcp` transport: it connects to the given
// socket and keeps the URL's host in the Host header. That transport sends plain HTTP
// even for an https URL, so HTTPS goes through a small HTTP/1.1 client here instead:
// TCP to 127.0.0.1, then TLS with the URL's host for SNI and the certificate check
// (Deno.startTls) and WPT's CA as the only extra root. Either way the URL keeps its
// host, as a browser's request does after resolving the name.

/** The hosts a wptserve config makes, as tools/serve's `make-hosts-file` lists them. */
export type WptServe = {
  /** The base domains: the main one and the alternate (not-web-platform.test). */
  domains: string[];
  /** Subdomains of each base domain that resolve (`subdomains` in tools/serve). */
  subdomains: string[];
  /** Ports by scheme, as in the wptserve config (`ports`). */
  ports: Record<string, number[]>;
  /** WPT's test CA (PEM), trusted for HTTPS in this mode only. */
  caPEM?: string;
};

/** WPT's default names (tools/serve/serve.py ConfigBuilder: `subdomains`; the
 * not_subdomains, `nonexistent`, are left unresolved, as WPT means them to be). */
export const wptSubdomains = ["www", "www1", "www2", "xn--n8j6ds53lwwkrqhv28a", "xn--lve-6lad"];
export const wptDomains = ["web-platform.test", "not-web-platform.test"];

/** The ports of this runner's wptserve config (wpt-score.py serve) that a fetch may use:
 * http, http-local, http-public; https, https-local, https-public. (Its HTTP/2 server on
 * 9000 is not used: the HTTPS client here speaks HTTP/1.1.) */
export const wptPorts: Record<string, number[]> = { http: [8000, 8001, 8002, 8003], https: [8443, 8444, 8445, 8446] };

/** Every hostname of the mode: each base domain and each of its subdomains. */
export function wptHostnames(s: WptServe): Set<string> {
  const out = new Set<string>();
  for (const d of s.domains) {
    out.add(d);
    for (const sub of s.subdomains) out.add(`${sub}.${d}`);
  }
  return out;
}

/** Where a URL goes in WPT test mode: 127.0.0.1 and its port, or why it is refused. */
export function wptRoute(url: string, s: WptServe): { port: number; scheme: "http" | "https" } | { refused: string } {
  let u: URL;
  try { u = new URL(url); } catch { return { refused: `not a URL: ${url}` }; }
  const scheme = u.protocol === "http:" ? "http" : u.protocol === "https:" ? "https" : undefined;
  if (!scheme) return { refused: `WPT test mode fetches http and https only: ${u.protocol}` };
  if (u.username || u.password) return { refused: "credentials in URL" };
  if (!wptHostnames(s).has(u.hostname)) return { refused: `not a WPT host (test mode fetches only WPT's own names): ${u.hostname}` };
  const port = Number(u.port || (scheme === "http" ? 80 : 443));
  if (!(s.ports[scheme] ?? []).includes(port)) return { refused: `wptserve does not serve ${scheme} on port ${port}` };
  return { port, scheme };
}

/** A fetch that reaches only the local wptserve, by WPT's names. Redirects are followed
 * by hand, so each hop goes through the same check (a redirect off WPT's hosts is refused). */
export function wptFetcher(s: WptServe) {
  const clients = new Map<number, Deno.HttpClient>();
  const clientFor = (port: number, _scheme: string) => {
    let c = clients.get(port);
    if (!c) {
      c = Deno.createHttpClient({ proxy: { transport: "tcp", hostname: "127.0.0.1", port } });
      clients.set(port, c);
    }
    return c;
  };
  const fetchWpt = async (url: string, init: RequestInit = {}, hops = 0): Promise<Response> => {
    const r = wptRoute(url, s);
    if ("refused" in r) throw new TypeError(`WPT test mode refused ${url}: ${r.refused}`);
    const response = r.scheme === "https" ? await httpsGet(url, r.port, s.caPEM, init)
      : await fetch(url, { ...init, redirect: "manual", client: clientFor(r.port, r.scheme) } as RequestInit);
    const location = response.headers.get("location");
    // An XMLHttpRequest of a page (the engine follows redirects itself: Net.PageFetch).
    if ((init as { noFollow?: boolean }).noFollow) return Object.defineProperty(response, "finalURL", { value: url });
    if (response.status >= 300 && response.status < 400 && location) {
      await response.body?.cancel();
      if (hops >= 20) throw new TypeError(`too many redirects: ${url}`);
      return fetchWpt(new URL(location, url).href, init, hops + 1);
    }
    return Object.defineProperty(response, "finalURL", { value: url });
  };
  return { fetch: fetchWpt, close: () => { for (const c of clients.values()) c.close(); clients.clear(); } };
}

const MAX_RESPONSE_BYTES = 64 * 1048576;
/** A GET (or HEAD) over HTTPS to 127.0.0.1:port, with the URL's host for TLS (SNI and the
 * certificate check against WPT's CA) and in the Host header. HTTP/1.1, one request a
 * connection; the body by Content-Length, chunked coding, or to the end. */
async function httpsGet(url: string, port: number, caPEM: string | undefined, init: RequestInit): Promise<Response> {
  const u = new URL(url), method = (init.method ?? "GET").toUpperCase();
  if (method !== "GET" && method !== "HEAD") throw new TypeError(`WPT test mode HTTPS: ${method} not supported`);
  if (!caPEM) throw new TypeError("WPT test mode HTTPS: no WPT CA (tools/certs/cacert.pem)");
  const signal = init.signal ?? AbortSignal.timeout(30000);
  const tcp = await Deno.connect({ hostname: "127.0.0.1", port });
  const conn = await Deno.startTls(tcp, { hostname: u.hostname, caCerts: [caPEM] });
  const abort = () => { try { conn.close(); } catch { /* closed */ } };
  signal.addEventListener("abort", abort, { once: true });
  try {
    const extra = new Headers(init.headers);
    let head = `${method} ${u.pathname}${u.search} HTTP/1.1\r\nHost: ${u.host}\r\nConnection: close\r\nAccept-Encoding: identity\r\n`;
    extra.forEach((v, k) => { if (!/^(host|connection|content-length|transfer-encoding)$/i.test(k)) head += `${k}: ${v}\r\n`; });
    await conn.write(new TextEncoder().encode(head + "\r\n"));
    const chunks: Uint8Array[] = [];
    let length = 0;
    const buf = new Uint8Array(65536);
    while (true) {
      let n: number | null;
      try { n = await conn.read(buf); } catch (e) { if (length) break; throw e; }
      if (n === null) break;
      chunks.push(buf.slice(0, n)); length += n;
      if (length > MAX_RESPONSE_BYTES) throw new TypeError("WPT test mode HTTPS: response too large");
    }
    signal.throwIfAborted();
    const all = new Uint8Array(length);
    let at = 0;
    for (const c of chunks) { all.set(c, at); at += c.length; }
    const end = indexOf(all, [13, 10, 13, 10]);
    if (end < 0) throw new TypeError("WPT test mode HTTPS: no response head");
    const lines = new TextDecoder("latin1").decode(all.subarray(0, end)).split("\r\n");
    const status = Number(/^HTTP\/1\.[01] (\d{3})/.exec(lines[0])?.[1] ?? NaN);
    if (!(status >= 200 && status <= 599)) throw new TypeError(`WPT test mode HTTPS: bad status line ${lines[0]}`);
    const headers = new Headers();
    for (const l of lines.slice(1)) { const i = l.indexOf(":"); if (i > 0) headers.append(l.slice(0, i).trim(), l.slice(i + 1).trim()); }
    let body = all.subarray(end + 4);
    if (/chunked/i.test(headers.get("transfer-encoding") ?? "")) body = unchunk(body);
    else if (headers.has("content-length")) body = body.subarray(0, Number(headers.get("content-length")));
    headers.delete("transfer-encoding");
    const nullBody = method === "HEAD" || status === 204 || status === 304;
    return new Response(nullBody ? null : body, { status, headers });
  } finally {
    signal.removeEventListener("abort", abort);
    abort();
  }
}
function indexOf(a: Uint8Array, pat: number[]): number {
  outer: for (let i = 0; i + pat.length <= a.length; i++) {
    for (let j = 0; j < pat.length; j++) if (a[i + j] !== pat[j]) continue outer;
    return i;
  }
  return -1;
}
/** HTTP/1.1 chunked transfer coding (RFC 9112 section 7.1), trailers dropped. */
function unchunk(b: Uint8Array): Uint8Array {
  const out: Uint8Array[] = [];
  let at = 0, total = 0;
  while (at < b.length) {
    const eol = indexOf(b.subarray(at), [13, 10]);
    if (eol < 0) break;
    const size = parseInt(new TextDecoder("latin1").decode(b.subarray(at, at + eol)).split(";")[0].trim(), 16);
    at += eol + 2;
    if (!(size > 0)) break;
    out.push(b.subarray(at, at + size)); total += size;
    at += size + 2;
  }
  const r = new Uint8Array(total);
  let o = 0;
  for (const c of out) { r.set(c, o); o += c.length; }
  return r;
}
