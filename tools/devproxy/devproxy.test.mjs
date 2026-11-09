// Tests of the developer proxy. Local origin servers only; no internet.
import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import { createHash } from "node:crypto";
import fs from "node:fs";
import http from "node:http";
import https from "node:https";
import os from "node:os";
import path from "node:path";
import { after, before, test } from "node:test";
import tls from "node:tls";
import { fileURLToPath } from "node:url";
import zlib from "node:zlib";
import { SERVICES, tokenize, transformHtml } from "./services.mjs";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const PROXY = path.join(HERE, "devproxy.mjs");
const root = fs.mkdtempSync(path.join(fs.realpathSync(os.tmpdir()), "devproxy-test-"));
const home = path.join(root, "home");

function ossl(args) {
  execFileSync("openssl", args, { cwd: root, stdio: ["ignore", "ignore", "pipe"] });
}
function makeCa(name) {
  ossl(["genpkey", "-algorithm", "EC", "-pkeyopt", "ec_paramgen_curve:P-256", "-out", `${name}.key`]);
  ossl(["req", "-x509", "-new", "-key", `${name}.key`, "-subj", `/CN=${name}`, "-days", "2", "-sha256", "-out", `${name}.crt`]);
}
function makeLeaf(ca, name, san) {
  fs.writeFileSync(path.join(root, `${name}.ext`), `subjectAltName=${san}\n`);
  ossl(["genpkey", "-algorithm", "EC", "-pkeyopt", "ec_paramgen_curve:P-256", "-out", `${name}.key`]);
  ossl(["req", "-new", "-key", `${name}.key`, "-subj", `/CN=${name}`, "-out", `${name}.csr`]);
  ossl(["x509", "-req", "-in", `${name}.csr`, "-CA", `${ca}.crt`, "-CAkey", `${ca}.key`, "-set_serial", "7",
    "-days", "2", "-sha256", "-extfile", `${name}.ext`, "-out", `${name}.crt`]);
  return { key: fs.readFileSync(path.join(root, `${name}.key`)), cert: fs.readFileSync(path.join(root, `${name}.crt`)) };
}

const PAGE = `<!DOCTYPE html><html><head><title>T</title>
<link rel="stylesheet" href="/a.css"><link rel="preload" as="script" href="/a.js">
<SCRIPT src="/a.js"></SCRIPT><style>p>a{color:red}</style></head>
<body onload="x()"><p onclick='y()' class=c>Text <a href="/next">link</a></p>
<img src="/i.png"><iframe src="/f"></iframe><video src="/v"><source src="/s"></video>
<form action="javascript:z()"><input name=q></form></body></html>`;
let connections = 0;
function originHandler(req, res) {
  const u = new URL(req.url, "http://x");
  if (u.pathname === "/plain") {
    res.writeHead(200, "Fine", { "Content-Type": "text/plain", "X-Case-Kept": "Yes", "Content-Length": 5 });
    return res.end("hello");
  }
  if (u.pathname === "/chunked") {
    res.writeHead(201, { "Content-Type": "application/octet-stream" });
    res.write(Buffer.from([0, 1, 2, 255]));
    return res.end(Buffer.from([254, 13, 10, 0]));
  }
  if (u.pathname === "/secret") {
    res.writeHead(302, { "Set-Cookie": "sid=SECRETCOOKIEVALUE", Location: "/plain?token=SECRETLOCATION", "Content-Length": 0 });
    return res.end();
  }
  if (u.pathname === "/page") {
    res.writeHead(200, { "Content-Type": "text/html; charset=utf-8" });
    return res.end(PAGE);
  }
  if (u.pathname === "/gz") {
    res.writeHead(200, { "Content-Type": "text/html", "Content-Encoding": "gzip" });
    return res.end(zlib.gzipSync(PAGE));
  }
  if (u.pathname === "/a.js") {
    res.writeHead(200, { "Content-Type": "text/javascript" });
    return res.end("alert(1)");
  }
  if (u.pathname === "/a.css") {
    res.writeHead(200, { "Content-Type": "text/css" });
    return res.end("p{}");
  }
  if (u.pathname === "/i.png") {
    res.writeHead(200, { "Content-Type": "image/png" });
    return res.end(Buffer.from([137, 80, 78, 71]));
  }
  res.writeHead(404, { "Content-Length": 0 });
  res.end();
}
function startOrigin(server) {
  server.on("connection", () => { connections++; });
  return new Promise((resolve) => server.listen(0, "127.0.0.1", () => resolve(server.address().port)));
}
let plainOrigin, tlsOrigin, badOrigin, plainPort, tlsPort, badPort, testCaPem;
before(async () => {
  makeCa("testca");
  makeCa("otherca");
  testCaPem = path.join(root, "testca.crt");
  plainOrigin = http.createServer(originHandler);
  tlsOrigin = https.createServer(makeLeaf("testca", "good", "DNS:localhost"), originHandler);
  badOrigin = https.createServer(makeLeaf("otherca", "bad", "DNS:localhost"), originHandler);
  plainPort = await startOrigin(plainOrigin);
  tlsPort = await startOrigin(tlsOrigin);
  badPort = await startOrigin(badOrigin);
});
const running = new Set();
after(() => {
  for (const p of running) p.kill("SIGKILL");
  for (const s of [plainOrigin, tlsOrigin, badOrigin]) s.closeAllConnections?.(), s.close();
  fs.rmSync(root, { recursive: true, force: true });
});

function startProxy(args, env = {}, nodeArgs = []) {
  return new Promise((resolve, reject) => {
    const child = spawn(process.execPath, [...nodeArgs, PROXY, "--port", "0", ...args], {
      env: { ...process.env, FOAFNAUT_DEVPROXY_HOME: home, NODE_EXTRA_CA_CERTS: testCaPem, ...env },
      stdio: ["ignore", "pipe", "pipe"],
    });
    running.add(child);
    let out = "", err = "";
    child.stderr.on("data", (d) => { err += d; });
    child.stdout.on("data", (d) => {
      out += d;
      const m = /LISTENING 127\.0\.0\.1:(\d+)/.exec(out);
      if (m) resolve({ child, port: Number(m[1]), log: () => err, stop: () => stopChild(child) });
    });
    child.on("exit", (code) => { running.delete(child); reject(new Error(`exit ${code}: ${err}`)); });
  });
}
function stopChild(child) {
  return new Promise((resolve) => {
    if (child.exitCode !== null) return resolve();
    child.once("exit", resolve);
    child.kill("SIGTERM");
  });
}
const P = "--dangerously-allow-private-upstream";

function collect(res) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    res.on("data", (c) => chunks.push(c));
    res.on("end", () => resolve({ status: res.statusCode, statusMessage: res.statusMessage, rawHeaders: res.rawHeaders, body: Buffer.concat(chunks) }));
    res.on("error", reject);
  });
}
/** A plain request through the proxy, in absolute form. */
function viaPlain(proxyPort, url, { method = "GET", headers = {} } = {}) {
  return new Promise((resolve, reject) => {
    const req = http.request({ host: "127.0.0.1", port: proxyPort, method, path: url, headers, agent: false });
    req.on("response", (res) => collect(res).then(resolve, reject));
    req.on("error", reject);
    req.end();
  });
}
/** An HTTPS request through CONNECT, that trusts only the devproxy CA. */
function viaTls(proxyPort, url, { method = "GET", headers = {} } = {}) {
  const u = new URL(url);
  return new Promise((resolve, reject) => {
    const connect = http.request({ host: "127.0.0.1", port: proxyPort, method: "CONNECT", path: u.host, agent: false });
    connect.on("connect", (res, socket) => {
      assert.equal(res.statusCode, 200);
      const secure = tls.connect({ socket, servername: u.hostname, ca: fs.readFileSync(path.join(home, "ca", "ca.crt")), ALPNProtocols: ["http/1.1"] });
      secure.on("error", reject);
      secure.on("secureConnect", () => {
        const req = http.request({ createConnection: () => secure, method, path: u.pathname + u.search, headers: { Host: u.host, ...headers } });
        req.on("response", (r) => collect(r).then((value) => { secure.destroy(); resolve(value); }, reject));
        req.on("error", reject);
        req.end();
      });
    });
    connect.on("error", reject);
    connect.end();
  });
}
function endToEnd(raw) {
  const out = [];
  for (let i = 0; i < raw.length; i += 2) if (!["connection", "keep-alive"].includes(raw[i].toLowerCase())) out.push(raw[i], raw[i + 1]);
  return out;
}
function header(r, name) {
  for (let i = 0; i < r.rawHeaders.length; i += 2) if (r.rawHeaders[i].toLowerCase() === name) return r.rawHeaders[i + 1];
  return undefined;
}
function assertSame(a, b) {
  assert.equal(b.status, a.status);
  assert.equal(b.statusMessage, a.statusMessage);
  assert.deepEqual(endToEnd(b.rawHeaders), endToEnd(a.rawHeaders));
  assert.deepEqual(b.body, a.body);
}
let counter = 0;
const newDir = () => path.join(root, `rec-${++counter}`);

test("record then replay returns identical status, headers and body; replay works with the origin gone", async () => {
  const dir = newDir();
  const rec = await startProxy(["--record", dir, P]);
  const urls = [[viaPlain, `http://127.0.0.1:${plainPort}/plain`], [viaPlain, `http://127.0.0.1:${plainPort}/chunked`],
    [viaTls, `https://localhost:${tlsPort}/plain`], [viaTls, `https://localhost:${tlsPort}/chunked`]];
  const recorded = [];
  for (const [via, url] of urls) recorded.push(await via(rec.port, url));
  await rec.stop();
  assert.equal(recorded[0].status, 200);
  assert.equal(recorded[0].statusMessage, "Fine");
  assert.equal(recorded[3].body.length, 8);

  // A second recording from an origin that is closed before its replay.
  const gone = http.createServer(originHandler);
  const gonePort = await new Promise((r) => gone.listen(0, "127.0.0.1", () => r(gone.address().port)));
  const dir2 = newDir();
  const rec2 = await startProxy(["--record", dir2, P]);
  const before2 = await viaPlain(rec2.port, `http://127.0.0.1:${gonePort}/plain`);
  await rec2.stop();
  gone.closeAllConnections();
  await new Promise((r) => gone.close(r));

  const replay = await startProxy(["--replay", dir]);
  const count = connections;
  for (let i = 0; i < urls.length; i++) assertSame(recorded[i], await urls[i][0](replay.port, urls[i][1]));
  assert.equal(connections, count, "replay made an origin connection");
  await replay.stop();

  const replay2 = await startProxy(["--replay", dir2]);
  assertSame(before2, await viaPlain(replay2.port, `http://127.0.0.1:${gonePort}/plain`));
  await replay2.stop();
});

test("a miss is 504 with X-Devproxy: miss and the replay process opens no outbound connection", async () => {
  const dir = newDir();
  const rec = await startProxy(["--record", dir, P]);
  await viaPlain(rec.port, `http://127.0.0.1:${plainPort}/plain`);
  await rec.stop();
  const trap = path.join(root, "trap.mjs"), trapLog = path.join(root, "outbound.log");
  fs.writeFileSync(trap, `import net from "node:net"; import dns from "node:dns"; import fs from "node:fs";
const note = (w) => fs.appendFileSync(${JSON.stringify(trapLog)}, w + "\\n");
const connect = net.Socket.prototype.connect;
net.Socket.prototype.connect = function (...a) { note("connect " + JSON.stringify(a[0])); return connect.apply(this, a); };
// The listener's own bind resolves the literal 127.0.0.1; any request to that host would show as a connect.
const lookup = dns.lookup; dns.lookup = function (...a) { if (a[0] !== "127.0.0.1") note("lookup " + a[0]); return lookup.apply(this, a); };
`);
  fs.writeFileSync(trapLog, "");
  const replay = await startProxy(["--replay", dir], {}, ["--import", trap]);
  const count = connections;
  const plainMiss = await viaPlain(replay.port, `http://127.0.0.1:${plainPort}/never-recorded`);
  const tlsMiss = await viaTls(replay.port, `https://localhost:${tlsPort}/never-recorded`);
  for (const r of [plainMiss, tlsMiss]) {
    assert.equal(r.status, 504);
    assert.equal(header(r, "x-devproxy"), "miss");
  }
  assert.equal(connections, count, "a miss reached the origin");
  assert.match(replay.log(), /MISS GET http:\/\/127\.0\.0\.1:\d+\/never-recorded/);
  await replay.stop();
  assert.equal(fs.readFileSync(trapLog, "utf8"), "", "replay opened a connection or made a DNS lookup");
});

test("credentials are absent from the WARC and the manifest, and a redacted URL still replays", async () => {
  const dir = newDir();
  const rec = await startProxy(["--record", dir, P]);
  const url = `http://127.0.0.1:${plainPort}/secret?access_token=SECRETQUERY&keep=1&Signature=SECRETSIG`;
  const headers = { Authorization: "Bearer SECRETAUTH", Cookie: "a=SECRETCLIENTCOOKIE", "X-Api-Key": "SECRETAPIKEY" };
  const first = await viaPlain(rec.port, url, { headers });
  assert.equal(header(first, "set-cookie"), "sid=SECRETCOOKIEVALUE", "the client of a record run sees the origin's answer");
  await rec.stop();
  for (const file of ["recording.warc", "manifest.json"]) {
    const text = fs.readFileSync(path.join(dir, file), "latin1");
    assert.doesNotMatch(text, /SECRET/, `${file} holds a credential value`);
    assert.match(text, /access_token=REDACTED&keep=1/);
  }
  const replay = await startProxy(["--replay", dir]);
  const again = await viaPlain(replay.port, url);
  assert.equal(again.status, 302);
  assert.equal(header(again, "set-cookie"), undefined);
  assert.equal(header(again, "location"), `http://127.0.0.1:${plainPort}/plain?token=REDACTED`);
  await replay.stop();
});

test("the WARC is WARC/1.1, holds a request and a response, and the manifest carries the body hash and TLS summary", async () => {
  const dir = newDir();
  const rec = await startProxy(["--record", dir, P]);
  const r = await viaTls(rec.port, `https://localhost:${tlsPort}/plain`);
  await rec.stop();
  const warc = fs.readFileSync(path.join(dir, "recording.warc"), "latin1");
  assert.ok(warc.startsWith("WARC/1.1\r\nWARC-Type: warcinfo\r\n"));
  assert.match(warc, /WARC-Type: response\r\n/);
  assert.match(warc, /WARC-Type: request\r\n/);
  assert.match(warc, /Content-Type: application\/http;msgtype=response\r\n/);
  const [entry] = JSON.parse(fs.readFileSync(path.join(dir, "manifest.json"), "utf8")).entries;
  assert.equal(entry.status, 200);
  assert.equal(entry.sha256, createHash("sha256").update(r.body).digest("hex"));
  assert.equal(entry.tls.authorized, true);
  assert.match(entry.tls.protocol, /^TLS/);
  assert.equal(entry.tls.issuer, "testca");
  const tampered = warc.replace("hello", "jello");
  fs.writeFileSync(path.join(dir, "recording.warc"), tampered, "latin1");
  await assert.rejects(startProxy(["--replay", dir]), /exit 2.*digest differs/s);
});

test("refuses a non-loopback bind", async () => {
  for (const host of ["0.0.0.0", "::", "localhost", "192.168.1.2"]) {
    await assert.rejects(startProxy(["--passthrough", "--host", host]), /exit 2.*127\.0\.0\.1 only/s);
  }
});

test("an upstream certificate failure is reported and recorded, and is never bypassed", async () => {
  const dir = newDir();
  const rec = await startProxy(["--record", dir, P]);
  const url = `https://localhost:${badPort}/plain`;
  const r = await viaTls(rec.port, url);
  await rec.stop();
  assert.equal(r.status, 502);
  assert.equal(header(r, "x-devproxy"), "upstream-tls-failure");
  const { entries } = JSON.parse(fs.readFileSync(path.join(dir, "manifest.json"), "utf8"));
  assert.equal(entries.length, 1);
  assert.equal(entries[0].failure.code, "UNABLE_TO_VERIFY_LEAF_SIGNATURE");
  assert.doesNotMatch(fs.readFileSync(path.join(dir, "recording.warc"), "latin1"), /WARC-Type: response/);
  await assert.rejects(startProxy(["--passthrough"], { NODE_TLS_REJECT_UNAUTHORIZED: "0" }), /exit 2.*NODE_TLS_REJECT_UNAUTHORIZED/s);
});

test("the CA is private, named, and stays out of the recording; a private upstream is refused by default", async () => {
  const dir = newDir();
  const rec = await startProxy(["--record", dir]);
  assert.match(rec.log(), /DEVELOPMENT TOOL/);
  const refused = await viaPlain(rec.port, `http://127.0.0.1:${plainPort}/plain`);
  assert.equal(refused.status, 403);
  assert.equal(header(refused, "x-devproxy"), "refused-private");
  const viaName = await viaPlain(rec.port, `http://localhost:${plainPort}/plain`);
  assert.equal(viaName.status, 403);
  await rec.stop();
  const caDir = path.join(home, "ca");
  assert.equal(fs.statSync(caDir).mode & 0o777, 0o700);
  assert.equal(fs.statSync(home).mode & 0o777, 0o700);
  assert.equal(fs.statSync(path.join(caDir, "ca.key")).mode & 0o777, 0o600);
  const subject = execFileSync("openssl", ["x509", "-in", path.join(caDir, "ca.crt"), "-noout", "-subject"], { encoding: "utf8" });
  assert.match(subject, /Foafnaut devproxy \(pseudo-trusted, development only\)/);
  assert.deepEqual(fs.readdirSync(dir).sort(), ["manifest.json", "recording.warc"]);
  assert.doesNotMatch(fs.readFileSync(path.join(dir, "recording.warc"), "latin1"), /PRIVATE KEY/);
});

test("a request that is not a proxy request is refused; a recording in a git tree is refused", async () => {
  const proxy = await startProxy(["--passthrough", P]);
  const r = await viaPlain(proxy.port, "/plain");
  assert.equal(r.status, 400);
  assert.equal(header(r, "x-devproxy"), "not-a-proxy-request");
  await proxy.stop();
  const tree = path.join(root, "tree");
  fs.mkdirSync(path.join(tree, ".git"), { recursive: true });
  await assert.rejects(startProxy(["--record", path.join(tree, "r")]), /exit 2.*git tree/s);
});

// ---------------------------------------------------------------- services
const S = "X-Foafnaut-Devproxy";
test("the ladder has the three levels", () => {
  assert.deepEqual(Object.keys(SERVICES), ["full", "no-scripts", "text-css-links"]);
});
test("tokenizer: script holding </p>, attribute holding >, comments, uppercase tags", () => {
  const kinds = (s) => [...tokenize(s)].map((t) => (t.type === "start" || t.type === "end" ? `${t.type}:${t.name}` : t.type));
  assert.deepEqual(kinds("<script>a</p>b</script>x"), ["start:script", "raw", "end:script", "text"]);
  assert.deepEqual(kinds('<a title="x>y" href=z>t</a>'), ["start:a", "text", "end:a"]);
  assert.deepEqual(kinds("<!-- <script> --><P>"), ["comment", "start:p"]);
  assert.deepEqual(kinds("<!--><b>"), ["comment", "start:b"]);
  assert.deepEqual(kinds("<!-- x --!><b>"), ["comment", "start:b"]);
  assert.deepEqual(kinds("<SCRIPT>x</ScRiPt >"), ["start:script", "raw", "end:script"]);
  assert.deepEqual(kinds("a < b <1"), ["text"]);
  assert.deepEqual(kinds("<title><b></title>"), ["start:title", "raw", "end:title"]);
  assert.deepEqual(kinds("<textarea></p></textarea>"), ["start:textarea", "raw", "end:textarea"]);
  assert.deepEqual(kinds("<!DOCTYPE html><?pi x>"), ["bogus", "bogus"]);
  // Double-escaped script data: the inner </script> does not close the element.
  assert.deepEqual(kinds("<script><!-- <script>a</script> --></script>t"), ["start:script", "raw", "end:script", "text"]);
  const unterminated = [...tokenize('<a href="x')];
  assert.equal(unterminated[0].unterminated, true);
  const attrs = [...tokenize(`<a B='1' c="2" d=3 e/>`)][0].attrs.map((a) => [a.name, a.value]);
  assert.deepEqual(attrs, [["b", "1"], ["c", "2"], ["d", "3"], ["e", ""]]);
});
test("transform: tricky input", () => {
  const f = (s, level = "no-scripts") => transformHtml(s, level).output;
  assert.equal(f("<script>if(a</p>b){}</script><p>x</p>"), "<p>x</p>");
  assert.equal(f("<!-- <script>keep</script> --><p>x"), "<!-- <script>keep</script> --><p>x");
  assert.equal(f('<A TITLE="a>b" ONCLICK="c">t</A>'), '<A TITLE="a>b" >t</A>');
  assert.equal(f(`<a onclick="d"e>`), `<a e>`);
  assert.equal(f("<a/onclick=x>"), "<a/>");
  assert.equal(f("<SCRIPT SRC=a></SCRIPT\n>z"), "z");
  assert.equal(f("<script/>still script</script>z"), "z", "/> has no effect on a script element");
  assert.equal(f("<p online-id=1>"), "<p >", "an on-prefixed name counts as an event attribute");
  assert.equal(f("<p on=1>"), "<p on=1>");
  assert.equal(f("<video><video></video>x</video>y", "text-css-links"), "y");
  assert.equal(f("<svg/>y", "text-css-links"), "y");
  assert.equal(f("<svg><title>t</title></svg>y", "text-css-links"), "y");
  const r = transformHtml('<img src=a><img src=b onclick=c><script></script><p onclick=d srcset=e>', "text-css-links");
  assert.deepEqual(r.removed, { img: 2, script: 1, "on*": 1, "image-attribute": 1 });
});
test("each service on a local page, and the recording stays byte-identical", async () => {
  const dir = newDir();
  const url = `http://127.0.0.1:${plainPort}`;
  const rec = await startProxy(["--record", dir, P]);
  const original = await viaPlain(rec.port, `${url}/page`);
  const asRecorded = await viaPlain(rec.port, `${url}/a.js`);
  await viaPlain(rec.port, `${url}/a.css`);
  await viaPlain(rec.port, `${url}/i.png`);
  await viaPlain(rec.port, `${url}/gz`);
  await rec.stop();
  const hash = () => ["recording.warc", "manifest.json"].map((f) => createHash("sha256").update(fs.readFileSync(path.join(dir, f))).digest("hex")).join();
  const stamp = hash();

  const replay = await startProxy(["--replay", dir]);
  const get = (p, service) => viaPlain(replay.port, `${url}${p}`, { headers: service ? { [S]: service } : {} });

  assertSame(original, await get("/page")); // no header: unchanged, no Applied header.
  assert.equal(header(await get("/page"), "x-foafnaut-devproxy-applied"), undefined);

  const full = await get("/page", "full");
  assert.deepEqual(full.body, original.body);
  assert.equal(header(full, "x-foafnaut-devproxy-applied"), "full");

  const ns = await get("/page", "no-scripts");
  const nsText = ns.body.toString();
  assert.equal(header(ns, "x-foafnaut-devproxy-applied"), "no-scripts");
  assert.equal(header(ns, "content-length"), String(ns.body.length));
  assert.doesNotMatch(nsText, /<script|onclick|onload/i);
  assert.match(nsText, /<img src="\/i\.png">/);
  assert.match(replay.log(), /service no-scripts: .*\/page: removed script=1 on\*=2/);

  const brutal = await get("/page", "text-css-links");
  const text = brutal.body.toString();
  assert.equal(header(brutal, "x-foafnaut-devproxy-applied"), "text-css-links");
  for (const gone of [/<script/i, /onclick/, /onload/, /<img/, /<iframe/, /<video/, /<source/, /javascript:/, /rel="preload"/]) assert.doesNotMatch(text, gone);
  for (const kept of [/<title>T<\/title>/, /rel="stylesheet" href="\/a\.css"/, /<style>p>a\{color:red\}<\/style>/, /<a href="\/next">link<\/a>/, /<form/, /<input name=q>/, /Text/]) assert.match(text, kept);

  // Other content types: unchanged, except scripts at text-css-links.
  const js = await get("/a.js", "text-css-links");
  assert.equal(js.status, 204);
  assert.equal(js.body.length, 0);
  assert.equal(header(js, "x-foafnaut-devproxy-applied"), "text-css-links");
  assert.deepEqual((await get("/a.js", "no-scripts")).body, asRecorded.body);
  assert.deepEqual((await get("/a.css", "text-css-links")).body, Buffer.from("p{}"));
  assert.deepEqual((await get("/i.png", "text-css-links")).body, Buffer.from([137, 80, 78, 71]));

  const gz = await get("/gz", "text-css-links");
  assert.equal(header(gz, "content-encoding"), undefined);
  assert.doesNotMatch(gz.body.toString(), /<script/i);

  const unknown = await get("/page", "nonsense");
  assert.equal(unknown.status, 400);
  assert.equal(header(unknown, "x-devproxy"), "unknown-service");
  await replay.stop();
  assert.equal(hash(), stamp, "a transformed replay changed the recording");

  const defaulted = await startProxy(["--replay", dir, "--default-service", "no-scripts"]);
  const d = await viaPlain(defaulted.port, `${url}/page`);
  assert.equal(header(d, "x-foafnaut-devproxy-applied"), "no-scripts");
  assert.doesNotMatch(d.body.toString(), /<script/i);
  const fullOverride = await viaPlain(defaulted.port, `${url}/page`, { headers: { [S]: "full" } });
  assert.deepEqual(fullOverride.body, original.body);
  await defaulted.stop();
  await assert.rejects(startProxy(["--replay", dir, "--default-service", "nope"]), /exit 2.*unknown service/s);
});
test("the service header does not reach the origin or the recording", async () => {
  const seen = [];
  const origin = http.createServer((req, res) => { seen.push(req.headers); res.end("x"); });
  const port = await new Promise((r) => origin.listen(0, "127.0.0.1", () => r(origin.address().port)));
  const dir = newDir();
  const rec = await startProxy(["--record", dir, P]);
  await viaPlain(rec.port, `http://127.0.0.1:${port}/`, { headers: { [S]: "no-scripts" } });
  await rec.stop();
  origin.close();
  assert.equal(seen[0]["x-foafnaut-devproxy"], undefined);
  assert.doesNotMatch(fs.readFileSync(path.join(dir, "recording.warc"), "latin1"), /X-Foafnaut-Devproxy/i);
});
