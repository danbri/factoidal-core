#!/usr/bin/env node
// Foafnaut developer proxy: records real HTTP and HTTPS exchanges to WARC and
// replays them offline. A development tool for tests, not a user feature.
// See README.md in this directory for the trust rules.
import { X509Certificate, createHash, randomBytes, randomUUID } from "node:crypto";
import { execFile } from "node:child_process";
import dns from "node:dns";
import fs from "node:fs";
import http from "node:http";
import https from "node:https";
import net from "node:net";
import os from "node:os";
import path from "node:path";
import tls from "node:tls";
import { promisify } from "node:util";
import { applyService, hasService, serviceNames } from "./services.mjs";

const run = promisify(execFile);
const CA_NAME = "Foafnaut devproxy (pseudo-trusted, development only)";
const CA_DAYS = 30, LEAF_DAYS = 7, MIN_REMAINING_MS = 2 * 86400_000;
const MAX_BODY = 64 * 1048576, UPSTREAM_TIMEOUT_MS = 30_000;
const SERVICE_HEADER = "x-foafnaut-devproxy";
const HOP_BY_HOP = new Set(["connection", "proxy-connection", "keep-alive", "te", "trailer",
  "transfer-encoding", "upgrade", "proxy-authenticate", "proxy-authorization"]);
// Removed from what is stored, never hashed.
const CREDENTIAL_HEADERS = new Set(["authorization", "proxy-authorization", "cookie", "cookie2", "set-cookie",
  "set-cookie2", "x-api-key", "x-auth-token", "x-csrf-token", "x-xsrf-token", "x-amz-security-token"]);
const CREDENTIAL_PARAMS = new Set(["access_token", "id_token", "refresh_token", "token", "auth", "auth_token",
  "api_key", "apikey", "key", "password", "passwd", "pwd", "secret", "client_secret", "sig", "signature",
  "session", "sessionid", "session_id", "sid", "jsessionid", "phpsessid", "code", "x-amz-signature",
  "x-amz-credential", "x-amz-security-token", "x-goog-signature", "x-goog-credential"]);
const URL_HEADERS = new Set(["location", "content-location", "referer"]);
const REDACTED = "REDACTED";

function fail(message) {
  process.stderr.write(`devproxy: ${message}\n`);
  process.exit(2);
}
function log(message) {
  process.stderr.write(`devproxy: ${message}\n`);
}

// ----------------------------------------------------------------- arguments
const USAGE = `usage: devproxy.mjs (--record DIR|NAME | --replay DIR|NAME | --passthrough)
  [--port N] [--host 127.0.0.1] [--append] [--default-service NAME]
  [--dangerously-allow-private-upstream]
       devproxy.mjs --print-ca
A NAME with no slash is a directory under ~/.foafnaut-devproxy/recordings/.
Services: ${serviceNames().join(", ")}.`;

function parseArgs(argv) {
  const options = { mode: null, dir: null, port: 8899, host: "127.0.0.1", append: false,
    defaultService: null, allowPrivate: false, printCa: false };
  for (let i = 0; i < argv.length; i++) {
    const flag = argv[i];
    const value = () => {
      if (i + 1 >= argv.length) fail(`${flag} needs a value\n${USAGE}`);
      return argv[++i];
    };
    switch (flag) {
      case "--record": case "--replay":
        if (options.mode) fail(`choose one mode\n${USAGE}`);
        options.mode = flag.slice(2); options.dir = value(); break;
      case "--passthrough":
        if (options.mode) fail(`choose one mode\n${USAGE}`);
        options.mode = "passthrough"; break;
      case "--port": options.port = Number(value()); break;
      case "--host": options.host = value(); break;
      case "--append": options.append = true; break;
      case "--default-service": options.defaultService = value(); break;
      case "--dangerously-allow-private-upstream": options.allowPrivate = true; break;
      case "--print-ca": options.printCa = true; break;
      default: fail(`unknown argument ${flag}\n${USAGE}`);
    }
  }
  if (!options.mode && !options.printCa) fail(USAGE);
  if (options.host !== "127.0.0.1") fail(`refused: the proxy binds to 127.0.0.1 only, not ${options.host}`);
  if (!Number.isInteger(options.port) || options.port < 0 || options.port > 65535) fail("bad --port");
  if (options.defaultService && !hasService(options.defaultService)) {
    fail(`unknown service ${options.defaultService}; services: ${serviceNames().join(", ")}`);
  }
  return options;
}

// ------------------------------------------------------------ home and paths
const homeDir = () => process.env.FOAFNAUT_DEVPROXY_HOME ?? path.join(os.homedir(), ".foafnaut-devproxy");
function ensurePrivateDir(dir) {
  fs.mkdirSync(dir, { recursive: true, mode: 0o700 });
  fs.chmodSync(dir, 0o700);
}
function isInside(child, parent) {
  const rel = path.relative(parent, child);
  return rel === "" || (!rel.startsWith("..") && !path.isAbsolute(rel));
}
function insideGitTree(dir) {
  for (let at = path.resolve(dir); ; at = path.dirname(at)) {
    if (fs.existsSync(path.join(at, ".git"))) return at;
    if (at === path.dirname(at)) return null;
  }
}
function recordingDir(arg, caDir) {
  const dir = arg.includes("/") ? path.resolve(arg) : path.join(homeDir(), "recordings", arg);
  const gitTree = insideGitTree(dir);
  if (gitTree) fail(`refused: recording directory ${dir} is inside the git tree ${gitTree}; recordings are private`);
  if (isInside(dir, caDir) || isInside(caDir, dir)) fail(`refused: recording directory ${dir} overlaps the CA directory`);
  return dir;
}

// ---------------------------------------------------- pseudo-trusted local CA
async function openssl(args, cwd) {
  await run("openssl", args, { cwd, maxBuffer: 1048576 });
}
class LocalCa {
  constructor(dir) {
    this.dir = dir;
    this.key = path.join(dir, "ca.key");
    this.cert = path.join(dir, "ca.crt");
    this.leafDir = path.join(dir, "leaf");
    this.contexts = new Map();
  }
  async ensure() {
    ensurePrivateDir(path.dirname(this.dir));
    ensurePrivateDir(this.dir);
    if (fs.existsSync(this.key) && fs.existsSync(this.cert)) {
      const x = new X509Certificate(fs.readFileSync(this.cert));
      if (new Date(x.validTo).getTime() - Date.now() > MIN_REMAINING_MS) {
        ensurePrivateDir(this.leafDir);
        this.x509 = x;
        return;
      }
    }
    fs.rmSync(this.leafDir, { recursive: true, force: true });
    const work = fs.mkdtempSync(path.join(this.dir, "new-"));
    try {
      fs.writeFileSync(path.join(work, "ca.cnf"), [
        "[req]", "distinguished_name=dn", "x509_extensions=v3", "prompt=no",
        "[dn]", `CN=${CA_NAME}`,
        "[v3]", "basicConstraints=critical,CA:TRUE,pathlen:0", "keyUsage=critical,keyCertSign,cRLSign",
        "subjectKeyIdentifier=hash", ""].join("\n"), { mode: 0o600 });
      await openssl(["genpkey", "-algorithm", "EC", "-pkeyopt", "ec_paramgen_curve:P-256", "-out", "ca.key"], work);
      fs.chmodSync(path.join(work, "ca.key"), 0o600);
      await openssl(["req", "-x509", "-new", "-config", "ca.cnf", "-key", "ca.key", "-sha256",
        "-days", String(CA_DAYS), "-out", "ca.crt"], work);
      fs.renameSync(path.join(work, "ca.key"), this.key);
      fs.renameSync(path.join(work, "ca.crt"), this.cert);
    } finally {
      fs.rmSync(work, { recursive: true, force: true });
    }
    ensurePrivateDir(this.leafDir);
    this.x509 = new X509Certificate(fs.readFileSync(this.cert));
  }
  /** A TLS server context for one host; concurrent callers share one mint. */
  contextFor(host) {
    let pending = this.contexts.get(host);
    if (!pending) {
      pending = this.#mint(host);
      this.contexts.set(host, pending);
      pending.catch(() => this.contexts.delete(host));
    }
    return pending;
  }
  async #mint(host) {
    const isIp = net.isIP(host) !== 0;
    if (!isIp && !/^[a-z0-9._-]+$/.test(host)) throw new Error(`host name not accepted for a leaf: ${host}`);
    const stem = path.join(this.leafDir, createHash("sha256").update(host).digest("hex"));
    const keyFile = `${stem}.key`, certFile = `${stem}.crt`;
    if (!this.#leafUsable(keyFile, certFile)) {
      const work = fs.mkdtempSync(path.join(this.leafDir, "new-"));
      try {
        fs.writeFileSync(path.join(work, "leaf.ext"), [
          "basicConstraints=critical,CA:FALSE", "keyUsage=critical,digitalSignature",
          "extendedKeyUsage=serverAuth", `subjectAltName=${isIp ? "IP" : "DNS"}:${host}`, ""].join("\n"), { mode: 0o600 });
        await openssl(["genpkey", "-algorithm", "EC", "-pkeyopt", "ec_paramgen_curve:P-256", "-out", "leaf.key"], work);
        fs.chmodSync(path.join(work, "leaf.key"), 0o600);
        await openssl(["req", "-new", "-key", "leaf.key", "-subj", "/CN=Foafnaut devproxy leaf", "-out", "leaf.csr"], work);
        await openssl(["x509", "-req", "-in", "leaf.csr", "-CA", this.cert, "-CAkey", this.key, "-sha256",
          "-set_serial", `0x${randomBytes(16).toString("hex").replace(/^./, "1")}`,
          "-days", String(LEAF_DAYS), "-extfile", "leaf.ext", "-out", "leaf.crt"], work);
        fs.renameSync(path.join(work, "leaf.key"), keyFile);
        fs.renameSync(path.join(work, "leaf.crt"), certFile);
      } finally {
        fs.rmSync(work, { recursive: true, force: true });
      }
    }
    return tls.createSecureContext({ key: fs.readFileSync(keyFile), cert: fs.readFileSync(certFile) });
  }
  #leafUsable(keyFile, certFile) {
    if (!fs.existsSync(keyFile) || !fs.existsSync(certFile)) return false;
    const x = new X509Certificate(fs.readFileSync(certFile));
    return x.checkIssued(this.x509) && new Date(x.validTo).getTime() - Date.now() > 3600_000;
  }
}

// ------------------------------------------------------------ redaction, URLs
function redactQuery(search) {
  if (!search || search === "?") return "";
  const parts = search.slice(1).split("&").map((part) => {
    const eq = part.indexOf("=");
    if (eq < 0) return part;
    let name = part.slice(0, eq);
    try { name = decodeURIComponent(name.replace(/\+/g, " ")); } catch { /* keep the raw name */ }
    return CREDENTIAL_PARAMS.has(name.toLowerCase()) ? `${part.slice(0, eq)}=${REDACTED}` : part;
  });
  return `?${parts.join("&")}`;
}
/** The stored form of a URL: no user information, no fragment, no credential values. */
function storedUrl(url) {
  return url.origin + url.pathname + redactQuery(url.search);
}
function redactUrlValue(value, base) {
  try {
    const u = new URL(value, base);
    if (u.protocol !== "http:" && u.protocol !== "https:") return value;
    const q = redactQuery(u.search);
    const hasUser = u.username !== "" || u.password !== "";
    if (q === u.search && !hasUser) return value;
    return u.origin + u.pathname + q + u.hash;
  } catch { return value; }
}
function sha256(data) {
  return createHash("sha256").update(data).digest("hex");
}

// ----------------------------------------------------------------------- WARC
const CRLF = "\r\n";
function warcRecord(type, fields, block) {
  const lines = ["WARC/1.1", `WARC-Type: ${type}`];
  for (const [name, value] of fields) if (value !== undefined) lines.push(`${name}: ${value}`);
  lines.push(`WARC-Block-Digest: sha256:${sha256(block)}`, `Content-Length: ${block.length}`);
  return Buffer.concat([Buffer.from(lines.join(CRLF) + CRLF + CRLF, "latin1"), block, Buffer.from(CRLF + CRLF, "latin1")]);
}
function httpBlock(startLine, rawHeaders, body) {
  let head = startLine + CRLF;
  for (let i = 0; i < rawHeaders.length; i += 2) head += `${rawHeaders[i]}: ${rawHeaders[i + 1]}${CRLF}`;
  return Buffer.concat([Buffer.from(head + CRLF, "latin1"), body]);
}
const recordId = () => `<urn:uuid:${randomUUID()}>`;

class WarcWriter {
  constructor(dir, append) {
    this.dir = dir;
    this.file = path.join(dir, "recording.warc");
    this.manifestFile = path.join(dir, "manifest.json");
    this.seenChains = new Set();
    ensurePrivateDir(dir);
    if (fs.existsSync(this.file) && !append) {
      fail(`refused: ${this.file} exists; choose a new name, or pass --append`);
    }
    this.manifest = append && fs.existsSync(this.manifestFile)
      ? JSON.parse(fs.readFileSync(this.manifestFile, "utf8"))
      : { format: "foafnaut-devproxy manifest 1", warc: "recording.warc", entries: [] };
    if (!fs.existsSync(this.file)) {
      const info = Buffer.from([
        "software: foafnaut-devproxy", "format: WARC File Format 1.1",
        "description: development test recording; private; credential values removed", ""].join(CRLF), "latin1");
      this.#write(warcRecord("warcinfo", [["WARC-Record-ID", recordId()], ["WARC-Date", new Date().toISOString()],
        ["WARC-Filename", "recording.warc"], ["Content-Type", "application/warc-fields"]], info));
    }
    this.#writeManifest();
  }
  #write(buffer) {
    fs.appendFileSync(this.file, buffer, { mode: 0o600 });
  }
  #writeManifest() {
    const temporary = `${this.manifestFile}.tmp`;
    fs.writeFileSync(temporary, JSON.stringify(this.manifest, null, 1) + "\n", { mode: 0o600 });
    fs.renameSync(temporary, this.manifestFile);
  }
  writeExchange({ url, target, method, requestHeaders, requestBodyLength, response, removedRequest, removedResponse, connection, startedAt }) {
    const time = new Date(startedAt).toISOString();
    const responseId = recordId(), requestId = recordId();
    const payloadSha = sha256(response.body);
    const responseBlock = httpBlock(`HTTP/1.1 ${response.status} ${response.statusMessage}`, response.headers, response.body);
    this.#write(warcRecord("response", [["WARC-Record-ID", responseId], ["WARC-Date", time], ["WARC-Target-URI", url],
      ["WARC-IP-Address", connection?.remoteAddress], ["Content-Type", "application/http;msgtype=response"],
      ["WARC-Payload-Digest", `sha256:${payloadSha}`], ["Foafnaut-Method", method],
      ["Foafnaut-Removed-Headers", removedResponse.length ? removedResponse.join(",") : undefined]], responseBlock));
    const requestBlock = httpBlock(`${method} ${target} HTTP/1.1`, requestHeaders, Buffer.alloc(0));
    this.#write(warcRecord("request", [["WARC-Record-ID", requestId], ["WARC-Date", time], ["WARC-Target-URI", url],
      ["WARC-Concurrent-To", responseId], ["Content-Type", "application/http;msgtype=request"],
      ["Foafnaut-Request-Body-Omitted", requestBodyLength ? `length=${requestBodyLength}` : undefined],
      ["Foafnaut-Removed-Headers", removedRequest.length ? removedRequest.join(",") : undefined]], requestBlock));
    this.#writeMetadata(url, time, responseId, connection);
    this.manifest.entries.push({ url, method, status: response.status, time, sha256: payloadSha,
      bytes: response.body.length, tls: connection?.tls ?? null });
    this.#writeManifest();
  }
  writeFailure({ url, method, startedAt, code, message }) {
    const time = new Date(startedAt).toISOString();
    const block = Buffer.from(JSON.stringify({ failure: { code, message } }), "utf8");
    this.#write(warcRecord("metadata", [["WARC-Record-ID", recordId()], ["WARC-Date", time], ["WARC-Target-URI", url],
      ["Content-Type", "application/json"]], block));
    this.manifest.entries.push({ url, method, status: null, time, sha256: null, tls: null, failure: { code, message } });
    this.#writeManifest();
  }
  // Retrieval record: remote address, timing, TLS details. The certificate
  // chain in DER is written once per leaf certificate.
  #writeMetadata(url, time, responseId, connection) {
    if (!connection) return;
    const { chain, ...details } = connection;
    if (details.tls && chain && !this.seenChains.has(details.tls.fingerprint256)) {
      this.seenChains.add(details.tls.fingerprint256);
      details.certificateChainDerBase64 = chain;
    }
    const block = Buffer.from(JSON.stringify(details), "utf8");
    this.#write(warcRecord("metadata", [["WARC-Record-ID", recordId()], ["WARC-Date", time], ["WARC-Target-URI", url],
      ["WARC-Concurrent-To", responseId], ["Content-Type", "application/json"]], block));
  }
}

/** Reads a WARC file; checks each block digest; returns "METHOD URL" -> first response. */
function readWarc(file) {
  const data = fs.readFileSync(file);
  const index = new Map();
  let at = 0, records = 0;
  while (at < data.length) {
    const headEnd = data.indexOf("\r\n\r\n", at, "latin1");
    if (headEnd < 0) fail(`${file}: truncated WARC header at byte ${at}`);
    const lines = data.toString("latin1", at, headEnd).split(CRLF);
    if (lines[0] !== "WARC/1.1") fail(`${file}: not a WARC/1.1 record at byte ${at}`);
    const fields = new Map();
    for (const line of lines.slice(1)) {
      const colon = line.indexOf(":");
      fields.set(line.slice(0, colon).toLowerCase(), line.slice(colon + 1).trim());
    }
    const blockStart = headEnd + 4;
    const blockEnd = blockStart + Number(fields.get("content-length"));
    if (!Number.isFinite(blockEnd) || blockEnd + 4 > data.length) fail(`${file}: truncated record at byte ${at}`);
    const block = data.subarray(blockStart, blockEnd);
    const digest = fields.get("warc-block-digest");
    if (digest && digest !== `sha256:${sha256(block)}`) fail(`${file}: block digest differs at byte ${at}`);
    records++;
    if (fields.get("warc-type") === "response") addResponse(index, fields, block);
    at = blockEnd + 4;
  }
  return { index, records };
}
function addResponse(index, fields, block) {
  const headEnd = block.indexOf("\r\n\r\n", 0, "latin1");
  const lines = block.toString("latin1", 0, headEnd).split(CRLF);
  const match = /^HTTP\/1\.[01] (\d{3}) ?(.*)$/.exec(lines[0]);
  if (!match) return;
  const headers = [];
  for (const line of lines.slice(1)) {
    const colon = line.indexOf(":");
    headers.push(line.slice(0, colon), line.slice(colon + 2));
  }
  const key = `${fields.get("foafnaut-method")} ${fields.get("warc-target-uri")}`;
  if (index.has(key)) return; // The first response of a repeated request is the one replayed.
  index.set(key, { status: Number(match[1]), statusMessage: match[2], headers, body: block.subarray(headEnd + 4) });
}

// ------------------------------------------------------------------ the proxy
const PRIVATE = new net.BlockList();
for (const [a, bits] of [["0.0.0.0", 8], ["10.0.0.0", 8], ["100.64.0.0", 10], ["127.0.0.0", 8], ["169.254.0.0", 16],
  ["172.16.0.0", 12], ["192.0.0.0", 24], ["192.168.0.0", 16], ["198.18.0.0", 15], ["224.0.0.0", 4], ["240.0.0.0", 4]]) {
  PRIVATE.addSubnet(a, bits, "ipv4");
}
PRIVATE.addAddress("::1", "ipv6");
PRIVATE.addAddress("::", "ipv6");
for (const [a, bits] of [["fc00::", 7], ["fe80::", 10], ["ff00::", 8]]) PRIVATE.addSubnet(a, bits, "ipv6");
function isPrivateAddress(address) {
  const family = net.isIP(address);
  return family !== 0 && PRIVATE.check(address, family === 4 ? "ipv4" : "ipv6");
}
function privateRefusal(host, address) {
  const error = new Error(`${host} is the private address ${address}; refused without --dangerously-allow-private-upstream`);
  error.code = "EDEVPROXYPRIVATE";
  return error;
}
function guardedLookup(hostname, options, callback) {
  dns.lookup(hostname, { ...options, all: true }, (error, addresses) => {
    if (error) return callback(error);
    const bad = addresses.find((a) => isPrivateAddress(a.address));
    if (bad) return callback(privateRefusal(hostname, bad.address));
    if (options.all) return callback(null, addresses);
    return callback(null, addresses[0].address, addresses[0].family);
  });
}

const headerName = (raw, i) => raw[i].toLowerCase();
function connectionListed(raw) {
  const listed = new Set();
  for (let i = 0; i < raw.length; i += 2) {
    if (headerName(raw, i) === "connection") for (const v of raw[i + 1].split(",")) listed.add(v.trim().toLowerCase());
  }
  return listed;
}
function filterEndToEnd(raw) {
  const listed = connectionListed(raw), out = [];
  for (let i = 0; i < raw.length; i += 2) {
    const name = headerName(raw, i);
    if (!HOP_BY_HOP.has(name) && !listed.has(name)) out.push(raw[i], raw[i + 1]);
  }
  return out;
}
/** The stored form of headers: credentials removed, URLs in values redacted. */
function storedHeaders(raw, base) {
  const headers = [], removed = [];
  for (let i = 0; i < raw.length; i += 2) {
    const name = headerName(raw, i);
    if (CREDENTIAL_HEADERS.has(name)) { if (!removed.includes(name)) removed.push(name); continue; }
    headers.push(raw[i], URL_HEADERS.has(name) ? redactUrlValue(raw[i + 1], base) : raw[i + 1]);
  }
  return { headers, removed };
}
function readBody(stream, limit) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let length = 0;
    stream.on("data", (chunk) => {
      length += chunk.length;
      if (length > limit) {
        const error = new Error(`body is larger than ${limit} bytes`);
        error.code = "EDEVPROXYTOOLARGE";
        stream.destroy(error);
        return;
      }
      chunks.push(chunk);
    });
    stream.on("end", () => resolve(Buffer.concat(chunks)));
    stream.on("error", reject);
    stream.on("aborted", () => reject(Object.assign(new Error("stream aborted"), { code: "ECONNRESET" })));
  });
}
function connectionDetails(socket, startedAt, respondedAt) {
  const details = { remoteAddress: socket.remoteAddress, remotePort: socket.remotePort,
    timing: { startedAt: new Date(startedAt).toISOString(), firstResponseMs: respondedAt - startedAt } };
  if (socket.encrypted) {
    const peer = socket.getPeerCertificate(true);
    const chain = [];
    const seen = new Set();
    for (let c = peer; c && c.raw && !seen.has(c.fingerprint256); c = c.issuerCertificate) {
      seen.add(c.fingerprint256);
      chain.push(c.raw.toString("base64"));
    }
    details.chain = chain;
    details.tls = { protocol: socket.getProtocol(), cipher: socket.getCipher()?.name, alpn: socket.alpnProtocol || null,
      servername: socket.servername || null, keyExchange: socket.getEphemeralKeyInfo?.() ?? null,
      authorized: socket.authorized, subject: peer.subject?.CN ?? null, issuer: peer.issuer?.CN ?? null,
      fingerprint256: peer.fingerprint256, validFrom: peer.valid_from, validTo: peer.valid_to };
  }
  return details;
}
function failureHeader(error) {
  if (error.code === "EDEVPROXYPRIVATE") return { status: 403, tag: "refused-private" };
  if (error.code === "EDEVPROXYTOOLARGE") return { status: 502, tag: "too-large" };
  if (error.code === "EDEVPROXYTIMEOUT") return { status: 504, tag: "upstream-timeout" };
  if (/CERT|SSL|TLS|SIGNATURE|ISSUER/i.test(String(error.code))) return { status: 502, tag: "upstream-tls-failure" };
  return { status: 502, tag: "upstream-failure" };
}

class DevProxy {
  constructor(options, ca) {
    this.options = options;
    this.ca = ca;
    this.writer = null;
    this.index = null;
    if (options.mode === "record" || options.mode === "passthrough") {
      const agent = { keepAlive: true, maxSockets: 32 };
      this.agents = { "http:": new http.Agent(agent), "https:": new https.Agent({ ...agent, maxCachedSessions: 0 }) };
    }
    const handler = (req, res) => this.#handle(req, res).catch((error) => {
      log(`internal error: ${error.stack}`);
      res.destroy();
    });
    this.server = http.createServer(handler);
    this.inner = http.createServer(handler);
    this.server.on("connect", (req, socket, head) => this.#connect(req, socket, head));
    for (const s of [this.server, this.inner]) s.on("clientError", (_e, socket) => socket.destroy());
  }
  #connect(req, socket, head) {
    socket.on("error", () => {});
    const refuse = (status, tag) => socket.end(`HTTP/1.1 ${status} ${http.STATUS_CODES[status]}\r\nX-Devproxy: ${tag}\r\nConnection: close\r\n\r\n`);
    let target;
    try {
      target = new URL(`https://${req.url}`);
      if (target.username || target.password || target.pathname !== "/" || target.search || target.hash) throw new Error("not an authority");
    } catch { return refuse(400, "bad-connect"); }
    if (head.length) return refuse(400, "early-data");
    const host = target.hostname.replace(/^\[|\]$/g, "");
    this.ca.contextFor(host).then((secureContext) => {
      socket.write("HTTP/1.1 200 Connection Established\r\n\r\n");
      const secured = new tls.TLSSocket(socket, { isServer: true, secureContext, ALPNProtocols: ["http/1.1"] });
      secured.devproxyAuthority = target.host;
      secured.on("error", () => {});
      this.inner.emit("connection", secured);
    }).catch((error) => {
      log(`leaf certificate failed for ${host}: ${error.message}`);
      refuse(502, "leaf-failure");
    });
  }
  #answer(res, status, tag, text) {
    const body = Buffer.from(`${text}\n`, "utf8");
    res.writeHead(status, { "Content-Type": "text/plain; charset=utf-8", "Content-Length": body.length, "X-Devproxy": tag });
    res.end(body);
  }
  async #handle(req, res) {
    const authority = req.socket.devproxyAuthority;
    let url;
    try {
      if (authority) {
        if (!req.url.startsWith("/")) throw new Error("not origin form");
        url = new URL(`https://${authority}${req.url}`);
      } else {
        if (!/^http:\/\//i.test(req.url)) throw new Error("not absolute form");
        url = new URL(req.url);
      }
    } catch {
      req.resume();
      return this.#answer(res, 400, "not-a-proxy-request", "This is a forward proxy; it takes http:// request targets and CONNECT only.");
    }
    if (req.headers.upgrade) {
      req.resume();
      return this.#answer(res, 501, "upgrade-not-supported", "Protocol upgrades (WebSocket) are not supported.");
    }
    const requested = req.headers[SERVICE_HEADER];
    const service = requested ?? this.options.defaultService;
    if (service && !hasService(service)) {
      req.resume();
      return this.#answer(res, 400, "unknown-service", `Unknown service ${service}. Services: ${serviceNames().join(", ")}.`);
    }
    const stored = storedUrl(url);
    if (this.options.mode === "replay") {
      req.resume();
      const response = this.index.get(`${req.method} ${stored}`);
      if (!response) {
        log(`MISS ${req.method} ${stored}`);
        return this.#answer(res, 504, "miss", `Not in this recording: ${req.method} ${stored}`);
      }
      return this.#serve(req, res, stored, response, service);
    }
    return this.#forward(req, res, url, stored, service);
  }
  #serve(req, res, stored, response, service) {
    let out = response;
    if (service) {
      const result = applyService(service, response, stored);
      if (result.applied) {
        out = result;
        const kinds = Object.entries(result.removed).map(([k, n]) => `${k}=${n}`).join(" ");
        if (kinds) log(`service ${service}: ${stored}: removed ${kinds}`);
      } else {
        log(`service ${service} did not run on ${stored}: ${result.reason}`);
        out = { ...response, headers: [...response.headers, "X-Devproxy", "transform-failed"] };
      }
    }
    res.sendDate = false;
    res.writeHead(out.status, out.statusMessage, out.headers);
    res.end(req.method === "HEAD" ? undefined : out.body);
  }
  async #forward(req, res, url, stored, service) {
    const startedAt = Date.now();
    const recording = this.options.mode === "record";
    let requestBody;
    try {
      requestBody = await readBody(req, MAX_BODY);
    } catch (error) {
      log(`request body failed: ${error.message}`);
      return res.destroy();
    }
    const clientHeaders = filterEndToEnd(req.rawHeaders);
    const upstreamHeaders = ["Host", url.host];
    for (let i = 0; i < clientHeaders.length; i += 2) {
      const name = headerName(clientHeaders, i);
      if (name !== "host" && name !== SERVICE_HEADER && name !== "content-length") upstreamHeaders.push(clientHeaders[i], clientHeaders[i + 1]);
    }
    if (requestBody.length || req.headers["content-length"] !== undefined) upstreamHeaders.push("Content-Length", String(requestBody.length));
    let upstream;
    try {
      upstream = await this.#fetch(url, req.method, upstreamHeaders, requestBody, startedAt);
    } catch (error) {
      const { status, tag } = failureHeader(error);
      log(`${tag}: ${req.method} ${stored}: ${error.code ?? ""} ${error.message}`);
      if (recording) this.writer.writeFailure({ url: stored, method: req.method, startedAt, code: error.code ?? null, message: error.message });
      return this.#answer(res, status, tag, `${tag}: ${error.code ?? ""} ${error.message}`);
    }
    if (recording) {
      const responseStored = storedHeaders(upstream.response.headers, url.href);
      const requestStored = storedHeaders(upstreamHeaders, url.href);
      const target = new URL(stored);
      this.writer.writeExchange({ url: stored, method: req.method, target: target.pathname + target.search,
        requestHeaders: requestStored.headers, requestBodyLength: requestBody.length,
        response: { ...upstream.response, headers: responseStored.headers },
        removedRequest: requestStored.removed, removedResponse: responseStored.removed,
        connection: upstream.connection, startedAt });
    }
    this.#serve(req, res, stored, upstream.response, service);
  }
  #fetch(url, method, headers, body, startedAt) {
    const hostname = url.hostname.replace(/^\[|\]$/g, "");
    if (!this.options.allowPrivate && isPrivateAddress(hostname)) return Promise.reject(privateRefusal(hostname, hostname));
    const secure = url.protocol === "https:";
    return new Promise((resolve, reject) => {
      const request = (secure ? https : http).request({
        protocol: url.protocol, hostname, port: url.port || (secure ? 443 : 80), method,
        path: url.pathname + url.search, headers, agent: this.agents[url.protocol],
        ...(this.options.allowPrivate ? {} : { lookup: guardedLookup }),
        ...(secure ? { rejectUnauthorized: true, ...(net.isIP(hostname) ? {} : { servername: hostname }) } : {}),
      });
      request.setTimeout(UPSTREAM_TIMEOUT_MS, () => {
        request.destroy(Object.assign(new Error(`no answer in ${UPSTREAM_TIMEOUT_MS} ms`), { code: "EDEVPROXYTIMEOUT" }));
      });
      request.on("error", reject);
      request.on("response", (incoming) => {
        const connection = connectionDetails(incoming.socket, startedAt, Date.now());
        readBody(incoming, MAX_BODY).then((responseBody) => {
          const wire = filterEndToEnd(incoming.rawHeaders);
          const hasLength = wire.some((_, i) => i % 2 === 0 && headerName(wire, i) === "content-length");
          const noBody = method === "HEAD" || incoming.statusCode === 204 || incoming.statusCode === 304;
          if (!hasLength && !noBody) wire.push("Content-Length", String(responseBody.length));
          resolve({ response: { status: incoming.statusCode, statusMessage: incoming.statusMessage ?? "", headers: wire, body: responseBody }, connection });
        }, reject);
      });
      request.end(body);
    });
  }
  listen() {
    return new Promise((resolve, reject) => {
      this.server.on("error", reject);
      this.server.listen({ host: "127.0.0.1", port: this.options.port }, () => resolve(this.server.address()));
    });
  }
}

// ----------------------------------------------------------------------- main
const options = parseArgs(process.argv.slice(2));
if (process.env.NODE_TLS_REJECT_UNAUTHORIZED === "0") fail("refused: NODE_TLS_REJECT_UNAUTHORIZED=0 turns off upstream certificate checks");
const caDir = path.join(homeDir(), "ca");
const ca = new LocalCa(caDir);
if (options.printCa) {
  await ca.ensure();
  process.stdout.write(`${ca.cert}\n`);
  process.exit(0);
}
let dir = null;
if (options.dir !== null) dir = recordingDir(options.dir, caDir);
const proxy = new DevProxy(options, ca);
if (options.mode === "replay") {
  const file = path.join(dir, "recording.warc");
  if (!fs.existsSync(file)) fail(`no recording at ${file}`);
  const { index, records } = readWarc(file);
  proxy.index = index;
  log(`replay: ${index.size} responses from ${records} WARC records in ${file}`);
}
if (options.mode === "record") proxy.writer = new WarcWriter(dir, options.append);
await ca.ensure();
process.stderr.write(`devproxy: DEVELOPMENT TOOL. NOT A USER FEATURE. It decrypts HTTPS with a private CA:
devproxy:   ${ca.cert}
devproxy:   "${CA_NAME}"
devproxy: Give this CA only to a process under test (DENO_CERT). Do not add it to a system or login keychain.
devproxy: Mode: ${options.mode}${dir ? ` (${dir})` : ""}.
`);
if (options.allowPrivate) log("WARNING: --dangerously-allow-private-upstream is on: requests can reach private and loopback addresses.");
if (process.env.NODE_EXTRA_CA_CERTS) log(`WARNING: NODE_EXTRA_CA_CERTS adds a trusted CA for upstream connections: ${process.env.NODE_EXTRA_CA_CERTS}`);
const address = await proxy.listen().catch((error) => fail(`cannot listen: ${error.message}`));
process.stdout.write(`LISTENING ${address.address}:${address.port}\n`);
for (const signal of ["SIGINT", "SIGTERM"]) process.on(signal, () => process.exit(0));
