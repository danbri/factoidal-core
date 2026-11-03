#!/usr/bin/env node
// tests/whatwg-encoding/run.mjs — the web-platform-tests encoding tests
// (third_party/testing/wpt-encoding, provenance in
// third_party/testing/wpt-encoding-PROVENANCE.md) against the Lean WHATWG
// Encoding Standard engine (formal/lean4/L4Factoidal/WHATWG/Encoding).
// https://github.com/danbri/factoidal/issues/1167, milestone 2.
//
// This file is a test host. It gives the WPT test files the browser surfaces
// that they read: a testharness.js-compatible API, TextDecoder and
// TextEncoder, and for the legacy multi-byte pages an iframe document, an
// <a href> query and a GET form submission. Every decision about bytes, code
// points, labels and percent-encoding is made by the Lean program
// `l4whatwg-encoding serve`, which this file calls synchronously through two
// FIFOs. Two steps are done here and not in Lean, and are named in the report:
// reading `<meta charset>` of a test page with a regular expression (the HTML
// prescan is milestone 5 of issue 1167), and reading `<span>` elements of an
// iframe document with a regular expression (no HTML tree builder is used).
//
// Usage: node tests/whatwg-encoding/run.mjs BIN [--only SUBSTR] [--verbose]
// Exit 0 when every test that runs passes, or is an expected failure or a
// defective-test-data exclusion listed in tests/whatwg-encoding/expected-failures.json
// (each with its issue), and no listed case passes (a STALE entry fails the run).

import fs from "node:fs";
import path from "node:path";
import vm from "node:vm";
import os from "node:os";
import { spawn, execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const ROOT = path.resolve(HERE, "../..");
const WPT = path.join(ROOT, "third_party/testing/wpt-encoding");
const ENC = path.join(WPT, "encoding");

const args = process.argv.slice(2);
const BIN = args[0];
const only = args.includes("--only") ? args[args.indexOf("--only") + 1] : null;
const verbose = args.includes("--verbose");
if (!BIN || !fs.existsSync(BIN)) {
  console.error("usage: run.mjs PATH-TO-l4whatwg-encoding [--only SUBSTR] [--verbose]");
  process.exit(2);
}

// Rejections that a test leaves unhandled are its own business.
process.on("unhandledRejection", () => {});

// ---------------------------------------------------------------- Lean link
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "l4enc-"));
const reqPath = path.join(tmp, "req"), respPath = path.join(tmp, "resp");
execFileSync("mkfifo", [reqPath, respPath]);
const child = spawn(BIN, ["serve", reqPath, respPath], { stdio: ["ignore", "inherit", "inherit"] });
const reqFd = fs.openSync(reqPath, "w");
const respFd = fs.openSync(respPath, "r");
const rbuf = Buffer.alloc(1 << 20);
let pending = "";
function lean(line) {
  fs.writeSync(reqFd, line + "\n");
  const parts = [];
  for (;;) {
    const nl = pending.indexOf("\n");
    if (nl >= 0) {
      const out = parts.join("") + pending.slice(0, nl);
      pending = pending.slice(nl + 1);
      return out;
    }
    parts.push(pending);
    const n = fs.readSync(respFd, rbuf, 0, rbuf.length, null);
    if (n === 0) throw new Error("l4whatwg-encoding closed its answer pipe");
    pending = rbuf.toString("latin1", 0, n);
  }
}
function closeLean() {
  try { fs.writeSync(reqFd, "quit\n"); fs.closeSync(reqFd); fs.closeSync(respFd); } catch {}
  fs.rmSync(tmp, { recursive: true, force: true });
}

// Hex helpers shared with the in-realm code.
const hexBytes = (view) => {
  const tag = Object.prototype.toString.call(view);
  let u8;
  try {
    u8 = tag === "[object ArrayBuffer]" || tag === "[object SharedArrayBuffer]"
      ? new Uint8Array(view) : new Uint8Array(view.buffer, view.byteOffset, view.byteLength);
  } catch {
    return "-"; // a detached buffer holds no bytes (Web IDL "get a copy of the buffer source")
  }
  return u8.length ? Buffer.from(u8).toString("hex") : "-";
};
const hexUnits = (s) => {
  if (s.length === 0) return "-";
  const b = Buffer.alloc(s.length * 2);
  for (let i = 0; i < s.length; i++) b.writeUInt16BE(s.charCodeAt(i), 2 * i);
  return b.toString("hex");
};
const strOfUnits = (h) => {
  if (h === "-" || h === "") return "";
  const b = Buffer.from(h, "hex");
  const out = [];
  for (let i = 0; i < b.length; i += 2 * 8192) {
    const n = Math.min(8192, (b.length - i) / 2);
    const codes = new Array(n);
    for (let k = 0; k < n; k++) codes[k] = b.readUInt16BE(i + 2 * k);
    out.push(String.fromCharCode.apply(null, codes));
  }
  return out.join("");
};
const bytesOfHex = (h) => (h === "-" ? [] : Array.from(Buffer.from(h, "hex")));
const hexStr = (s) => (s.length ? Buffer.from(s, "utf8").toString("hex") : "-");

// ------------------------------------------- in-realm harness and bindings
// Evaluated inside each test's vm context, so that the classes and errors
// belong to the realm of the test (assert_throws_js compares constructors).
const REALM_SOURCE = String.raw`
(function (g, host) {
  "use strict";
  const results = host.results;
  const pendingAsync = new Set();
  function fmt(v) {
    if (typeof v === "string") return JSON.stringify(v.length > 200 ? v.slice(0, 200) + "..." : v);
    try { return String(v); } catch { return "<value>"; }
  }
  class AssertionError extends Error {}
  function fail(msg) { throw new AssertionError(msg); }
  g.assert_equals = (a, e, d) => {
    if (!(a === e || (a !== a && e !== e)) || (a === 0 && e === 0 && 1 / a !== 1 / e))
      fail((d ? d + ": " : "") + "expected " + fmt(e) + " but got " + fmt(a));
  };
  g.assert_not_equals = (a, e, d) => { if (a === e) fail((d || "") + " got disallowed value " + fmt(a)); };
  g.assert_true = (v, d) => { if (v !== true) fail((d || "") + " expected true got " + fmt(v)); };
  g.assert_false = (v, d) => { if (v !== false) fail((d || "") + " expected false got " + fmt(v)); };
  g.assert_array_equals = (a, e, d) => {
    if (!a || a.length !== e.length) fail((d || "") + " lengths differ: " + (a && a.length) + " vs " + e.length);
    for (let i = 0; i < e.length; i++) if (a[i] !== e[i]) fail((d || "") + " index " + i + ": expected " + fmt(e[i]) + " got " + fmt(a[i]));
  };
  g.assert_throws_js = (ctor, f, d) => {
    try { f(); } catch (e) {
      if (e instanceof AssertionError) throw e;
      if (!(e instanceof ctor) && !(e && e.constructor && e.constructor.name === ctor.name))
        fail((d || "") + " threw " + fmt(e) + ", expected " + ctor.name);
      return;
    }
    fail((d || "") + " did not throw " + ctor.name);
  };
  g.assert_unreached = (d) => fail("reached unreachable code: " + (d || ""));
  function record(name, err) {
    results.push({ name, ok: !err, msg: err ? String(err && err.message || err) : "" });
  }
  function makeTest(name) {
    const t = {
      name, finished: false, cleanups: [],
      step(f, thisObj, ...a) {
        if (t.finished) return;
        try { return f.apply(thisObj, a); } catch (e) { t.finish(e); }
      },
      step_func(f, thisObj) { return (...a) => t.step(f, thisObj === undefined ? t : thisObj, ...a); },
      step_func_done(f, thisObj) { return (...a) => { if (f) t.step(f, thisObj === undefined ? t : thisObj, ...a); t.done(); }; },
      unreached_func(d) { return t.step_func(() => g.assert_unreached(d)); },
      add_cleanup(f) { t.cleanups.push(f); },
      step_timeout(f, ms) { return g.setTimeout(t.step_func(f), ms); },
      done() { t.finish(null); },
      finish(err) {
        if (t.finished) return;
        t.finished = true; pendingAsync.delete(t);
        for (const c of t.cleanups) { try { c(); } catch {} }
        record(name, err);
      },
    };
    return t;
  }
  g.test = (f, name) => { const t = makeTest(name); t.step(f, t, t); if (!t.finished) t.done(); };
  g.async_test = (f, name) => {
    if (typeof f === "string") { name = f; f = null; }
    const t = makeTest(name); pendingAsync.add(t);
    if (f) t.step(f, t, t);
    return t;
  };
  g.promise_test = (f, name) => {
    const t = makeTest(name); pendingAsync.add(t);
    host.promises.push(Promise.resolve().then(() => f(t)).then(() => t.done(), (e) => t.finish(e)));
  };
  g.setup = (f) => { if (typeof f === "function") f(); };
  g.step_timeout = (f, ms) => g.setTimeout(f, ms);
  g.promise_rejects_js = (t, ctor, p, d) => Promise.resolve(p).then(
    () => fail((d || "") + " promise resolved, expected rejection with " + ctor.name),
    (e) => { if (!(e instanceof ctor) && !(e && e.constructor && e.constructor.name === ctor.name)) fail((d || "") + " rejected with " + fmt(e) + ", expected " + ctor.name); });
  g.promise_rejects_exactly = (t, v, p, d) => Promise.resolve(p).then(
    () => fail((d || "") + " promise resolved, expected rejection"),
    (e) => { if (e !== v) fail((d || "") + " rejected with " + fmt(e) + ", expected " + fmt(v)); });
  g.done = () => {};
  g.format_value = fmt;
  host.finishAll = () => { for (const t of [...pendingAsync]) t.finish(new Error("test did not complete")); };

  // Web IDL helpers.
  const toStr = (v) => "" + v;
  const isBuf = (v) => { const s = Object.prototype.toString.call(v); return s === "[object ArrayBuffer]" || s === "[object SharedArrayBuffer]"; };
  const L = host.lean;
  let nextId = 0;
  class TextDecoder {
    #id; #encoding; #fatal; #ignoreBOM;
    constructor(label = "utf-8", options = undefined) {
      label = toStr(label);
      if (options !== undefined && options !== null && typeof options !== "object" && typeof options !== "function")
        throw new TypeError("options is not a dictionary");
      const fatal = !!(options && options.fatal), ignoreBOM = !!(options && options.ignoreBOM);
      const id = "d" + (nextId++);
      const r = L("tdnew " + id + " " + host.hexStr(label) + " " + (fatal ? 1 : 0) + " " + (ignoreBOM ? 1 : 0));
      if (r === "range") throw new RangeError("The encoding label provided ('" + label + "') is invalid.");
      if (!r.startsWith("ok ")) throw new Error("l4whatwg-encoding: " + r);
      this.#id = id; this.#encoding = r.slice(3); this.#fatal = fatal; this.#ignoreBOM = ignoreBOM;
    }
    get encoding() { return this.#encoding; }
    get fatal() { return this.#fatal; }
    get ignoreBOM() { return this.#ignoreBOM; }
    decode(input = undefined, options = undefined) {
      const id = this.#id;
      // Web IDL converts the arguments in order (input, then options); the
      // bytes are copied after both conversions (decode() step 3).
      if (input !== undefined && !(ArrayBuffer.isView(input) || isBuf(input))) throw new TypeError("input is not a BufferSource");
      if (options !== undefined && options !== null && typeof options !== "object") throw new TypeError("options is not a dictionary");
      const stream = !!(options && options.stream);
      let has = 0, hex = "-";
      if (input !== undefined) { has = 1; hex = host.hexBytes(input); }
      const r = L("tddec " + id + " " + (stream ? 1 : 0) + " " + has + " " + hex);
      if (r === "type") throw new TypeError("The encoded data was not valid.");
      if (!r.startsWith("ok ")) throw new Error("l4whatwg-encoding: " + r);
      return host.strOfUnits(r.slice(3));
    }
  }
  Object.defineProperty(TextDecoder.prototype, Symbol.toStringTag, { value: "TextDecoder", configurable: true });
  class TextEncoder {
    get encoding() { return "utf-8"; }
    encode(input = "") {
      const r = L("te " + host.hexUnits(toStr(input)));
      return new Uint8Array(host.bytesOfHex(r.slice(3)));
    }
    encodeInto(source, destination) {
      const s = toStr(source);
      if (!(destination instanceof Uint8Array)) throw new TypeError("destination is not a Uint8Array");
      const [ok, read, written, hex] = L("teinto " + host.hexUnits(s) + " " + destination.length).split(" ");
      const bytes = host.bytesOfHex(hex);
      if (bytes.length) destination.set(bytes, 0);
      return { read: Number(read), written: Number(written) };
    }
  }
  Object.defineProperty(TextEncoder.prototype, Symbol.toStringTag, { value: "TextEncoder", configurable: true });
  // XMLHttpRequest for data: URLs only (harness: the MIME type's charset
  // parameter is read with a regular expression; Lean decodes).
  class XMLHttpRequest {
    open(method, url) { this.url = String(url); this.charset = null; }
    overrideMimeType(m) { const r = /charset="?([^";]*)"?/i.exec(String(m)); this.charset = r ? r[1] : null; }
    send() {
      const url = this.url;
      if (!url.startsWith("data:")) throw new Error("this host serves only data: URLs");
      const body = url.slice(url.indexOf(",") + 1);
      const r = L("xhrtext " + (this.charset === null ? "-" : host.hexStr(this.charset)) + " " + host.hexStr(body));
      g.setTimeout(() => { this.responseText = host.strOfUnits(r.slice(3)); if (this.onload) this.onload(); }, 0);
    }
  }
  g.XMLHttpRequest = XMLHttpRequest;
  class TextDecoderStream {
    #encoding; #fatal; #ignoreBOM; #transform;
    constructor(label = "utf-8", options = undefined) {
      label = toStr(label);
      if (options !== undefined && options !== null && typeof options !== "object" && typeof options !== "function")
        throw new TypeError("options is not a dictionary");
      const fatal = !!(options && options.fatal), ignoreBOM = !!(options && options.ignoreBOM);
      const id = "s" + (nextId++);
      const r = L("tdnew " + id + " " + host.hexStr(label) + " " + (fatal ? 1 : 0) + " " + (ignoreBOM ? 1 : 0));
      if (r === "range") throw new RangeError("The encoding label provided ('" + label + "') is invalid.");
      this.#encoding = r.slice(3); this.#fatal = fatal; this.#ignoreBOM = ignoreBOM;
      const out = (r, c) => {
        if (r === "type") throw new TypeError("The encoded data was not valid.");
        const s = host.strOfUnits(r.slice(3));
        if (s !== "") c.enqueue(s);
      };
      this.#transform = new g.TransformStream({
        transform(chunk, c) {
          if (!(ArrayBuffer.isView(chunk) || isBuf(chunk))) throw new TypeError("chunk is not a BufferSource");
          out(L("tdschunk " + id + " " + host.hexBytes(chunk)), c);
        },
        flush(c) { out(L("tdsflush " + id), c); },
      });
    }
    get encoding() { return this.#encoding; }
    get fatal() { return this.#fatal; }
    get ignoreBOM() { return this.#ignoreBOM; }
    get readable() { return this.#transform.readable; }
    get writable() { return this.#transform.writable; }
  }
  Object.defineProperty(TextDecoderStream.prototype, Symbol.toStringTag, { value: "TextDecoderStream", configurable: true });
  class TextEncoderStream {
    #transform;
    constructor() {
      const id = "e" + (nextId++);
      L("tesnew " + id);
      const out = (r, c) => { const b = host.bytesOfHex(r.slice(3)); if (b.length) c.enqueue(new Uint8Array(b)); };
      this.#transform = new g.TransformStream({
        transform(chunk, c) { out(L("teschunk " + id + " " + host.hexUnits(toStr(chunk))), c); },
        flush(c) { out(L("tesflush " + id), c); },
      });
    }
    get encoding() { return "utf-8"; }
    get readable() { return this.#transform.readable; }
    get writable() { return this.#transform.writable; }
  }
  Object.defineProperty(TextEncoderStream.prototype, Symbol.toStringTag, { value: "TextEncoderStream", configurable: true });
  g.TextDecoderStream = TextDecoderStream;
  g.TextEncoderStream = TextEncoderStream;
  g.TextDecoder = TextDecoder;
  g.TextEncoder = TextEncoder;
})
`;

// ------------------------------------------------------------ test running
function newRealm(extra) {
  const host = {
    results: [], promises: [], lean, hexBytes, hexUnits, strOfUnits, bytesOfHex, hexStr,
    timers: 0,
  };
  const sandbox = {
    console,
    location: { search: "", href: "http://web-platform.test/" },
    setTimeout: (f, ms, ...a) => { host.timers++; return setTimeout(() => { host.timers--; f(...a); }, ms || 0); },
    clearTimeout: (h) => { host.timers--; clearTimeout(h); },
    queueMicrotask,
    MessageChannel,
    ReadableStream, WritableStream, TransformStream, CountQueuingStrategy, ByteLengthQueuingStrategy,
    ...extra,
  };
  sandbox.self = sandbox; sandbox.window = sandbox; sandbox.globalThis = sandbox;
  const ctx = vm.createContext(sandbox);
  vm.runInContext(REALM_SOURCE, ctx)(ctx, host);
  return { ctx, host };
}

async function settle(host) {
  for (let i = 0; i < 2000; i++) {
    await Promise.all(host.promises);
    await new Promise((r) => setTimeout(r, 0));
    if (host.timers <= 0) break;
  }
  await Promise.all(host.promises);
  host.finishAll();
}

function runScript(ctx, file, code) {
  vm.runInContext(code, ctx, { filename: path.relative(ROOT, file) });
}

function resolveSrc(pageFile, src) {
  if (src === "/resources/testharness.js" || src === "/resources/testharnessreport.js") return null;
  if (src.startsWith("/common/")) return path.join(WPT, src);
  if (src.startsWith("/encoding/")) return path.join(WPT, src);
  if (src.startsWith("/")) return "unsupported:" + src;
  return path.join(path.dirname(pageFile), src);
}

// .any.js and .window.js files.
async function runAnyJs(file) {
  const src = fs.readFileSync(file, "utf8");
  const metas = [...src.matchAll(/^\/\/ META: (\w+)=(.*)$/gm)].map((m) => [m[1], m[2].trim()]);
  const variants = metas.filter(([k]) => k === "variant").map(([, v]) => v);
  const { ctx, host } = newRealm({});
  // Run the variant that tests this engine: the TextDecoder variant of the
  // single-byte test (the XMLHttpRequest variant needs an HTTP server).
  if (variants.includes("?TextDecoder")) ctx.location.search = "?TextDecoder";
  for (const [k, v] of metas) {
    if (k !== "script") continue;
    const p = resolveSrc(file, v);
    if (p === null) continue;
    if (p.startsWith("unsupported:")) throw new Error("META script " + v + " is not vendored");
    runScript(ctx, p, fs.readFileSync(p, "utf8"));
  }
  runScript(ctx, file, src);
  await settle(host);
  return host.results;
}

// --- HTML pages
function headerCharset(file) {
  const h = file + ".headers";
  if (!fs.existsSync(h)) return null;
  const m = /charset=([^\s;]+)/i.exec(fs.readFileSync(h, "latin1"));
  return m ? m[1] : null;
}
// The <meta charset> of a page, read with a regular expression over the bytes
// as ASCII (harness step; the HTML prescan is milestone 5 of issue 1167).
function metaCharset(bytes) {
  const m = /<meta\s+charset\s*=\s*["']?([^"'\s>]+)/i.exec(bytes.toString("latin1").slice(0, 1024));
  return m ? m[1] : null;
}
function leanDecode(bytes, label) {
  const r = lean("decode " + hexStr(label) + " " + (bytes.length ? bytes.toString("hex") : "-"));
  if (!r.startsWith("ok ")) throw new Error("decode with label " + label + ": " + r);
  return strOfUnits(r.slice(3));
}
function documentEncodingLabel(file, bytes) {
  return headerCharset(file) || metaCharset(bytes) || "windows-1252";
}

// The <span> elements of an iframe document (harness step: a regular
// expression, not an HTML tree builder). A span with a character reference
// or markup in its text is refused rather than read wrongly.
function spansOf(text) {
  const out = [];
  for (const m of text.matchAll(/<span((?:\s+data-[a-z]+="[^"]*")*)\s*>([\s\S]*?)<\/span>/g)) {
    const dataset = {};
    for (const a of m[1].matchAll(/data-([a-z]+)="([^"]*)"/g)) dataset[a[1]] = a[2];
    if (/[&<]/.test(m[2])) throw new Error("span text needs an HTML parser: " + JSON.stringify(m[2].slice(0, 40)));
    out.push({ dataset, textContent: m[2] });
  }
  return out;
}

function makeDocument(pageFile, pageText, pageLabel, sandboxRef) {
  const iframes = [], forms = [], inputs = [], loadListeners = [];
  const docEnc = lean("label " + hexStr(pageLabel));
  const docEncName = docEnc.startsWith("ok ") ? docEnc.slice(3) : "windows-1252";
  const iframeSrcs = [...pageText.matchAll(/<iframe\s+([^>]*)>/g)].map((m) => {
    const attrs = {};
    for (const a of m[1].matchAll(/(\w+)="([^"]*)"/g)) attrs[a[1]] = a[2];
    return attrs;
  });
  function iframeFromSrc(attrs) {
    const el = { tagName: "IFRAME", id: attrs.id, name: attrs.name, _doc: null, onload: null };
    Object.defineProperty(el, "contentDocument", {
      get() {
        if (!el._doc) {
          const f = path.join(path.dirname(pageFile), attrs.src);
          const bytes = fs.readFileSync(f);
          const label = headerCharset(f);
          if (!label) throw new Error("iframe " + attrs.src + " has no Content-Type charset (needs the HTML prescan)");
          const spans = spansOf(leanDecode(bytes, label));
          el._doc = { querySelectorAll: (sel) => { if (sel !== "span") throw new Error("selector " + sel); return spans; } };
        }
        return el._doc;
      },
    });
    el.contentWindow = { get document() { return el.contentDocument; } };
    return el;
  }
  for (const a of iframeSrcs) iframes.push(iframeFromSrc(a));
  function makeA() {
    let href = "", search = "";
    return {
      get href() { return href; },
      set href(v) {
        href = String(v);
        const q = href.indexOf("?");
        if (q < 0) { search = ""; return; }
        let query = href.slice(q + 1);
        const h = query.indexOf("#");
        if (h >= 0) query = query.slice(0, h);
        // URL parser, query state, special URL: percent-encode after encoding
        // with the document's encoding and the special-query set (in Lean).
        const r = lean("pe " + hexStr(pageLabel) + " special-query 0 " + hexUnits(query));
        const s = Buffer.from(r.slice(3) === "-" ? "" : r.slice(3), "hex").toString("latin1");
        search = s === "" ? "" : "?" + s;
      },
      get search() { return search; },
    };
  }
  function makeForm() {
    const form = { tagName: "FORM", children: [], method: "GET", action: "", acceptCharset: "", target: "" };
    form.appendChild = (c) => { form.children.push(c); };
    form.submit = () => {
      const frame = iframes.find((f) => f.id === form.target || f.name === form.target);
      // application/x-www-form-urlencoded serializer with the form's encoding
      // (in Lean); the name is ASCII here.
      const label = form.acceptCharset || pageLabel;
      const pairs = form.children.filter((c) => c.tagName === "INPUT").map((c) => {
        const enc = (s) => {
          const r = lean("pe " + hexStr(label) + " application/x-www-form-urlencoded 1 " + hexUnits(s));
          return Buffer.from(r.slice(3) === "-" ? "" : r.slice(3), "hex").toString("latin1");
        };
        return enc(c.name) + "=" + enc(c.value || "");
      });
      const query = pairs.join("&");
      sandboxRef.setTimeout(() => {
        frame.contentWindow = { location: { search: query ? "?" + query : "" } };
        if (frame.onload) frame.onload();
      }, 0);
    };
    return form;
  }
  const body = {
    appendChild(el) {
      if (el.tagName === "IFRAME") iframes.push(el);
      if (el.tagName === "FORM") { forms.push(el); for (const c of el.children) if (c.tagName === "INPUT") inputs.push(c); }
    },
  };
  const document = {
    body,
    characterSet: docEncName,
    getElementById(id) { return iframes.find((f) => f.id === id) || null; },
    createElement(tag) {
      tag = tag.toLowerCase();
      if (tag === "a") return makeA();
      if (tag === "iframe") return { tagName: "IFRAME", onload: null, contentWindow: null };
      if (tag === "form") return makeForm();
      if (tag === "input") return { tagName: "INPUT", id: "", name: "", value: "" };
      throw new Error("createElement " + tag + " is not provided by this host");
    },
    getElementsByTagName(tag) {
      tag = tag.toLowerCase();
      if (tag === "iframe") return iframes;
      if (tag === "form") return forms;
      if (tag === "input") return inputs;
      return [];
    },
    querySelector(sel) {
      if (sel === "meta[charset]") return { getAttribute: () => metaCharset(Buffer.from(pageText, "latin1")) || pageLabel };
      throw new Error("querySelector " + sel + " is not provided by this host");
    },
  };
  return { document, loadListeners };
}

async function runHtmlPage(file) {
  const bytes = fs.readFileSync(file);
  const label = documentEncodingLabel(file, bytes);
  const text = leanDecode(bytes, label);
  const sandboxRef = {};
  const { ctx, host } = newRealm({});
  sandboxRef.setTimeout = ctx.setTimeout;
  const { document, loadListeners } = makeDocument(file, text, label, sandboxRef);
  ctx.document = document;
  ctx.addEventListener = (type, f) => { if (type === "load") loadListeners.push(f); };
  ctx.frames = [];
  const scripts = [...text.matchAll(/<script(?:\s+src=["']?([^"'\s>]+)["']?)?[^>]*>([\s\S]*?)<\/script>/g)];
  for (const m of scripts) {
    if (m[1]) {
      const p = resolveSrc(file, m[1]);
      if (p === null) continue;
      if (p.startsWith("unsupported:")) throw new Error("script " + m[1] + " is not vendored");
      runScript(ctx, p, fs.readFileSync(p, "utf8"));
    } else if (m[2].trim()) {
      runScript(ctx, file, m[2]);
    }
  }
  const onload = /<body[^>]*\sonload="([^"]*)"/.exec(text);
  for (const f of loadListeners) f();
  if (onload) runScript(ctx, file, onload[1]);
  await settle(host);
  return host.results;
}

// ------------------------------------------------------------ the corpus
// Files that need a surface this host does not give, with the reason. They
// are reported as not run; https://github.com/danbri/factoidal/issues/1184
// tracks them.
const NOT_RUN = {
  "idlharness.any.js": "Web IDL interface checks (idlharness.js and WebIDLParser.js are not vendored)",
  "textdecoder-copy.any.js": "needs ArrayBuffer transfer across workers",
  "sharedarraybuffer.https.html": null,
  "bom-handling.html": "needs an HTML document loader (document.characterSet of a loaded page)",
  "remove-only-one-bom.html": "needs an HTML document loader (frames, body.textContent)",
  "sniffing.html": "needs an HTML document loader",
  "invalid-realm.window.js": "needs a second realm from an iframe",
  "realms.window.js": "needs realms from iframes",
  "from-cross-realm.html": "crash test; needs window.open",
  "stringification-crash.html": "crash test; needs Worker and Blob URLs",
  "iso2022jp-encode-form-errors-stateful.html": "needs an HTML document loader (a data: URL document in an iframe, postMessage)",
  "utf-32.html": "needs an HTML and XML document loader",
  "utf-32-from-win1252.html": "needs an HTML and XML document loader",
  "json-document-utf8.html": "needs an HTTP server (resources/json-charset.py)",
  "unsupported-labels.window.js": "needs an HTTP server (resources/text-plain-charset.py)",
  "single-byte-decoder-iframe.window.js": "needs an HTTP server (resources/single-byte-raw.py)",
  "eof-shift_jis.html": "reftest (needs a renderer)",
  "eof-utf-8-one.html": "reftest (needs a renderer)",
  "eof-utf-8-two.html": "reftest (needs a renderer)",
  "eof-utf-8-three.html": "reftest (needs a renderer)",
};

function listTests() {
  const out = [];
  const walk = (dir) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true }).sort((a, b) => a.name.localeCompare(b.name))) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) { if (e.name !== "resources") walk(p); continue; }
      const rel = path.relative(ENC, p);
      if (/\.(any|window)\.js$/.test(e.name)) out.push(rel);
      else if (/\.html$/.test(e.name) && !/-ref\.html$/.test(e.name) && !/_(chars|errors)/.test(e.name))
        out.push(rel);
    }
  };
  walk(ENC);
  return out;
}

const expected = JSON.parse(fs.readFileSync(path.join(HERE, "expected-failures.json"), "utf8"));
const xfail = new Map(Object.entries(expected.failures || {}));
const defective = new Map(Object.entries(expected.defective || {}));

let pass = 0, fail = 0, xfails = 0, stale = 0, excluded = 0;
const notRun = [];
const failures = [];
const perFile = [];
for (const rel of listTests()) {
  if (only && !rel.includes(only)) continue;
  const base = path.basename(rel);
  if (base in NOT_RUN && NOT_RUN[base]) { notRun.push([rel, NOT_RUN[base]]); continue; }
  const file = path.join(ENC, rel);
  let results;
  try {
    results = rel.endsWith(".js") ? await runAnyJs(file) : await runHtmlPage(file);
  } catch (e) {
    results = [{ name: "(file)", ok: false, msg: "harness error: " + (e && e.stack || e) }];
  }
  let p = 0, f = 0;
  for (const r of results) {
    const key = rel + " :: " + r.name;
    if (defective.has(key)) {
      if (r.ok) { stale++; failures.push(["STALE defective-data exclusion (now passes)", key, defective.get(key)]); }
      else excluded++;
      continue;
    }
    if (xfail.has(key)) {
      if (r.ok) { stale++; failures.push(["STALE expected failure (now passes)", key, xfail.get(key)]); }
      else xfails++;
      continue;
    }
    if (r.ok) { p++; pass++; } else { f++; fail++; failures.push([r.msg, key, ""]); }
  }
  perFile.push([rel, p, f, results.length]);
  if (verbose) console.log(`${rel}: ${p} pass, ${f} fail (out of ${results.length})`);
}
closeLean();

for (const [msg, key, why] of failures.slice(0, 200)) console.log(`FAIL ${key}\n     ${msg.split("\n")[0]}${why ? " [" + why + "]" : ""}`);
if (failures.length > 200) console.log(`... ${failures.length - 200} more failures`);
for (const [rel, why] of notRun) console.log(`NOT RUN ${rel}: ${why} (https://github.com/danbri/factoidal/issues/1184)`);
const total = pass + fail + xfails + stale;
console.log(`whatwg-encoding (WPT encoding/, Lean engine): ${pass} pass, ${fail} fail, ${xfails} expected-fail, ${stale} stale (out of ${total}); ${excluded} excluded (defective test data); ${perFile.length} files run, ${notRun.length} files not run`);
if (args.includes("--json")) {
  fs.writeFileSync(args[args.indexOf("--json") + 1], JSON.stringify({ pass, fail, xfails, stale, excluded, total, files: perFile, notRun }, null, 1));
}
process.exit(fail === 0 && stale === 0 ? 0 : 1);
