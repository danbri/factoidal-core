// Response services of the Foafnaut developer proxy: a test aid that makes a
// page simpler at serving time. It is NOT a sanitiser and NOT a security
// boundary: the tokenizer has no tree construction and the output is not safe
// to treat as safe. Recordings are never changed by this file.
import zlib from "node:zlib";

// ---------------------------------------------------------------- the ladder
// One row per service, from least to most removal. To add a level, add a row.
//   elements       start tags removed with their subtree (or alone, when void)
//   voidElements   start tags removed alone
//   attributes     attribute test: (name, value) => kind to remove, or null
//   tagRule        (name, attrs) => kind to remove the whole tag, or null
//   dropScripts    answer 204 for script resources
export const SERVICES = Object.freeze({
  full: {},
  "no-scripts": {
    elements: ["script"],
    attributes: eventAttribute,
  },
  "text-css-links": {
    elements: ["script", "iframe", "object", "video", "audio", "picture",
      "canvas", "svg", "applet", "frameset"],
    voidElements: ["img", "image", "embed", "source", "track", "frame"],
    attributes: (name, value) => eventAttribute(name) ?? scriptUrl(name, value) ?? imageAttribute(name),
    tagRule: brutalTagRule,
    dropScripts: true,
  },
});

function eventAttribute(name) {
  return name.length > 2 && name.startsWith("on") ? "on*" : null;
}
const URL_ATTRIBUTES = new Set(["href", "src", "action", "formaction", "xlink:href"]);
function scriptUrl(name, value) {
  if (!URL_ATTRIBUTES.has(name)) return null;
  const compact = value.replace(/[\u0000- ]/g, "").toLowerCase();
  return compact.startsWith("javascript:") ? "javascript-url" : null;
}
function imageAttribute(name) {
  return name === "srcset" || name === "background" || name === "poster" ? "image-attribute" : null;
}
function attr(attrs, wanted) {
  return attrs.find((a) => a.name === wanted)?.value;
}
function brutalTagRule(name, attrs) {
  if (name === "link") {
    const rel = (attr(attrs, "rel") ?? "").toLowerCase().split(/\s+/);
    return rel.includes("stylesheet") ? null : "link-not-stylesheet";
  }
  if (name === "meta" && (attr(attrs, "http-equiv") ?? "").trim().toLowerCase() === "refresh") return "meta-refresh";
  if (name === "input" && (attr(attrs, "type") ?? "").trim().toLowerCase() === "image") return "input-image";
  return null;
}

export const serviceNames = () => Object.keys(SERVICES);
export const hasService = (name) => Object.hasOwn(SERVICES, name);

// ------------------------------------------------------------------ tokenizer
// Follows the tokenization section of the WHATWG HTML Standard for the parts a
// tag rewrite needs: comments, bogus comments, tags with attributes, raw text
// and RCDATA elements, and the escaped states of script data. It does not
// construct a tree (no foreign content, no adoption agency, no implied tags).
const RAW_TEXT = new Set(["script", "style", "xmp", "iframe", "noembed", "noframes", "textarea", "title"]);
const isWs = (c) => c === " " || c === "\t" || c === "\n" || c === "\f" || c === "\r";
const isLetter = (c) => c !== undefined && /^[a-zA-Z]$/.test(c);

/** Yields tokens {type, start, end, ...} that cover the whole input, in order. */
export function* tokenize(s) {
  let i = 0, textStart = 0;
  const n = s.length;
  function* flushText(to) {
    if (to > textStart) yield { type: "text", start: textStart, end: to };
  }
  while (i < n) {
    if (s[i] !== "<") { i++; continue; }
    const c = s[i + 1];
    let token = null;
    if (s.startsWith("<!--", i)) token = readComment(s, i);
    else if (c === "!" || c === "?") token = readBogus(s, i);
    else if (c === "/") {
      const d = s[i + 2];
      if (isLetter(d)) token = readTag(s, i, true);
      else if (d === ">") token = { type: "bogus", start: i, end: i + 3 };
      else if (d !== undefined) token = readBogus(s, i);
    } else if (isLetter(c)) token = readTag(s, i, false);
    if (!token) { i++; continue; }
    yield* flushText(i);
    yield token;
    i = textStart = token.end;
    if (token.type === "start") {
      if (token.name === "plaintext") {
        if (i < n) yield { type: "raw", start: i, end: n, element: "plaintext" };
        i = textStart = n;
      } else if (RAW_TEXT.has(token.name) && !token.unterminated) {
        const end = token.name === "script" ? scriptEnd(s, i) : rawEnd(s, i, token.name);
        if (end > i) yield { type: "raw", start: i, end, element: token.name };
        i = textStart = end;
      }
    }
  }
  yield* flushText(n);
}

function readComment(s, i) {
  // <!--> and <!---> are abrupt closings; --!> also closes a comment.
  if (s.startsWith(">", i + 4)) return { type: "comment", start: i, end: i + 5 };
  if (s.startsWith("->", i + 4)) return { type: "comment", start: i, end: i + 6 };
  const a = s.indexOf("-->", i + 4), b = s.indexOf("--!>", i + 4);
  if (a < 0 && b < 0) return { type: "comment", start: i, end: s.length };
  if (b >= 0 && (a < 0 || b < a)) return { type: "comment", start: i, end: b + 4 };
  return { type: "comment", start: i, end: a + 3 };
}
function readBogus(s, i) {
  const e = s.indexOf(">", i + 1);
  return { type: "bogus", start: i, end: e < 0 ? s.length : e + 1 };
}
function readTag(s, start, isEnd) {
  const n = s.length;
  let i = start + (isEnd ? 2 : 1);
  const nameStart = i;
  while (i < n && !isWs(s[i]) && s[i] !== "/" && s[i] !== ">") i++;
  const name = s.slice(nameStart, i).toLowerCase();
  const attrs = [];
  let selfClosing = false;
  for (;;) {
    while (i < n && (isWs(s[i]) || s[i] === "/")) {
      selfClosing = s[i] === "/" && s[i + 1] === ">";
      i++;
    }
    if (i >= n) return { type: isEnd ? "end" : "start", name, attrs, start, end: n, unterminated: true };
    if (s[i] === ">") { i++; break; }
    selfClosing = false;
    const attrStart = i;
    i++; // the first character is part of the name, even "=".
    while (i < n && !isWs(s[i]) && s[i] !== "/" && s[i] !== ">" && s[i] !== "=") i++;
    const attrName = s.slice(attrStart, i).toLowerCase();
    let j = i;
    while (j < n && isWs(s[j])) j++;
    let value = "";
    if (s[j] === "=") {
      j++;
      while (j < n && isWs(s[j])) j++;
      const q = s[j];
      if (q === '"' || q === "'") {
        const close = s.indexOf(q, j + 1);
        if (close < 0) return { type: isEnd ? "end" : "start", name, attrs, start, end: n, unterminated: true };
        value = s.slice(j + 1, close);
        i = close + 1;
      } else if (q === ">") {
        i = j; // missing value: ">" ends the tag.
      } else {
        const v = j;
        while (j < n && !isWs(s[j]) && s[j] !== ">") j++;
        value = s.slice(v, j);
        i = j;
      }
    }
    attrs.push({ name: attrName, value, start: attrStart, end: i });
  }
  return { type: isEnd ? "end" : "start", name, attrs, selfClosing, start, end: i };
}
function closesAt(s, i, name) {
  if (!s.startsWith("</", i) || s.slice(i + 2, i + 2 + name.length).toLowerCase() !== name) return false;
  const after = s[i + 2 + name.length];
  return after === undefined ? false : isWs(after) || after === "/" || after === ">";
}
function rawEnd(s, from, name) {
  for (let i = s.indexOf("</", from); i >= 0; i = s.indexOf("</", i + 2)) {
    if (closesAt(s, i, name)) return i;
  }
  return s.length;
}
// Script data with its escaped and double-escaped states: inside <!-- a nested
// <script> ... </script> does not close the element.
function scriptEnd(s, from) {
  let state = "data";
  for (let i = from; i < s.length; i++) {
    if (s[i] === "-" && s.startsWith("-->", i) && state !== "data") { state = "data"; i += 2; continue; }
    if (s[i] !== "<") continue;
    // The dashes of <!-- also count towards -->, so <!--> leaves the state again.
    if (state === "data" && s.startsWith("<!--", i)) { state = "escaped"; i += 1; continue; }
    if (closesAt(s, i, "script")) {
      if (state === "double") { state = "escaped"; continue; }
      return i;
    }
    if (state === "escaped" && s.slice(i + 1, i + 7).toLowerCase() === "script") {
      const after = s[i + 7];
      if (after !== undefined && (isWs(after) || after === "/" || after === ">")) state = "double";
    }
  }
  return s.length;
}

// ------------------------------------------------------------------ transform
/** Applies a service row to HTML text. Returns {output, removed}. */
export function transformHtml(source, serviceName) {
  const service = SERVICES[serviceName];
  const elements = new Set(service.elements ?? []);
  const voids = new Set(service.voidElements ?? []);
  const removed = {};
  const count = (kind) => { removed[kind] = (removed[kind] ?? 0) + 1; };
  const out = [];
  let skipping = null, depth = 0;
  for (const t of tokenize(source)) {
    if (skipping) {
      if (t.type === "start" && t.name === skipping && !endsItself(t)) depth++;
      if (t.type === "end" && t.name === skipping && --depth === 0) { skipping = null; }
      continue;
    }
    if (t.type !== "start" && t.type !== "end") { out.push(source.slice(t.start, t.end)); continue; }
    if (voids.has(t.name)) { if (t.type === "start") count(t.name); continue; }
    if (elements.has(t.name)) {
      if (t.type === "end") continue; // a stray end tag.
      count(t.name);
      if (!endsItself(t)) { skipping = t.name; depth = 1; }
      continue;
    }
    if (t.type === "start") {
      const kind = service.tagRule?.(t.name, t.attrs);
      if (kind) { count(kind); continue; }
      out.push(rewriteAttributes(source, t, service, count));
    } else out.push(source.slice(t.start, t.end));
  }
  return { output: out.join(""), removed };
}
// "/>" ends an element only in foreign content; on an HTML element it has no effect.
const endsItself = (t) => t.selfClosing && t.name === "svg";
function rewriteAttributes(source, t, service, count) {
  if (!service.attributes) return source.slice(t.start, t.end);
  let result = "", at = t.start;
  for (const a of t.attrs) {
    const kind = service.attributes(a.name, a.value);
    if (!kind) continue;
    count(kind);
    result += source.slice(at, a.start);
    at = a.end;
  }
  return result + source.slice(at, t.end);
}

// ----------------------------------------------------------------- at serving
const SCRIPT_TYPES = new Set(["text/javascript", "application/javascript", "application/x-javascript",
  "application/ecmascript", "text/ecmascript", "text/jscript", "application/x-ecmascript"]);
function headerValue(raw, wanted) {
  for (let i = 0; i < raw.length; i += 2) if (raw[i].toLowerCase() === wanted) return raw[i + 1];
  return undefined;
}
function withoutHeaders(raw, names) {
  const out = [];
  for (let i = 0; i < raw.length; i += 2) if (!names.has(raw[i].toLowerCase())) out.push(raw[i], raw[i + 1]);
  return out;
}
function decodeBody(body, encoding) {
  switch ((encoding ?? "identity").trim().toLowerCase()) {
    case "identity": case "": return body;
    case "gzip": case "x-gzip": return zlib.gunzipSync(body);
    case "deflate": try { return zlib.inflateSync(body); } catch { return zlib.inflateRawSync(body); }
    case "br": return zlib.brotliDecompressSync(body);
    case "zstd": return zlib.zstdDecompressSync(body);
    default: throw new Error(`content coding not supported: ${encoding}`);
  }
}

/**
 * Applies a named service to a response about to be served. The inputs are not
 * changed. Returns {status, statusMessage, headers, body, removed, applied}.
 * `applied` is false when the service could not run; the caller then serves
 * the page unchanged and says so.
 */
export function applyService(serviceName, response, requestUrl) {
  const service = SERVICES[serviceName];
  const applied = (r) => ({ ...r, headers: [...r.headers, "X-Foafnaut-Devproxy-Applied", serviceName], applied: true });
  const contentType = (headerValue(response.headers, "content-type") ?? "").split(";")[0].trim().toLowerCase();
  if (service.dropScripts && isScriptResource(contentType, requestUrl)) {
    return applied({ status: 204, statusMessage: "No Content", headers: [], body: Buffer.alloc(0), removed: { "script-resource": 1 } });
  }
  const untouched = () => applied({ ...response, removed: {} });
  if (!service.elements && !service.voidElements && !service.attributes) return untouched();
  if (contentType !== "text/html" || response.body.length === 0) return untouched();
  const fullType = (headerValue(response.headers, "content-type") ?? "").toLowerCase();
  if (/charset\s*=\s*"?utf-?16/.test(fullType)) return { ...response, removed: {}, applied: false, reason: "UTF-16 is not supported" };
  let bytes;
  try {
    bytes = decodeBody(response.body, headerValue(response.headers, "content-encoding"));
  } catch (error) {
    return { ...response, removed: {}, applied: false, reason: String(error.message) };
  }
  if ((bytes[0] === 0xff && bytes[1] === 0xfe) || (bytes[0] === 0xfe && bytes[1] === 0xff)) {
    return { ...response, removed: {}, applied: false, reason: "UTF-16 is not supported" };
  }
  // Latin-1 maps each byte to one code unit, so every byte that is not touched
  // is written back unchanged, whatever the page's encoding is.
  const { output, removed } = transformHtml(bytes.toString("latin1"), serviceName);
  const body = Buffer.from(output, "latin1");
  const headers = withoutHeaders(response.headers, new Set(["content-encoding", "content-length", "etag", "digest", "content-md5", "accept-ranges"]));
  headers.push("Content-Length", String(body.length));
  return applied({ status: response.status, statusMessage: response.statusMessage, headers, body, removed });
}
function isScriptResource(contentType, requestUrl) {
  if (SCRIPT_TYPES.has(contentType)) return true;
  if (contentType !== "" && contentType !== "application/octet-stream" && contentType !== "text/plain") return false;
  try { return /\.m?js$/i.test(new URL(requestUrl).pathname); } catch { return false; }
}
