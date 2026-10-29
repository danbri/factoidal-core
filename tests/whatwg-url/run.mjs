// tests/whatwg-url/run.mjs — the web-platform-tests url/ data files over the
// Lean WHATWG URL Standard engine (`l4whatwg-url batch`), as the WPT test
// files read them (https://github.com/danbri/factoidal/issues/1167,
// milestone 3).
//
//   node tests/whatwg-url/run.mjs BIN [--verbose]
//
// Each WPT test file named below is a short loop over a JSON file. This runner
// does the same loop: it converts every JSON string to a USVString (as WebIDL
// does for the URL constructor), sends the request to the Lean engine, and
// compares the answer with the expectation, attribute by attribute. It makes
// no URL decision itself.
//
// Output: one line per test file and a total line
//   "N pass, M fail, X expected-fail, S stale (out of T)".
// Expected failures are in expected-failures.json, each with an open issue.
import { readFileSync, writeFileSync, mkdtempSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { tmpdir } from "node:os";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const HERE = dirname(fileURLToPath(import.meta.url));
const ROOT = join(HERE, "..", "..");
const WPT = join(ROOT, "third_party", "testing", "wpt-url", "url");
const BIN = process.argv[2];
const VERBOSE = process.argv.includes("--verbose");
if (!BIN) {
  console.error("usage: run.mjs BIN [--verbose]");
  process.exit(2);
}

const load = (name) => JSON.parse(readFileSync(join(WPT, "resources", name), "utf8"));
const usv = (s) => s.toWellFormed();
const hex = (s) => (s === "" ? "-" : Buffer.from(usv(s), "utf8").toString("hex"));
const unhex = (h) => (h === "-" ? "" : Buffer.from(h, "hex").toString("utf8"));
const FIELDS = ["href", "protocol", "username", "password", "host", "hostname", "port",
  "pathname", "search", "searchParams", "hash", "origin"];

// Each test: { file, name, req, check(answer) → null | "message" }.
const tests = [];

// url-constructor.any.js
const urlData = [...load("urltestdata.json"), ...load("urltestdata-javascript-only.json")];
for (const t of urlData) {
  if (typeof t === "string") continue;
  const base = t.base !== null && t.base !== undefined ? t.base : undefined;
  const name = `Parsing: <${t.input}> ${base ? "against <" + base + ">" : "without base"}`;
  const req = `parse ${hex(t.input)} ${base === undefined ? "*" : hex(base)}`;
  tests.push({ file: "url-constructor.any.js", name, req, check: (a) => {
    if (t.failure) return a === null ? null : "expected TypeError";
    if (a === null) return "unexpected TypeError";
    for (const f of ["href", "protocol", "username", "password", "host", "hostname", "port",
      "pathname", "search", "hash"]) {
      if (a[f] !== t[f]) return `${f}: got ${JSON.stringify(a[f])}, expected ${JSON.stringify(t[f])}`;
    }
    if ("searchParams" in t && a.searchParams !== t.searchParams) {
      return `searchParams: got ${JSON.stringify(a.searchParams)}, expected ${JSON.stringify(t.searchParams)}`;
    }
    return null;
  } });
  // url-origin.any.js
  if ("origin" in t) {
    tests.push({ file: "url-origin.any.js", name: `Origin parsing: <${t.input}> ${base ? "against <" + base + ">" : "without base"}`,
      req, check: (a) => (a !== null && a.origin === t.origin) ? null
        : `origin: got ${a === null ? "TypeError" : JSON.stringify(a.origin)}, expected ${JSON.stringify(t.origin)}` });
  }
}

// url-setters.any.js
const setters = load("setters_tests.json");
for (const [prop, cases] of Object.entries(setters)) {
  if (prop === "comment") continue;
  for (const c of cases) {
    const name = `URL: Setting <${c.href}>.${prop} = '${c.new_value}'${c.comment ? " " + c.comment : ""}`;
    tests.push({ file: "url-setters.any.js", name, req: `set ${hex(c.href)} ${prop} ${hex(c.new_value)}`,
      check: (a) => {
        if (a === null) return "unexpected TypeError";
        for (const [k, v] of Object.entries(c.expected)) {
          if (a[k] !== v) return `${k}: got ${JSON.stringify(a[k])}, expected ${JSON.stringify(v)}`;
        }
        return null;
      } });
  }
}

// toascii.window.js: the URL type (the <a> and <area> types need an HTML
// document: https://github.com/danbri/factoidal/issues/1187).
for (const t of load("toascii.json")) {
  if (typeof t === "string") continue;
  tests.push({ file: "toascii.window.js", name: `${t.input} (using URL)`,
    req: `parse ${hex("https://" + t.input + "/x")} *`, check: (a) => {
      if (t.output === null) return a === null ? null : "expected TypeError";
      if (a === null) return "unexpected TypeError";
      if (a.host !== t.output || a.hostname !== t.output || a.pathname !== "/x"
        || a.href !== "https://" + t.output + "/x") return `host ${JSON.stringify(a.host)}, href ${JSON.stringify(a.href)}`;
      return null;
    } });
  for (const val of ["host", "hostname"]) {
    tests.push({ file: "toascii.window.js", name: `${t.input} (using URL.${val})`,
      req: `set ${hex("https://x/x")} ${val} ${hex(t.input)}`, check: (a) => {
        if (a === null) return "unexpected TypeError";
        const want = t.output !== null ? t.output : "x";
        return a[val] === want ? null : `${val}: got ${JSON.stringify(a[val])}, expected ${JSON.stringify(want)}`;
      } });
  }
}

// IdnaTestV2.any.js and IdnaTestV2-removed.any.js
for (const [file, json] of [["IdnaTestV2.any.js", "IdnaTestV2.json"], ["IdnaTestV2-removed.any.js", "IdnaTestV2-removed.json"]]) {
  for (const t of load(json)) {
    if (typeof t === "string") continue;
    if (file === "IdnaTestV2.any.js" && t.input === "") continue;
    tests.push({ file, name: `ToASCII("${t.input}")${t.comment ? " " + t.comment : ""}`,
      req: `parse ${hex("https://" + t.input + "/x")} *`, check: (a) => {
        if (t.output === null) return a === null ? null : `expected TypeError, got host ${JSON.stringify(a.host)}`;
        if (a === null) return "unexpected TypeError";
        if (a.host !== t.output || a.hostname !== t.output || a.pathname !== "/x"
          || a.href !== `https://${t.output}/x`) return `host ${JSON.stringify(a.host)}`;
        return null;
      } });
  }
}

// url-statics-canparse.any.js and url-statics-parse.any.js (their cases are
// inline in the test files; copied here).
const statics = [
  [undefined, undefined, false], ["aaa:b", undefined, true], [undefined, "aaa:b", false],
  [undefined, "https://test:test/", false], ["aaa:/b", undefined, true], [undefined, "aaa:/b", true],
  ["https://test:test", undefined, false], ["a", "https://b/", true],
];
for (const [url, base, expected] of statics) {
  tests.push({ file: "url-statics-canparse.any.js", name: `URL.canParse(${url}, ${base})`,
    req: `canparse ${url === undefined ? "*" : hex(url)} ${base === undefined ? "*" : hex(base)}`,
    raw: true, check: (a) => (a === `ok ${expected}` ? null : `got ${a}`) });
}

// percent-encoding.window.js: the document's encoding is the output encoding
// of the URL parser; the href is that of resources/percent-encoding.py.
for (const t of load("percent-encoding.json")) {
  if (typeof t === "string") continue;
  for (const enc of Object.keys(t.output)) {
    tests.push({ file: "percent-encoding.window.js", name: `Input ${t.input} with encoding ${enc}`,
      req: `parseenc ${enc} ${hex("https://doesnotmatter.invalid/?" + t.input + "#" + t.input)} ${hex("https://web-platform.test/")}`,
      check: (a) => {
        if (a === null) return "unexpected failure";
        if (a.hash !== `#${t.output["utf-8"]}`) return `hash ${JSON.stringify(a.hash)}`;
        if (a.search !== `?${t.output[enc]}`) return `search ${JSON.stringify(a.search)}`;
        return null;
      } });
  }
}

// Run the engine once over every request.
const dir = mkdtempSync(join(tmpdir(), "whatwg-url-"));
const reqFile = join(dir, "req.txt");
const respFile = join(dir, "resp.txt");
writeFileSync(reqFile, tests.map((t) => t.req).join("\n") + "\n");
const t0 = Date.now();
execFileSync(BIN, ["batch", reqFile, respFile], { stdio: "inherit", timeout: 600000 });
const ms = Date.now() - t0;
const answers = readFileSync(respFile, "utf8").split("\n");

const xfail = JSON.parse(readFileSync(join(HERE, "expected-failures.json"), "utf8"));
const xfailKeys = new Map(xfail.cases.map((c) => [`${c.file}\u0000${c.name}`, c]));
const seenX = new Set();
const perFile = new Map();
let pass = 0, fail = 0, xf = 0, stale = 0;
tests.forEach((t, i) => {
  const line = answers[i] ?? "";
  let a;
  if (t.raw) a = line;
  else if (line === "fail") a = null;
  else if (line.startsWith("ok ")) {
    const parts = line.slice(3).split(" ");
    a = Object.fromEntries(FIELDS.map((f, k) => [f, unhex(parts[k])]));
  } else a = { error: line };
  const msg = t.check(a);
  const key = `${t.file}\u0000${t.name}`;
  const x = xfailKeys.get(key);
  const row = perFile.get(t.file) ?? { pass: 0, fail: 0, xfail: 0, stale: 0 };
  if (x) {
    seenX.add(key);
    if (msg) { xf++; row.xfail++; }
    else { stale++; row.stale++; console.log(`STALE expected failure (now passes): ${t.file}: ${t.name} (${x.issue})`); }
  } else if (msg) {
    fail++; row.fail++;
    if (VERBOSE || fail <= 40) console.log(`FAIL ${t.file}: ${t.name}: ${msg}`);
  } else { pass++; row.pass++; }
  perFile.set(t.file, row);
});
for (const k of xfailKeys.keys()) {
  if (!seenX.has(k)) { stale++; console.log(`STALE expected failure (no such test): ${k.replace("\u0000", ": ")}`); }
}
for (const [f, r] of perFile) {
  console.log(`${f}: ${r.pass} pass, ${r.fail} fail, ${r.xfail} expected-fail, ${r.stale} stale (out of ${r.pass + r.fail + r.xfail + r.stale})`);
}
console.log(`whatwg-url (wpt url/, Lean engine): ${pass} pass, ${fail} fail, ${xf} expected-fail, ${stale} stale (out of ${pass + fail + xf + stale}); engine time ${ms} ms`);
process.exit(fail === 0 && stale === 0 ? 0 : 1);
