// Factoidal side of the Turtle differential campaign
// (https://github.com/danbri/factoidal-core/issues/1184; tools/diffcampaign/turtle.py).
// For each document: Factoidal reads the Turtle; Oxigraph's N-Quads (ox.jsonl)
// are read as N-Quads; both datasets are canonicalised with RDFC-1.0 and the
// canonical forms compared. Prints "agrees on N of M documents".
// Usage: node turtle-factoidal.mjs cases.jsonl ox.jsonl [module] [--keep DIR] [--json FILE]
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { join } from "node:path";

const args = process.argv.slice(2);
const opt = (k) => (args.includes(k) ? args[args.indexOf(k) + 1] : undefined);
const [cases, oxf] = args;
const mod = args[2] && !args[2].startsWith("--") ? args[2] : "@factoidal/core";
const keep = opt("--keep");
const out = opt("--json");
const spec = mod.startsWith(".") || mod.startsWith("/") ? pathToFileURL(mod).href : mod;
const fd = await import(spec);
const read = (f) => readFileSync(f, "utf8").split("\n").filter(Boolean).map((l) => JSON.parse(l));
const ox = new Map(read(oxf).map((r) => [r.id, r]));
const tally = { agree: 0, "xmlliteral-ns": 0, differ: 0, "one refuses": 0, "both refuse": 0, missing: 0 };
const BASE = "http://example.org/base/";
if (keep) mkdirSync(keep, { recursive: true });
let total = 0;
for (const c of read(cases)) {
  total++;
  const o = ox.get(c.id);
  if (!o) { tally.missing++; continue; }
  let f;
  try { f = { ok: true, canon: await fd.canonicalize(c.data, { format: c.format || "turtle", baseIRI: BASE }) }; }
  catch (e) { f = { ok: false, error: String(e && e.message || e).slice(0, 300) }; }
  if (!o.ok && !f.ok) { tally["both refuse"]++; continue; }
  let why = null, oc = null;
  if (o.ok !== f.ok) why = "one refuses";
  else {
    try { oc = await fd.canonicalize(o.nquads, { format: "nquads" }); }
    catch (e) { why = "cannot read Oxigraph's N-Quads: " + String(e && e.message || e).slice(0, 200); }
    if (!why) why = oc === f.canon ? null : "differ";
    // rdf:XMLLiteral: RDF/XML takes the value by exclusive canonicalisation, so it
    // keeps only the namespace declarations that are visibly used; Oxigraph 0.5.13
    // keeps every declaration in scope. Count "the same up to XMLLiteral namespace
    // declarations" apart, so that this one known difference hides no other.
    if (why === "differ" && f.canon.includes("XMLLiteral>")) {
      const strip = (t) => t.split("\n").map((l) => l.includes("XMLLiteral>")
        ? l.replace(/ xmlns(:[A-Za-z0-9_.-]+)?=\\"[^"\\]*\\"/g, "") : l).join("\n");
      try {
        const a = await fd.canonicalize(strip(oc), { format: "nquads" });
        const b = await fd.canonicalize(strip(f.canon), { format: "nquads" });
        if (a === b) why = "xmlliteral-ns";
      } catch { /* keep "differ" */ }
    }
  }
  if (!why) { tally.agree++; continue; }
  tally[why === "one refuses" ? "one refuses" : why === "xmlliteral-ns" ? "xmlliteral-ns" : "differ"]++;
  if (why === "xmlliteral-ns") continue;
  if (keep) writeFileSync(join(keep, `${c.id}.json`), JSON.stringify({ why, data: c.data, oxigraph: o, oxigraphCanonical: oc, factoidal: f }, null, 1));
}
console.log(`${(read(cases)[0] || {}).format || "turtle"} differential: agrees on ${tally.agree} of ${total} documents; ` +
  `${tally["xmlliteral-ns"]} the same up to XMLLiteral namespace declarations; ${tally.differ} differ, ` +
  `${tally["one refuses"]} refused by one reader, ${tally["both refuse"]} refused by both, ${tally.missing} missing`);
if (out) writeFileSync(out, JSON.stringify({ documents: total, ...tally }));
