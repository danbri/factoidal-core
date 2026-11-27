// Factoidal side of the SPARQL differential campaign
// (https://github.com/danbri/factoidal-core/issues/1184; tools/diffcampaign/sparql.py).
// Reads cases.jsonl, answers each query with @factoidal/core in the SPARQL 1.1
// Query Results JSON Format, writes one JSON line per case.
// Usage: node tools/diffcampaign/sparql-factoidal.mjs cases.jsonl out.jsonl [module]
// `module` defaults to "@factoidal/core"; give a path to test a local build.
import { readFileSync, writeFileSync } from "node:fs";
import { pathToFileURL } from "node:url";

const [cases, out, mod = "@factoidal/core"] = process.argv.slice(2);
const spec = mod.startsWith(".") || mod.startsWith("/") ? pathToFileURL(mod).href : mod;
const fd = await import(spec);
const lines = readFileSync(cases, "utf8").split("\n").filter(Boolean);
const results = [];
for (const line of lines) {
  const c = JSON.parse(line);
  try {
    let json = await fd.query(c.data, c.query, { format: "ntriples", output: "json" });
    if (typeof json !== "string") json = JSON.stringify(json);
    results.push(JSON.stringify({ id: c.id, ok: true, json }));
  } catch (e) {
    results.push(JSON.stringify({ id: c.id, ok: false, error: String(e && e.message || e).slice(0, 300) }));
  }
}
writeFileSync(out, results.join("\n") + "\n");
console.log(`factoidal: answered ${results.length} cases`);
