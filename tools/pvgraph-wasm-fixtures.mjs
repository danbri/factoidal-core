// Recompute native Lean fixtures through the actual Wasm API. This host only
// transports JSON and compares answers; it implements no graph semantics.
import {readFileSync, writeFileSync} from "node:fs";
import {createHash} from "node:crypto";
import {resolve} from "node:path";
import {pathToFileURL} from "node:url";
import {isDeepStrictEqual} from "node:util";
import {sourceProvenance} from "./pvgraph-evidence-provenance.mjs";

const args = typeof Deno !== "undefined" ? Deno.args : process.argv.slice(2);
const [loader, nativeFixtures, outputFixtures, sha] = args;
if (args.length !== 4 || !/\.js$/.test(loader ?? "") ||
    !/^[a-f0-9]{40}$/.test(sha ?? "")) {
  throw Error("Usage: pvgraph-wasm-fixtures.mjs LOADER.js NATIVE_JSONL OUTPUT_JSONL HEAD_SHA");
}
const digest = bytes => createHash("sha256").update(bytes).digest("hex");
const source = readFileSync(nativeFixtures);
const fixtures = source.toString("utf8").trim().split(/\r?\n/).map(JSON.parse);
if (!fixtures.length || new Set(fixtures.map(x => x.case)).size !== fixtures.length) {
  throw Error("Missing or duplicate native fixtures");
}
const {loadL4} = await import(pathToFileURL(resolve(loader)).href);
const engine = await loadL4();
const reflection = engine.call("ops", []);
for (const op of ["pvgraphAdmit", "pvgraphEvaluate", "pvgraphGpuPlan"]) {
  if (!reflection.ops.includes(op)) throw Error("Wasm lacks required operation: " + op);
}
const call = (op, values) => {
  try { return engine.call(op, values.map(JSON.stringify)); }
  catch (error) {
    if (error.envelope?.ok === false) return error.envelope;
    throw error;
  }
};
const equal = (a, b, label) => {
  if (!isDeepStrictEqual(a, b)) throw Error(label);
};
const rows = [], cases = [];
for (const fixture of fixtures) {
  const sizes = Object.fromEntries(Object.entries(fixture.input).map(([name, value]) =>
    [name, Array.isArray(value) ? value.length : 1]));
  const admitted = call("pvgraphAdmit", [fixture.pvgraph]);
  if (admitted.ok !== true) throw Error(fixture.case + ": Wasm admission refused");
  equal(admitted.pvgraph, fixture.pvgraph, fixture.case + ": admission changed the graph");
  const evaluated = call("pvgraphEvaluate", [fixture.pvgraph, fixture.input]);
  const planned = call("pvgraphGpuPlan", [fixture.pvgraph, sizes]);
  if (fixture.eligible) {
    if (evaluated.ok !== true || planned.ok !== true) {
      throw Error(fixture.case + ": Wasm evaluation or planning refused");
    }
    equal(evaluated.outputs, fixture.expected, fixture.case + ": native/Wasm outputs differ");
    equal(planned.plan, fixture.plan, fixture.case + ": native/Wasm plans differ");
    rows.push({...fixture, plan: planned.plan, expected: evaluated.outputs});
    cases.push({name: fixture.case, nativeWasmPlanEqual: true, nativeWasmOutputEqual: true});
  } else {
    if (evaluated.ok !== false || planned.ok !== false) {
      throw Error(fixture.case + ": Wasm accepted a native refusal");
    }
    rows.push({...fixture, plan: null, expected: null});
    cases.push({name: fixture.case, evaluationAndPlanningRefused: true});
  }
}
const output = rows.map(x => JSON.stringify(x)).join("\n") + "\n";
const provenance = sourceProvenance(sha, resolve(loader.replace(/\.js$/, ".wasm")));
writeFileSync(outputFixtures, output, {flag: "wx"});
console.log(JSON.stringify({schema: "pvgraph-native-wasm-fixtures-v1", status: "pass",
  provenance, engineProfile: reflection.engine,
  nativeFixturesSha256: digest(source), wasmFixturesSha256: digest(output), cases,
  scope: "Exact API outputs and emitted plans; execute the resulting fixtures with the device smoke runner for WebGPU observations."
}, null, 2));
