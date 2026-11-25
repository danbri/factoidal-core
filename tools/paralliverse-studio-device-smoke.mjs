import {readFile} from "node:fs/promises";
import {connectWordGpu} from "../docs/web/hub/paralliverse/word-gpu.mjs";

const [path, sourceCommit] = Deno.args;
if (!path || !/^[0-9a-f]{40}$/.test(sourceCommit || "")) throw new Error("Usage: studio-device-smoke FIXTURES SOURCE_COMMIT");
const records = (await readFile(path, "utf8")).trim().split("\n").map(JSON.parse);
const header = records.shift();
if (header.kind !== "shaders" || header.schemaVersion !== 1 || records.length !== header.caseCount) {
  throw new Error("Incompatible native Lean device fixtures.");
}
const sources = Object.fromEntries(header.sources.map(x => [x.selector, x.source]));
let lost;
const gpu = await connectWordGpu(sources, message => { lost = message; });
const wordBytes = words => {
  const bytes = new Uint8Array(words.length * 4);
  const view = new DataView(bytes.buffer);
  words.forEach((word, i) => view.setUint32(4 * i, word, true));
  return bytes;
};
const cases = [];
try {
  for (const {name, result} of records) {
    if (!result.gpuEligible || !result.executionPlan) throw new Error(`${name}: fixture has no selected GPU program.`);
    const actual = await gpu.run(result.executionPlan);
    const expected = wordBytes(result.output);
    const payloadMatches = actual.packed.byteLength === expected.byteLength &&
      actual.packed.every((byte, i) => byte === expected[i]);
    if (lost || !payloadMatches || !actual.fullMatches || !actual.canariesMatch) {
      throw new Error(`${name}: actual GPU result differs from the native Lean oracle (${lost || "byte mismatch"}).`);
    }
    cases.push({name, words: result.input.length, passes: actual.passCount,
      payloadMatches, fullMatches: actual.fullMatches, canariesMatch: actual.canariesMatch,
      endToEndMs: actual.endToEndMs});
  }
  const lengths = new Set(cases.map(x => x.words));
  for (const n of [0, 1, 64, 65, 129, 1024]) {
    if (!lengths.has(n)) throw new Error(`Missing physical dispatch boundary ${n}.`);
  }
  console.log(JSON.stringify({format: "paralliverse-studio-device-v1", sourceCommit, status: "pass",
    adapter: gpu.adapter, isFallbackAdapter: gpu.isFallbackAdapter, cases}, null, 2));
} finally {
  gpu.close();
}
