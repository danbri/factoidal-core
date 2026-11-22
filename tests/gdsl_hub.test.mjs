import test from "node:test";
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {fileURLToPath} from "node:url";
import path from "node:path";
import {createPVGraphWasm,listExamples}
  from "../npm/factoidal/gdsl.mjs";

const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),"..");
const read=name=>readFileSync(path.join(root,name),"utf8");

test("one Lean-owned PVGraph API with five shared-domain examples",()=>{
  const s=read("docs/specs/gdsl-0.2.md");
  assert.match(s,/Every GDSL domain uses the same canonical PVGraph document/);
  assert.match(s,/JavaScript is a host binding/);
  assert.match(s,/S-expression reader is planned/);
  assert.equal(listExamples().length,5);
  assert.equal(typeof createPVGraphWasm,"function");
  const entry=read("npm/factoidal/gdsl.mjs");
  assert.doesNotMatch(entry,/gdsl-graph\.mjs|runPVGraphCPU|checkPVGraph|fromPVSexpr/);
});
test("Hub delegates PVGraph admission and interpretation to Lean/Wasm",()=>{
  const page=read("docs/web/hub/gssl/index.njk");
  const explorer=read("docs/web/hub/gssl/graph-explorer.mjs");
  const app=read("docs/web/hub/gssl/app.mjs");
  const site=read("docs/.eleventy.js");
  const pkg=JSON.parse(read("npm/factoidal/package.json"));
  for(const id of ["gdsl-example","gdsl-json","gdsl-bindings",
    "gdsl-diagram","gdsl-cpu-output","gdsl-gpu-output","gdsl-agreement"])
    assert.match(page,new RegExp('id="'+id+'"'));
  assert.match(page,/docs\/specs\/gdsl-0\.2\.md/);
  assert.match(explorer,/createPVGraphWasm/);
  assert.match(explorer,/\.admit\(doc\)/);
  assert.match(explorer,/\.evaluate\(doc,supplied\)/);
  assert.match(explorer,/loadEngine/);
  assert.match(explorer,/createElementNS/);
  assert.doesNotMatch(explorer,/fromPVSexpr|runPVGraphCPU|CORE_OPERATORS/);
  assert.doesNotMatch(explorer,/\beval\s*\(|new\s+Function\s*\(/);
  assert.match(app,/mountPVGraph\(\)/);
  assert.match(site,/web\/hub\/gssl/);
  assert.ok(pkg.exports["./gdsl"]);
});
test("No independent PVGraph checker, interpreter or parser is distributed",()=>{
  const forbidden=[
    "npm/factoidal/lib/gdsl-graph.mjs",
    "npm/factoidal/lib/gdsl-webgpu.mjs",
    "npm/factoidal/lib/pvgraph-lean-admission.mjs",
  ];
  for(const name of forbidden){
    assert.throws(()=>read(name),/ENOENT/,name);
  }
  const s=read("npm/factoidal/lib/gdsl-wasm-builder.mjs");
  assert.match(s,/pvgraphBuild/);
  assert.match(s,/pvgraphAdmit/);
  assert.match(s,/pvgraphEvaluate/);
  assert.doesNotMatch(s,/runPVGraphCPU|checkPVGraph/);
});
