import test from "node:test";
import assert from "node:assert/strict";
import {readFileSync} from "node:fs";
import {fileURLToPath} from "node:url";
import path from "node:path";
import {example,listExamples,fromPVSexpr,runPVGraphCPU}
  from "../npm/factoidal/gdsl.mjs";

const dir=path.resolve(path.dirname(fileURLToPath(import.meta.url)),"..");
const text=relative=>readFileSync(path.join(dir,relative),"utf8");
test("GDSL 0.2 replaces the separate syntax proposal in earlier specification",()=>{
  const spec=text("docs/specs/gdsl-0.2.md");
  const older=text("docs/specs/gssl-0.1.md");
  const residency=text("docs/20261121-gssl-residency-worklets.md");
  assert.match(spec,/Every GDSL domain uses the same canonical PVGraph dataflow document/);
  assert.match(spec,/register.*operator/i);
  assert.match(spec,/S-expressions/);
  assert.match(spec,/JavaScript computational PVGraph constructor/);
  assert.match(spec,/typed.*link/i);
  assert.match(spec,/same graph/i);
  assert.match(older,/Superseded for new language design/);
  assert.match(residency,/The GPU is not inherently an RDF store/);
  assert.match(residency,/is no\s+longer part of the GDSL language specification/);
});
test("all five domain examples generate valid common graphs, parser and results",()=>{
  for(const info of listExamples()){
    const e=example(info.id);
    assert.deepEqual(fromPVSexpr(e.sexpr),e.pvgraph);
    assert.ok(e.pvgraph.nodes.some(n=>n.op==="core.input"));
    assert.ok(e.pvgraph.nodes.some(n=>n.op==="core.output"));
    assert.ok(e.pvgraph.links.length>0);
    assert.ok(Object.keys(runPVGraphCPU(e.pvgraph,e.input).outputs).length>0);
  }
});
test("GDSL Hub editor, graph rendering, bindings, CPU and GPU share one canonical API",()=>{
  const page=text("docs/web/hub/gssl/index.njk");
  const app=text("docs/web/hub/gssl/app.mjs");
  const graphApp=text("docs/web/hub/gssl/graph-explorer.mjs");
  const site=text("docs/.eleventy.js");
  const home=text("docs/web/hub/index.md");
  const pkg=JSON.parse(text("npm/factoidal/package.json"));
  const entry=text("npm/factoidal/gdsl.mjs");
  for(const id of ["gdsl-example","gdsl-sexpr","gdsl-js","gdsl-bindings",
    "gdsl-diagram","gdsl-cpu","gdsl-gpu","gdsl-agreement"])
    assert.match(page,new RegExp('id="'+id+'"'));
  assert.match(page,/docs\/specs\/gdsl-0\.2\.md/);
  assert.match(graphApp,/from "\.\.\/\.\.\/\.\.\/npm\/factoidal\/gdsl\.mjs"/);
  for(const fn of ["fromPVSexpr","toPVSexpr","runPVGraphCPU","PVGraph",
    "createElementNS"]){
    assert.ok(graphApp.includes(fn));
  }
  assert.match(graphApp,/createElementNS/);
  assert.doesNotMatch(graphApp,/runPVGraphGPU\s*\(/);
  assert.match(page,/native Lean 4 toolkit/i);
  assert.match(graphApp,/dataflow/i);
  assert.match(app,/mountPVGraph\(\)/);
  assert.match(site,/web\/hub\/gssl/);
  assert.match(site,/"gdsl.mjs"/);
  assert.match(home,/href="\.\/gssl\//);
  assert.ok(pkg.exports["./gdsl"]);
  assert.match(entry,/from "\.\/lib\/gdsl-graph\.mjs"/);
});
test("The Hub has no competing domain parser or unchecked eval of source text",()=>{
  const source=text("docs/web/hub/gssl/graph-explorer.mjs");
  assert.doesNotMatch(source,/\beval\s*\(/);
  assert.doesNotMatch(source,/new\s+Function\s*\(/);
  assert.doesNotMatch(source,/\bdomainDsl\s*\(/);
});
