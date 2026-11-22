// Exact engine integration test: Lean XSLT4 → Lean JSON-LD → RDF named
// dataset → SPARQL XML → Lean XSLT4 HTML. No JS RDF interpreter.
import test from "node:test";
import assert from "node:assert/strict";
import * as core from "../npm/factoidal/index.mjs";
import {runXmlFolder,DEFAULT_QUERY} from "../npm/factoidal/lib/xml-rdf-folder.mjs";
import {fixtures} from "../docs/web/hub/xml-rdf/fixtures.mjs";

test("real Lean 4 XML folder-to-named-SPARQL-to-HTML workflow",async()=>{
  await core.ready();
  const stages=[];
  const result=await runXmlFolder(core,fixtures,{query:DEFAULT_QUERY,
    onStage:e=>stages.push(e)});
  assert.equal(result.sourceCount,3);
  assert.deepEqual(result.graphs.map(g=>g.triples),
    [2,2,2]);
  assert.equal(result.backend,"lean-indexed");
  assert.match(result.queryXml,/<(?:\w+:)?sparql\b/i);
  for(const name of ["Alice","Bob","Cara"])
    assert.ok(result.html.includes(name),"missing result "+name);
  for(const graph of result.graphs)
    assert.ok(result.html.includes(graph.graph),"missing provenance "+graph.graph);
  assert.equal(stages.filter(s=>s.status==="done"&&s.id.startsWith("rdf:")).length,3);
});
