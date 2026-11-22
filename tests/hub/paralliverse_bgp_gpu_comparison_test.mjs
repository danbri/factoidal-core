import test from "node:test";
import assert from "node:assert/strict";
import {makeFixture,TERM_IDS,LABEL_BASE,personIri,personWord,SIZES}
  from "../../docs/web/hub/paralliverse/bgp-fixtures.mjs";
import {compareBGPResults,makeBgpTrace}
  from "../../docs/web/hub/paralliverse/bgp-comparison.mjs";
import {validateTriples}
  from "../../docs/web/hub/paralliverse/integer-bgp-gpu.mjs";

for (const n of SIZES) {
  test("One lexical graph, distinct typed u32 triples, "+n+" people", () => {
    const fixture=makeFixture(n);
    assert.equal(fixture.integerGraph.length,fixture.triples);
    assert.equal(validateTriples(fixture.integerGraph,
      TERM_IDS.knows,TERM_IDS.worksOn,TERM_IDS.Atlas),4*n);
    const ids=new Set([TERM_IDS.knows,TERM_IDS.worksOn,TERM_IDS.Atlas,
      TERM_IDS.Orion,TERM_IDS.label]);
    for(let i=0;i<n;i++){
      assert.equal(personWord(personIri(i),n),i+1);
      ids.add(i+1);
      ids.add(LABEL_BASE+i);
    }
    assert.equal(ids.size,2*n+5,"All RDF term kinds use disjoint IDs");
    assert.deepEqual(fixture.integerGraph[0],[1,TERM_IDS.knows,2]);
    assert.deepEqual(fixture.integerGraph[2*n],
      [1,TERM_IDS.worksOn,TERM_IDS.Atlas]);
    assert.deepEqual(fixture.integerGraph[3*n],[1,TERM_IDS.label,LABEL_BASE]);
    assert.equal(new Set(fixture.integerGraph.map(t=>t.join(","))).size,4*n);
    assert.equal(fixture.blocks.knows.trim().split("\n").length,2*n);
    assert.equal(fixture.blocks.projects.trim().split("\n").length,n);
    assert.equal(fixture.blocks.labels.trim().split("\n").length,n);
  });
}

// Check the *entire* generated lexical graph against its integer-coded
// representation, rather than trusting that two parallel generators agree.
test("All lexical RDF triples encode to exactly the GPU input graph", () => {
  const termId = iri => {
    const base="https://example.org/paralliverse/";
    assert.ok(iri.startsWith(base));
    const part=iri.slice(base.length);
    if(part.startsWith("person/")) {
      const raw=part.slice("person/".length);
      assert.match(raw,/^[0-9]{4}$/);
      return Number(raw)+1;
    }
    assert.ok(Object.hasOwn(TERM_IDS,part),"Unexpected fixture term "+part);
    return TERM_IDS[part];
  };
  for(const n of SIZES){
    const fixture=makeFixture(n);
    const lexical=[fixture.blocks.knows,fixture.blocks.projects,fixture.blocks.labels]
      .flatMap(block=>block.trim().split("\n"));
    assert.equal(lexical.length,fixture.integerGraph.length);
    const mapped=lexical.map(line=>{
      const m=/^<([^>]+)> <([^>]+)> (?:<([^>]+)>|"Person ([0-9]+)") \.$/.exec(line);
      assert.ok(m,"Expected a complete N-Triples fixture statement: "+line);
      const object=m[3] ? termId(m[3]) : LABEL_BASE+Number(m[4]);
      return [termId(m[1]),termId(m[2]),object];
    });
    assert.deepEqual(mapped,fixture.integerGraph,"Full RDF text/u32 graph agreement at "+n);
  }
});

test("BGP comparator checks solution MULTISET, not ORDER BY position", () => {
  const lean=[
    {personId:2,colleagueId:7},
    {personId:3,colleagueId:7},
    {personId:2,colleagueId:7},
  ];
  const gpu=[[3,7],[2,7],[2,7]];
  const result=compareBGPResults(lean,gpu);
  assert.equal(result.equal,true);
  assert.equal(result.cpuRows,3);
  assert.match(result.summary,/bag equivalence/);
});

test("BGP comparator reports duplicate loss and extra bindings", () => {
  const lean=[{personId:2,colleagueId:7},{personId:2,colleagueId:7}];
  const actual=compareBGPResults(lean,[[2,7],[3,7]]);
  assert.equal(actual.equal,false);
  assert.deepEqual(actual.differingPairs,[
    {pair:[2,7],lean:2,gpu:1},{pair:[3,7],lean:0,gpu:1}]);
  assert.throws(()=>compareBGPResults(lean,[[2,7],[NaN,1]]),
    /unsigned 32-bit/);
});

test("No fabricated GPU evidence before actual device output", () => {
  const trace=makeBgpTrace(null,null);
  assert.equal(trace.gpuStages.every(s=>!s.observed),true);
  assert.match(trace.gpuStages.at(-1).note,/No GPU query result/);
});
