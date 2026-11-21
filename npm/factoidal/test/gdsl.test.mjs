import test from "node:test";
import assert from "node:assert/strict";
import {
  GDSL_VERSION,PVGraph,example,listExamples,fromPVSexpr,toPVSexpr,
  runPVGraphCPU,runPVGraphGPU,CORE_OPERATORS,
} from "@factoidal/core/gdsl";

test("one experimental package subpath exports all GDSL interfaces",()=>{
  assert.equal(GDSL_VERSION,"gdsl/0.2");
  assert.equal(typeof PVGraph,"function");
  assert.equal(typeof runPVGraphCPU,"function");
  assert.equal(typeof runPVGraphGPU,"function");
  assert.ok(CORE_OPERATORS instanceof Map);
  assert.equal(listExamples().length,5);
});
test("GDSL common graph and S-expression survive the npm package boundary",()=>{
  for(const preset of listExamples()){
    const e=example(preset.id);
    assert.deepEqual(fromPVSexpr(toPVSexpr(e.pvgraph)),e.pvgraph);
    assert.ok(Object.keys(runPVGraphCPU(e.pvgraph,e.input).outputs).length>0);
  }
});
