import test from "node:test";
import assert from "node:assert/strict";
import {
  GDSL_VERSION,graph,example,listExamples,fromSexpr,toSexpr,
  runCPU,runGraphGPU,CORE_OPERATORS,
} from "@factoidal/core/gdsl";

test("one experimental package subpath exports all GDSL interfaces",()=>{
  assert.equal(GDSL_VERSION,"gdsl/0.2");
  assert.equal(typeof graph,"function");
  assert.equal(typeof runCPU,"function");
  assert.equal(typeof runGraphGPU,"function");
  assert.ok(CORE_OPERATORS instanceof Map);
  assert.equal(listExamples().length,5);
});
test("GDSL common graph and S-expression survive the npm package boundary",()=>{
  for(const preset of listExamples()){
    const e=example(preset.id);
    assert.deepEqual(fromSexpr(toSexpr(e.graph)),e.graph);
    assert.ok(Object.keys(runCPU(e.graph,e.input).outputs).length>0);
  }
});
