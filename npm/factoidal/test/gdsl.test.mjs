import test from "node:test";
import assert from "node:assert/strict";
import {createPVGraphWasm,listExamples,example} from "@factoidal/core/gdsl";

test("only Lean/Wasm-backed PVGraph operations are public",async()=>{
  const api=await import("@factoidal/core/gdsl");
  assert.deepEqual(Object.keys(api).sort(),[
    "createGsslResidentSession","createPVGraphWasm","example","listExamples","runPVGraph"
  ]);
  assert.equal(listExamples().length,5);
  await assert.rejects(createPVGraphWasm(async()=>({
    call:()=>({ok:true,ops:[]})
  })),/requires a rebuilt Lean engine/);
});
test("examples require the Lean/Wasm backend",async()=>{
  assert.deepEqual(listExamples().map(e=>e.domain),
    ["signal","font","motion","image","basic"]);
  await assert.rejects(example("signal",async()=>({call:()=>({ok:true,ops:[]})})),
    /requires a rebuilt Lean engine/);
});
