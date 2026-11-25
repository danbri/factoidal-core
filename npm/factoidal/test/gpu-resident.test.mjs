import test from "node:test";
import assert from "node:assert/strict";
import {createGsslResidentSession}
  from "@factoidal/core/gpu-resident";

test("optional generic GPU subpath is exported without loading RDF or Wasm",()=>{
  assert.equal(typeof createGsslResidentSession,"function");
});

test("generic resident session rejects invalid configuration before GPU access",async()=>{
  await assert.rejects(createGsslResidentSession({byteBudget:3}),/4-aligned/);
  await assert.rejects(createGsslResidentSession({inspectMaxWords:-1}),/capacity/);
});
