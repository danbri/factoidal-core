// host_contract_source_test.ts: the hosts' sources against the host contract
// (formal/lean4/L4Factoidal/HostContract/Model.lean), with no engine. The engine checks recorded
// traces (host_contract_check.ts); this check fails sooner, at the source:
//   - every `op` a host writes in a request is an operation of `HostContract.ops`;
//   - host-trace.mjs records the relaxing fields and drops the measurement fields that Lean lists;
//   - the window and the Hub take the scroll limit from page-load.mjs, not from a copy.
import {strict as assert} from "node:assert";
import {MEASURE_FIELDS,RELAX_FIELDS} from "../../../docs/web/hub/foafnaut/host-trace.mjs";

const lab=new URL(".",import.meta.url).pathname,root=new URL("../../../",import.meta.url).pathname;
const model=await Deno.readTextFile(`${root}formal/lean4/L4Factoidal/HostContract/Model.lean`);
const listOf=(name:string)=>{
  const m=model.match(new RegExp(`def ${name} : List String := \\[([^\\]]*)\\]`));
  assert.ok(m,`Model.lean has no ${name}`);
  return [...m[1].matchAll(/"([^"]+)"/g)].map(x=>x[1]);
};
const ops=new Set([...model.matchAll(/⟨"([A-Za-z]+)", \.(state|query|counter|hostFact)/g)].map(m=>m[1]));
const hosts=["native_html_engine.ts","run_html.ts","native_html_document.ts","textnaut/textnaut.ts",
  "../../../docs/web/hub/foafnaut/browser-worker.mjs","../../../docs/web/hub/foafnaut/link-route.mjs",
  "../../../docs/web/hub/textnaut/engine-core.mjs","../../../docs/web/hub/epub/worker.mjs"];

Deno.test("host contract: every op a host sends is in HostContract.ops",async()=>{
  assert.ok(ops.size>=60,`only ${ops.size} operations read from Model.lean`);
  const unknown:string[]=[];
  for(const host of hosts){
    const source=await Deno.readTextFile(`${lab}${host}`);
    for(const m of source.matchAll(/op: ?['"]([a-zA-Z]+)['"]/g))if(!ops.has(m[1]))unknown.push(`${host}: ${m[1]}`);
  }
  assert.deepEqual(unknown,[],"add the operation to HostContract.ops (with its kind and needs), or do not send it");
});

Deno.test("host contract: host-trace.mjs uses Lean's field lists",()=>{
  assert.deepEqual(RELAX_FIELDS,listOf("relaxFields"));
  assert.deepEqual(MEASURE_FIELDS,listOf("measureFields"));
});

Deno.test("host contract: one scroll limit for the window and the Hub",async()=>{
  for(const host of ["run_html.ts","../../../docs/web/hub/foafnaut/browser-worker.mjs"]){
    const source=await Deno.readTextFile(`${lab}${host}`);
    assert.ok(/scrollLimitOf\(/.test(source),`${host} does not take the scroll limit from page-load.mjs`);
    assert.ok(!/60\*scale/.test(source),`${host} has its own copy of the scroll limit`);
  }
});
