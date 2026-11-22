// Actual Mesa/WebGPU GPU execution of the integer-coded BGP fragment.
// The *expected* results and count/offset arrays are emitted by native
// Lean 4, never computed by this JavaScript harness.
import {runIntegerBgpGpu,COUNT,SCAN,EMIT} from "../docs/web/hub/paralliverse/integer-bgp-gpu.mjs";
import {runCompactedBgpGpu,SHADERS} from "../docs/web/hub/paralliverse/integer-bgp-compact-gpu.mjs";

const [filename, commit] = Deno.args;
if(!filename || !/^[a-f0-9]{40}$/.test(commit??""))
  throw new Error("Usage: integer-bgp-device-smoke.mjs LEAN.jsonl SHA");
const rows=(await Deno.readTextFile(filename)).trim().split("\n").map(JSON.parse);
if(rows.length!==5 || rows.some(x=>x.kind!=="fixture"))
  throw new Error("Incomplete native Lean BGP fixture stream.");
const hashes=[];
for(const source of [COUNT,SCAN,EMIT,...SHADERS]){
  const digest=await crypto.subtle.digest("SHA-256",new TextEncoder().encode(source));
  hashes.push(Array.from(new Uint8Array(digest),x=>x.toString(16).padStart(2,"0")).join(""));
}
const output={format:"paralliverse-integer-bgp-gpu-v1",sourceCommit:commit,
  status:"fail",denoVersion:Deno.version.deno,
  provenance:"Native Lean integer BGP oracle versus actual Deno WebGPU",
  shaderHashes:hashes,cases:[]};
try{
  for(const test of rows){
    const start=performance.now();
    const actual=await runIntegerBgpGpu(test.triples);
    for(const [name,expect,got] of [
      ["row match counts",test.counts,actual.counts],
      ["exclusive offsets",test.offsets,actual.offsets],
      ["BGP solution bindings",test.expected,actual.pairs],
    ]){
      const e=JSON.stringify(expect),a=JSON.stringify(got);
      if(e!==a)throw new Error(test.people+" people "+name+": "+a.slice(0,900)+" != "+e.slice(0,900));
    }
    if(actual.solutionCount!==test.expected.length)
      throw new Error("GPU total does not match the native Lean solution multiset.");
    const compactStarted=performance.now();
    const compact=await runCompactedBgpGpu(test.triples);
    for(const [name,expect,got] of [
      ["compacted knows projection",test.left,compact.leftRows],
      ["compacted Atlas projection",test.right,compact.rightRows],
      ["compacted join counts",test.joinCounts,compact.counts],
      ["compacted join offsets",test.joinOffsets,compact.offsets],
      ["compacted GPU joined bindings",test.expected,compact.pairs],
    ]){
      const e=JSON.stringify(expect),a=JSON.stringify(got);
      if(e!==a)throw new Error(test.people+" people "+name+": "+a.slice(0,900)+" != "+e.slice(0,900));
    }
    output.cases.push({people:test.people,triples:test.triples.length,
      pairs:actual.solutionCount,adapter:actual.adapter,
      isFallbackAdapter:actual.isFallbackAdapter,
      devicePipeline:actual.engine,
      elapsedMs:Math.round((performance.now()-start)*10)/10,
      compacted:{
        actualWebGPU:true,algorithm:compact.backend,
        leftRows:compact.leftCount,rightRows:compact.rightCount,
        comparisonsPerPass:compact.leftCount*compact.rightCount,
        pairs:compact.solutionCount,
        elapsedMs:Math.round((performance.now()-compactStarted)*10)/10,
        validatedAllIntermediateRows:true,
      }});
  }
  output.status="pass";
}catch(e){
  output.error=e instanceof Error?e.stack:String(e);
  console.error(e);
  Deno.exitCode=1;
}
console.log(JSON.stringify(output,null,2));
