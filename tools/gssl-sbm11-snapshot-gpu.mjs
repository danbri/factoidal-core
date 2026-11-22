// Experimental execution of a frozen GSSL snapshot through the real
// WebGPU backends. This is a device-observation API, *not* a proved
// CertifiedCandidate. The actual shipping SPARQL evaluator is not routed
// through this module.
//
// A request is accepted only if a current, authenticated host-side lease
// matches both before dispatch and after complete GPU readback. The
// immutable input uses exact SBM11 UInt64 values; dense32 is an injective
// snapshot-local remapping, never an unchecked truncation.
import {executeIfCurrent} from "./gssl-sbm11-snapshot.mjs";
import {runSbm11BgpGpu} from "./gssl-sbm11-webgpu.mjs";
import {denseRemap64,decodeDensePairs} from "./gssl-sbm11-dense-u32.mjs";
import {runIntegerBgpGpu} from "../docs/web/hub/paralliverse/integer-bgp-gpu.mjs";

export async function observeSnapshotBgp(request,{current,signal,maxSolutions}={}) {
  return executeIfCurrent(request,{
    current,signal,
    execute:async(graph,query,lease)=>{
      if(lease.layout==="direct64Lanes") {
        const result=await runSbm11BgpGpu(graph,query,{maxSolutions});
        return {
          ...result,layout:lease.layout,
          encoding:"exact two-u32 lanes per SBM11 TermId",
        };
      }
      if(lease.layout==="dense32Snapshot") {
        const dense=denseRemap64(graph,query);
        const result=await runIntegerBgpGpu(dense.triples,dense.queryConstants,
          {maxSolutions});
        const pairs=decodeDensePairs(result.pairs,dense);
        return {
          ...result,pairs,layout:lease.layout,
          dictionarySize:dense.dictionarySize,
          encoding:"reversible snapshot-local u32 remapping of SBM11 TermId",
        };
      }
      throw new RangeError("Unsupported GPU ID representation.");
    },
  });
}
