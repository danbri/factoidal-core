// Experimental GSSL snapshot identity gate for SBM11 GPU requests.
// Host control-plane only: this does NOT prove WGSL compiler/driver behavior.
// The immutable source and query buffers are hashed *before* dispatch.
// The caller must supply a genuine SBM11 generation and codebook digest.
// No raw GPU response becomes a Lean CertifiedCandidate merely by passing this.
import {packTriples64,parseId} from "./gssl-sbm11-webgpu.mjs";

const validDigest = x => typeof x === "string" && /^[a-f0-9]{64}$/i.test(x);
const validText = x => typeof x === "string" && x.length > 0 && x.length <= 1024;
const FIELDS=["sourceId","generation","graphId","graphDigest","codebookDigest",
  "queryDigest","requestNumber","layout"];
const layouts = new Set(["direct64Lanes","dense32Snapshot"]);
function encodeWordsLE(words) {
  const out = new Uint8Array(words.length*4);
  const view = new DataView(out.buffer);
  for(let i=0;i<words.length;i++)view.setUint32(i*4,words[i],true);
  return out;
}
async function sha256Hex(bytes) {
  const d=await crypto.subtle.digest("SHA-256",bytes);
  return [...new Uint8Array(d)].map(x=>x.toString(16).padStart(2,"0")).join("");
}
export function leaseEqual(a,b) {
  return Boolean(a && b) && FIELDS.every(key=>a[key]===b[key]);
}
// Create a copied, frozen source graph so late caller mutations cannot change
// the GPU input without also changing its content hash.
export async function createSnapshotRequest({
  sourceId,generation,graphId,codebookDigest,requestNumber,layout,
  triples,queryConstants,queryText,
}) {
  if(!validText(sourceId)||!validText(generation))
    throw new TypeError("An authentic source and generation identifier are required.");
  if(!validText(queryText))
    throw new TypeError("The exact SPARQL query text must be supplied for request identity.");
  if(!validDigest(codebookDigest))
    throw new TypeError("The codebook manifest SHA-256 must be supplied.");
  if(!Number.isSafeInteger(requestNumber)||requestNumber<1)
    throw new RangeError("Unique positive request ticket required.");
  if(!layouts.has(layout))throw new RangeError("Unknown GPU representation.");
  const graphId64=parseId(graphId);
  const graph=Object.freeze(packTriples64(triples).triples.map(row=>Object.freeze(row)));
  const query=Object.freeze({
    knows:parseId(queryConstants.knows),works:parseId(queryConstants.works),
    atlas:parseId(queryConstants.atlas),
  });
  const payload=packTriples64(graph).words;
  const queryWords = new Uint32Array(6);
  const constants=[query.knows,query.works,query.atlas];
  for(let i=0;i<3;i++){
    queryWords[2*i]=Number(constants[i]&0xffffffffn);
    queryWords[2*i+1]=Number(constants[i]>>32n);
  }
  // Include the exact UTF-8 query bytes, not just the three fixed constants.
  // Distinct SELECT projections or variable names must not share a lease.
  const queryTextBytes=new TextEncoder().encode(queryText);
  const queryLaneBytes=encodeWordsLE(queryWords);
  const queryBytes=new Uint8Array(4+queryTextBytes.length+queryLaneBytes.length);
  new DataView(queryBytes.buffer).setUint32(0,queryTextBytes.length,true);
  queryBytes.set(queryTextBytes,4);
  queryBytes.set(queryLaneBytes,4+queryTextBytes.length);
  const [graphDigest,queryDigest]=await Promise.all([
    sha256Hex(encodeWordsLE(payload)),sha256Hex(queryBytes),
  ]);
  const lease=Object.freeze({sourceId,generation,graphId:graphId64.toString(),
    graphDigest,codebookDigest:codebookDigest.toLowerCase(),queryDigest,
    requestNumber,layout});
  return Object.freeze({lease,graph,query});
}
function refused(reason) {return {status:"fallback",reason,result:null};}
// Only observed data may cross this boundary. Certification still requires
// a theorem about the exact backend, query, and active RDF graph.
export async function executeIfCurrent(request,{current,execute,signal}){
  if(typeof current!=="function"||typeof execute!=="function")
    throw new TypeError("Both current-lease provider and backend are required.");
  if(signal?.aborted)return refused("cancelled");
  if(!leaseEqual(current(),request.lease))return refused("stale-before-dispatch");
  let result;
  try{result=await execute(request.graph,request.query,request.lease);}
  catch(error){return refused("device-failed: "+(error?.message||String(error)));}
  if(signal?.aborted)return refused("cancelled");
  if(!leaseEqual(current(),request.lease))return refused("stale-after-readback");
  if(result == null)return refused("missing-device-readback");
  return {status:"observed-not-certified",reason:null,result,lease:request.lease};
}
