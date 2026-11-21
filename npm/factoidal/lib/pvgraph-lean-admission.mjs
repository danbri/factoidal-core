// GDSL PVGraph: fail-closed admission capability produced by *native Lean*.
//
// No user-writable {approved:true} flag, hash-only permit, or caller-provided
// "verifier" callback can authorize the public GPU runner. Only an actual
// local Lean interpreter invocation can create the opaque capability.
//
// The returned token is process-local (WeakMap) and bound to *both* the exact
// checked PVGraph document and its typed input bytes. Changing either
// invalidates it. This does not make the JavaScript/WGSL implementation a
// verified refinement of Lean; the host OS, Lean executable/toolchain and
// native output channel are trusted.
//
// Browser support requires a separate audited Lean/Wasm bridge: in a normal
// browser this native verifier deliberately refuses, and the public GPU
// executor will not submit a pass.

import {checkPVGraph,runPVGraphCPU,createOperatorRegistry}
  from "./gdsl-graph.mjs";

const capabilities=new WeakMap();
// Independent fixed core semantics: exported registries may be extended
// or mutated by applications and cannot authorize a GPU execution.
const VERIFIED_CORE=createOperatorRegistry();
const MAX_LEAN_JSON_BYTES=1024*1024;

function normalizeInputs(pvgraph,inputs){
  if(!inputs||typeof inputs!=="object"||Array.isArray(inputs))
    throw new TypeError("PVGraph requires named typed input bindings.");
  const sources=pvgraph.nodes.filter(n=>n.op==="core.input");
  if(Object.keys(inputs).length!==sources.length||
    sources.some(n=>!Object.hasOwn(inputs,n.params.name)))
    throw new TypeError("PVGraph admission requires all and only declared inputs.");
  const normalized=Object.create(null);
  for(const n of sources){
    const v=inputs[n.params.name];
    if(n.params.type==="buffer<u32>"&&(Array.isArray(v)||v instanceof Uint32Array))
      normalized[n.params.name]=Array.from(v);
    else normalized[n.params.name]=v;
  }
  return normalized;
}
async function sha256(s){
  if(!globalThis.crypto?.subtle)
    throw new Error("PVGraph requires WebCrypto SHA-256.");
  const bytes=new TextEncoder().encode(s);
  const digest=new Uint8Array(await globalThis.crypto.subtle.digest("SHA-256",bytes));
  return [...digest].map(v=>v.toString(16).padStart(2,"0")).join("");
}
async function identity(pvgraph,bindings){
  const typedInputs=normalizeInputs(pvgraph,bindings);
  const bytes=JSON.stringify({pvgraph,bindings:typedInputs});
  if(bytes.length>MAX_LEAN_JSON_BYTES)
    throw new RangeError("PVGraph Lean admission payload exceeds 1 MiB.");
  return {bytes,typedInputs,digest:await sha256(bytes)};
}
function canonicalJSON(value){
  if(Array.isArray(value))return value.map(canonicalJSON);
  if(value&&typeof value==="object")
    return Object.fromEntries(Object.entries(value)
      .sort(([a],[b])=>a.localeCompare(b))
      .map(([k,v])=>[k,canonicalJSON(v)]));
  return value;
}
const same=(a,b)=>JSON.stringify(canonicalJSON(a))===
  JSON.stringify(canonicalJSON(b));

/** Obtain a process-local, graph-and-input-bound admission from the REAL
 * Lean GraphEvaluate.evaluate? runner. No injected callback is allowed.
 * The native runtime must be built from the intended repository source.
 *
 * This uses only the Lean source checkout accompanying this module. The
 * package does not accept a caller-supplied, unverified Lean working tree.
 * Installing @factoidal/core without these Lean sources fails closed.
 */
export async function admitPVGraphWithLean(doc,bindings){
  const pvgraph=checkPVGraph(doc,{registry:VERIFIED_CORE});
  // The local JS reference is checked independently against native Lean.
  // Do not leave an unhandled SHA-256 promise if CPU input validation fails.
  const local=runPVGraphCPU(pvgraph,bindings,{registry:VERIFIED_CORE}).outputs;
  const {typedInputs,digest}=await identity(pvgraph,bindings);
  let execFile,fs,tmpdir,join,fileURLToPath;
  try{
    ({execFile}=await import("node:child_process"));
    fs=await import("node:fs/promises");
    ({tmpdir}=await import("node:os"));
    ({join}=await import("node:path"));
    ({fileURLToPath}=await import("node:url"));
  }catch{
    throw new Error("PVGraph Lean admission unavailable: trusted native Lean bridge is not installed.");
  }
  const cwd=fileURLToPath(new URL("../../../formal/lean4/",import.meta.url));
  const executable=fileURLToPath(new URL("../../../formal/lean4/Harness/GdslGraphEval.lean",import.meta.url));
  try{await fs.access(executable);}catch{throw new Error(
    "PVGraph requires the local Lean 4 toolkit and repository Harness/GdslGraphEval.lean; no verification performed.");}
  const root=await fs.mkdtemp(join(tmpdir(),"gdsl-pvgraph-lean-"));
  const fixture=join(root,"request.jsonl");
  try{
    await fs.writeFile(fixture,JSON.stringify({case:digest,pvgraph,bindings:typedInputs})+"\n");
    const result=await new Promise((resolve,reject)=>{
      execFile("lake",["env","lean","--run","Harness/GdslGraphEval.lean",fixture],{
        cwd,timeout:120000,maxBuffer:MAX_LEAN_JSON_BYTES,windowsHide:true,
      },(error,stdout,stderr)=>{
        if(error)return reject(new Error("PVGraph Lean evaluation did not complete: "+
          [stderr,stdout,error.message].filter(Boolean).join("\n").slice(0,3600)));
        resolve({stdout,stderr});
      });
    });
    const lines=result.stdout.trim().split(/\r?\n/);
    if(lines.length!==1)throw Error("PVGraph Lean output must be exactly one JSONL record.");
    let answer;
    try{answer=JSON.parse(lines[0]);}
    catch{throw new Error("PVGraph Lean output is not a JSON record.");}
    if(!answer||answer.case!==digest||answer.accepted!==true||
       !Object.hasOwn(answer,"outputs")||!same(answer.outputs,local))
      throw new Error("PVGraph Lean rejected or disagreed with the checked computation.");
    const token=Object.freeze(Object.create(null));
    capabilities.set(token,Object.freeze({
      digest,expected:answer.outputs,
      verifier:"native Lean 4 GraphJson.decodeCertified? + GraphEvaluate.evaluate?",
    }));
    return token;
  }finally{
    await fs.rm(root,{recursive:true,force:true});
  }
}

/** Invoked only by runPVGraphGPU, before creating the WebGPU session.
  * Recheck binding identity to prevent stale or replayed permits. */
export async function requirePVGraphLeanAdmission(token,pvgraph,bindings){
  const state=token&&typeof token==="object"?capabilities.get(token):undefined;
  if(!state)throw new Error(
    "PVGraph GPU refused: missing native Lean admission for this exact PVGraph and inputs.");
  const {digest}=await identity(pvgraph,bindings);
  if(digest!==state.digest)throw new Error(
    "PVGraph GPU refused: Lean admission does not match current PVGraph/inputs.");
  return state;
}

/** Post-execution check against the value evaluated by native Lean before
 * dispatch. No CPU-host reference is treated as a proof of the GPU driver. */
export function assertPVGraphLeanOutput(state,outputs){
  if(!state||!same(outputs,state.expected))
    throw new Error("PVGraph GPU result disagrees with independently executed Lean semantics.");
}
