// GDSL 0.2 WebGPU execution of the SAME canonical typed dataflow graph.
// Only a fixed, trusted WGSL kernel and admitted opcodes, never arbitrary
// user-authored WGSL. Pure CPU semantics belong to gdsl-graph.mjs.
// Observational evidence only; no general Lean/WGSL refinement theorem.
import {checkPVGraph,CORE_OPERATORS,MAX_BUFFER_WORDS} from "./gdsl-graph.mjs";
import {createGsslResidentSession} from "./gpu-resident.mjs";
import {requirePVGraphLeanAdmission,assertPVGraphLeanOutput}
  from "./pvgraph-lean-admission.mjs";

const CODES=Object.freeze({
  "u32.map.add":1,"u32.map.mul":2,"u32.map.xor":3,
  "u32.zip.add":4,"u32.zip.xor":5,"u32.scan.sum":6,
  "u32.reduce.sum":7,"u32.scalar.add":8,"u32.broadcast":9,
});
export const GDSL_GRAPH_WGSL=String.raw`
@group(0) @binding(0) var<storage, read> inputA: array<u32>;
@group(0) @binding(1) var<storage, read> inputB: array<u32>;
@group(0) @binding(2) var<storage, read_write> result: array<u32>;
@group(0) @binding(3) var<storage, read> config: array<u32>;
@compute @workgroup_size(64, 1, 1)
fn main(@builtin(global_invocation_id) id: vec3<u32>) {
  let op=config[0];
  let n=config[1];
  let k=config[2];
  let i=id.x;
  // Scan and reduction deliberately run in a *single* GPU invocation.
  // This is portable correctness experimentation, NOT a performance claim.
  if(op==6u||op==7u) {
    if(i!=0u){return;}
    var sum=0u;
    for(var j=0u;j<n;j=j+1u) {
      sum=sum+inputA[j];
      if(op==6u){result[j]=sum;}
    }
    if(op==7u){result[0]=sum;}
    return;
  }
  if(op==8u){
    if(i==0u){result[0]=inputA[0]+inputB[0];}
    return;
  }
  if(i>=n){return;}
  if(op==1u){result[i]=inputA[i]+k;}
  else if(op==2u){result[i]=inputA[i]*k;}
  else if(op==3u){result[i]=inputA[i]^k;}
  else if(op==4u){result[i]=inputA[i]+inputB[i];}
  else if(op==5u){result[i]=inputA[i]^inputB[i];}
  else if(op==9u){result[i]=inputA[0];}
}
`;
const integer=x=>Number.isInteger(x)&&x>=0&&x<=0xffffffff;
const typeOfInput=t=>t==="scalar<u32>"?"scalar":"buffer";
function readInput(v,type){
  if(typeOfInput(type)==="scalar"){
    if(!integer(v))throw new TypeError("GDSL GPU scalar input must be exact uint32.");
    return [v>>>0];
  }
  if(!Array.isArray(v)&&!(v instanceof Uint32Array))
    throw new TypeError("GDSL GPU buffer must be an Array or Uint32Array.");
  if(v.length>MAX_BUFFER_WORDS||Array.from(v).some(x=>!integer(x)))
    throw new RangeError("GDSL GPU buffer exceeds bounds or contains non-u32 values.");
  return Array.from(v,x=>x>>>0);
}
async function hashGraph(graph){
  const bytes=new TextEncoder().encode(JSON.stringify(graph));
  const h=new Uint8Array(await crypto.subtle.digest("SHA-256",bytes));
  return [...h.slice(0,8)].map(v=>v.toString(16).padStart(2,"0")).join("");
}
function inbound(graph,id){
  return new Map(graph.links.filter(l=>l.to.node===id)
    .map(l=>[l.to.port,l.from.node]));
}
function ports(op){
  if(op==="u32.map.add"||op==="u32.map.mul"||op==="u32.map.xor"||
     op==="u32.scan.sum"||op==="u32.reduce.sum")return ["x"];
  if(op==="u32.broadcast")return ["value","shape"];
  return ["a","b"];
}

/** Runs an entire admitted graph through the same shared dataflow topology.
 * A caller-supplied generic resident session may be reused across graphs.
 * With no session supplied, one is created and always closed on return.
 */
export async function runPVGraphGPU(doc,bindings,{admission=null,session=null,
    registry=CORE_OPERATORS,readbackMaxWords=256}={}){
  const g=checkPVGraph(doc,{registry});
  if(!Number.isSafeInteger(readbackMaxWords)||readbackMaxWords<1||
      readbackMaxWords>256)
    throw new RangeError("GDSL diagnostic readback bound is 1..256.");
  if(!bindings||typeof bindings!=="object"||Array.isArray(bindings))
    throw new TypeError("GDSL GPU expects named input bindings.");
  const inputs=g.nodes.filter(n=>n.op==="core.input");
  if(Object.keys(bindings).length!==inputs.length||
    inputs.some(n=>!Object.prototype.hasOwnProperty.call(bindings,n.params.name)))
    throw new TypeError("GDSL GPU expects all and only graph inputs.");
  // Check the *whole* program before touching the device: no partial
  // execution of graphs with unknown domain-specific operators.
  const unsupported=g.nodes.filter(n=>!["core.input","core.output",
      "u32.scalar.const"].includes(n.op)&&!Object.hasOwn(CODES,n.op));
  if(unsupported.length)
    throw new Error("GDSL GPU refuses unsupported op: "+
      unsupported.map(n=>n.op).join(","));
  const bound=new Map(inputs.map(n=>[n.id,readInput(
    bindings[n.params.name],n.params.type)]));
  // Mandatory: real native-Lean-checked admission of this exact program
  // AND input content. No GPU adapter/session/buffer is created beforehand.
  // A caller-created {approved:true} object, a hash, or stale permit fails.
  const leanState=await requirePVGraphLeanAdmission(admission,g,bindings);
  const prefix="gdsl-"+await hashGraph(g)+"-";
  let owned=false;
  if(!session){
    session=await createGsslResidentSession({
      byteBudget:8*1024*1024,inspectMaxWords:256});
    owned=true;
  }
  const values=new Map(),outputs=Object.create(null),trace=[];
  let dispatched=0;
  function ensure(id,count){
    const bytes=Math.max(4,count*4);
    const previous=session.status().resources.find(r=>r.id===id);
    if(previous&&previous.bytes!==bytes)session.release(id);
    if(!session.status().resources.some(r=>r.id===id))
      session.allocate(id,bytes);
  }
  async function upload(id,words){
    await session.upload(id,new Uint32Array(words.length?words:[0]));
  }
  try{
    await session.compile("gdsl-v02-graph",GDSL_GRAPH_WGSL);
    const dummy=prefix+"zero";
    await upload(dummy,[0]);
    for(const node of g.nodes){
      const id=prefix+node.id;
      if(node.op==="core.input"){
        const data=bound.get(node.id);
        await upload(id,data);
        values.set(node.id,{id,length:data.length,type:node.params.type});
        trace.push({id:node.id,op:node.op,status:"host-input",length:data.length});
        continue;
      }
      if(node.op==="u32.scalar.const"){
        await upload(id,[node.params.value]);
        values.set(node.id,{id,length:1,type:"scalar<u32>"});
        trace.push({id:node.id,op:node.op,status:"host-constant",length:1});
        continue;
      }
      const refs=inbound(g,node.id);
      if(node.op==="core.output"){
        const src=values.get(refs.get("in"));
        values.set(node.id,src);
        outputs[node.params.name]=src;
        trace.push({id:node.id,op:node.op,status:"alias",length:src.length});
        continue;
      }
      const inputs=Object.fromEntries(ports(node.op).map(port=>
        [port,values.get(refs.get(port))]));
      const a=inputs.x||inputs.a||inputs.value;
      const b=inputs.b||inputs.shape;
      if(!a||(["u32.zip.add","u32.zip.xor","u32.scalar.add",
          "u32.broadcast"].includes(node.op)&&!b))
        throw new Error("GDSL GPU missing admitted input buffer.");
      if((node.op==="u32.zip.add"||node.op==="u32.zip.xor")&&
          a.length!==b.length)
        throw new RangeError("GDSL GPU zip length mismatch.");
      let count=a.length;
      if(node.op==="u32.broadcast")count=b.length;
      if(node.op==="u32.reduce.sum"||node.op==="u32.scalar.add")
        count=1;
      ensure(id,count);
      const cfg=prefix+node.id+"-cfg";
      const length=(node.op==="u32.reduce.sum"||
        node.op==="u32.scan.sum")?a.length:count;
      await upload(cfg,[CODES[node.op],length,node.params.value??0,0]);
      await session.dispatch({
        kernel:"gdsl-v02-graph",
        bindings:[
          {binding:0,id:a.id},
          {binding:1,id:b?.id??dummy},
          {binding:2,id},
          {binding:3,id:cfg},
        ],
        writes:[id],
        workgroups:[Math.max(1,Math.ceil(count/64)),1,1],
      });
      dispatched++;
      const type=registry.get(node.op).outputs.out;
      values.set(node.id,{id,length:count,type});
      trace.push({id:node.id,op:node.op,status:"gpu-compute",length:count});
    }
    const results=Object.create(null);
    for(const [name,info] of Object.entries(outputs)){
      const words=[];
      for(let at=0;at<info.length;at+=readbackMaxWords){
        const part=await session.inspect(info.id,{
          offsetWords:at,countWords:Math.min(readbackMaxWords,info.length-at)});
        words.push(...part.words);
      }
      results[name]=info.type==="scalar<u32>"?words[0]:words;
    }
    // The final observed device value must match the independent Lean
    // interpreter; mismatch is a failed execution, never certified success.
    assertPVGraphLeanOutput(leanState,results);
    return {status:"observed-not-proven",leanAdmission:"native-checked",
      outputs:results,trace,
      gpuDispatches:dispatched,pvgraph:g,resident:session.status()};
  }finally{
    if(owned){try{session.close();}catch{}}
  }
}
