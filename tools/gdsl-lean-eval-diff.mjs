// Executable semantic differential: the *same serialized canonical graph*
// and its named inputs go into the JS runPVGraphCPU and native Lean evaluate?.
// Not proof of arbitrary JS/Lean semantics or GPU correctness.
import {readFileSync,writeFileSync} from "node:fs";
import {PVGraph,runPVGraphCPU,checkPVGraph}
  from "../npm/factoidal/lib/gdsl-graph.mjs";
import {example} from "../npm/factoidal/lib/gdsl-examples.mjs";

const clone=v=>JSON.parse(JSON.stringify(v));
const all=[];
let seed=0x7fa91357;
function randomU32(){
  seed=(Math.imul(seed,1664525)+1013904223)>>>0;
  return seed;
}
function sample(n){
  return Array.from({length:n},(_,i)=>
    i%5===0?0xffffffff:i%5===1?0x80000000:randomU32());
}
function add(label,document,bindings){
  if(all.some(x=>x.case===label))throw Error("reused semantic corpus ID");
  let expected;
  try{
    const accepted=checkPVGraph(document);
    expected={case:label,accepted:true,
      outputs:runPVGraphCPU(accepted,bindings).outputs};
  }catch{
    expected={case:label,accepted:false};
  }
  all.push({case:label,pvgraph:document,bindings:clone(bindings),expected});
}
for(const domain of ["signal","font","motion","image","basic"]){
  const e=example(domain);
  add(domain+"-sample",e.pvgraph,e.input);
  const keys=Object.keys(e.input);
  add(domain+"-empty",e.pvgraph,Object.fromEntries(keys.map(k=>[k,[]])));
  add(domain+"-high",e.pvgraph,Object.fromEntries(keys.map(k=>[k,
    [0,1,0x80000000,0xffffffff,0x7fffffff,0xaaaaaaaa,0x55555555]])));
  add(domain+"-duplicates",e.pvgraph,Object.fromEntries(keys.map(k=>[k,
    [1,1,1,1,9,9,9,0,0,0,4294967295,4294967295]])));
  for(let i=0;i<12;i++){
    const len=i===0?1:(i%4)*7+1;
    add(domain+"-random-"+i,e.pvgraph,Object.fromEntries(keys.map(k=>[k,sample(len)])));
  }
}
{
  const g=PVGraph();
  const scalar=g.input("amount","scalar<u32>");
  const template=g.input("template");
  const repeated=g.op("u32.broadcast",{value:scalar,shape:template});
  const out=g.op("u32.zip.add",{a:template,b:repeated});
  g.output("shifted",out);
  for(const k of [0,1,0x80000000,0xffffffff]){
    add("scalar-input-"+k,g.build(),
      {amount:k,template:[0,1,2,3,0xffffffff]});
  }
  add("scalar-input-wrong-type",g.build(),
    {amount:[8],template:[0,1,2]});
}
{
  const g=PVGraph();
  const a=g.input("a","scalar<u32>");
  const b=g.input("b","scalar<u32>");
  const sum=g.op("u32.scalar.add",{a,b});
  g.output("out",sum,"scalar<u32>");
  for(const [a,b] of [[0,0],[0xffffffff,1],[0x80000000,0x80000000],
    [2,15],[0x55555555,0xaaaaaaaa]])
    add("scalar-sum-"+a+"-"+b,g.build(),{a,b});
}
{
  const e=example("motion");
  add("motion-zip-mismatch",e.pvgraph,{positions:[1,2],velocities:[1,2,3]});
  add("motion-too-long",e.pvgraph,{positions:sample(4097),velocities:sample(4097)});
  add("motion-missing-binding",e.pvgraph,{positions:[2,3]});
  add("motion-extra-binding",e.pvgraph,{...e.input,extra:[1]});
  add("motion-wrong-word",e.pvgraph,{positions:[2.2],velocities:[3]});
}
{
  const e=example("signal");
  const d=clone(e.pvgraph);
  d.nodes[1].op="u32.not-registered";
  add("invalid-op",d,e.input);
}
const lines=xs=>xs.map(x=>JSON.stringify(x)).join("\n")+"\n";
const [, ,cmd,...args]=process.argv;
if(cmd==="emit"){
  const [fixtures,expectedPath]=args;
  if(!fixtures||!expectedPath)throw Error("usage: emit INPUT.jsonl EXPECT.jsonl");
  writeFileSync(fixtures,lines(all.map(({case:id,pvgraph,bindings})=>
    ({case:id,pvgraph,bindings}))));
  writeFileSync(expectedPath,lines(all.map(x=>x.expected)));
  console.log(JSON.stringify({semanticCases:all.length,
    accepted:all.filter(x=>x.expected.accepted).length,
    refused:all.filter(x=>!x.expected.accepted).length}));
}else if(cmd==="compare"){
  const [expectedFile,actualFile]=args;
  if(!expectedFile||!actualFile)throw Error("usage: compare EXPECT.jsonl ACTUAL.jsonl");
  const parse=p=>readFileSync(p,"utf8").trim().split("\n").map(JSON.parse);
  const expected=parse(expectedFile),actual=parse(actualFile);
  if(expected.length!==actual.length)throw Error("Native Lean semantic corpus is incomplete.");
  const normalize=o=>{
    if(Array.isArray(o))return o.map(normalize);
    if(o&&typeof o==="object")return Object.fromEntries(
      Object.entries(o).sort(([a],[b])=>a.localeCompare(b))
        .map(([k,v])=>[k,normalize(v)]));
    return o;
  };
  for(let i=0;i<expected.length;i++){
    if(JSON.stringify(normalize(expected[i]))!==
       JSON.stringify(normalize(actual[i])))
      throw Error("Lean/JS semantic disagreement: "+
        JSON.stringify({expected:expected[i],actual:actual[i]}));
  }
  console.log(JSON.stringify({status:"pass",cases:expected.length,
    accepted:expected.filter(x=>x.accepted).length,
    refused:expected.filter(x=>!x.accepted).length,
    evidence:"same JSON graph/input interpreted by independent native Lean and JS",
    caveat:"differential checks, not semantic refinement theorem"},null,2));
}else throw Error("Expected emit or compare");
