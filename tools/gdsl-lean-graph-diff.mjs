// GDSL 0.2 shared-format differential corpus: the real JS checker versus
// Lean GraphJson.decode? on the EXACT SAME canonical JSON documents.
// This is TEST EVIDENCE, not an all-input proof of parser correctness.
import {readFileSync,writeFileSync} from "node:fs";
import {example} from "../npm/factoidal/lib/gdsl-examples.mjs";
import {checkPVGraph} from "../npm/factoidal/lib/gdsl-graph.mjs";

const clone=x=>JSON.parse(JSON.stringify(x));
const cases=[];
function add(name,pvgraph){
  if(cases.some(x=>x.case===name))throw Error("duplicate case "+name);
  let admitted;
  try{checkPVGraph(pvgraph);admitted=true;}
  catch{admitted=false;}
  cases.push({case:name,pvgraph,admitted});
}
function edit(name,doc,mutate){
  const d=clone(doc);mutate(d);add(name,d);
}
for(const domain of ["signal","font","motion","image","basic"]){
  const base=example(domain).pvgraph;
  add(domain+"-positive",base);
  edit(domain+"-duplicate-id",base,d=>d.nodes[1].id=d.nodes[0].id);
  edit(domain+"-duplicate-producer",base,d=>d.links.push(clone(d.links[0])));
  edit(domain+"-missing-input",base,d=>d.links.splice(0,1));
  edit(domain+"-wrong-kind",base,d=>d.links[0].kind="scalar");
  edit(domain+"-wrong-type",base,d=>d.links[0].type="f32");
  edit(domain+"-absent-target",base,d=>d.links[0].to.node="Gone");
  edit(domain+"-back-edge",base,d=>d.links[0].from.node=d.nodes.at(-1).id);
  edit(domain+"-unknown-operator",base,d=>d.nodes[1].op="domain.unknown");
  edit(domain+"-extra-node-field",base,d=>d.nodes[0].arbitrary=true);
  edit(domain+"-extra-link-field",base,d=>d.links[0].arbitrary=true);
  edit(domain+"-extra-top-field",base,d=>d.arbitrary=true);
  edit(domain+"-wrong-version",base,d=>d.version="gdsl/0.3");
  edit(domain+"-nonascii-identifier",base,d=>d.nodes[0].id="êxample");
  edit(domain+"-missing-nodes",base,d=>delete d.nodes);
  edit(domain+"-no-output",base,d=>d.nodes.pop());
}
const signal=example("signal").pvgraph;
edit("signal-unknown-param",signal,d=>d.nodes[1].params.unexpected=9);
edit("signal-negative-u32",signal,d=>d.nodes[1].params.value=-1);
edit("signal-overflow-u32",signal,d=>d.nodes[1].params.value=4294967296);
edit("signal-float-u32",signal,d=>d.nodes[1].params.value=1.5);
edit("signal-string-u32",signal,d=>d.nodes[1].params.value="3");
edit("signal-missing-param",signal,d=>delete d.nodes[1].params.value);
edit("signal-invalid-input-name",signal,d=>d.nodes[0].params.name="x y");
edit("signal-invalid-input-type",signal,d=>d.nodes[0].params.type="buffer<str>");
edit("signal-duplicate-output-name",signal,d=>{
  const old=d.nodes.find(x=>x.op==="core.output");
  const second=clone(old);
  second.id="DifferentOutput";
  d.nodes.push(second);
  // There are still two declared output nodes with the same logical name.
  const link=d.links.find(x=>x.to.node===old.id);
  d.links.push({...clone(link),to:{node:second.id,port:"in"}});
});
edit("signal-extra-128",signal,d=>{
  // Exceed 128 declared nodes; keep JSON syntactically legitimate.
  for(let i=0;i<140;i++)d.nodes.push({id:"J"+i,op:"core.input",
    params:{name:"J"+i,type:"scalar<u32>"}});
});
edit("signal-extra-links",signal,d=>{
  for(let i=0;i<400;i++)d.links.push(clone(d.links[0]));
});
edit("signal-invalid-json-reference",signal,d=>d.links[0].from.arbitrary=0);
edit("signal-invalid-parameter-map",signal,d=>d.nodes[1].params=null);
edit("signal-duplicate-output-port",signal,d=>{
  const first=d.links.find(l=>l.to.node===d.nodes.at(-1).id);
  d.links.push(clone(first));
});

// Legitimate perturbations of built-in operations and identifiers.
for(const n of [0,1,2147483648,4294967295]){
  const d=clone(signal);
  d.nodes.find(x=>x.op==="u32.map.mul").params.value=n;
  add("signal-u32-"+n,d);
}
{
  const d=clone(example("font").pvgraph);
  d.nodes[0].id="Valid_Id.2";
  for(const l of d.links){
    if(l.from.node==="advances")l.from.node="Valid_Id.2";
    if(l.to.node==="advances")l.to.node="Valid_Id.2";
  }
  add("font-ascii-identifier",d);
}
const all=cases.map(({case:id,pvgraph})=>({case:id,pvgraph}));
const expected=cases.map(({case:id,admitted})=>({case:id,admitted}));

function lines(xs){return xs.map(x=>JSON.stringify(x)).join("\n")+"\n";}
const [, ,command,...args]=process.argv;
if(command==="emit"){
  const [fixtures,verdicts]=args;
  if(!fixtures||!verdicts)throw Error("usage: emit cases.jsonl js-verdicts.jsonl");
  writeFileSync(fixtures,lines(all));
  writeFileSync(verdicts,lines(expected));
  console.log(JSON.stringify({cases:all.length,
    jsAccepted:expected.filter(x=>x.admitted).length,
    jsRejected:expected.filter(x=>!x.admitted).length,
    fixturePath:fixtures,verdictPath:verdicts}));
}else if(command==="compare"){
  const [jsFile,leanFile]=args;
  if(!jsFile||!leanFile)throw Error("usage: compare js-verdicts.jsonl lean-verdicts.jsonl");
  const parse=p=>readFileSync(p,"utf8").trim().split("\n").map(JSON.parse);
  const expected=parse(jsFile),actual=parse(leanFile);
  if(expected.length!==actual.length)
    throw Error("Incomplete native Lean corpus: "+actual.length+"/"+expected.length);
  let accepted=0,rejected=0;
  for(let i=0;i<expected.length;i++){
    const a=expected[i],b=actual[i];
    if(a.case!==b.case||a.admitted!==b.admitted)
      throw Error("GDSL JS/Lean disagreement: "+JSON.stringify({js:a,lean:b}));
    if(b.admitted)accepted++;else rejected++;
  }
  console.log(JSON.stringify({status:"pass",
    evidence:"JS and native Lean independently admitted/refused identical GDSL JSON",
    cases:actual.length,accepted,rejected,
    limitation:"differential evidence; no full JS parser refinement proof"},null,2));
}else throw Error("expected emit or compare");
