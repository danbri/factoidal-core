import test from "node:test";
import assert from "node:assert/strict";
import {
  GDSL_VERSION,MAX_NODES,MAX_LINKS,CORE_OPERATORS,
  createOperatorRegistry,PVGraph,checkPVGraph,toPVSexpr,fromPVSexpr,runPVGraphCPU
} from "../npm/factoidal/lib/gdsl-graph.mjs";
import {example,listExamples}
  from "../npm/factoidal/lib/gdsl-examples.mjs";
import {GDSL_PVGRAPH_WGSL,runPVGraphGPU}
  from "../npm/factoidal/lib/gdsl-webgpu.mjs";

const copy=x=>JSON.parse(JSON.stringify(x));
const entries=o=>Object.entries(o).sort(([a],[b])=>a.localeCompare(b));
test("all five real-world illustrations use one graph schema and sexpr grammar",()=>{
  assert.equal(GDSL_VERSION,"gdsl/0.2");
  assert.deepEqual(listExamples().map(x=>x.domain),
    ["signal","font","motion","image","basic"]);
  for(const info of listExamples()){
    const {pvgraph:doc,sexpr,input}=example(info.id);
    assert.deepEqual(checkPVGraph(doc),doc);
    assert.deepEqual(fromPVSexpr(sexpr),doc);
    assert.equal(toPVSexpr(fromPVSexpr(sexpr)),sexpr);
    const ref=runPVGraphCPU(doc,input);
    const ref2=runPVGraphCPU(fromPVSexpr(sexpr),input);
    assert.deepEqual(entries(ref.outputs),entries(ref2.outputs));
    assert.equal(ref.trace.length,doc.nodes.length);
    assert.ok(doc.links.every(l=>l.kind==="buffer"||l.kind==="scalar"));
    assert.ok(doc.nodes.every(n=>n.op.includes(".")));
    assert.ok(entries(ref.outputs).length>=1);
  }
});
test("single basic graph covers fanout, zip, scan, reduction with exact numeric answers",()=>{
  const run=runPVGraphCPU(example("signal").pvgraph,example("signal").input);
  const waves=example("signal").input.waves;
  const bands=waves.map(x=>((Math.imul(x,257)>>>0)^((x+31)>>>0))>>>0);
  let acc=0;
  assert.deepEqual(run.outputs.bands,bands);
  assert.deepEqual(run.outputs.phase,bands.map(x=>(acc=(acc+x)>>>0)));
  assert.equal(run.outputs.intensity,acc);
});
test("glyph positions and line width are both returned through typed links",()=>{
  const e=example("font"),r=runPVGraphCPU(e.pvgraph,e.input);
  let sum=0;
  assert.deepEqual(r.outputs.penPositions,e.input.advances.map(x=>(sum=(sum+x+1)>>>0)));
  assert.equal(r.outputs.lineWidth,sum);
  assert.equal(e.pvgraph.links.filter(x=>x.kind==="scalar").length,1);
});
test("wire shape and duplicate reference rules are enforced before execution",()=>{
  const doc=example("signal").pvgraph;
  const copyWith = transform=>{const d=copy(doc);transform(d);return d;};
  assert.throws(()=>checkPVGraph(copyWith(g=>g.nodes[1].id=g.nodes[0].id)),/Duplicate node ID/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links[0].kind="scalar")) ,/kind/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links[0].type="f32")) ,/kind/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links[0].to.node="missing")) ,/missing/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links[0].to.port="unknown")) ,/port/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links.push(copy(g.links[0])))) ,/more than one/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links.pop())) ,/Wrong inbound/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links[0].from.node="phase")) ,/forward/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.nodes[1].params.value=0x100000000)) ,/uint32/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.nodes[1].unexpected=1)) ,/exactly/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.links[0].unexpected=1)) ,/exactly/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.version="sparql-experimental")) ,/version/);
  assert.throws(()=>checkPVGraph(copyWith(g=>g.nodes[1].op="other.dsl")) ,/Unknown operator/);
});
test("sexpr refusals have bounded grammar, no evaluation of JavaScript",()=>{
  const s=example("motion").sexpr;
  for(const wrong of [
    s.slice(0,-1),
    s+")",
    s.replace("(pvgraph gdsl/0.2","(pvgraph gdsl/0.1"),
    s.replace("(link ","(wrong "),
    s.replace("u32.zip.add","u32.unknown"),
    s.replace("buffer u32","event u32"),
    s.replace("(param value 4)","(param value 4294967296)"),
    s.replace("(param value 4)","(param value 4) (param value 4)"),
    "(pvgraph gdsl/0.2 (node x core.input (param name "+'"'+"__proto__"+'"'+" ) (param type "+'"'+"buffer<u32>"+'"'+")))",
  ])assert.throws(()=>fromPVSexpr(wrong));
  assert.throws(()=>fromPVSexpr("(".repeat(10000)),/oversized|token limit|nesting/);
});
test("CPU validator rejects lossy floats, mismatched zip arrays, or wrong input shape",()=>{
  const motion=example("motion");
  assert.throws(()=>runPVGraphCPU(motion.pvgraph,{positions:[1],velocities:[2,3]}),/zip/);
  assert.throws(()=>runPVGraphCPU(motion.pvgraph,{positions:[1.25],velocities:[2]}),/uint32/);
  assert.throws(()=>runPVGraphCPU(motion.pvgraph,{positions:[1],velocities:[-1]}),/uint32/);
  assert.throws(()=>runPVGraphCPU(motion.pvgraph,{positions:[1],velocities:[2],extra:[]}),/All and only/);
  assert.throws(()=>runPVGraphCPU(motion.pvgraph,{positions:[],velocities:[0x100000000]}),/uint32/);
  assert.throws(()=>runPVGraphCPU(motion.pvgraph,{}),/All and only/);
});
test("empty and duplicate buffers preserve list semantics",()=>{
  const e=example("font");
  assert.deepEqual(entries(runPVGraphCPU(e.pvgraph,{advances:[]}).outputs),
    entries({penPositions:[],lineWidth:0}));
  assert.deepEqual(runPVGraphCPU(e.pvgraph,{advances:[3,3,3]}).outputs.penPositions,[4,8,12]);
});
test("domain extensions register ops but may not change the syntax or override core",()=>{
  const registry=createOperatorRegistry([{
    name:"font.advances.double",inputs:{x:"buffer<u32>"},
    outputs:{out:"buffer<u32>"},params:{},execute:({x})=>x.map(n=>(n*2)>>>0),
  }]);
  const g=PVGraph({registry});
  const x=g.input("advances");
  const y=g.op("font.advances.double",{x},{},{id:"double"});
  g.output("result",y);
  const d=g.build();
  assert.equal(runPVGraphCPU(d,{advances:[3,4]},{registry}).outputs.result[0],6);
  assert.deepEqual(fromPVSexpr(toPVSexpr(d,{registry}),{registry}),d);
  assert.throws(()=>checkPVGraph(d),/Unknown operator/);
  assert.throws(()=>createOperatorRegistry([{
    name:"u32.map.add",inputs:{x:"buffer<u32>"},
    outputs:{out:"buffer<u32>"},params:{},execute:()=>[],
  }]),/Duplicate/);
});
test("canonical registry supports every basic operation independent of a domain",()=>{
  for(const name of ["u32.map.add","u32.map.mul","u32.map.xor",
    "u32.zip.add","u32.zip.xor","u32.scan.sum",
    "u32.reduce.sum","u32.scalar.const","u32.scalar.add","u32.broadcast"]){
    assert.ok(CORE_OPERATORS.has(name),name);
  }
  assert.match(GDSL_PVGRAPH_WGSL,/arrayLength|config\[1\]|let n=config\[1\]/);
  assert.match(GDSL_PVGRAPH_WGSL,/op==6u\|\|op==7u/);
  assert.doesNotMatch(GDSL_PVGRAPH_WGSL,/\bu64\b/);
});

test("PVGraph GPU is fail-closed without native Lean admission, including forged flags",async()=>{
  const e=example("signal");
  const before=globalThis.navigator?.gpu;
  await assert.rejects(runPVGraphGPU(e.pvgraph,e.input),/missing native Lean admission/);
  await assert.rejects(runPVGraphGPU(e.pvgraph,e.input,{
    admission:{approved:true,admitted:true,version:"gdsl/0.2"}
  }),/missing native Lean admission/);
  assert.strictEqual(globalThis.navigator?.gpu,before);
  // No WebGPU adapter, session, pipeline or buffer can be reached here.
});

test("PVGraph GPU cannot replace its verified core operator semantics",async()=>{
  const e=example("signal");
  const custom=new Map(CORE_OPERATORS);
  await assert.rejects(runPVGraphGPU(e.pvgraph,e.input,{
    registry:custom,admission:{approved:true},
  }),/refuses arbitrary operator registries/);
  const old=CORE_OPERATORS.get("u32.map.mul");
  try{
    // The public registry is an app extension surface, not the GPU TCB.
    CORE_OPERATORS.set("u32.map.mul",{
      inputs:{},outputs:{out:"scalar<u32>"},params:{},
      execute:()=>0,
    });
    await assert.rejects(runPVGraphGPU(e.pvgraph,e.input),
      /missing native Lean admission/);
  }finally{
    CORE_OPERATORS.set("u32.map.mul",old);
  }
});
