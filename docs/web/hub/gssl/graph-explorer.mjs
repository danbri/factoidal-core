// One GDSL graph under every domain example: editor, typed link renderer,
// JS builder view, CPU reference, and actual WebGPU observed execution.
// Text input is parsed and never run as host JavaScript. GPU results are not
// certified by Lean or by equality of a handful of test cases.
import {
  example,listExamples,fromPVSexpr,toPVSexpr,runPVGraphCPU,
  CORE_OPERATORS,
} from "../../../npm/factoidal/gdsl.mjs";

const $=id=>document.getElementById(id);
const status=$("gdsl-status"),source=$("gdsl-sexpr"),
  bindings=$("gdsl-bindings"),options=$("gdsl-example");
let active=false;
const eq=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const ns="http://www.w3.org/2000/svg";
function svg(tag,attributes={},text=null){
  const el=document.createElementNS(ns,tag);
  for(const [k,v] of Object.entries(attributes))el.setAttribute(k,String(v));
  if(text!==null)el.textContent=String(text);
  return el;
}
function setStatus(message,kind="neutral"){
  status.textContent=message;status.dataset.kind=kind;
}
function busy(v){
  active=v;
  for(const id of ["gdsl-example","gdsl-check","gdsl-cpu","gdsl-gpu","gdsl-release"]){
    const el=$(id);
    if(id==="gdsl-release")el.disabled=true;
    else el.disabled=v;
  }
}
function inputMap(doc,id){
  const map=new Map();
  for(const l of doc.links)if(l.to.node===id)map.set(l.to.port,l.from.node);
  return map;
}
function builderSource(doc){
  const rows=["import { graph } from '@factoidal/core/gdsl';","const g = PVGraph();"];
  const refs=new Map();
  for(const [index,node] of doc.nodes.entries()){
    const variable="n"+index;
    const incoming=inputMap(doc,node.id);
    let line;
    if(node.op==="core.input")
      line="g.input("+JSON.stringify(node.params.name)+","+
        JSON.stringify(node.params.type)+",{id:"+
        JSON.stringify(node.id)+"})";
    else if(node.op==="core.output")
      line="g.output("+JSON.stringify(node.params.name)+","+
        refs.get(incoming.get("in"))+","+
        JSON.stringify(node.params.type)+",{id:"+
        JSON.stringify(node.id)+"})";
    else{
      const s=CORE_OPERATORS.get(node.op);
      const args=Object.keys(s.inputs).map(port=>
        JSON.stringify(port)+":"+refs.get(incoming.get(port))).join(",");
      line="g.op("+JSON.stringify(node.op)+",{"+args+"},"+
        JSON.stringify(node.params)+",{id:"+JSON.stringify(node.id)+"})";
    }
    rows.push("const "+variable+" = "+line+";");
    refs.set(node.id,variable);
  }
  rows.push("const document = g.build();");
  return rows.join("\n");
}
function graphSVG(doc){
  const root=$("gdsl-diagram");
  root.replaceChildren();
  const depth=new Map(),columns=new Map();
  for(const node of doc.nodes){
    const previous=doc.links.filter(l=>l.to.node===node.id)
      .map(l=>(depth.get(l.from.node)??0)+1);
    const d=Math.max(0,...previous);
    depth.set(node.id,d);
    if(!columns.has(d))columns.set(d,[]);
    columns.get(d).push(node.id);
  }
  const locations=new Map();
  for(const [d,ids] of columns){
    ids.forEach((id,i)=>locations.set(id,{x:20+185*d,y:24+82*i}));
  }
  const width=Math.max(400,...[...locations.values()].map(p=>p.x+175));
  const height=Math.max(145,...[...locations.values()].map(p=>p.y+72));
  root.setAttribute("viewBox","0 0 "+width+" "+height);
  root.style.minWidth=width+"px";
  root.style.height=height+"px";
  root.append(svg("title",{},"GDSL operator nodes connected by typed dataflow links"));
  const defs=svg("defs");
  for(const [id,color] of [["buffer","#7ad7ca"],["scalar","#d7a6f3"]]){
    const marker=svg("marker",{id:"gdsl-arrow-"+id,
      viewBox:"0 0 10 10",refX:9,refY:5,markerWidth:5,markerHeight:5,
      orient:"auto-start-reverse"});
    marker.append(svg("path",{d:"M0 0L10 5L0 10Z",fill:color}));
    defs.append(marker);
  }
  root.append(defs);
  for(const l of doc.links){
    const a=locations.get(l.from.node),b=locations.get(l.to.node);
    const x=a.x+165,y=a.y+29,tx=b.x,ty=b.y+29;
    const bend=(x+tx)/2;
    const p=svg("path",{d:"M"+x+" "+y+" C"+bend+" "+y+" "+bend+" "+ty+" "+tx+" "+ty,
      fill:"none",stroke:l.kind==="scalar"?"#d7a6f3":"#7ad7ca",
      "stroke-width":2,"marker-end":"url(#gdsl-arrow-"+l.kind+")"});
    p.append(svg("title",{},
      l.from.node+"."+l.from.port+" → "+l.to.node+"."+l.to.port+
      " : "+l.kind+"<"+l.type+">"));
    root.append(p);
  }
  for(const n of doc.nodes){
    const p=locations.get(n.id);
    const g=svg("g");
    const origin=n.op==="core.input",terminal=n.op==="core.output";
    const color=origin?"#38566f":terminal?"#416b60":"#293a54";
    g.append(svg("rect",{x:p.x,y:p.y,width:165,height:59,rx:9,
      fill:color,stroke:terminal?"#92dfc6":"#7198b1","stroke-width":1.2}));
    const title=n.id.length>21?n.id.slice(0,18)+"…":n.id;
    g.append(svg("text",{x:p.x+9,y:p.y+20,fill:"#f0f7ff",
      "font-size":13,"font-weight":700},title));
    const op=n.op.length>25?n.op.slice(0,22)+"…":n.op;
    g.append(svg("text",{x:p.x+9,y:p.y+41,fill:"#bfd1e7",
      "font-size":10},op));
    const tooltip=svg("title",{},n.id+" : "+n.op+
      " "+JSON.stringify(n.params));
    g.append(tooltip);
    root.append(g);
  }
  return {nodes:doc.nodes.length,links:doc.links.length};
}
function showStats(run){
  if(!run){
    $("gdsl-resources").textContent="No GPU session allocated.";
    return;
  }
  const s=run.resident;
  $("gdsl-resources").textContent=JSON.stringify({
    status:run.status,computePasses:run.gpuDispatches,
    uploads:s.uploads,reusedUploads:s.reuses,compiledPipelines:s.createdPipelines,
    commandSubmissions:s.submissions,readbacks:s.readbacks,
    retainedBuffers:s.resourceCount,trackedBytes:s.usedBytes,
  },null,2);
  $("gdsl-trace").textContent=run.trace.map(t=>
    t.id.padEnd(20)+" "+t.op.padEnd(23)+" "+t.status+" ("+t.length+" words)").join("\n");
}
function documentAndBindings(){
  if(source.value.length>65536||bindings.value.length>65536)
    throw new RangeError("GDSL editor input is bounded.");
  const doc=fromPVSexpr(source.value);
  let supplied;
  try{supplied=JSON.parse(bindings.value);}
  catch{throw new SyntaxError("Input bindings must be valid JSON.");}
  if(!supplied||Array.isArray(supplied)||typeof supplied!=="object")
    throw new TypeError("GDSL inputs must be a JSON object.");
  return {doc,supplied};
}
function validate(){
  const {doc}=documentAndBindings();
  $("gdsl-js").textContent=builderSource(doc);
  graphSVG(doc);
  setStatus("Admitted canonical GDSL 0.2 graph: "+doc.nodes.length+
    " operator nodes, "+doc.links.length+" typed links.","success");
  return doc;
}
function preset(id){
  const e=example(id);
  source.value=e.sexpr;
  bindings.value=JSON.stringify(e.input,null,2);
  $("gdsl-description").textContent=e.description;
  $("gdsl-cpu-output").textContent="Not executed";
  $("gdsl-gpu-output").textContent="Not executed";
  $("gdsl-agreement").textContent="No comparison yet.";
  $("gdsl-agreement").dataset.match="pending";
  showStats();
  validate();
}
function runCPUOnly(){
  if(active)return;
  try{
    const {doc,supplied}=documentAndBindings();
    validate();
    const run=runPVGraphCPU(doc,supplied);
    $("gdsl-cpu-output").textContent=JSON.stringify(run.outputs,null,2);
    $("gdsl-gpu-output").textContent="Not executed for this graph.";
    $("gdsl-agreement").textContent="CPU reference only (no device execution).";
    $("gdsl-agreement").dataset.match="pending";
    $("gdsl-trace").textContent=run.trace.map(t=>
      t.id+" / "+t.op+" → "+JSON.stringify(t.value)).join("\n");
    setStatus("CPU graph completed with "+doc.nodes.length+" nodes.","success");
  }catch(e){setStatus(e?.message||String(e),"error");}
}
function describeNativeGate(){
  if(active)return;
  try{
    const {doc,supplied}=documentAndBindings();
    validate();
    const cpu=runPVGraphCPU(doc,supplied);
    $("gdsl-cpu-output").textContent=JSON.stringify(cpu.outputs,null,2);
    $("gdsl-gpu-output").textContent=
      "Not executed. PVGraph WebGPU execution requires a native Lean 4 toolkit"+
      " and an input-bound Lean admission. Static GitHub Pages cannot issue one.";
    $("gdsl-agreement").dataset.match="pending";
    $("gdsl-agreement").textContent=
      "Unverified JavaScript CPU output only; no PVGraph GPU submission.";
    setStatus("Native Lean toolkit required: use admitPVGraphWithLean(pvgraph, inputs)"+
      " before runPVGraphGPU(pvgraph, inputs, {admission}).","neutral");
  }catch(e){setStatus(e?.message||String(e),"error");}
}
export function mountPVGraph(){
  const presets=listExamples();
  if(!presets.length)throw Error("GDSL has no registered graph examples.");
  options.addEventListener("change",()=>preset(options.value));
  $("gdsl-check").addEventListener("click",()=>{
    if(active)return;
    try{validate();}catch(e){setStatus(e?.message||String(e),"error");}
  });
  $("gdsl-cpu").addEventListener("click",runCPUOnly);
  $("gdsl-gpu").addEventListener("click",describeNativeGate);
  preset("signal");
}
