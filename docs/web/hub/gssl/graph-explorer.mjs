// PVGraph workbench. JS only renders UI and marshals commands.
// Lean/Wasm owns construction, admission, types and evaluation.
import {createPVGraphWasm,runPVGraph,example,listExamples}
  from "../../../npm/factoidal/gdsl.mjs";
import {loadEngine} from "../../../npm/factoidal/browser.js";

const $=id=>document.getElementById(id);
const status=$("gdsl-status"),source=$("gdsl-json"),bindings=$("gdsl-bindings"),
  options=$("gdsl-example");
const ns="http://www.w3.org/2000/svg";
let bridgePromise=null;
let active=false;
const bridge=()=>bridgePromise??=(createPVGraphWasm(loadEngine));
function svg(tag,attributes={},text=null){
  const el=document.createElementNS(ns,tag);
  for(const [k,v] of Object.entries(attributes))el.setAttribute(k,String(v));
  if(text!==null)el.textContent=String(text);
  return el;
}
function setStatus(msg,kind="neutral"){
  status.textContent=msg;
  status.dataset.kind=kind;
}
function busy(v){
  active=v;
  for(const id of ["gdsl-example","gdsl-check","gdsl-cpu","gdsl-gpu"]){
    const el=$(id);
    if(el)el.disabled=v;
  }
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

function inputDocument(){
  if(source.value.length>65536||bindings.value.length>65536)
    throw new RangeError("PVGraph input exceeds editor limit");
  const doc=JSON.parse(source.value);
  const supplied=JSON.parse(bindings.value);
  if(!supplied||Array.isArray(supplied)||typeof supplied!=="object")
    throw new TypeError("Named inputs must be a JSON object");
  return {doc,supplied};
}
async function validate(){
  const {doc}=inputDocument();
  const accepted=await (await bridge()).admit(doc);
  graphSVG(accepted);
  $("gdsl-js").textContent=accepted.nodes
    .map(n=>n.id+" : "+n.op+" "+JSON.stringify(n.params)).join("\n");
  setStatus("Lean/Wasm admitted "+accepted.nodes.length+
    " operator nodes and "+accepted.links.length+" typed links.","success");
  return accepted;
}
async function preset(id){
  const e=await example(id,loadEngine);
  source.value=JSON.stringify(e.pvgraph,null,2);
  bindings.value=JSON.stringify(e.input,null,2);
  $("gdsl-description").textContent=e.description;
  $("gdsl-cpu-output").textContent="Not executed";
  $("gdsl-gpu-output").textContent="Not executed";
  $("gdsl-agreement").textContent="No GPU comparison";
  $("gdsl-trace").textContent="Reference execution is performed by Lean/Wasm.";
  $("gdsl-resources").textContent="No PVGraph GPU session";
  await validate();
}
async function runCPU(){
  const doc=await validate();
  const {supplied}=inputDocument();
  const outputs=await (await bridge()).evaluate(doc,supplied);
  $("gdsl-cpu-output").textContent=JSON.stringify(outputs,null,2);
  $("gdsl-gpu-output").textContent="Not executed";
  $("gdsl-agreement").textContent="Lean/Wasm reference evaluation only.";
}
async function runGPU(){
  const doc=await validate();
  const {supplied}=inputDocument();
  const observed=await runPVGraph({
    pvgraph:doc,bindings:supplied,loadEngine,requireGPU:true,minWords:0
  });
  const expected=await (await bridge()).evaluate(doc,supplied);
  const actual=observed.outputs;
  const agreement=JSON.stringify(expected)===JSON.stringify(actual);
  $("gdsl-cpu-output").textContent=JSON.stringify(expected,null,2);
  $("gdsl-gpu-output").textContent=JSON.stringify({
    status:observed.status,outputs:actual,
    gpuDispatches:observed.dispatches,timing:observed.timing
  },null,2);
  $("gdsl-agreement").textContent=agreement
    ?"Complete GPU readback equals Lean/Wasm reference for these inputs."
    :"GPU and Lean/Wasm disagree; no correct output claimed.";
  $("gdsl-agreement").dataset.match=agreement?"yes":"no";
  $("gdsl-resources").textContent=JSON.stringify(observed.device,null,2);
  setStatus(agreement?"WebGPU observed; source-level proof is separate.":
    "GPU output differs from Lean/Wasm",agreement?"success":"error");
  if(!agreement)throw Error("PVGraph GPU/Lean mismatch");
}
async function action(fn){
  if(active)return;
  busy(true);
  try{await fn();}catch(e){setStatus(e?.message||String(e),"error");}
  finally{busy(false);}
}
export function mountPVGraph(){
  if(!listExamples().length)throw Error("No PVGraph examples");
  options.addEventListener("change",()=>action(()=>preset(options.value)));
  $("gdsl-check").addEventListener("click",()=>action(validate));
  $("gdsl-cpu").addEventListener("click",()=>action(runCPU));
  $("gdsl-gpu").addEventListener("click",()=>action(runGPU));
  action(()=>preset("signal"));
}
