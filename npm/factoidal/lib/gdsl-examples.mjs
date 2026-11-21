// All examples use the same GDSL 0.2 graph constructor, typed ports,
// graph document and S-expression grammar. No application-owned parser.
import {PVGraph,toPVSexpr} from "./gdsl-graph.mjs";

function createSignalLoom(){
  const g=PVGraph();
  const waves=g.input("waves");
  const harmonics=g.op("u32.map.mul",{x:waves},{value:257},{id:"harmonics"});
  const bias=g.op("u32.map.add",{x:waves},{value:31},{id:"bias"});
  const mixed=g.op("u32.zip.xor",{a:harmonics,b:bias},{},{id:"interference"});
  const scan=g.op("u32.scan.sum",{x:mixed},{},{id:"phase"});
  const total=g.op("u32.reduce.sum",{x:mixed},{},{id:"intensity"});
  g.output("bands",mixed);
  g.output("phase",scan);
  g.output("intensity",total,"scalar<u32>");
  return {title:"Signal interference loom",domain:"signal",
    description:"Fan out one signal into two paths, multiply and bias, braid by XOR, then form prefix phases and total energy.",
    input:{waves:[1,2,3,5,8,13,21,34,55,89,144,233]},
    pvgraph:g.build()};
}
function createGlyphLayout(){
  const g=PVGraph();
  const advances=g.input("advances");
  const adjusted=g.op("u32.map.add",{x:advances},{value:1},{id:"spacing"});
  const x=g.op("u32.scan.sum",{x:adjusted},{},{id:"penPositions"});
  const width=g.op("u32.reduce.sum",{x:adjusted},{},{id:"lineWidth"});
  g.output("penPositions",x);
  g.output("lineWidth",width,"scalar<u32>");
  return {title:"Glyph pen positioning",domain:"font",
    description:"Turn glyph advance widths into cumulative pen positions and a line width. Real typographic shaping remains a separate domain operator.",
    input:{advances:[8,5,9,0,6,7,5,8,3,9]},
    pvgraph:g.build()};
}
function createParticleMotion(){
  const g=PVGraph();
  const positions=g.input("positions");
  const velocities=g.input("velocities");
  const delta=g.op("u32.map.mul",{x:velocities},{value:4},{id:"motionDelta"});
  const next=g.op("u32.zip.add",{a:positions,b:delta},{},{id:"nextPositions"});
  const aggregate=g.op("u32.reduce.sum",{x:next},{},{id:"total"});
  g.output("positionsAfterStep",next);
  g.output("positionChecksum",aggregate,"scalar<u32>");
  return {title:"Particle motion step",domain:"motion",
    description:"Scale per-particle velocities by a time step, add them elementwise to positions, and reduce for inspection.",
    input:{positions:[100,200,300,400,500,600,700,800],
      velocities:[2,4,1,8,3,0,5,7]},
    pvgraph:g.build()};
}
function createPixelMasks(){
  const g=PVGraph();
  const pixels=g.input("pixels");
  const altered=g.op("u32.map.xor",{x:pixels},{value:0x00ff00ff},{id:"maskChannels"});
  const total=g.op("u32.reduce.sum",{x:altered},{},{id:"checksum"});
  g.output("rgbaWords",altered);
  g.output("checksum",total,"scalar<u32>");
  return {title:"Pixel channel mask",domain:"image",
    description:"Transform packed 32-bit pixel words and compute a checksum. Actual colour management and rendering belong to separate operators.",
    input:{pixels:[0xff204080,0xff607080,0xffc0d0e0,0xffffffff,0x00000000]},
    pvgraph:g.build()};
}
function createConstantShape(){
  const g=PVGraph();
  const template=g.input("template");
  const constant=g.op("u32.scalar.const",{},{value:29},{id:"constant"});
  const band=g.op("u32.broadcast",{value:constant,shape:template},{},{id:"broadcast"});
  const added=g.op("u32.zip.add",{a:template,b:band},{},{id:"offset"});
  g.output("result",added);
  return {title:"Scalar-to-buffer broadcast",domain:"basic",
    description:"Create a typed scalar, broadcast it over the input shape and add through an explicit buffer link.",
    input:{template:[0,1,2,3,4,5,6,7]},
    pvgraph:g.build()};
}
const factories={
  signal:createSignalLoom,
  font:createGlyphLayout,
  motion:createParticleMotion,
  image:createPixelMasks,
  basic:createConstantShape,
};
export function listExamples(){
  return Object.entries(factories).map(([id,fn])=>{
    const {title,description,domain}=fn();
    return {id,title,description,domain};
  });
}
export function example(id){
  if(!Object.prototype.hasOwnProperty.call(factories,id))
    throw new RangeError("Unknown GDSL example "+String(id));
  const x=factories[id]();
  return {...x,id,sexpr:toPVSexpr(x.pvgraph)};
}
