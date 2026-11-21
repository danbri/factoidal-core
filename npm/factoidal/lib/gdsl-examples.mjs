// PVGraph examples are recipes for the Lean/Wasm builder.
// All operator and link semantics, admission and evaluation live in Lean.
import {createPVGraphWasm} from "./gdsl-wasm-builder.mjs";
const B="buffer<u32>", S="scalar<u32>";
const op=(g,name,args,params={},resultType=B,id)=>g.op(name,args,params,{resultType,id});

const presets={
  signal:{
    title:"Signal interference loom",domain:"signal",
    description:"Scale and offset waves, combine them with XOR, then scan and reduce.",
    input:{waves:[1,2,3,5,8,13,21,34,55,89,144,233]},
    author(g){
      const x=g.input("waves");
      const a=op(g,"u32.map.mul",{x},{value:257},B,"harmonics");
      const b=op(g,"u32.map.add",{x},{value:31},B,"bias");
      const mixed=op(g,"u32.zip.xor",{a,b}, {},B,"interference");
      const phase=op(g,"u32.scan.sum",{x:mixed},{},B,"phase");
      const total=op(g,"u32.reduce.sum",{x:mixed},{},S,"intensity");
      g.output("bands",mixed);
      g.output("phase",phase);
      g.output("intensity",total);
    }
  },
  font:{
    title:"Glyph pen positioning",domain:"font",
    description:"Accumulate glyph advance widths and compute line width.",
    input:{advances:[8,5,9,0,6,7,5,8,3,9]},
    author(g){
      const x=g.input("advances");
      const spaced=op(g,"u32.map.add",{x},{value:1},B,"spacing");
      const pens=op(g,"u32.scan.sum",{x:spaced},{},B,"penPositions");
      const width=op(g,"u32.reduce.sum",{x:spaced},{},S,"lineWidth");
      g.output("penPositions",pens);
      g.output("lineWidth",width);
    }
  },
  motion:{
    title:"Particle motion step",domain:"motion",
    description:"Advance positions by scaled velocities and compute a checksum.",
    input:{positions:[100,200,300,400,500,600,700,800],
      velocities:[2,4,1,8,3,0,5,7]},
    author(g){
      const positions=g.input("positions");
      const velocities=g.input("velocities");
      const delta=op(g,"u32.map.mul",{x:velocities},{value:4},B,"motionDelta");
      const next=op(g,"u32.zip.add",{a:positions,b:delta},{},B,"nextPositions");
      const total=op(g,"u32.reduce.sum",{x:next},{},S,"total");
      g.output("positionsAfterStep",next);
      g.output("positionChecksum",total);
    }
  },
  image:{
    title:"Pixel channel mask",domain:"image",
    description:"XOR packed RGBA words and calculate a checksum.",
    input:{pixels:[0xff204080,0xff607080,0xffc0d0e0,0xffffffff,0]},
    author(g){
      const x=g.input("pixels");
      const masked=op(g,"u32.map.xor",{x},{value:0x00ff00ff},B,"maskChannels");
      const total=op(g,"u32.reduce.sum",{x:masked},{},S,"checksum");
      g.output("rgbaWords",masked);
      g.output("checksum",total);
    }
  },
  basic:{
    title:"Scalar-to-buffer broadcast",domain:"basic",
    description:"Broadcast a scalar over a buffer's shape and add it.",
    input:{template:[0,1,2,3,4,5,6,7]},
    author(g){
      const template=g.input("template");
      const value=op(g,"u32.scalar.const",{}, {value:29},S,"constant");
      const band=op(g,"u32.broadcast",{value,shape:template},{},B,"broadcast");
      const result=op(g,"u32.zip.add",{a:template,b:band},{},B,"offset");
      g.output("result",result);
    }
  }
};

export function listExamples(){
  return Object.entries(presets).map(([id,p])=>({
    id,title:p.title,description:p.description,domain:p.domain
  }));
}
export async function example(id,loadEngine){
  if(!Object.hasOwn(presets,id))throw new RangeError("Unknown PVGraph example "+id);
  const preset=presets[id],g=await createPVGraphWasm(loadEngine);
  preset.author(g);
  const pvgraph=await g.build();
  return {id,title:preset.title,description:preset.description,
    domain:preset.domain,input:preset.input,pvgraph};
}
