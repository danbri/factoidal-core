// Byte transport for a finished frame. Typed arrays remain binary sections; the
// envelope identifies the engine request that produced the frame. No page rules.
import type {HTMLLayers} from "./native_html_engine.ts";
export type PostedFrame={request:number;layers:HTMLLayers;workerMs:number};
const encoder=new TextEncoder(),decoder=new TextDecoder();
export const FRAME_SLOT_BYTES=128*1024*1024;
export function encodeFrame(frame:PostedFrame):Uint8Array {
  const parts:Uint8Array[]=[];
  const head=encoder.encode(JSON.stringify(frame,(_key,value)=>{
    if(value instanceof Float32Array||value instanceof Uint32Array||value instanceof Uint8Array){
      const section=parts.length;parts.push(new Uint8Array(value.buffer,value.byteOffset,value.byteLength));
      return {$section:section,type:value.constructor.name};
    }
    return value;
  }));
  const lengths=[head.length,...parts.map(p=>p.length)];
  const total=4+lengths.length*4+lengths.reduce((n,l)=>n+Math.ceil(l/4)*4,0);
  if(total>FRAME_SLOT_BYTES)throw new Error("presenter frame exceeds the 128 MiB transport slot");
  const result=new Uint8Array(total),view=new DataView(result.buffer);
  view.setUint32(0,lengths.length,true);
  let at=4+lengths.length*4;
  [head,...parts].forEach((p,i)=>{view.setUint32(4+i*4,p.length,true);result.set(p,at);at+=Math.ceil(p.length/4)*4;});
  return result;
}
export function decodeFrame(bytes:Uint8Array):PostedFrame {
  const view=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  if(bytes.length<8)throw new Error("short presenter frame");
  const count=view.getUint32(0,true);
  if(!count||count>32||4+count*4>bytes.length)throw new Error("invalid presenter section count");
  const parts:Uint8Array[]=[];
  let at=4+count*4;
  for(let i=0;i<count;i++){
    const length=view.getUint32(4+i*4,true);
    if(at+length>bytes.length)throw new Error("short presenter section");
    parts.push(bytes.subarray(at,at+length));at+=Math.ceil(length/4)*4;
  }
  return JSON.parse(decoder.decode(parts[0]),(_key,value)=>{
    if(value&&typeof value==="object"&&Number.isInteger(value.$section)){
      const part=parts[value.$section+1];if(!part)throw new Error("missing presenter section");
      switch(value.type){
        case "Uint8Array":return part;
        case "Float32Array":return new Float32Array(part.buffer,part.byteOffset,part.byteLength/4);
        case "Uint32Array":return new Uint32Array(part.buffer,part.byteOffset,part.byteLength/4);
        default:throw new Error("invalid presenter section type");
      }
    }
    return value;
  });
}
