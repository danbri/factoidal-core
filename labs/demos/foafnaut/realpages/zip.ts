// A small ZIP reader and writer for the page snapshots (snapshot.ts writes, replay.ts reads):
// deflate (raw) or stored entries, no ZIP64, a fixed date (1980-01-01) so that the same files
// give the same bytes.

const CRC=new Uint32Array(256).map((_,n)=>{let c=n;for(let k=0;k<8;k++)c=c&1?0xedb88320^(c>>>1):c>>>1;return c>>>0;});
export function crc32(b:Uint8Array):number{let c=0xffffffff;for(let i=0;i<b.length;i++)c=CRC[(c^b[i])&255]^(c>>>8);return (c^0xffffffff)>>>0;}

async function through(b:Uint8Array,t:TransformStream<Uint8Array,Uint8Array>):Promise<Uint8Array>{
  return new Uint8Array(await new Response(new Blob([new Uint8Array(b)]).stream().pipeThrough(t)).arrayBuffer());
}
const deflate=(b:Uint8Array)=>through(b,new CompressionStream("deflate-raw") as unknown as TransformStream<Uint8Array,Uint8Array>);
const inflate=(b:Uint8Array)=>through(b,new DecompressionStream("deflate-raw") as unknown as TransformStream<Uint8Array,Uint8Array>);

export async function writeZip(files:{name:string;data:Uint8Array}[]):Promise<Uint8Array>{
  const parts:Uint8Array[]=[],central:Uint8Array[]=[];let offset=0;
  const enc=new TextEncoder();
  for(const f of files){
    const name=enc.encode(f.name),crc=crc32(f.data),packed=await deflate(f.data);
    const store=packed.length>=f.data.length,body=store?f.data:packed,method=store?0:8;
    const local=new Uint8Array(30+name.length),lv=new DataView(local.buffer);
    lv.setUint32(0,0x04034b50,true);lv.setUint16(4,20,true);lv.setUint16(6,0x0800,true);lv.setUint16(8,method,true);
    lv.setUint16(10,0,true);lv.setUint16(12,0x21,true);lv.setUint32(14,crc,true);lv.setUint32(18,body.length,true);
    lv.setUint32(22,f.data.length,true);lv.setUint16(26,name.length,true);local.set(name,30);
    const cen=new Uint8Array(46+name.length),cv=new DataView(cen.buffer);
    cv.setUint32(0,0x02014b50,true);cv.setUint16(4,20,true);cv.setUint16(6,20,true);cv.setUint16(8,0x0800,true);cv.setUint16(10,method,true);
    cv.setUint16(12,0,true);cv.setUint16(14,0x21,true);cv.setUint32(16,crc,true);cv.setUint32(20,body.length,true);cv.setUint32(24,f.data.length,true);
    cv.setUint16(28,name.length,true);cv.setUint32(42,offset,true);cen.set(name,46);
    parts.push(local,body);central.push(cen);offset+=local.length+body.length;
  }
  const size=central.reduce((n,c)=>n+c.length,0),end=new Uint8Array(22),ev=new DataView(end.buffer);
  ev.setUint32(0,0x06054b50,true);ev.setUint16(8,files.length,true);ev.setUint16(10,files.length,true);ev.setUint32(12,size,true);ev.setUint32(16,offset,true);
  const all=[...parts,...central,end],out=new Uint8Array(all.reduce((n,p)=>n+p.length,0));let o=0;for(const p of all){out.set(p,o);o+=p.length;}
  return out;
}

export async function readZip(zip:Uint8Array):Promise<Map<string,Uint8Array>>{
  const v=new DataView(zip.buffer,zip.byteOffset,zip.byteLength);
  let e=zip.length-22;while(e>=0&&v.getUint32(e,true)!==0x06054b50)e--;
  if(e<0)throw new Error("not a ZIP file");
  const count=v.getUint16(e+10,true);let p=v.getUint32(e+16,true);
  const out=new Map<string,Uint8Array>(),dec=new TextDecoder();
  for(let i=0;i<count;i++){
    if(v.getUint32(p,true)!==0x02014b50)throw new Error("bad ZIP directory");
    const method=v.getUint16(p+10,true),crc=v.getUint32(p+16,true),csize=v.getUint32(p+20,true),nlen=v.getUint16(p+28,true),
      xlen=v.getUint16(p+30,true),clen=v.getUint16(p+32,true),at=v.getUint32(p+42,true);
    const name=dec.decode(zip.subarray(p+46,p+46+nlen));
    const start=at+30+v.getUint16(at+26,true)+v.getUint16(at+28,true),raw=zip.subarray(start,start+csize);
    const data=method===0?raw.slice():method===8?await inflate(raw):(()=>{throw new Error(`ZIP method ${method}`);})();
    if(crc32(data)!==crc)throw new Error(`ZIP entry ${name}: CRC mismatch`);
    out.set(name,data);p+=46+nlen+xlen+clen;
  }
  return out;
}
