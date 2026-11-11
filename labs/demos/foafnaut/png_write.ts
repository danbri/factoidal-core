// A PNG file of RGBA pixels (8 bits, no filter, zlib by CompressionStream), for pictures that
// tests and tools take of what a host drew (run_html.ts --shot, shader_gallery_bench.ts --png).
const table=Array.from({length:256},(_,n)=>{let c=n;for(let k=0;k<8;k++)c=c&1?0xedb88320^(c>>>1):c>>>1;return c>>>0;});
const crc=(b:Uint8Array)=>{let c=0xffffffff;for(const x of b)c=table[(c^x)&255]^(c>>>8);return (c^0xffffffff)>>>0;};
function chunk(type:string,data:Uint8Array):Uint8Array{
  const out=new Uint8Array(12+data.length),view=new DataView(out.buffer);
  view.setUint32(0,data.length);out.set(new TextEncoder().encode(type),4);out.set(data,8);
  view.setUint32(8+data.length,crc(out.subarray(4,8+data.length)));
  return out;
}
export async function pngOf(width:number,height:number,rgba:Uint8Array):Promise<Uint8Array>{
  const raw=new Uint8Array((width*4+1)*height);
  for(let y=0;y<height;y++)raw.set(rgba.subarray(y*width*4,(y+1)*width*4),y*(width*4+1)+1);
  const deflated=new Uint8Array(await new Response(new Blob([raw]).stream().pipeThrough(new CompressionStream("deflate"))).arrayBuffer());
  const head=new Uint8Array(13),view=new DataView(head.buffer);
  view.setUint32(0,width);view.setUint32(4,height);head.set([8,6,0,0,0],8);
  const parts=[new Uint8Array([137,80,78,71,13,10,26,10]),chunk("IHDR",head),chunk("IDAT",deflated),chunk("IEND",new Uint8Array())];
  const out=new Uint8Array(parts.reduce((n,p)=>n+p.length,0));
  let at=0;for(const p of parts){out.set(p,at);at+=p.length;}
  return out;
}
/** The pixels of a texture with COPY_SRC, as RGBA rows (BGRA swapped). */
export async function texturePixels(device:GPUDevice,texture:GPUTexture):Promise<Uint8Array>{
  const w=texture.width,h=texture.height,bpr=Math.ceil(w*4/256)*256;
  const buffer=device.createBuffer({size:bpr*h,usage:GPUBufferUsage.COPY_DST|GPUBufferUsage.MAP_READ});
  const encoder=device.createCommandEncoder();
  encoder.copyTextureToBuffer({texture},{buffer,bytesPerRow:bpr},[w,h]);
  device.queue.submit([encoder.finish()]);
  await buffer.mapAsync(GPUMapMode.READ);
  const src=new Uint8Array(buffer.getMappedRange()),rgba=new Uint8Array(w*h*4),bgra=texture.format.startsWith("bgra");
  for(let y=0;y<h;y++){
    const row=src.subarray(y*bpr,y*bpr+w*4);rgba.set(row,y*w*4);
    if(bgra)for(let x=0;x<w;x++){const i=y*w*4+x*4;const b=rgba[i];rgba[i]=rgba[i+2];rgba[i+2]=b;}
  }
  buffer.unmap();buffer.destroy();
  return rgba;
}
