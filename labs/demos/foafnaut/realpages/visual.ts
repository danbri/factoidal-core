// "Does the layout look right" as a number (layout_similarity): the structural similarity
// (SSIM) of Foafnaut's picture of a page against headless Chrome's, on grey levels shrunk to
// 1/16, in 8x8 windows. At that size text lines are grey bars, so the score follows where the
// blocks of the page are. Windows that are flat and alike in both pictures are left out, so a
// blank picture against a page of text scores near 0 and white space does not lift the score of
// a wrong layout. Measured on the survey of 2026-11-15: Hacker News 0.50, the Spinal Tap page
// 0.61, Wikipedia articles without their side columns 0.12 to 0.20, a blank BBC page 0.04.
// Both pictures are of the page area only: the browser's own bar is cut off Foafnaut's
// picture, and Chrome draws at the size of the page area.
// PNG decoding is here too (8-bit, non-interlaced: what run_html.ts and Chrome write).

export type Grey={width:number;height:number;data:Float32Array};

async function inflate(bytes:Uint8Array):Promise<Uint8Array>{
  const stream=new Blob([new Uint8Array(bytes)]).stream().pipeThrough(new DecompressionStream("deflate"));
  return new Uint8Array(await new Response(stream).arrayBuffer());
}

/** Decode a PNG to grey levels 0..255 (alpha composited on white). */
export async function decodePNG(png:Uint8Array):Promise<Grey>{
  const sig=[137,80,78,71,13,10,26,10];
  if(!sig.every((b,i)=>png[i]===b))throw new Error("not a PNG");
  const view=new DataView(png.buffer,png.byteOffset,png.byteLength);
  let p=8,width=0,height=0,depth=0,type=0,interlace=0,palette:Uint8Array|undefined;
  const idat:Uint8Array[]=[];
  while(p+8<=png.length){
    const len=view.getUint32(p),name=String.fromCharCode(...png.subarray(p+4,p+8)),body=png.subarray(p+8,p+8+len);
    if(name==="IHDR"){width=view.getUint32(p+8);height=view.getUint32(p+12);depth=body[8];type=body[9];interlace=body[12];}
    else if(name==="PLTE")palette=body;
    else if(name==="IDAT")idat.push(body);
    else if(name==="IEND")break;
    p+=12+len;
  }
  if(depth!==8||interlace!==0)throw new Error(`PNG depth ${depth} interlace ${interlace} not read`);
  const channels={0:1,2:3,3:1,4:2,6:4}[type as 0|2|3|4|6];
  if(!channels)throw new Error(`PNG colour type ${type} not read`);
  const all=new Uint8Array(idat.reduce((n,c)=>n+c.length,0));let o=0;for(const c of idat){all.set(c,o);o+=c.length;}
  const raw=await inflate(all);
  const stride=width*channels,bpp=channels;
  const cur=new Uint8Array(stride),prev=new Uint8Array(stride);
  const data=new Float32Array(width*height);
  for(let y=0;y<height;y++){
    const f=raw[y*(stride+1)],line=raw.subarray(y*(stride+1)+1,(y+1)*(stride+1));
    for(let i=0;i<stride;i++){
      const a=i>=bpp?cur[i-bpp]:0,b=prev[i],c=i>=bpp?prev[i-bpp]:0;let v=line[i];
      if(f===1)v+=a;else if(f===2)v+=b;else if(f===3)v+=(a+b)>>1;
      else if(f===4){const pp=a+b-c,pa=Math.abs(pp-a),pb=Math.abs(pp-b),pc=Math.abs(pp-c);v+=pa<=pb&&pa<=pc?a:pb<=pc?b:c;}
      cur[i]=v&255;
    }
    for(let x=0;x<width;x++){
      let r:number,g:number,bl:number,al=255;const i=x*channels;
      if(type===0){r=g=bl=cur[i];}
      else if(type===4){r=g=bl=cur[i];al=cur[i+1];}
      else if(type===3){const k=cur[i]*3;r=palette?.[k]??0;g=palette?.[k+1]??0;bl=palette?.[k+2]??0;}
      else {r=cur[i];g=cur[i+1];bl=cur[i+2];if(type===6)al=cur[i+3];}
      const lum=0.299*r+0.587*g+0.114*bl;
      data[y*width+x]=(lum*al+255*(255-al))/255;
    }
    prev.set(cur);
  }
  return {width,height,data};
}

/** Rows [top, top+height) of a picture. */
export function crop(g:Grey,top:number,height:number,width=g.width):Grey{
  const h=Math.max(0,Math.min(height,g.height-top)),w=Math.min(width,g.width),data=new Float32Array(w*h);
  for(let y=0;y<h;y++)for(let x=0;x<w;x++)data[y*w+x]=g.data[(y+top)*g.width+x];
  return {width:w,height:h,data};
}

/** Box-filtered to 1/k size: text lines become grey bars, so the score follows where the
blocks of a page are (columns, headings, images), not single glyphs. */
export function shrink(g:Grey,k:number):Grey{
  const w=Math.floor(g.width/k),h=Math.floor(g.height/k),data=new Float32Array(w*h);
  for(let y=0;y<h;y++)for(let x=0;x<w;x++){
    let sum=0;for(let j=0;j<k;j++)for(let i=0;i<k;i++)sum+=g.data[(y*k+j)*g.width+x*k+i];
    data[y*w+x]=sum/(k*k);
  }
  return {width:w,height:h,data};
}

const FLAT=4;
/** Mean SSIM over the 8x8 windows (no overlap) of the common area of two grey pictures shrunk
to 1/k (default 16: a window covers 128 by 128 pixels), leaving out windows that are flat and
alike in both. */
export function ssim(a0:Grey,b0:Grey,k=16):number{
  const a=shrink(a0,k),b=shrink(b0,k),w=Math.min(a.width,b.width),h=Math.min(a.height,b.height);
  const C1=(0.01*255)**2,C2=(0.03*255)**2,N=8;
  let sum=0,n=0;
  for(let y=0;y+N<=h;y+=N)for(let x=0;x+N<=w;x+=N){
    let ma=0,mb=0;
    for(let j=0;j<N;j++)for(let i=0;i<N;i++){ma+=a.data[(y+j)*a.width+x+i];mb+=b.data[(y+j)*b.width+x+i];}
    ma/=N*N;mb/=N*N;
    let va=0,vb=0,cov=0;
    for(let j=0;j<N;j++)for(let i=0;i<N;i++){
      const da=a.data[(y+j)*a.width+x+i]-ma,db=b.data[(y+j)*b.width+x+i]-mb;va+=da*da;vb+=db*db;cov+=da*db;
    }
    va/=N*N-1;vb/=N*N-1;cov/=N*N-1;
    // Windows flat in both pictures (margins, empty background) say nothing about layout: a
    // blank page against a page of text would otherwise score by its white space.
    if(va<FLAT&&vb<FLAT&&Math.abs(ma-mb)<16)continue;
    sum+=((2*ma*mb+C1)*(2*cov+C2))/((ma*ma+mb*mb+C1)*(va+vb+C2));n++;
  }
  return n?Math.round(1000*sum/n)/1000:0;
}

/** SSIM of Foafnaut's picture (its bar of `top` rows cut off) against Chrome's of the page area. */
export async function pageSimilarity(foafnautPNG:Uint8Array,chromePNG:Uint8Array,top:number):Promise<number>{
  const f=await decodePNG(foafnautPNG),c=await decodePNG(chromePNG);
  return ssim(crop(f,top,f.height-top),c);
}
