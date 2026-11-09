// Colour emoji pixels (issue 1276): the engine's Lean COLR renderer (ColrRaster, through
// `web-render-native FONT PX 0 --colour-glyph TEXT OUT`) against reference PNGs drawn by an
// independent renderer, blackrenderer with Skia (emoji_reference.py writes them, as Base64,
// with the box of each glyph, to fixtures/emoji-reference/manifest.json). Each glyph must have the same box, and
// pixels close to the reference: anti-aliasing differs at edges (Skia's coverage against
// 16 sample rows a pixel), so the check bounds the mean difference and the share of pixels
// that differ by more than 32 in a channel (premultiplied by alpha).
// deno test --no-check --no-config --allow-read --allow-run --allow-write labs/demos/foafnaut/emoji_pixels_test.ts
import {inflateSync} from "node:zlib";

const lab=new URL("./",import.meta.url);
const fonts=new URL("../../../third_party/fonts/",import.meta.url);
const references=new URL("fixtures/emoji-reference/",lab);
const native=new URL(".build/web-render/web-render-native",lab).pathname;
const noNative=(()=>{try{Deno.statSync(native);return false;}catch{return true;}})();
function assert(ok:boolean,message:string){if(!ok)throw new Error(message);}

type Image={width:number;height:number;rgba:Uint8Array};
/** An 8-bit RGBA PNG (colour type 6, no interlace), with the five row filters. */
export function decodePNG(bytes:Uint8Array):Image {
  const view=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  let at=8,width=0,height=0;const idat:Uint8Array[]=[];
  while(at<bytes.length){
    const length=view.getUint32(at),type=new TextDecoder().decode(bytes.subarray(at+4,at+8));
    const body=bytes.subarray(at+8,at+8+length);
    if(type==="IHDR"){
      width=view.getUint32(at+8);height=view.getUint32(at+12);
      assert(body[8]===8&&body[9]===6&&body[12]===0,"PNG must be 8-bit RGBA, not interlaced");
    }else if(type==="IDAT")idat.push(body);
    at+=12+length;
  }
  const joined=new Uint8Array(idat.reduce((n,part)=>n+part.length,0));
  idat.reduce((at,part)=>{joined.set(part,at);return at+part.length;},0);
  const raw=new Uint8Array(inflateSync(joined)),stride=width*4,rgba=new Uint8Array(height*stride);
  for(let y=0;y<height;y++){
    const filter=raw[y*(stride+1)],row=raw.subarray(y*(stride+1)+1,(y+1)*(stride+1));
    for(let x=0;x<stride;x++){
      const a=x>=4?rgba[y*stride+x-4]:0,b=y>0?rgba[(y-1)*stride+x]:0,c=x>=4&&y>0?rgba[(y-1)*stride+x-4]:0;
      const p=a+b-c,pa=Math.abs(p-a),pb=Math.abs(p-b),pc=Math.abs(p-c);
      const predict=[0,a,b,(a+b)>>1,pa<=pb&&pa<=pc?a:pb<=pc?b:c][filter];
      rgba[y*stride+x]=(row[x]+predict)&255;
    }
  }
  return {width,height,rgba};
}

/** Mean of the largest channel difference of each pixel (colour premultiplied by alpha),
and the share of pixels where it is over 32. */
function difference(a:Image,b:Image){
  let total=0,big=0;
  for(let i=0;i<a.width*a.height;i++){
    let d=Math.abs(a.rgba[4*i+3]-b.rgba[4*i+3]);
    for(let k=0;k<3;k++)d=Math.max(d,Math.abs(a.rgba[4*i+k]*a.rgba[4*i+3]-b.rgba[4*i+k]*b.rgba[4*i+3])/255);
    total+=d;if(d>32)big++;
  }
  return {mean:total/(a.width*a.height),big:big/(a.width*a.height)};
}

type Case={name:string;font:string;text:string;px:number;width:number;height:number;left:number;top:number;png:string};
Deno.test({name:"colour emoji drawn by Lean match an independent COLR renderer (blackrenderer, Skia)",ignore:noNative,fn:async()=>{
  const cases:Case[]=JSON.parse(await Deno.readTextFile(new URL("manifest.json",references)));
  const dir=await Deno.makeTempDir({prefix:"emoji-pixels-"});
  try{
    for(const c of cases){
      const out=`${dir}/${c.name}`;
      const run=new Deno.Command(native,{args:[new URL(c.font,fonts).pathname,String(c.px),"0","--colour-glyph",c.text,out],stdout:"piped",stderr:"piped"}).outputSync();
      assert(run.success,`${c.name}: ${new TextDecoder().decode(run.stderr)}`);
      const answer=JSON.parse(new TextDecoder().decode(run.stdout));
      assert(answer.glyphs.length===1,`${c.name}: ${answer.glyphs.length} colour glyphs`);
      const g=answer.glyphs[0];
      assert(g.width===c.width&&g.height===c.height&&g.left===c.left&&g.top===c.top,`${c.name}: box ${JSON.stringify(g)}, reference ${JSON.stringify(c)}`);
      const index=(await Array.fromAsync(Deno.readDir(dir))).map(e=>e.name).find(n=>n.startsWith(c.name+"-"))!;
      const lean=decodePNG(await Deno.readFile(`${dir}/${index}`));
      const reference=decodePNG(Uint8Array.from(atob(c.png),ch=>ch.charCodeAt(0)));
      const {mean,big}=difference(lean,reference);
      console.log(`${c.name.padEnd(16)} mean ${mean.toFixed(2)}, over 32: ${(100*big).toFixed(2)}%, drawn in ${g.us} us`);
      assert(mean<=4&&big<=0.025,`${c.name}: mean difference ${mean.toFixed(2)}, ${(100*big).toFixed(2)}% of pixels over 32`);
    }
  }finally{await Deno.remove(dir,{recursive:true});}
}});
