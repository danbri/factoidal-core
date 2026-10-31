// Local regression tests for a deliberately restricted SVG experiment.
// These are not official W3C test-suite results or a conformance claim.
import {loadSVG,validateSVG} from "./svg_engine.ts";
import {encodePPM,unpad,checkPixels} from "./svg_gpu.ts";
function equal(a:unknown,b:unknown){if(JSON.stringify(a)!==JSON.stringify(b))throw new Error(`${JSON.stringify(a)} != ${JSON.stringify(b)}`);}
function assert(b:boolean,message:string){if(!b)throw new Error(message);}
function rejects(action:()=>unknown,contains:string){let message="";try{action();}catch(error){message=String(error);}assert(message.includes(contains),`Expected ${contains}; got ${message||"success"}`);}
const wrap=(body:string,attrs="")=>`<svg xmlns="http://www.w3.org/2000/svg" width="64" height="64" ${attrs}>${body}</svg>`;

Deno.test("SVG XML.NamespaceView resolves real namespaces and rejects lexical lookalikes",async()=>{
 const e=await loadSVG();const simple=wrap('<rect width="20" height="20" fill="red"/>');
 const prefixed='<s:svg xmlns:s="http://www.w3.org/2000/svg" width="64" height="64"><s:rect width="20" height="20" fill="red"/></s:svg>';
 equal(e.compile(simple),e.compile(prefixed));
 for(const xml of [simple.replace('http://www.w3.org/2000/svg','urn:wrong'),'<svg width="64" height="64"/>'])rejects(()=>e.compile(xml),"namespace");
 rejects(()=>e.compile(wrap('<rect xmlns="" width="1" height="1"/>')),"foreign/non-SVG");
 rejects(()=>e.compile(wrap('<rect xmlns:f="http://www.w3.org/2000/svg" f:fill="red" width="20" height="20"/>')),"qualified attribute");
 rejects(()=>e.compile(wrap('<z:rect width="1" height="1"/>')),"namespace");
 rejects(()=>e.compile(wrap('<rect xmlns:a="urn:x" xmlns:b="urn:x" a:q="1" b:q="2"/>')),"namespace");
 rejects(()=>e.compile(wrap('<rect></circle>')),"XML:");
 equal(e.compile(wrap('<rect x="&#49;.5" width="10" height="10"/>')).data[8],1.5);
});

Deno.test("SVG default and inherited paints keep currentColor symbolic until the leaf",async()=>{
 const e=await loadSVG();equal(e.sample(wrap('<rect width="20" height="20"/>'),5,5),[0,0,0]);
 equal(e.sample(wrap('<line x1="1" y1="5.5" x2="40" y2="5.5"/>'),10,5),[255,255,255]);
 const inherited=wrap('<g fill="currentColor" color="red"><g fill-opacity=".5"><rect width="20" height="20" color="blue" fill-opacity=".25"/></g></g>');
 equal(e.sample(inherited,5,5),[191,191,255]);
 equal(e.sample(wrap('<g fill="red"><rect width="20" height="20" fill="inherit"/></g>'),5,5),[255,0,0]);
 equal(e.sample(wrap('<g fill="red"><rect width="20" height="20" fill="none"/></g>'),5,5),[255,255,255]);
});

Deno.test("SVG preserves signed fractional/exponent coordinates and px lengths",async()=>{
 const e=await loadSVG();const a=e.compile(wrap('<rect x="-.25e1" y="+.125" width="1.275e1px" height="8.5"/>'));
 equal(a.data.slice(8,12),[-2.5,.125,12.75,8.5]);
 equal(e.sample(wrap('<circle cx="10.5" cy="10.5" r="4.25" fill="#0f0"/>'),10,10),[0,255,0]);
 for(const value of ['NaN','Infinity','1e','--2','1.2.3','1e13','1000001','20%','1cm'])rejects(()=>e.compile(wrap(`<rect x="${value}" width="4" height="4"/>`)),"SVG profile:");
});

Deno.test("SVG viewBox meet alignment, none and slice match known viewport examples",async()=>{
 const e=await loadSVG();const doc=(par="",vb="0 0 100 100",width=200,height=100)=>`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="${vb}" ${par}><rect width="100" height="100"/></svg>`;
 equal(e.compile(doc()).data.slice(0,8),[1,1,50,0,0,0,200,100]);
 equal(e.sample(doc(),5,50),[255,255,255]);equal(e.sample(doc(),100,50),[0,0,0]);
 for(const [alignment,offset]of [['xMinYMid',0],['xMidYMid',50],['xMaxYMid',100]]as const)equal(e.compile(doc(`preserveAspectRatio="${alignment} meet"`)).data.slice(0,4),[1,1,offset,0]);
 for(const [alignment,offset]of [['xMidYMin',0],['xMidYMid',50],['xMidYMax',100]]as const)equal(e.compile(doc(`preserveAspectRatio="${alignment} meet"`,undefined,100,200)).data.slice(0,4),[1,1,0,offset]);
 equal(e.compile(doc('preserveAspectRatio="none"')).data.slice(0,4),[2,1,0,0]);
 equal(e.compile(doc('preserveAspectRatio="xMidYMid slice"')).data.slice(0,4),[2,2,0,-50]);
 equal(e.sample(doc('preserveAspectRatio="xMidYMid slice"'),0,0),[0,0,0]);
 equal(e.compile(doc('', '-10 -20 100 100')).data.slice(0,6),[1,1,50,0,-10,-20]);
 rejects(()=>e.compile(doc('', '0 0 0 100')),"viewBox dimensions");
 rejects(()=>e.compile(doc('', '0,0,,100,100')),"numeric list");
});

Deno.test("SVG butt-cap lines, centered rectangle/circle strokes and zero widths",async()=>{
 const e=await loadSVG();const line=wrap('<line x1="10" y1="10.5" x2="20" y2="10.5" stroke="black" stroke-width="4"/>');
 equal(e.sample(line,8,10),[255,255,255]);equal(e.sample(line,10,10),[0,0,0]);equal(e.sample(line,20,10),[255,255,255]);
 equal(e.sample(wrap('<line x1="1" y1="4.5" x2="50" y2="4.5" stroke="black" stroke-width="0"/>'),8,4),[255,255,255]);
 equal(e.sample(wrap('<circle cx="10.5" cy="10.5" r="5" fill="none" stroke="black" stroke-width="0"/>'),15,10),[255,255,255]);
 const rect=wrap('<rect x="10" y="10" width="10" height="10" fill="none" stroke="blue" stroke-width="2"/>');
 equal(e.sample(rect,9,9),[0,0,255]);equal(e.sample(rect,15,15),[255,255,255]);equal(e.sample(rect,8,15),[255,255,255]);
 equal(e.sample(wrap('<line x1="10" x2="10" y1="10" y2="10" stroke="black" stroke-width="8"/>'),10,10),[255,255,255]);
});

Deno.test("SVG element opacity composites fill and stroke once, unlike separate paint opacities",async()=>{
 const e=await loadSVG();const circle=(extra:string)=>wrap(`<circle cx="16.5" cy="16.5" r="10" fill="red" stroke="blue" stroke-width="8" ${extra}/>`);
 equal(e.sample(circle('opacity=".5"'),24,16),[128,128,255]);
 equal(e.sample(circle('opacity=".5"'),16,16),[255,128,128]);
 equal(e.sample(circle('fill-opacity=".5" stroke-opacity=".5"'),24,16),[128,64,191]);
 for(const property of ['opacity','fill-opacity','stroke-opacity'])rejects(()=>e.compile(circle(`${property}="0.5px"`)),"SVG profile:");
 rejects(()=>e.compile(wrap('<g opacity=".5"><rect width="20" height="20"/></g>')),"unsupported attribute");
});

Deno.test("SVG round line caps use capsule geometry with inherited overrides",async()=>{
 const e=await loadSVG();
 for(const [ax,ay,bx,by,width] of [[10,10.5,20,10.5,4],[7.25,8.75,23.25,22.75,5],[16.5,16.5,16.5,16.5,7]]) {
  const doc=wrap(`<line x1="${ax}" y1="${ay}" x2="${bx}" y2="${by}" stroke="black" stroke-width="${width}" stroke-linecap="round"/>`);
  e.compile(doc);
  for(let y=0;y<32;y++)for(let x=0;x<32;x++) {
   const dx=bx-ax,dy=by-ay,len=dx*dx+dy*dy;
   const t=len===0?0:Math.max(0,Math.min(1,((x+.5-ax)*dx+(y+.5-ay)*dy)/len));
   const hit=(x+.5-ax-t*dx)**2+(y+.5-ay-t*dy)**2<=(width/2)**2;
   equal(e.sample(doc,x,y),hit?[0,0,0]:[255,255,255]);
  }
 }
 const inherited=wrap('<g stroke="black" stroke-width="4" stroke-linecap="round"><line x1="10" y1="10.5" x2="20" y2="10.5"/><line x1="10" y1="30.5" x2="20" y2="30.5" stroke-linecap="butt"/></g>');
 equal(e.sample(inherited,8,10),[0,0,0]);equal(e.sample(inherited,8,30),[255,255,255]);
 equal(e.sample(wrap('<line x1="10" y1="10" x2="10" y2="10" stroke="black" stroke-width="0" stroke-linecap="round"/>'),10,10),[255,255,255]);
 rejects(()=>e.compile(wrap('<line stroke="black" stroke-linecap="square"/>')),"unsupported stroke-linecap");
});

Deno.test("SVG ellipse fill and polygon nonzero/evenodd winding are implemented in Lean",async()=>{
 const e=await loadSVG();const ellipse=wrap('<ellipse cx="20.5" cy="20.5" rx="10" ry="5" fill="rgb(100%,0%,0%)"/>');
 equal(e.sample(ellipse,20,20),[255,0,0]);equal(e.sample(ellipse,20,26),[255,255,255]);
 const polygon=(rule:string)=>wrap(`<polygon points="5,5 25,5 25,25 5,25 5,5 25,5 25,25 5,25" fill-rule="${rule}"/>`);
 equal(e.sample(polygon('nonzero'),10,10),[0,0,0]);equal(e.sample(polygon('evenodd'),10,10),[255,255,255]);
 rejects(()=>e.compile(wrap('<ellipse rx="auto" ry="5"/>')),"SVG profile:");
 rejects(()=>e.compile(wrap('<ellipse rx="5"/>')),"explicit numeric rx and ry");
 rejects(()=>e.compile(wrap('<ellipse rx="5" ry="5" stroke="black"/>')),"ellipse stroke");
 rejects(()=>e.compile(wrap('<polygon points="0 0 10 0 10 10" stroke="black"/>')),"polygon stroke");
});

Deno.test("SVG zero dimensions disable painting; negative geometry is an explicit refusal",async()=>{
 const e=await loadSVG();const a=e.compile(wrap('<rect width="0" height="20"/><circle r="0"/><ellipse rx="0" ry="8"/>'));
 equal(a.primitiveCount,0);equal(e.sample(wrap(''),10,10),[255,255,255]);
 for(const shape of ['<rect width="-1" height="5"/>','<circle r="-1"/>','<ellipse rx="-1" ry="4"/>'])rejects(()=>e.compile(wrap(shape)),"negative");
 equal(e.compile(wrap('<rect width="0" height="20" transform="translate(1)"/>')).primitiveCount,0);
 rejects(()=>e.compile(wrap('<rect width="0" height="20" transform="perspective(1)"/>')),"unsupported transform");
});

Deno.test("SVG fractional/tiny root viewport and explicit embedding viewport have valid artifacts",async()=>{
 const e=await loadSVG();const doc='<svg xmlns="http://www.w3.org/2000/svg" width="1.25px" height=".5"><rect width="2" height="2"/></svg>';
 const a=e.compile(doc);equal([a.width,a.height],[2,1]);equal(a.data.slice(6,8),[1.25,.5]);
 const tiny=e.compile('<svg xmlns="http://www.w3.org/2000/svg" width="1" height="1"><rect width="1" height="1"/></svg>');
 equal(tiny.checks,[{x:0,y:0,rgb:[0,0,0]}]);
 equal(e.compile('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 10 10"/>',40,20).data.slice(0,4),[2,2,10,0]);
 rejects(()=>e.compile('<svg xmlns="http://www.w3.org/2000/svg"/>'),"root width");
 rejects(()=>e.compile(wrap(''),40,0),"both output dimensions");
 rejects(()=>e.compile('<svg xmlns="http://www.w3.org/2000/svg" width="100%" height="100%"/>',40,20),"unsupported unit");
});

Deno.test("SVG refuses unsupported features rather than silently losing rendering semantics",async()=>{
 const e=await loadSVG();
 for(const element of ['path','polyline','text','use','image','foreignObject','defs','style','linearGradient','filter','clipPath','mask','script','svg'])rejects(()=>e.compile(wrap(`<${element}/>`)),"SVG profile:");
 for(const attrs of ['style="fill:red"','class="red"','transform="perspective(1)"','stroke-dasharray="2 2"','stroke-linecap="square"','stroke-linejoin="bevel"','rx="2"','filter="url(#f)"'])rejects(()=>e.compile(wrap(`<rect width="20" height="20" ${attrs}/>`)),"unsupported");
 rejects(()=>e.compile('<?xml-stylesheet href="a.css"?>'+wrap('')),"processing instruction");
 rejects(()=>e.compile('<!DOCTYPE svg>'+wrap('')),"DOCTYPE");
 rejects(()=>e.compile('<?xml version="1.0" encoding="ISO-8859-1"?>'+wrap('')),"UTF-8");
 equal(e.sample(wrap('<rect width="20" height="20" fill="url(#missing)"/>'),5,5),[255,255,255]);
 rejects(()=>e.compile(wrap('<rect id="gradient" width="20" height="20" fill="url(#gradient)"/>')),"referenced paint server unsupported");
});

Deno.test("SVG artifact/input limits and GPU row/readback encoding are checked without a GPU",async()=>{
 const e=await loadSVG();const a=e.compile(wrap('<circle r="1"/>'));
 rejects(()=>e.compile(wrap('')+'\0'),"Invalid SVG input ABI");
 rejects(()=>e.compile('x'.repeat(1048577)),"Invalid SVG input ABI");
 rejects(()=>e.compile(wrap('<rect width="1" height="1"/>'.repeat(12289))),"primitive count");
 rejects(()=>validateSVG({...a,data:[NaN]}),"Invalid Lean SVG artifact");
 const rgba=new Uint8Array(a.width*a.height*4);for(const p of a.checks)rgba.set([...p.rgb,255],(p.y*a.width+p.x)*4);checkPixels(a,rgba);
 const p=a.checks[0];rgba[(p.y*a.width+p.x)*4]=255-p.rgb[0];rejects(()=>checkPixels(a,rgba),"readback mismatch");
 const rows=new Uint8Array(512);rows.set([1,2,3,255]);rows.set([4,5,6,255],256);equal([...encodePPM(unpad(rows,1,2,256),1,2).slice(11)],[1,2,3,4,5,6]);
});

Deno.test("SVG storage artifact stays bounded and uses compact data-driven geometry",async()=>{
 const e=await loadSVG();
 const large=e.compile(wrap('<circle cx="5" cy="5" r="2"/>'.repeat(2000)));
 equal(large.binding,"read-only-storage");equal(large.primitiveCount,2000);equal(large.data.length,40008);
 assert(large.wgsl.includes("var<storage,read>"),"SVG is not storage backed");
 assert(large.wgsl.includes("for(var primitive=")&&large.wgsl.length<32768,"shader expands per primitive");
 rejects(()=>validateSVG({...large,binding:"uniform"}),"Invalid Lean SVG artifact");
 rejects(()=>validateSVG({...large,data:Array(262148).fill(0)}),"Invalid Lean SVG artifact");
 const points=Array.from({length:64},(_,i)=>`${i%8},${Math.floor(i/8)}`).join(' ');
 rejects(()=>e.compile(wrap(`<polygon points="${points}"/>`.repeat(1800))),"storage data");
});

Deno.test("SVG gallery is an actual parsed document with Float data and generated WGSL",async()=>{
 const e=await loadSVG();const xml=await Deno.readTextFile(new URL('svg-fixtures/gallery.svg',import.meta.url));
 const a=e.compile(xml);equal([a.width,a.height,a.primitiveCount],[640,420,9]);
 assert(a.data.some(n=>n<0)&&a.data.some(n=>!Number.isInteger(n)),"Lost signed/fractional scene data");
 assert(a.wgsl.includes('var winding:i32')&&a.wgsl.includes('element.a*opacity'),"Missing polygon/composite lowering");
});

Deno.test("SVG non-rendering metadata and missing local paint fallback follow upstream cases",async()=>{
 const e=await loadSVG();
 for(const name of ['fallback-001.svg','fallback-002.svg']){
  const xml=await Deno.readTextFile(new URL(`../../../tests/external/svg/upstream/svg/painting/reftests/${name}`,import.meta.url));
  const artifact=e.compile(xml,800,600);equal([artifact.width,artifact.height],[800,600]);
  equal(e.sample(xml,5,5,800,600),[0,128,0]);equal(e.sample(xml,101,5,800,600),[255,255,255]);
 }
 const hidden=wrap('<metadata><rect width="64" height="64" fill="red"/><data xmlns="urn:private">opaque</data></metadata>');
 equal(e.sample(hidden,5,5),[255,255,255]);
 equal(e.sample(wrap('<g fill="url(#missing) currentColor" color="red"><rect width="20" height="20" color="green"/></g>'),5,5),[0,128,0]);
 for(const body of ['<h:link xmlns:h="http://www.w3.org/1999/xhtml" rel="stylesheet" href="x.css"/>',
  '<rect width="20" height="20" fill="url(other.svg#x) green"/>',
  '<rect id="x" width="20" height="20" fill="url(#%78) green"/>',
  '<rect width="20" height="20" fill="url(#bad id) green"/>'])rejects(()=>e.compile(wrap(body)),"unsupported");
});

Deno.test("SVG affine transforms compose in SVG order and preserve local stroke geometry",async()=>{
 const e=await loadSVG();
 const doc=(t:string,shape='<rect width="8" height="6"/>')=>wrap(`<g transform="${t}">${shape}</g>`);
 equal(e.sample(doc('translate(10,20) scale(2,3)'),11,21),[0,0,0]);
 equal(e.sample(doc('scale(2,3) translate(10,20)'),11,21),[255,255,255]);
 const nested=wrap('<g transform="translate(10,20)"><g transform="scale(2,3)"><rect width="8" height="6"/></g></g>');
 for(const [x,y] of [[10,20],[25,37],[26,38],[9,20]])equal(e.sample(nested,x,y),e.sample(doc('translate(10,20)scale(2,3)'),x,y));
 equal(e.sample(doc('rotate(90,10,10)','<rect x="10" y="10" width="6" height="3"/>'),8,12),[0,0,0]);
 equal(e.sample(doc('skewX(45)','<rect width="4" height="4"/>'),5,2),[0,0,0]);
 equal(e.sample(doc('skewY(45)','<rect width="4" height="4"/>'),2,5),[0,0,0]);
 equal(e.sample(doc('scale(-1,1)','<rect x="-20" y="5" width="10" height="10"/>'),15,10),[0,0,0]);
 // Independent analytic local-circle outline under a general affine CTM.
 const [a,b,c,d,tx,ty]=[2,1,-.5,1,20,10],det=a*d-b*c;
 const circle=doc(`matrix(${a},${b},${c},${d},${tx},${ty})`,'<circle cx="5" cy="5" r="4" fill="none" stroke="black" stroke-width="2"/>');
 for(let y=0;y<40;y+=3)for(let x=0;x<50;x+=3){
  const dx=x+.5-tx,dy=y+.5-ty,lx=(d*dx-c*dy)/det,ly=(-b*dx+a*dy)/det;
  const r2=(lx-5)**2+(ly-5)**2;equal(e.sample(circle,x,y),r2>=9&&r2<=25?[0,0,0]:[255,255,255]);
 }
 const tiny=e.compile(doc('scale(1000)scale(1000)scale(1000)','<circle r="3"/>'));
 equal(tiny.data.slice(-8),[1e-9,0,0,0,0,1e-9,0,0]);
 equal(e.compile(wrap('<rect x=".0000001" width="1" height="1"/>')).data[8],1e-7);
 const baseline=e.compile(wrap('<circle r="3"/>')),identity=e.compile(doc('translate(0) scale(1)','<circle r="3"/>'));
 equal(identity.data,baseline.data);equal(e.compile(doc('translate(1)','<circle r="3"/>')).data.length,baseline.data.length+8);
 const mixed=wrap('<rect width="2" height="2" transform="translate(5)"/><circle cx="20" cy="20" r="3"/><polygon points="0,0 5,0 0,5" transform="translate(30,30)"/>');
 equal(e.sample(mixed,20,20),[0,0,0]);equal(e.sample(mixed,31,31),[0,0,0]);
 assert(e.compile(mixed).wgsl.includes('var p=worldP')&&e.compile(mixed).wgsl.includes('header.w>=2u'),"Missing dynamic inverse CTM lowering");
 equal(e.sample(doc('matrix(1,2,2,4,0,0)','<rect width="64" height="64"/>'),5,5),[255,255,255]);
 for(const t of ['matrix(1,2)','translate(1),','scale(1e-12)','skewX(90)','translate(1)'.repeat(33)])rejects(()=>e.compile(doc(t)),"SVG profile:");
 rejects(()=>e.compile(wrap('<circle r="1" transform="translate(1)"/>'.repeat(10000))),"storage data");
 rejects(()=>e.compile('<svg xmlns="http://www.w3.org/2000/svg" width="64" height="64" transform="translate(1)"/>'),"unsupported attribute");
});
