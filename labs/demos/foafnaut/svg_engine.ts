// @deno-types="./svg-engine.d.ts"
import createModule from "./.build/engines/svg-engine.mjs";
export type SVGArtifact={
  abi:"lean-svg-v1";profile:"painted-primitives-experiment";width:number;height:number;
  binding:"read-only-storage";primitiveCount:number;data:number[];wgsl:string;tree?:RetainedNode[]|null;checks:{x:number;y:number;rgb:number[]}[];
};
export type RetainedNode=
  |{kind:"group";id:string|null;transform:number[];clip?:{bounds:number[];transform:number[]};children:RetainedNode[]}
  |{kind:"paint";geometry:"rect"|"circle"|"ellipse"|"line"|"polygon"|"path"};

// Validate the packed ABI only. SVG interpretation, geometry, clipping and
// painter order are produced in Lean; this decoder never renders a shape.
function validateStorage(a:SVGArtifact):void {
  const d=a.data,rows=d.length/4;
  const uint=(v:number,max=0xffffffff)=>Number.isSafeInteger(v)&&v>=0&&v<=max;
  let cursor=2,records=0;
  while(cursor<rows){
    if(++records>a.primitiveCount||cursor+5>rows)throw new Error("Invalid Lean SVG storage cursor");
    const start=cursor*4,tag=d[start+4],count=d[start+5],rule=d[start+6],mode=d[start+7];
    const dashCount=d[start+18],hasDash=d[start+19];
    if(!uint(tag,6)||tag<1||!uint(count,rows*2)||!uint(rule,1)||!uint(mode,rows*4+3)||
      !uint(dashCount,rows/5)||!uint(hasDash,1)||(!hasDash&&dashCount!==0)||
      (tag<=4&&count!==0))throw new Error("Invalid Lean SVG integer header");
    const shapeRows=tag===6?count:Math.ceil(count/2),affineRows=mode%4>=2?2:0,clipCount=Math.floor(mode/4);
    const dashStart=cursor+5+shapeRows,clipStart=dashStart+5*dashCount+affineRows;
    const next=clipStart+3*clipCount;
    if(!Number.isSafeInteger(next)||next>rows)throw new Error("Invalid Lean SVG storage bounds");
    for(let i=0;i<dashCount;i++){
      const p=(dashStart+5*i)*4;
      if(![2,4,7].includes(d[p+4])||d[p+5]!==0||d[p+6]!==0||d[p+7]!==0)
        throw new Error("Invalid Lean SVG dash record");
    }
    for(let i=0;i<clipCount;i++){
      const p=(clipStart+3*i)*4;
      if(!uint(d[p+3],1)||d[p+7]!==0||(d[p+3]===1&&!(d[p+10]>0&&d[p+11]>0)))
        throw new Error("Invalid Lean SVG clip record");
    }
    cursor=next;
  }
  if(cursor!==rows||records!==a.primitiveCount)throw new Error("Invalid Lean SVG record count");
}
export function validateSVG(value:unknown):SVGArtifact {
  const a=value as SVGArtifact;
  let retainedNodeCount=0;
  const validTree=(nodes:unknown,depth=0):nodes is RetainedNode[]=>Array.isArray(nodes)&&depth<=32&&nodes.every((node:unknown)=>{
    if(++retainedNodeCount>16384||!node||typeof node!=="object")return false;
    const n=node as RetainedNode;
    if(n.kind==="paint")return ["rect","circle","ellipse","line","polygon","path"].includes(n.geometry);
    const floats=(v:unknown,length:number)=>Array.isArray(v)&&v.length===length&&v.every(x=>typeof x==="number"&&Number.isFinite(x)&&Number.isFinite(Math.fround(x)));
    return n.kind==="group"&&(n.id===null||typeof n.id==="string")&&floats(n.transform,6)&&
      (n.clip===undefined||!!n.clip&&floats(n.clip.bounds,4)&&floats(n.clip.transform,6))&&validTree(n.children,depth+1);
  });
  if(!a||a.abi!=="lean-svg-v1"||a.profile!=="painted-primitives-experiment"||a.binding!=="read-only-storage"||
    ![a.width,a.height].every(n=>Number.isInteger(n)&&n>=1&&n<=4096)||
    !Number.isInteger(a.primitiveCount)||a.primitiveCount<0||a.primitiveCount>12288||
    !Array.isArray(a.data)||a.data.length<8||a.data.length>262144||a.data.length%4!==0||!a.data.every(n=>Number.isFinite(n)&&Number.isFinite(Math.fround(n)))||
    typeof a.wgsl!=="string"||a.wgsl.length>1048576||(a.tree!==undefined&&a.tree!==null&&!validTree(a.tree))||!Array.isArray(a.checks)||!a.checks.length||
    !a.checks.every(p=>Number.isInteger(p.x)&&Number.isInteger(p.y)&&p.x>=0&&p.x<a.width&&p.y>=0&&p.y<a.height&&Array.isArray(p.rgb)&&p.rgb.length===3&&p.rgb.every(c=>Number.isInteger(c)&&c>=0&&c<=255)))throw new Error("Invalid Lean SVG artifact");
  validateStorage(a);return a;
}
export async function loadSVG(){
  const module=await createModule();
  const call=(name:string,xml:string,width:number,height:number,extra:number[]=[],documentURL?:string)=>{
    if(typeof xml!=="string"||xml.includes("\0")||[...xml].length>1048576)throw new Error("Invalid SVG input ABI");
    if(![width,height,...extra].every(n=>Number.isInteger(n)&&n>=0&&n<=0xffffffff))throw new Error("Invalid SVG numeric ABI");
    if((name==="svg_call_url"&&documentURL===undefined)||(documentURL!==undefined&&(typeof documentURL!=="string"||documentURL.includes("\0")||[...documentURL].length>1048576)))throw new Error("Invalid SVG URL ABI");
    const values:(string|number)[]=[xml,width,height,...extra],types=["string",...values.slice(1).map(()=>"number")];
    if(documentURL!==undefined){values.push(documentURL);types.push("string");}
    const pointer=module.ccall(name,"number",types,values);
    if(!pointer)throw new Error("SVG WASM initialization/allocation failed");
    try{const result=JSON.parse(module.UTF8ToString(pointer));if(result.error)throw new Error(`SVG profile: ${result.error}`);return result;}
    finally{module.ccall("svg_free",null,["number"],[pointer]);}
  };
  return {
    compile:(xml:string,width=0,height=0)=>validateSVG(call("svg_call",xml,width,height)),
    compileWithURL:(xml:string,documentURL:string,width=0,height=0)=>validateSVG(call("svg_call_url",xml,width,height,[],documentURL)),
    sample:(xml:string,x:number,y:number,width=0,height=0):number[]=>call("svg_pixel",xml,width,height,[x,y]).rgb,
  };
}
