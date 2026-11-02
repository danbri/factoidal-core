// @deno-types="./svg-engine.d.ts"
import createModule from "./.build/engines/svg-engine.mjs";
export type SVGArtifact={
  abi:"lean-svg-v1";profile:"painted-primitives-experiment";width:number;height:number;
  binding:"read-only-storage";primitiveCount:number;data:number[];wgsl:string;tree?:RetainedNode[]|null;checks:{x:number;y:number;rgb:number[]}[];
};
export type RetainedNode=
  |{kind:"group";id:string|null;transform:number[];children:RetainedNode[]}
  |{kind:"paint";geometry:"rect"|"circle"|"ellipse"|"line"|"polygon"|"path"};
export function validateSVG(value:unknown):SVGArtifact {
  const a=value as SVGArtifact;
  let retainedNodeCount=0;
  const validTree=(nodes:unknown,depth=0):nodes is RetainedNode[]=>Array.isArray(nodes)&&depth<=32&&nodes.every((node:unknown)=>{
    if(++retainedNodeCount>16384||!node||typeof node!=="object")return false;
    const n=node as RetainedNode;
    if(n.kind==="paint")return ["rect","circle","ellipse","line","polygon","path"].includes(n.geometry);
    return n.kind==="group"&&(n.id===null||typeof n.id==="string")&&Array.isArray(n.transform)&&n.transform.length===6&&n.transform.every(x=>Number.isFinite(x)&&Number.isFinite(Math.fround(x)))&&validTree(n.children,depth+1);
  });
  if(!a||a.abi!=="lean-svg-v1"||a.profile!=="painted-primitives-experiment"||a.binding!=="read-only-storage"||
    ![a.width,a.height].every(n=>Number.isInteger(n)&&n>=1&&n<=4096)||
    !Number.isInteger(a.primitiveCount)||a.primitiveCount<0||a.primitiveCount>12288||
    !Array.isArray(a.data)||a.data.length<8||a.data.length>262144||a.data.length%4!==0||!a.data.every(n=>Number.isFinite(n)&&Number.isFinite(Math.fround(n)))||
    typeof a.wgsl!=="string"||a.wgsl.length>1048576||(a.tree!==undefined&&a.tree!==null&&!validTree(a.tree))||!Array.isArray(a.checks)||!a.checks.length||
    !a.checks.every(p=>Number.isInteger(p.x)&&Number.isInteger(p.y)&&p.x>=0&&p.x<a.width&&p.y>=0&&p.y<a.height&&Array.isArray(p.rgb)&&p.rgb.length===3&&p.rgb.every(c=>Number.isInteger(c)&&c>=0&&c<=255)))throw new Error("Invalid Lean SVG artifact");
  return a;
}
export async function loadSVG(){
  const module=await createModule();
  const call=(name:string,xml:string,width:number,height:number,extra:number[]=[])=>{
    if(typeof xml!=="string"||xml.includes("\0")||[...xml].length>1048576)throw new Error("Invalid SVG input ABI");
    if(![width,height,...extra].every(n=>Number.isInteger(n)&&n>=0&&n<=0xffffffff))throw new Error("Invalid SVG numeric ABI");
    const values=[xml,width,height,...extra],types=["string",...values.slice(1).map(()=>"number")];
    const pointer=module.ccall(name,"number",types,values);
    if(!pointer)throw new Error("SVG WASM initialization/allocation failed");
    try{const result=JSON.parse(module.UTF8ToString(pointer));if(result.error)throw new Error(`SVG profile: ${result.error}`);return result;}
    finally{module.ccall("svg_free",null,["number"],[pointer]);}
  };
  return {
    compile:(xml:string,width=0,height=0)=>validateSVG(call("svg_call",xml,width,height)),
    sample:(xml:string,x:number,y:number,width=0,height=0):number[]=>call("svg_pixel",xml,width,height,[x,y]).rgb,
  };
}
