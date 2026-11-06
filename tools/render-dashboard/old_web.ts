// Render each page of the old-web mirror through the browser's own document
// path. A page counts as rendered when its frame has data. Prints one JSON object.
// usage: deno run ... old_web.ts WIDTH HEIGHT
import {loadHTML} from "../../labs/demos/foafnaut/native_html_engine.ts";
import {prepareHTML} from "../../labs/demos/foafnaut/native_html_document.ts";

const [width,height]=Deno.args.map(Number);
const root=new URL("../../third_party/testing/old-web/",import.meta.url);
const pages:string[]=[];
const walk=async(dir:URL,path:string)=>{for await(const entry of Deno.readDir(dir)){
  if(entry.isDirectory)await walk(new URL(entry.name+"/",dir),path+entry.name+"/");
  else if(entry.name.endsWith(".html"))pages.push(path+entry.name);
}};
await walk(root,"");
pages.sort();
const cases=[];
let engine=await loadHTML();
for(let index=0;index<pages.length;index++){
  // One engine runs out of memory on the whole set: the known render leak.
  if(index%10===9)engine=await loadHTML();
  const row:{page:string,status:string,reason?:string,bytes?:number}={page:pages[index],status:"RENDERED"};
  try{
    const frame=(await prepareHTML(engine,new URL(pages[index],root).href)).compile(width,height);
    row.bytes=frame.data.length;
    if(!frame.data.length){row.status="EMPTY";row.reason="Frame has no data";}
  }catch(error){row.status="REFUSED";row.reason=String((error as Error)?.message??error).slice(0,300);}
  cases.push(row);
}
console.log(JSON.stringify({total:cases.length,cases}));
