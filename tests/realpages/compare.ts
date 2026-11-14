// Compares first pictures across rounds: per page and engine the time to a first picture, from the results CSVs that
// score.ts writes (numbers and URLs only; no page content).
// deno run -A tests/realpages/compare.ts --csv results-r1.csv,results-r2.csv [--engines sha1,sha2,...] [--pages id,id]
//   [--out compare.csv]
// Prints a Markdown table (seconds; "none" = no picture within the limit, "fetch" = the host's first fetch failed, "-" =
// not measured), then per engine: pages with a picture, crashes, and two medians: over the pages with a picture, and over
// every page whose first fetch worked with "none" counted as the 180 s limit.
const a=Deno.args,opt=(n:string)=>{const i=a.indexOf(n);return i<0?undefined:a[i+1];};
const LIMIT=180000;
function parseCSV(text:string):Record<string,string>[]{
  const rows:string[][]=[];let row:string[]=[],f="",q=false;
  for(let i=0;i<text.length;i++){const c=text[i];
    if(q){if(c==='"'){if(text[i+1]==='"'){f+='"';i++;}else q=false;}else f+=c;}
    else if(c==='"')q=true;else if(c===","){row.push(f);f="";}else if(c==="\n"){row.push(f);rows.push(row);row=[];f="";}else f+=c;}
  if(f||row.length){row.push(f);rows.push(row);}
  const [h,...b]=rows;return b.filter(r=>r.length===h.length).map(r=>Object.fromEntries(h.map((k,i)=>[k,r[i]])));
}
const all:Record<string,string>[]=[];
for(const f of (opt("--csv")??"").split(",").filter(Boolean))all.push(...parseCSV(await Deno.readTextFile(f)));
const engines=opt("--engines")?.split(",")??[...new Set(all.map(r=>r.engine))];
const pageIds=opt("--pages")?.split(",")??[...new Set(all.map(r=>r.page))];
const at=(p:string,e:string)=>all.findLast(r=>r.page===p&&r.engine===e);
type Cell={ms:number|null;state:"picture"|"none"|"fetch"|"crash"|"missing";peakMiB:number|null;exitCode:string};
const cell=(r:Record<string,string>|undefined):Cell=>{
  if(!r)return {ms:null,state:"missing",peakMiB:null,exitCode:""};
  const peak=r.peakMiB?Number(r.peakMiB):null;
  if(r.crashed==="true")return {ms:r.firstPictureMs?Number(r.firstPictureMs):null,state:"crash",peakMiB:peak,exitCode:r.exitCode};
  if(r.firstPictureMs&&r.picture==="true")return {ms:Number(r.firstPictureMs),state:"picture",peakMiB:peak,exitCode:r.exitCode};
  if(/host error|fetch failed|HTTP \d/.test(r.cause))return {ms:null,state:"fetch",peakMiB:peak,exitCode:r.exitCode};
  return {ms:null,state:"none",peakMiB:peak,exitCode:r.exitCode};
};
const show=(c:Cell)=>c.state==="picture"?(c.ms!/1000).toFixed(1):c.state==="none"?"none":c.state==="fetch"?"fetch":c.state==="crash"?"crash":"-";
const med=(v:number[])=>{if(!v.length)return null;const s=[...v].sort((x,y)=>x-y),m=s.length>>1;return s.length%2?s[m]:(s[m-1]+s[m])/2;};
const lines:string[]=[];
lines.push(`| page | ${engines.map(e=>e.slice(0,9)).join(" | ")} | Chrome |`);
lines.push(`|---|${engines.map(()=>"---:").join("|")}|---:|`);
const out:string[]=["page,engine,state,firstPictureMs,peakMiB,exitCode,chromeFirstPictureMs"];
for(const p of pageIds){
  const cells=engines.map(e=>cell(at(p,e)));
  const chrome=all.find(r=>r.page===p&&r.chromeFirstPictureMs)?.chromeFirstPictureMs;
  lines.push(`| ${p} | ${cells.map(show).join(" | ")} | ${chrome?(Number(chrome)/1000).toFixed(2):"-"} |`);
  engines.forEach((e,i)=>{const c=cells[i];if(c.state!=="missing")out.push([p,e,c.state,c.ms??"",c.peakMiB??"",c.exitCode,chrome??""].join(","));});
}
lines.push("");
lines.push("| engine | pages measured | with a picture | none in 180 s | first fetch failed | crash | median, pages with a picture | median, none = 180 s |");
lines.push("|---|---:|---:|---:|---:|---:|---:|---:|");
for(const e of engines){
  const cs=pageIds.map(p=>cell(at(p,e))).filter(c=>c.state!=="missing");
  const pic=cs.filter(c=>c.state==="picture").map(c=>c.ms!);
  const capped=cs.filter(c=>c.state!=="fetch").map(c=>c.state==="picture"?c.ms!:LIMIT);
  const m1=med(pic),m2=med(capped);
  lines.push(`| ${e.slice(0,9)} | ${cs.length} | ${pic.length} | ${cs.filter(c=>c.state==="none").length} | ${cs.filter(c=>c.state==="fetch").length} | ${cs.filter(c=>c.state==="crash").length} | ${m1===null?"-":(m1/1000).toFixed(1)+" s"} | ${m2===null?"-":(m2/1000).toFixed(1)+" s"} |`);
}
console.log(lines.join("\n"));
const o=opt("--out");if(o)await Deno.writeTextFile(o,out.join("\n")+"\n");
