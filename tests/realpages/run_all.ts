// Runs the page list: per page the Chrome reference, then each engine, one at a time; then image facts.
// deno run -A tests/realpages/run_all.ts --work DIR --round NAME --engines sha1,sha2,... [--only id,id] [--resume] [--ref-round NAME]
// Engines: DIR/eng/<sha>/foafnaut/libweb-render.dylib with host DIR/host/<sha>/labs/demos/foafnaut (patched); see setup.sh.
const a=Deno.args,opt=(n:string,d?:string)=>{const i=a.indexOf(n);return i<0?d:a[i+1];};
const H=new URL(".",import.meta.url).pathname.replace(/\/$/,"");
// The work folder (scratch; never committed): eng/<sha>/foafnaut/libweb-render.dylib, host/<sha>/ (git archive, patched), rounds/.
const R=opt("--work")??Deno.env.get("REALPAGES_WORK")!;
const round=opt("--round")!,engines=opt("--engines")!.split(","),only=opt("--only")?.split(",");
const pages:{id:string;url:string;kind:string}[]=JSON.parse(await Deno.readTextFile(`${H}/pages.json`));
const run=async(cmd:string,args:string[],limitMs:number)=>{
  const c=new Deno.Command(cmd,{args,stdout:"piped",stderr:"piped"}).spawn();
  const timer=setTimeout(()=>{try{c.kill("SIGKILL");}catch{/* */}},limitMs);
  const o=await c.output();clearTimeout(timer);
  return {code:o.code,out:new TextDecoder().decode(o.stdout),err:new TextDecoder().decode(o.stderr)};
};
const freeDiskGiB=async()=>{const o=(await run("df",["-k","/"],10000)).out.trim().split("\n")[1].split(/\s+/);return Number(o[3])/1048576;};
const freeMemGiB=async()=>{const o=(await run("vm_stat",[],10000)).out;const pg=(k:string)=>Number(new RegExp(`${k}:\\s+(\\d+)`).exec(o)?.[1]??0);
  return (pg("Pages free")+pg("Pages inactive")+pg("Pages speculative")+pg("Pages purgeable"))*16384/2**30;};
const log=(s:string)=>{console.log(`${new Date().toISOString()} ${s}`);};
const facts=async(png:string,top:number)=>{
  try{await Deno.stat(png);}catch{return;}
  const r=await run(`${R}/imgfacts`,[png,String(top),"1280","935"],60000);
  if(r.code===0)await Deno.writeTextFile(png.replace(/\.png$/,".facts.json"),r.out);
};
for(const p of pages){
  if(only&&!only.includes(p.id))continue;
  const disk=await freeDiskGiB();if(disk<1.5){log(`STOP: ${disk.toFixed(2)} GiB free on disk`);break;}
  let mem=await freeMemGiB();
  for(let i=0;i<10&&mem<1.5;i++){log(`waiting: ${mem.toFixed(2)} GiB memory free`);await new Promise(r=>setTimeout(r,60000));mem=await freeMemGiB();}
  if(mem<1.5){log("STOP: memory short");break;}
  const D=`${R}/rounds/${round}/${p.id}`;await Deno.mkdir(D,{recursive:true});
  // --ref-round NAME: keep that round's Chrome reference (chrome.json and the facts of its pictures) instead of measuring
  // Chrome again, so the engine numbers of the two rounds compare against the same reference.
  const refRound=opt("--ref-round");
  if(refRound&&!(await Deno.stat(`${D}/chrome.json`).catch(()=>null))){
    const S=`${R}/rounds/${refRound}/${p.id}`;
    try{for await(const f of Deno.readDir(S))
      if(f.isFile&&(f.name==="chrome.json"||/^c-.*\.facts\.json$/.test(f.name)))await Deno.copyFile(`${S}/${f.name}`,`${D}/${f.name}`);}
    catch{log(`${p.id}: no reference in round ${refRound}; Chrome is measured`);}
  }
  if(!((a.includes("--resume")||refRound)&&(await Deno.stat(`${D}/chrome.json`).catch(()=>null)))){
    const c=await run("deno",["run","-A",`${H}/chrome_ref.ts`,"--url",p.url,"--out",D,"--viewport","1280x935","--profile",`${R}/.chrome-profile`],150000);
    log(`${p.id} chrome: ${c.out.trim()||c.err.trim().slice(0,300)}`);
    for(const n of ["load","scroll","pretype","type","link"]){await facts(`${D}/c-${n}.png`,0);if(n!=="load")await Deno.remove(`${D}/c-${n}.png`).catch(()=>{});}
  }
  let ref:any={};try{ref=JSON.parse(await Deno.readTextFile(`${D}/chrome.json`));}catch{/* no reference */}
  for(const sha of engines){
    const E=`${D}/${sha}`;if(a.includes("--resume")&&(await Deno.stat(`${E}/engine.json`).catch(()=>null)))continue;
    await Deno.mkdir(E,{recursive:true});
    const steps:unknown[]=["rp-quiet:3000:60000",`rp-shot:${E}/e-load.png`,"rp-scroll:down","rp-quiet:1500:15000",`rp-shot:${E}/e-scroll.png`,"rp-scroll:up","rp-quiet:1000:10000"];
    const inp=ref.dom?.input;
    if(inp){const [x,y,w,h]=inp.box;steps.push(`rp-shot:${E}/e-pretype.png`,`rp-click:${Math.round(x+w/2)}:${Math.round(y+h/2)}`,[9,116,0],[9,101,0],[9,115,0],[9,116,0],"rp-quiet:1500:10000",`rp-shot:${E}/e-type.png`);}
    const fl=ref.dom?.firstLink;
    if(fl)steps.push(`rp-link:${fl.href}`,"rp-nav:30000","rp-quiet:2000:30000",`rp-shot:${E}/e-link.png`);
    const r=await run("deno",["run","-A",`${H}/engine_run.ts`,"--host",`${R}/host/${sha}/labs/demos/foafnaut`,"--engine",`${R}/eng/${sha}/foafnaut/libweb-render.dylib`,
      "--url",p.url,"--out",E,"--steps",JSON.stringify(steps),"--first-limit-s","180","--total-limit-s","360","--mem-limit-mib","4096"],420000);
    log(`${p.id} ${sha}: ${r.out.trim()||("driver failed: "+r.err.trim().slice(0,300))}`);
    let ej:any={};try{ej=JSON.parse(await Deno.readTextFile(`${E}/engine.json`));}catch{/* none */}
    for(const s of ej.shots??[]){await facts(s.file,s.top??65);
      // disk: keep only the load picture of the last engine for checking by eye; the facts files hold the numbers
      if(!(String(s.file).endsWith("/e-load.png")&&sha===engines.at(-1)))await Deno.remove(s.file).catch(()=>{});}
  }
}
log("done");
