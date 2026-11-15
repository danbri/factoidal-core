// The options of run_html.ts that the real-page survey (realpages/survey.ts) relies on, on a
// local fixture in the off-screen window: --shot FILE --shot-at-end writes the picture when
// --watch-sweep ends (after the last frame, not at the first idle frame), and
// --liberal-report json prints each System entry once as {"type":"native-html-skip",...}
// (fixtures/liberal/missing-css.html: the stylesheet that is not there). Without the options,
// neither line is printed; --shot-at-end without --shot is refused. Then the survey itself on
// that one lab page with no Chrome and no network (pages file made here), so its summary fields
// stay what compare.ts and the workflow read.
// NOT RUN (exit 0) off macOS, or with no window library or engine. About 15 s.
// Run: deno run --no-check --no-config --allow-read --allow-run --allow-env --allow-write realpages_check.ts
const here=new URL(".",import.meta.url).pathname;
const windowLib=`${here}.build/native/libnative-window.dylib`;
const engineLib=Deno.env.get("WEB_RENDER_DYLIB")??`${here}.build/web-render/engines/libweb-render.dylib`;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
// Offline replay (realpages/replay.ts), any platform: a host preloaded with it gets the
// snapshot's answers, a 404 for a URL not in it, the recorded address for a name, and the real
// fetch for file: URLs.
{
  const {writeZip}=await import("./realpages/zip.ts");
  const dir=await Deno.makeTempDir(),enc=new TextEncoder();
  const manifest={entries:[
    {url:"https://replay.test/",status:301,headers:[["location","https://www.replay.test/page"]],remote_ip:"203.0.113.7"},
    {url:"https://www.replay.test/page",status:200,headers:[["content-type","text/html"],["content-encoding","gzip"]],body:"bodies/0001",remote_ip:"2001:db8::7"}]};
  Deno.writeFileSync(`${dir}/s.zip`,await writeZip([{name:"manifest.json",data:enc.encode(JSON.stringify(manifest))},{name:"bodies/0001",data:enc.encode("<p>replayed</p>")}]));
  Deno.writeTextFileSync(`${dir}/local.txt`,"local");
  Deno.writeTextFileSync(`${dir}/main.ts`,`const r=await fetch("https://replay.test/");const m=await fetch("https://replay.test/x");
const h=await fetch("https://replay.test/",{redirect:"manual"});const f=await fetch(new URL("file://${dir}/local.txt"));
console.log(JSON.stringify({status:r.status,url:r.url,body:await r.text(),enc:r.headers.get("content-encoding"),miss:m.status,manual:h.status,
loc:h.headers.get("location"),file:await f.text(),a:await Deno.resolveDns("replay.test","A"),aaaa:await Deno.resolveDns("www.replay.test","AAAA"),none:await Deno.resolveDns("other.test","A")}));`);
  const o=await new Deno.Command(Deno.execPath(),{args:["run","-A","--preload",`${here}realpages/replay.ts`,`${dir}/main.ts`],env:{REALPAGES_REPLAY:`${dir}/s.zip`},stdout:"piped",stderr:"piped"}).output();
  const got=new TextDecoder().decode(o.stdout).trim(),err=new TextDecoder().decode(o.stderr);
  const want=JSON.stringify({status:200,url:"https://www.replay.test/page",body:"<p>replayed</p>",enc:null,miss:404,manual:301,loc:"https://www.replay.test/page",
    file:"local",a:["203.0.113.7"],aaaa:["2001:db8::7"],none:[]});
  await Deno.remove(dir,{recursive:true});
  if(got!==want||!err.includes('"realpages-replay-miss"')||!err.includes('{"type":"realpages-replay","hits":3,"misses":1}')){
    console.error(`realpages_check.ts FAILED: replay\n  got  ${got}\n  want ${want}\n  ${err.slice(-400)}`);Deno.exit(1);}
  console.log("replay: snapshot answers, redirects, misses, names and file: as expected");
}
if(Deno.build.os!=="darwin"){console.log("NOT RUN: realpages_check.ts needs the macOS window library");Deno.exit(0);}
for(const need of [windowLib,engineLib,`${here}.build/native-html/runtime/web-render.mjs`])
  if(!exists(need)){console.log(`NOT RUN: realpages_check.ts needs ${need}`);Deno.exit(0);}

const tmp=await Deno.makeTempDir();
const failures:string[]=[];
const run=async(extra:string[])=>{
  const o=await new Deno.Command(Deno.execPath(),{cwd:here,args:["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A",
    "run_html.ts","--offscreen","--offscreen-size","800x600@1","--text-size","100","--no-state","--be-liberal-in-what-we-accept","--native-engine",engineLib,
    "--url",new URL("./fixtures/liberal/missing-css.html",import.meta.url).href,...extra],stdout:"piped",stderr:"piped"}).output();
  return {code:o.code,out:new TextDecoder().decode(o.stdout),err:new TextDecoder().decode(o.stderr)};
};
const events=(text:string)=>text.split("\n").filter(l=>l.startsWith("{\"type\":")).map(l=>JSON.parse(l) as Record<string,unknown>);
try{
  const shot=`${tmp}/end.png`;
  const a=await run(["--shot",shot,"--shot-at-end","--liberal-report","json","--watch-sweep","3"]);
  const ev=events(a.out),types=ev.map(e=>e.type);
  const skips=ev.filter(e=>e.type==="native-html-skip");
  if(a.code!==0)failures.push(`exit ${a.code}: ${a.err.slice(-400)}`);
  if(skips.length!==1||skips[0].feature!=="external stylesheet"||skips[0].source!=="System")failures.push(`skips: ${JSON.stringify(skips)}`);
  const shotAt=types.lastIndexOf("native-html-shot"),lastFrame=types.lastIndexOf("native-html-frame");
  if(shotAt<0)failures.push("no native-html-shot line");
  else if(shotAt<lastFrame)failures.push("--shot-at-end: the picture was taken before the last frame");
  const png=exists(shot)?Deno.readFileSync(shot):new Uint8Array();
  if(!(png[0]===137&&png[1]===80))failures.push("--shot-at-end: no PNG written");
  const b=await run(["--watch-sweep","2"]);
  if(events(b.out).some(e=>e.type==="native-html-skip"||e.type==="native-html-shot"))failures.push("without the options a skip or shot line was printed");
  const c=await run(["--shot-at-end","--watch-sweep","1"]);
  if(c.code===0||!/--shot-at-end needs --shot/.test(c.out+c.err))failures.push("--shot-at-end without --shot was not refused");
  // The survey on one lab page: no network, no Chrome.
  const pages=`${tmp}/pages.json`;
  Deno.writeTextFileSync(pages,JSON.stringify({defaults:{viewport:"800x600",budgets:{first_frame_s:60}},
    pages:[{id:"missing-css",url:"lab:fixtures/liberal/missing-css.html",scroll:false}]}));
  const s=await new Deno.Command(Deno.execPath(),{cwd:here,args:["run","-A","realpages/survey.ts","--engine",engineLib,"--out",`${tmp}/survey`,
    "--pages",pages,"--no-chrome","--watch","2","--timeout","90","--retries","0"],stdout:"piped",stderr:"piped"}).output();
  if(s.code!==0)failures.push(`survey exit ${s.code}: ${new TextDecoder().decode(s.stderr).slice(-400)}`);
  else{
    const sum=JSON.parse(Deno.readTextFileSync(`${tmp}/survey/summary.json`));
    const r=sum.pages[0];
    console.log(`survey row: ${JSON.stringify({verdict:r.verdict,first_frame_s:r.first_frame_s,first_layout_ms:r.first_layout_ms,prims:r.prims,cpu_idle_pct:r.cpu_idle_pct,rss_peak_mb:r.rss_peak_mb,skips_count:r.skips_count,shot:r.shot})}`);
    if(sum.schema!=="foafnaut-realpages/1"||!sum.host.shot_at_end||!sum.host.liberal_report)failures.push(`summary header: ${JSON.stringify(sum.host)}`);
    if(r.state!=="ok"||r.crashed||r.skips_count!==1||r.shot!=="end"||!(r.first_frame_s>0)||!(r.prims>0)||!(r.rss_peak_mb>0))failures.push(`survey row: ${JSON.stringify(r)}`);
  }
}catch(error){failures.push(String(error));}
finally{await Deno.remove(tmp,{recursive:true}).catch(()=>{});}
if(failures.length){console.error("realpages_check.ts FAILED:\n  "+failures.join("\n  "));Deno.exit(1);}
console.log("realpages_check.ts: --shot-at-end, --liberal-report json and the survey's summary as expected");
