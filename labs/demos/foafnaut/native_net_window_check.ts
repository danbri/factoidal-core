// The window's page requests end to end (issue 374): run_html.ts off screen loads a page from a
// local server; its scripts make an async XMLHttpRequest (each event and readyState in order),
// a sync one in a later task, two fetch() calls (one of a data: URL, answered by the engine),
// and a cross-origin request with no CORS header, which must fail. The engine decides every
// request (Net.PageFetch); run_html.ts and native_net.ts move the bytes.
// Usage: deno run -A --unstable-ffi --unstable-webgpu native_net_window_check.ts [run_html args...]
// (test.sh passes --native-engine when the library is built). Exit 0 when every line is seen.
const lab=new URL(".",import.meta.url).pathname;
const seen:string[]=[];
const other=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},()=>new Response("secret"));
const page=`<!doctype html><title>net</title><script>
const log=m=>console.log('net '+m);
const x=new XMLHttpRequest(),ev=[];
for(const t of ['readystatechange','loadstart','progress','load','loadend'])x.addEventListener(t,()=>ev.push(t+x.readyState));
x.onloadend=()=>{
  log('async '+x.status+' '+x.responseText+' '+ev.join(','));
  const y=new XMLHttpRequest();y.open('GET','/data?s',false);y.send();log('sync '+y.status+' '+y.responseText);
  fetch('/data?f').then(r=>r.text()).then(t=>log('fetch '+t),e=>log('fetch failed '+e));
  fetch('data:,inline').then(r=>r.text()).then(t=>log('dataurl '+t),e=>log('dataurl failed '+e));
  const z=new XMLHttpRequest();z.open('GET','http://127.0.0.1:${other.addr.port}/x');
  z.onerror=()=>log('cors refused '+z.status+' ['+z.responseText+']');z.onload=()=>log('cors LEAK '+z.responseText);z.send();
};
x.open('GET','/data?a');x.send();
</script>`;
const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},req=>{
  const u=new URL(req.url);
  if(u.pathname==="/page.html")return new Response(page,{headers:{"content-type":"text/html;charset=utf-8"}});
  if(u.pathname==="/data")return new Response("ok"+u.search.slice(1),{headers:{"content-type":"text/plain"}});
  return new Response("no",{status:404});
});
const want=[
  "net async 200 oka readystatechange1,loadstart1,readystatechange2,readystatechange3,progress3,readystatechange4,load4,loadend4",
  "net sync 200 oks","net fetch okf","net dataurl inline","net cors refused 0 []",
];
const child=new Deno.Command("deno",{args:["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A",
  `${lab}run_html.ts`,"--offscreen","--no-state","--url",`http://127.0.0.1:${server.addr.port}/page.html`,...Deno.args],stdout:"piped",stderr:"piped"}).spawn();
const reader=(s:ReadableStream<Uint8Array>)=>(async()=>{let rest="";for await(const c of s.pipeThrough(new TextDecoderStream())){rest+=c;const lines=rest.split("\n");rest=lines.pop()??"";
  for(const l of lines){const m=/page: (net .*)$/.exec(l);if(m)seen.push(m[1]);if(/page error/.test(l))seen.push("ERROR "+l);}}})();
const done=Promise.all([reader(child.stdout),reader(child.stderr)]);
const deadline=Date.now()+30000;
while(Date.now()<deadline&&!want.every(w=>seen.includes(w)))await new Promise(r=>setTimeout(r,100));
try{child.kill("SIGTERM");}catch{/* ended */}
await child.status;await done.catch(()=>{});
await server.shutdown();await other.shutdown();
const missing=want.filter(w=>!seen.includes(w));
if(missing.length||seen.some(l=>l.startsWith("ERROR")||l.includes("LEAK"))){
  console.error("page requests in the window failed. Missing:",missing,"\nSeen:",seen);Deno.exit(1);
}
console.log("page requests in the window: async and sync XMLHttpRequest, fetch, data: URL and a CORS refusal, as expected");
