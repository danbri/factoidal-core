// A small local site for the everyday-use checks (daily_use_check.ts, docs/foafnaut-daily-use.md):
// a search form (GET), a form that posts, a sign-in that sets a cookie, links that open tabs, a
// download, a missing page and a page that redirects. Every page is an original construct, laid
// out with absolute positions so a test can press a field at a known place. Loopback only.
//
//   deno run --allow-net daily_use_server.ts [PORT]   (prints the address, serves until killed)

const field="position:absolute;left:40px;width:400px;height:40px;font:20px sans-serif";
const button="position:absolute;left:460px;width:120px;height:40px;font:20px sans-serif";
const page=(title:string,body:string)=>`<!doctype html><html><head><meta charset="utf-8"><title>${title}</title></head>`+
  `<body style="margin:0;font:20px sans-serif">${body}</body></html>`;
const escape=(s:string)=>s.replace(/[&<>"]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;"})[c]!);

/** The fields' places in CSS pixels: the first field of every form page, and its button. */
export const PLACES={field:{x:240,y:60},button:{x:520,y:60},second:{x:240,y:140}};

function form(method:string,action:string,extra=""){
  return `<form method="${method}" action="${action}">`+
    `<input name="q" style="${field};top:40px" aria-label="Query">`+
    `<input name="r" style="${field};top:120px" aria-label="Second">`+
    `<button style="${button};top:40px">Go</button></form>${extra}`;
}

export async function handle(request:Request):Promise<Response>{
  const url=new URL(request.url);
  const html=(body:string,init:ResponseInit={})=>new Response(body,{...init,headers:{"content-type":"text/html; charset=utf-8",...(init.headers??{})}});
  const cookie=Object.fromEntries((request.headers.get("cookie")??"").split(/;\s*/).filter(Boolean).map(kv=>{const i=kv.indexOf("=");return [kv.slice(0,i),kv.slice(i+1)];}));
  switch(url.pathname){
    case "/search.html":return html(page("Search",form("get","/results")));
    // The same form on a page with a script: the page has a script session.
    case "/search-scripted.html":return html(page("Search",form("get","/results","<script>document.title='Search';</script>")));
    case "/results":return html(page(`Results: ${escape(url.searchParams.get("q")??"")}`,`<p>q=${escape(url.searchParams.get("q")??"")}</p>`));
    case "/post.html":return html(page("Post",form("post","/posted")));
    case "/posted":{
      if(request.method!=="POST")return html(page("Not a POST",""),{status:405});
      const q=new URLSearchParams(await request.text()).get("q")??"";
      return new Response(null,{status:303,headers:{location:`/results?q=${encodeURIComponent("posted "+q)}`}});
    }
    case "/login.html":return html(page("Sign in",form("post","/login")));
    case "/login":{
      if(request.method!=="POST")return html(page("Not a POST",""),{status:405});
      return new Response(null,{status:303,headers:{location:"/me","set-cookie":"sid=s3cr3t; Path=/; HttpOnly; Max-Age=86400"}});
    }
    case "/me":return html(page(cookie.sid==="s3cr3t"?"Signed in":"Not signed in",""));
    case "/links.html":return html(page("Links",
      `<a href="/results?q=same" style="position:absolute;left:40px;top:40px;font:30px sans-serif">same tab</a>`+
      `<a href="/results?q=blank" target="_blank" style="position:absolute;left:40px;top:120px;font:30px sans-serif">new tab</a>`+
      `<a href="/file.bin" style="position:absolute;left:40px;top:200px;font:30px sans-serif">download</a>`+
      `<a href="/missing" style="position:absolute;left:40px;top:280px;font:30px sans-serif">missing</a>`));
    case "/file.bin":return new Response(new Uint8Array(1024).fill(7),{headers:{"content-type":"application/octet-stream","content-disposition":'attachment; filename="file.bin"'}});
    case "/redirect":return new Response(null,{status:302,headers:{location:"/results?q=moved"}});
    default:return html(page("Not here","<h1>404</h1>"),{status:404});
  }
}

if(import.meta.main){
  const port=Number(Deno.args[0]??0);
  const server=Deno.serve({hostname:"127.0.0.1",port,onListen:({port})=>console.log(`http://127.0.0.1:${port}/`)},handle);
  await server.finished;
}
