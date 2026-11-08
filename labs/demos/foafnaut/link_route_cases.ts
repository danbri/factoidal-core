// Links for the differential test of the link rules (WebRoute.lean, link_route_test.ts):
// relative and absolute links of the site, other sites, every foafnaut: page and command,
// mailto:, javascript:, data: and odd ones, on the pages and sites of both hosts.

export type LinkCase={href:string;base:string;origin:string;pages:string;files:boolean};

const hubOrigin="https://danbri.github.io",hubPages=hubOrigin+"/factoidal-core/web/hub/foafnaut/pages/";
const localOrigin="http://127.0.0.1:8123",localPages=localOrigin+"/web/hub/foafnaut/pages/";
const nativePages="file:///Users/someone/factoidal-core/labs/demos/foafnaut/pages/";

/** The sites and the pages a link is on. */
export const places:{origin:string;pages:string;files:boolean;bases:string[]}[]=[
  {origin:hubOrigin,pages:hubPages,files:false,bases:[hubPages+"index.html",hubPages+"deep/dir/page.html?x=1#top","foafnaut:sparql/q=ASK"]},
  {origin:localOrigin,pages:localPages,files:false,bases:[localPages+"index.html"]},
  {origin:"",pages:nativePages,files:true,bases:[nativePages+"index.html","https://example.org/dir/page.html?q#f","foafnaut:graph"]},
];

const builtin=["graph","bookmarks","history","settings","wasm","sparql","help"];
const commands=["back","forward","reload","new","close","home","source","theme","zoom","bookmark","unbookmark","pod","sync","sparql-step","classic"];

function hrefsFor(origin:string):string[]{
  const out:string[]=[];
  for(const name of [...builtin,...commands,"nothing","Graph",""]){
    out.push(`foafnaut:${name}`,`foafnaut:${name}/`,`foafnaut:${name}/x`,`FOAFNAUT:${name}`,` foafnaut:${name} `,`foafnaut:${name}\n`);
  }
  out.push("foafnaut:sparql/q=SELECT+*+WHERE+%7B%7D&step=2","foafnaut:sparql/q=a/b","foafnaut:wasm/hello.wasm#main","foafnaut:wasm/sub/x.wasm",
    "foafnaut:theme/arcade","foafnaut:zoom/150","foafnaut:bookmark/a,b","Foafnaut:graph","foafnaut:/graph","foafnaut:graph#x","foafnaut:graph?x",
    "foaf\tnaut:graph","\u0001foafnaut:graph");
  const paths=["","/","a.html","./a.html","../a.html","../../../../../x.html","/root.html","dir/","a/./b/../c.html","a b.html","a%20b.html",
    "\u00e9.html","\u4e2d\u6587.html","a\\b.html","%2e%2e/x","a/%2e/b","a/%2E%2e/b","x%2ey.html","a\"b","a<b>c","a`b","a{b}c","a^b","a|b","a[b]",
    "a'b","~user/x","a:b","./a:b","%","%zz","a%2fb","a;p=1/b","a//b",".","..","./","../"];
  const tails=["","?q=1","?a=1&b=2","?a b","?it's","?\"q\"","?<q>","?\u00e9","#f","#a b","#\u00e9","#`x`","?q#f","?","#"];
  for(const path of paths)for(const tail of tails)out.push(path+tail);
  out.push("?only","#only","  status.html\n","sta\ttus.html","\tstatus.html\r\n"," ","\u0000x.html","x.html\u0000");
  const hosts=[origin.replace(/^https?:\/\//,""),"example.org","EXAMPLE.org","github.com","www.github.com","GitHub.com","sub.github.com","duckduckgo.com",
    "localhost:8080","127.0.0.1","127.0.0.1:8123","0x7f.0.0.1","1.2.3","256.1.1.1","01.2.3.4","1.2.3.4.","[::1]","user@example.org","user:pw@example.org",
    "@example.org","example.org:99999","example.org:abc","example.org:","example.org:80","example.org:443","example.org:0080","a..b","a.b.","under_score.org",
    "exa mple.org","ex%41mple.org","\u00e9xample.org","xn--xample-9ua.org","example.org.","a-b.c-d.org","EXAMPLE.ORG:8080"];
  for(const host of hosts)for(const scheme of ["http","https","HTTPS"])for(const rest of ["","/","/a/../b.html","/x?q=1#f","/a b"])
    out.push(`${scheme}://${host}${rest}`,`//${host}${rest}`);
  out.push(`${origin}/web/hub/foafnaut/pages/status.html`,`${origin.toUpperCase()}/A.html`,`${origin}:443/x`,`${origin}:80/x`);
  out.push("http:x","http:/x","https:x","http:\\\\example.org\\x","https:\\/example.org/x","http:///example.org/x","http://","https://?q","HTTP://EXAMPLE.ORG/A",
    "http://example.org\\a\\b?c\\d#e\\f","https://example.org/a/../../b","https://example.org?q","https://example.org#f");
  out.push("mailto:someone@example.org","MAILTO:someone@example.org","mailto:a b@example.org","mailto:?subject=hi there","mailto:x@y.org#f g",
    "mailto:\u00e9@example.org","tel:+1 234 5678","tel:+44","sms:123","sms:123?body=hello world","Tel:1");
  out.push("javascript:alert(1)","JavaScript:void(0)"," javascript:x","java\nscript:alert(1)","data:text/html,<p>x</p>","DATA:,x",
    "data:image/png;base64,AAAA","file:///etc/passwd","file://localhost/etc/hosts","FILE:///x","file:/x","file:x","file://host/x","file://LOCALHOST/x",
    "file:///a/../b","file:///a%20b","ftp://example.org/x","about:blank","about:config","blob:https://example.org/uuid","ws://example.org/","wss://x",
    "chrome://settings","intent://x#Intent;end","x-unknown:y","c:/windows","urn:isbn:1","news:comp.lang","view-source:https://x");
  return out;
}

/** Every link of every place, a few thousand. */
export function linkCases():LinkCase[]{
  const cases:LinkCase[]=[];
  for(const place of places)for(const base of place.bases)for(const href of hrefsFor(place.origin||"https://example.org"))
    cases.push({href,base,origin:place.origin,pages:place.pages,files:place.files});
  return cases;
}
