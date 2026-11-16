// Hub copies (2026-11-16): the Hub can not read other sites (no fetch proxy, and their servers
// do not allow it with CORS), so the deploy puts copies of a few openly licensed pages beside
// this file (copies/, made by tools/hub-copies.mjs from the snapshots in danbri/factoidal-builds
// third_party/realpages/, listed in labs/demos/foafnaut/realpages/hub-copies.json). A host asks
// here for the bytes of an address of another site; the answer is the copy's bytes under the
// original address, or nothing. The engine decides what the bytes mean, as for any page.
// The list is fetched once, and only when a page of another site is asked for: a visit that
// stays on this site costs nothing.
const base=new URL('./copies/',import.meta.url).href;
let index;
const load=()=>index??=fetch(base+'index.json').then(r=>r.ok?r.json():{}).catch(()=>({}));

/** The copy of `url` (redirects followed, at most 5): `{url, href, type, copy}` where `url` is
the address the copy answers for, `href` the copy's file on this site, `type` the recorded
Content-Type and `copy` the page's record (title, licence, attribution, fetched); or undefined. */
export async function copyOf(url){
  let at=String(url).split('#')[0];
  const known=await load();
  for(let hop=0;hop<6;hop++){
    const entry=known.urls?.[at];
    if(!entry)return undefined;
    if(entry.location){at=new URL(entry.location,at).href;continue;}
    return {url:at,href:base+entry.file,type:entry.type??'',copy:(known.copies??[]).find(c=>c.id===entry.id)};
  }
  return undefined;
}

/** The bytes of the copy of `url`: `{url, bytes, contentType, copy}`, or undefined. */
export async function fetchCopy(url){
  const found=await copyOf(url);
  if(!found)return undefined;
  const response=await fetch(found.href);
  if(!response.ok)return undefined;
  return {url:found.url,bytes:new Uint8Array(await response.arrayBuffer()),contentType:found.type,copy:found.copy};
}

/** Every page with a copy: `[{id, url, title, licence, attribution, fetched}]`. */
export async function copyList(){return (await load()).copies??[];}

// Reading another site directly (2026-11-16). A page on the Hub may read another site when
// that site allows it with CORS (Access-Control-Allow-Origin): that is the host browser's
// own rule, not a proxy, and no credentials are sent. Wikimedia sites allow it on their REST
// API: an article address (https://LANG.wikipedia.org/wiki/TITLE, the mobile host LANG.m...,
// and the other Wikimedia projects) is read from /api/rest_v1/page/html/TITLE, whose HTML has
// <base href="//LANG.wikipedia.org/wiki/">, so its links and images resolve to the real site.
// Other sites are tried as they are (some allow it: W3C, WHATWG, RFC Editor, PEPs, CommonMark,
// CNN lite, wttr.in on 2026-11-16); an origin that refuses once is not asked again in this page.
const wikimedia=/^([a-z0-9-]+)(?:\.m)?\.(wikipedia|wiktionary|wikisource|wikibooks|wikiquote|wikivoyage|wikinews|wikiversity)\.org$/;
/** The Wikimedia REST address of an article address, or undefined. */
export function wikimediaRest(url){
  let u;try{u=new URL(url);}catch{return undefined;}
  const m=wikimedia.exec(u.hostname);
  if(u.protocol!=='https:'||!m||!u.pathname.startsWith('/wiki/')||u.pathname.length<=6)return undefined;
  return `https://${m[1]}.${m[2]}.org/api/rest_v1/page/html/${u.pathname.slice(6)}`;
}
/** The article address a Wikimedia address stands for: the desktop host, no query. */
const wikimediaArticle=url=>{const u=new URL(url),m=wikimedia.exec(u.hostname);return `https://${m[1]}.${m[2]}.org${u.pathname}`;};
const refused=new Set();
/** The bytes of `url` of another site: the Hub's copy, else a direct read the site allows (CORS).
`{url, bytes, contentType, copy?, via}`; undefined when neither works. */
export async function fetchOutside(url){
  // The answer keeps the address's fragment: the page is shown at it, as in any browser.
  const hash=(()=>{try{return new URL(url).hash;}catch{return '';}})();
  const got=await fetchOutsideBytes(url);
  if(!got||!hash)return got;
  const u=new URL(got.url);if(!u.hash)u.hash=hash;
  return {...got,url:u.href};
}
async function fetchOutsideBytes(url){
  const copy=await fetchCopy(url);
  if(copy)return {...copy,via:'copy'};
  let u;try{u=new URL(url);}catch{return undefined;}
  if(u.protocol!=='https:'&&u.protocol!=='http:')return undefined;
  const rest=wikimediaRest(url),target=rest??url,origin=new URL(target).origin;
  if(refused.has(origin))return undefined;
  try{
    const response=await fetch(target,{mode:'cors',credentials:'omit',referrerPolicy:'no-referrer'});
    if(!response.ok)return undefined;
    return {url:rest?wikimediaArticle(url):(response.url||url),bytes:new Uint8Array(await response.arrayBuffer()),
      contentType:response.headers.get('content-type')??'',via:rest?'wikimedia-api':'cors'};
  }catch{refused.add(origin);return undefined;}
}
