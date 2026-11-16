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
