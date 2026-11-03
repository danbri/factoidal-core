// The local broker provides native network access. A static deployment needs
// a CORS-capable endpoint; this module does not silently bypass that boundary.
export async function fetchResource(url,{signal,maxBytes=1048576,fetchImpl=fetch,endpoint='/resource'}={}){
  const response=await fetchImpl(`${endpoint}?url=${encodeURIComponent(url)}&maxBytes=${maxBytes}`,{signal,credentials:'same-origin'});
  if(!response.ok){let detail=await response.text();throw Error(detail||`Resource broker HTTP ${response.status}`);}
  const bytes=new Uint8Array(await response.arrayBuffer());
  if(bytes.length>maxBytes)throw Error('Resource exceeds transport limit');
  return {requestedURL:url,url:response.headers.get('X-Factoidal-Resource-URL')??url,contentType:response.headers.get('X-Factoidal-Content-Type')??'',bytes,
    text(){try{return new TextDecoder('utf-8',{fatal:true}).decode(bytes);}catch{throw Error('This MVP requires UTF-8 document bytes');}}};
}
