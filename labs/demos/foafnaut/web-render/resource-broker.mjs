// Native HTTP byte capability. This module does not parse document contents.
export class ResourceError extends Error {
  constructor(message,status=502){super(message);this.status=status;}
}
export function resourceURL(value,base){
  let url;try{url=new URL(value,base);}catch{throw new ResourceError('Invalid resource URL',400);}
  if(!['http:','https:'].includes(url.protocol))throw new ResourceError('Only HTTP and HTTPS URLs are supported',400);
  if(url.username||url.password)throw new ResourceError('URLs with credentials are not supported',400);
  url.hash='';return url;
}
export async function fetchResourceBytes(value,{signal,maxBytes=1048576,timeout=20000,fetchImpl=fetch}={}){
  const requestedURL=resourceURL(value).href;
  const deadline=AbortSignal.timeout(timeout),combined=signal?AbortSignal.any([signal,deadline]):deadline;
  let url=new URL(requestedURL),response;
  try{
    for(let redirects=0;;redirects++){
      response=await fetchImpl(url,{signal:combined,redirect:'manual',headers:{Accept:'*/*','User-Agent':'Factoidal-Lean-Browser-MVP/1'},credentials:'omit'});
      if(![301,302,303,307,308].includes(response.status))break;
      const location=response.headers.get('location');await response.body?.cancel();
      if(!location)throw new ResourceError('Redirect has no Location');
      if(redirects>=8)throw new ResourceError('Too many resource redirects');
      url=resourceURL(location,url);
    }
    if(!response.ok){await response.body?.cancel();throw new ResourceError(`Resource HTTP ${response.status}`,response.status===404?404:502);}
    const length=Number(response.headers.get('content-length'));
    if(length>maxBytes){await response.body?.cancel();throw new ResourceError(`Resource exceeds ${maxBytes} byte limit`,413);}
    const chunks=[];let size=0;
    for await(const chunk of response.body??[]){size+=chunk.byteLength;if(size>maxBytes)throw new ResourceError(`Resource exceeds ${maxBytes} byte limit`,413);chunks.push(chunk);}
    const bytes=new Uint8Array(size);let offset=0;for(const chunk of chunks){bytes.set(chunk,offset);offset+=chunk.byteLength;}
    return {requestedURL,url:url.href,contentType:response.headers.get('content-type')??'application/octet-stream',bytes};
  }catch(error){
    if(error instanceof ResourceError)throw error;
    if(deadline.aborted)throw new ResourceError('Resource request timed out',504);
    if(signal?.aborted)throw error;
    throw new ResourceError(`Resource fetch failed: ${error.message??error}`);
  }
}
