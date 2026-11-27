// host-trace.mjs: the boundary trace of a host, for the host contract check (test mode only).
//
// Every host shell is code that is not Lean. The engine describes what it may cross
// (formal/lean4/L4Factoidal/HostContract/Model.lean) and checks recorded traces against that and
// against each other (Trace.lean; the engine op `hostContract`, WebHostContract.lean). This module
// records one line per call of the engine's C ABI: the export, the request's `op`, digests of the
// HTML, the request and the answer, the viewport, and the policy-relaxing fields the request set.
// Nothing here reads a page or decides anything; with no sink the hosts never call it, so a run
// that is not a test pays nothing.
//
// Hosts: labs/demos/foafnaut/native_html_engine.ts (the window, Textnaut, the parity paths; native
// and Wasm builds), docs/web/hub/foafnaut/browser-worker.mjs (the Hub). Check:
// labs/demos/foafnaut/host_contract_check.ts.

/** The request fields with which a host relaxes an engine policy (HostContract.relaxFields). */
export const RELAX_FIELDS=['hostCors','address','network','navigations','liberal','scripting','dangerouslyPermitAudio'];

/** Top-level answer fields that are measurements (HostContract.measureFields): an answer is
digested without them. host_contract_check.ts fails when the engine's list differs from this. */
export const MEASURE_FIELDS=['ns'];

/** An answer as the trace digests it: a JSON object answer without its measurement fields. */
export function comparable(answer) {
  if(typeof answer!=='string'||answer[0]!=='{')return answer;
  try{
    const value=JSON.parse(answer);
    if(!value||typeof value!=='object'||Array.isArray(value)||!MEASURE_FIELDS.some(k=>k in value))return answer;
    for(const k of MEASURE_FIELDS)delete value[k];
    return JSON.stringify(value);
  }catch{return answer;}
}

/** A 64-bit FNV-1a digest as 16 hex digits, of a string (UTF-16 units) or bytes. Not a security
digest: it only has to tell two answers apart in a test. */
export function digest(value) {
  let a=0x811c9dc5,b=0x01000193^0x5bd1e995;
  if(typeof value==='string'){
    for(let i=0;i<value.length;i++){const c=value.charCodeAt(i);a=Math.imul(a^c,0x01000193);b=Math.imul(b^(c+i),0x01000193);}
  }else{
    const bytes=value instanceof Uint8Array?value:new Uint8Array(value);
    for(let i=0;i<bytes.length;i++){const c=bytes[i];a=Math.imul(a^c,0x01000193);b=Math.imul(b^(c+i),0x01000193);}
  }
  return (a>>>0).toString(16).padStart(8,'0')+(b>>>0).toString(16).padStart(8,'0');
}

/** The relaxation fields a request sets: present and relaxing (`scripting` relaxes when false,
the others when not false). */
export function relaxations(request) {
  const out=[];
  for(const k of RELAX_FIELDS){
    if(!(k in request))continue;
    const v=request[k];
    if(k==='scripting'?v===false:v!==false&&v!==undefined&&v!==null)out.push(k);
  }
  return out;
}

/** One trace line for a document call (`web_document_call` or `_bin`). */
export function documentLine(symbol,html,requestJSON,width,height,answer) {
  let request={};
  try{request=JSON.parse(requestJSON);}catch{/* the engine refuses it; recorded as op "" */}
  return {x:symbol,op:typeof request.op==='string'?request.op:'render',h:digest(html),q:digest(requestJSON),
    w:width,ht:height,a:digest(comparable(answer)),f:relaxations(request)};
}

/** One trace line for a byte call (font, image, decode). */
export function bytesLine(symbol,op,bytes,label,answer) {
  return {x:symbol,op,h:'',q:digest(bytes)+digest(label),w:0,ht:0,a:digest(comparable(answer)),f:[]};
}

/** Wrap a host's engine calls (`{text, bytes, font, image?, decode?}`, as native_html_engine.ts
builds them) so that each call adds a line to `sink` (a function). The answers pass unchanged. */
export function traceBackends(backends,sink) {
  const out={
    text:(html,request,width,height)=>{const a=backends.text(html,request,width,height);sink(documentLine('web_document_call',html,request,width,height,a));return a;},
    bytes:(html,request,width,height)=>{const a=backends.bytes(html,request,width,height);sink(documentLine('web_document_call_bin',html,request,width,height,a));return a;},
    font:(bytes,family,sha256,fallback)=>{const a=backends.font(bytes,family,sha256,fallback);sink(bytesLine('web_document_font_call_bin','fontBytes',bytes,`${family} ${sha256} ${fallback}`,a));return a;},
  };
  if(backends.image)out.image=(bytes,key,sha256)=>{const a=backends.image(bytes,key,sha256);sink(bytesLine('web_document_image_call_bin','imageBytes',bytes,`${key} ${sha256}`,a));return a;};
  if(backends.decode)out.decode=(bytes,charset,fallback,locale)=>{const a=backends.decode(bytes,charset,fallback,locale);
    sink(bytesLine('web_document_decode2_call_bin','decode',bytes,`${charset} ${fallback} ${locale}`,a));return a;};
  return out;
}

/** Record the calls a host makes through an Emscripten module's `ccall` (the Hub's hosts call
the Wasm build this way): `module.ccall` is replaced by one that records each call of a document
export, reading the answer from the module's memory before the host frees it. For tests only; a
host that is not traced never calls this. */
export function traceModule(module,sink) {
  const ccall=module.ccall.bind(module);
  const text=pointer=>pointer?module.UTF8ToString(pointer):'';
  const heapBytes=(at,length)=>module.HEAPU8.slice(at,at+length);
  module.ccall=(name,result,types,args)=>{
    const pointer=ccall(name,result,types,args);
    try{
      if(name==='web_document_call')sink(documentLine(name,args[0],args[1],args[2],args[3],text(pointer)));
      else if(name==='web_document_call_bin'){
        const total=pointer?new DataView(module.HEAPU8.buffer,module.HEAPU8.byteOffset+pointer,4).getUint32(0,true):0;
        sink(documentLine(name,args[0],args[1],args[2],args[3],heapBytes(pointer,total)));
      }
      else if(name==='web_document_font_call_bin')sink(bytesLine(name,'fontBytes',heapBytes(args[0],args[1]),`${args[2]} ${args[3]} ${args[4]===2?'web':args[4]===1}`,text(pointer)));
      else if(name==='web_document_image_call_bin')sink(bytesLine(name,'imageBytes',heapBytes(args[0],args[1]),`${args[2]} ${args[3]}`,text(pointer)));
      else if(name==='web_document_decode2_call_bin'||name==='web_document_decode_call_bin')
        sink(bytesLine('web_document_decode2_call_bin','decode',heapBytes(args[0],args[1]),`${args[2]} ${args[3]??''} ${args[4]??''}`,text(pointer)));
    }catch{/* a trace line that can not be made is left out; the check then finds a gap */}
    return pointer;
  };
  return module;
}
