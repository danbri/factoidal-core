// Vetted font-library data transport only. Request segmentation and CSS stay in Lean.
import {spawn} from 'node:child_process';
import {stat} from 'node:fs/promises';
import {dirname,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
const lab=resolve(dirname(fileURLToPath(import.meta.url)),'..');
const limits={requests:4096,word:65536,text:1048576,output:16777216};
const bytes=value=>Buffer.byteLength(value,'utf8');

export function validateFontRequests(value){
  if(!value||value.schema!=='factoidal-font-requests-v1'||!Array.isArray(value.requests)||value.requests.length>limits.requests)
    throw Error('font broker: expected bounded factoidal-font-requests-v1');
  const seen=new Set();let textBytes=0;
  for(const request of value.requests){
    if(!request||typeof request.family!=='string'||bytes(request.family)>256||!request.family||
      typeof request.text!=='string'||!request.text||bytes(request.text)>limits.word||request.text.includes('\0')||
      !Number.isInteger(request.pixelSize)||request.pixelSize<1||request.pixelSize>512)
      throw Error('font broker: invalid family, text or integer pixel size');
    // JSON strings can contain unpaired UTF-16 surrogates; never let replacement
    // characters change the text that Lean asked the font library to shape.
    if(Buffer.from(request.text,'utf8').toString('utf8')!==request.text)
      throw Error('font broker: text is not Unicode scalar values');
    textBytes+=bytes(request.text);
    if(textBytes>limits.text)throw Error('font broker: aggregate text exceeds 1MiB');
    const key=JSON.stringify([request.family.toLowerCase(),request.pixelSize,request.text]);
    if(seen.has(key))throw Error('font broker: duplicate request');
    seen.add(key);
  }
  return value.requests;
}

function runShape(adapter,args){return new Promise((resolvePromise,reject)=>{
  const child=spawn(adapter,args,{stdio:['ignore','pipe','pipe']});
  const chunks=[];let size=0,error='',done=false;
  const finish=(problem,result)=>{if(done)return;done=true;clearTimeout(timer);problem?reject(problem):resolvePromise(result);};
  const timer=setTimeout(()=>{child.kill('SIGKILL');finish(Error('font broker: shaping timeout'));},30000);
  child.stdout.on('data',chunk=>{size+=chunk.length;if(size>limits.output){child.kill('SIGKILL');finish(Error('font broker: shaped record exceeds 16MiB'));}else chunks.push(chunk);});
  child.stderr.on('data',chunk=>{if(error.length<4096)error+=chunk.toString('utf8').slice(0,4096-error.length);});
  child.on('error',problem=>finish(problem));
  child.on('close',code=>{if(code!==0){finish(Error('font broker: '+(error.trim()||`adapter exited ${code}`)));return;}
    try{finish(null,JSON.parse(Buffer.concat(chunks).toString('utf8')));}catch{finish(Error('font broker: adapter returned invalid JSON'));}
  });
});}

/** Exact single-family binding, not CSS fallback or font matching. Defaults use
 * the actual local Arial file. No font bytes are copied into the repository. */
export function createFontBroker({adapter=resolve(lab,'.build/font-shape'),fonts}={}){
  const configured=fonts??{'Arial':process.env.FACTOIDAL_FONT_FILE??'/System/Library/Fonts/Supplemental/Arial.ttf'};
  const bindings=new Map(Object.entries(configured).map(([family,path])=>[family.toLowerCase(),resolve(path)]));
  const cache=new Map();let cacheBytes=0,queue=Promise.resolve();
  async function shape(value){
    const requests=validateFontRequests(value);
    if(requests.length===0)return [];
    const families=new Set(requests.map(request=>request.family.toLowerCase()));
    if(families.size!==1)throw Error('font broker: one exact font family per document supported');
    const fontPath=bindings.get(requests[0].family.toLowerCase());
    if(!fontPath)throw Error(`font broker: no explicit font file for family ${requests[0].family}`);
    const info=await stat(fontPath);
    const records=[];let totalBytes=2;
    for(const request of requests){
      const key=JSON.stringify([fontPath,info.size,info.mtimeMs,info.ctimeMs,request.pixelSize,request.text]);
      let entry=cache.get(key);
      if(!entry){
        const data=await runShape(adapter,[fontPath,request.text,String(request.pixelSize)]);
        if(data.schema!=='factoidal-font-data-v1'||data.family?.toLowerCase()!==request.family.toLowerCase()||
          data.text!==request.text||data.bitmapPixelSize!==request.pixelSize)
          throw Error('font broker: supplied file family/text/size differs from Lean request');
        if(data.direction!=='ltr')throw Error('font broker: horizontal LTR required');
        if(!Array.isArray(data.glyphs)||data.glyphs.some(glyph=>glyph.id===0))
          throw Error('font broker: missing glyph requires explicit fallback policy');
        entry={data,bytes:bytes(JSON.stringify(data))};
        // Bounded whole-record LRU. The final typed Lean decoder checks identity,
        // geometry, source clusters, resource counts and aggregate budgets again.
        while(cacheBytes+entry.bytes>limits.output&&cache.size){const oldest=cache.keys().next().value;cacheBytes-=cache.get(oldest).bytes;cache.delete(oldest);}
        if(entry.bytes<=limits.output){cache.set(key,entry);cacheBytes+=entry.bytes;}
      }else{cache.delete(key);cache.set(key,entry);}
      totalBytes+=entry.bytes+(records.length?1:0);
      if(totalBytes>limits.output)throw Error('font broker: aggregate data exceeds 16MiB');
      records.push(entry.data);
    }
    return records;
  }
  // One shaping job at a time also bounds concurrent HTTP callers. Failed work
  // must not poison the queue for the next edited document.
  return value=>{const result=queue.then(()=>shape(value));queue=result.catch(()=>{});return result;};
}
