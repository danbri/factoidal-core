// Frame time of the CPU backend (SVGRaster.lean), native and Wasm
// (docs/designissues/2026-11-08-cpu-render-backend.md, section 9).
//
// For each page: the time of a render without CPU pixels (what a GPU host asks Lean for)
// and with cpu:true (the same, plus the CPU pixels); the difference is the CPU draw. Both
// as one frame of the view (no shell) and as the two layers of a band (shell, layers:true:
// the chrome and up to 512 rows each side of the view), which a scroll inside the band
// reuses with no Lean call. Native through web-render-native --document-bin, Wasm through
// the engine module's web_document_call_bin in Node.
//
// node labs/demos/foafnaut/cpu_render_bench.mjs [--pages index.html,status.html,svg-gallery.html]
//   [--width 800] [--height 600] [--repeat 3] [--native PATH] [--wasm DIR]
import fs from 'node:fs';import path from 'node:path';import os from 'node:os';
import {spawnSync} from 'node:child_process';import {fileURLToPath,pathToFileURL} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const lab=fileURLToPath(new URL('.',import.meta.url)),root=path.resolve(lab,'../../..');
const pages=opt('--pages','index.html,status.html,svg-gallery.html').split(',');
const width=Number(opt('--width','800')),height=Number(opt('--height','600')),repeat=Number(opt('--repeat','3'));
const native=opt('--native',path.join(lab,'.build/web-render/web-render-native')),wasmDir=opt('--wasm',path.join(lab,'.build/web-render/engines'));
const font=path.join(root,'third_party/fonts/noto-sans/NotoSans-Regular.ttf');
const forms={frame:{op:'render',textScalePercent:150,checks:false},
  band:{op:'render',textScalePercent:150,checks:false,layers:true,shell:{tabs:[{title:''}],active:0,scroll:0}}};
const median=xs=>[...xs].sort((a,b)=>a-b)[Math.floor(xs.length/2)];
const rows=[];
const work=fs.mkdtempSync(path.join(os.tmpdir(),'cpu-render-bench-'));
try{
  if(fs.existsSync(native))for(const page of pages)for(const [form,options] of Object.entries(forms)){
    const ms={};
    for(const cpu of [false,true]){
      const file=path.join(work,'options.json');fs.writeFileSync(file,JSON.stringify({...options,...(cpu?{cpu:true}:{})}));
      const r=spawnSync(native,[path.join(lab,'pages',page),String(width),String(height),'--document-bin',file,font,path.join(work,'out.bin'),String(repeat)],{encoding:'utf8',timeout:900000});
      const answer=JSON.parse(r.stdout.trim().split('\n').at(-1));ms[cpu?'cpu':'gpu']=median(answer.us)/1000;
    }
    rows.push({engine:'native',page,form,leanMs:+ms.gpu.toFixed(1),withCpuMs:+ms.cpu.toFixed(1),cpuDrawMs:+(ms.cpu-ms.gpu).toFixed(1)});
    console.log(JSON.stringify(rows.at(-1)));
  }
  if(fs.existsSync(path.join(wasmDir,'web-render.mjs'))){
    const {default:createModule}=await import(pathToFileURL(path.join(wasmDir,'web-render.mjs')));
    const module=await createModule();
    const bytes=fs.readFileSync(font),input=module._malloc(bytes.length);module.HEAPU8.set(bytes,input);
    const loaded=module.ccall('web_document_font_call_bin','number',['number','number','string','string','number'],[input,bytes.length,'Noto Sans','cli',0]);
    module.ccall('web_render_free',null,['number'],[loaded]);module._free(input);
    const call=(html,options)=>{const p=module.ccall('web_document_call_bin','number',['string','string','number','number','number'],[html,JSON.stringify(options),width,height,0]);
      const size=new DataView(module.HEAPU8.buffer,p,4).getUint32(0,true);module.ccall('web_render_free',null,['number'],[p]);return size;};
    for(const page of pages)for(const [form,options] of Object.entries(forms)){
      const html=fs.readFileSync(path.join(lab,'pages',page),'utf8'),ms={};
      for(const cpu of [false,true]){
        const times=[];
        for(let i=0;i<=repeat;i++){const t=performance.now();call(html,{...options,...(cpu?{cpu:true}:{}),repeat:i});times.push(performance.now()-t);}
        ms[cpu?'cpu':'gpu']=median(times.slice(1));
      }
      rows.push({engine:'wasm',page,form,leanMs:+ms.gpu.toFixed(1),withCpuMs:+ms.cpu.toFixed(1),cpuDrawMs:+(ms.cpu-ms.gpu).toFixed(1)});
      console.log(JSON.stringify(rows.at(-1)));
    }
  }
}finally{fs.rmSync(work,{recursive:true,force:true});}
if(!rows.length)console.log('NOT RUN: no native engine and no Wasm engine');
