// The reference pixels of the Canvas 2D scenes (canvas2d-scenes.js), drawn by headless
// Chrome: writes canvas2d-reference.json, which canvas2d_test.ts compares the Foafnaut
// engine's pixels with (record docs/designissues/2026-11-08-canvas-2d.md).
// Run: node canvas2d_reference.mjs   (CHROME=/path/to/chrome overrides the browser)
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import {execFileSync} from 'node:child_process';
import zlib from 'node:zlib';
import {fileURLToPath} from 'node:url';
const here=path.dirname(fileURLToPath(import.meta.url));
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: canvas2d_reference.mjs needs Chrome (set CHROME)');process.exit(0);}
// With log, one scene a task (setTimeout), so an engine with a step budget a task
// (BubblePopJS) draws them all; Chrome's reference draws them in one script.
export const scenePage=(scenes,log)=>`<!doctype html><html><body><pre id="out"></pre><script>
${scenes}
const hexes='0123456789abcdef',tab=[];
for(let i=0;i<256;i++)tab.push(hexes[i>>4]+hexes[i&15]);
const out={};
function scene([name,draw]){
  const cv=document.createElement('canvas');cv.width=48;cv.height=48;
  const c=cv.getContext('2d');draw(c);
  const d=c.getImageData(0,0,48,48).data,parts=[];
  for(let i=0;i<d.length;i++)parts.push(tab[d[i]]);
  const h=parts.join('');
  ${log?"console.log('scene '+name+' '+h);":"out[name]=h;"}
}
${log?"canvas2dScenes.forEach((s,i)=>setTimeout(()=>scene(s),i));":"canvas2dScenes.forEach(scene);document.getElementById('out').textContent=JSON.stringify(out);"}
</script></body></html>`;
if(process.argv[1]===fileURLToPath(import.meta.url)){
  const work=fs.mkdtempSync(path.join(os.tmpdir(),'canvas2d-ref-'));
  const file=path.join(work,'scenes.html');
  fs.writeFileSync(file,scenePage(fs.readFileSync(path.join(here,'canvas2d-scenes.js'),'utf8'),false));
  const dom=execFileSync(CHROME,['--headless=new','--disable-gpu','--force-color-profile=srgb',`--user-data-dir=${path.join(work,'profile')}`,'--dump-dom',`file://${file}`],{encoding:'utf8',maxBuffer:1<<26});
  const json=/<pre id="out">([^<]*)<\/pre>/.exec(dom)?.[1];
  if(!json)throw Error('Chrome gave no pixels');
  const version=execFileSync(CHROME,['--version'],{encoding:'utf8'}).trim();
  // Each scene's RGBA as raw DEFLATE in Base64 (about 20 KB for the 27 scenes, not 500 KB of hex).
  const scenes=Object.fromEntries(Object.entries(JSON.parse(json.replaceAll('&quot;','"')))
    .map(([k,h])=>[k,zlib.deflateRawSync(Buffer.from(h,'hex'),{level:9}).toString('base64')]));
  fs.writeFileSync(path.join(here,'canvas2d-reference.json'),JSON.stringify({browser:version,size:48,encoding:'RGBA, raw DEFLATE (RFC 1951), Base64',scenes},null,1)+'\n');
  fs.rmSync(work,{recursive:true,force:true});
  console.log('canvas2d-reference.json from',version);
}
