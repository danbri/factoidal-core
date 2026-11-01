import './shader-editor.mjs';
// UI/file/canvas transport only. No SVG geometry or drawing decisions here.
class SvgGpuLab extends HTMLElement{
 #worker;#serial=0;#busy=false;#dirty=false;#hasFrame=false;#running=0;#queued=false;#manual=false;
 connectedCallback(){
  this.innerHTML=`<main><header><div><p class="eyebrow">FACTOIDAL / SOLVING</p><h1>Solving<br><span>An SVG-scene rendering pipeline.</span></h1><p class="intro">The native renderer, running in your browser. Edit the markup and watch the same Lean engine turn it into GPU work.</p></div><span class="badge">LOCAL EXPERIMENT</span></header>
  <div class="flow" aria-label="Rendering pipeline"><span>SVG source</span><b>→</b><span>Lean · WASM</span><b>→</b><span>WGSL + render plan</span><b>→</b><span>WebGPU</span></div>
  <section class="workspace"><div class="editor-panel"><div class="toolbar"><label>Scene <select id="fixture"><option value="gallery.svg">Painted shapes</option><option value="affine.svg">Affine transformations</option><option value="linear-paths.svg">Paths & winding</option></select></label><button id="open">Open SVG</button><input id="file" type="file" accept=".svg,image/svg+xml" hidden></div><div class="editor-tabs" role="tablist" aria-label="Source editor"><button id="svg-tab" role="tab" aria-selected="true">SVG</button><button id="wgsl-tab" role="tab" aria-selected="false">WGSL / GPU</button></div><div id="svg-pane"><label class="sr-only" for="source">Editable SVG source</label><textarea id="source" spellcheck="false" aria-describedby="editor-hint"></textarea><div class="editor-footer"><small id="editor-hint">⌘ / Ctrl + Enter to render · local files stay on this machine</small><button class="primary" id="render">Render SVG</button></div></div><shader-editor id="wgsl-pane" hidden></shader-editor></div>
  <div class="output-panel"><div class="output-title"><h2>GPU output</h2><button id="download" disabled>Save PNG</button></div><div class="canvas-wrap"><canvas id="canvas" width="640" height="420" aria-label="Rendered SVG pixels"></canvas><p id="placeholder">Loading the Lean renderer…</p></div><p id="status" role="status" aria-live="polite">Preparing the first scene…</p><div class="metrics" id="metrics"></div></div></section>
  <section class="notes"><article><h2>Same renderer. Different host.</h2><p>Lean parses SVG, computes geometry, generates shaders and specifies GPU commands. The host transports bytes and presents pixels. The browser’s SVG renderer is not used for this output.</p></article><article><h2>What this experiment establishes</h2><p>In generated mode, the existing bridge checks selected GPU pixels against Lean’s expected values. This is a restricted SVG implementation, not full SVG conformance or a proof of every pixel. Rendering uses an offscreen GPU texture and CPU readback for presentation.</p></article></section>
  <details><summary>Inspect the rendered shader and runtime evidence</summary><div class="inspect"><section><h2>Rendered WGSL module</h2><pre id="shader">Render a scene to inspect its shader.</pre></section><section><h2>Frame evidence</h2><pre id="evidence"></pre><a href="./provenance.json" target="_blank" rel="noopener">Runtime/source hashes and artifact scope</a></section></div></details><footer>Experimental local build · Unsupported SVG features produce errors; no silent renderer fallback.</footer></main>`;
  const q=id=>this.querySelector('#'+id);this.q=q;
  for(const which of ['svg','wgsl'])q(which+'-tab').onclick=()=>{for(const mode of ['svg','wgsl']){q(mode+'-pane').hidden=mode!==which;q(mode+'-tab').setAttribute('aria-selected',String(mode===which));}};
  q('wgsl-pane').addEventListener('shader-edit',()=>{this.#manual=true;this.#invalidate();});
  q('wgsl-pane').addEventListener('shader-apply',()=>{this.#manual=true;this.#render(true);});
  q('wgsl-pane').addEventListener('shader-reset',()=>{this.#manual=false;this.#render(false);});
  this.#worker=new Worker(new URL('./worker.mjs',import.meta.url),{type:'module'});
  this.#worker.onmessage=({data})=>this.#receive(data);
  this.#worker.onerror=e=>{this.#setBusy(false);this.#fail(e.message||'Renderer worker failed to load.');};
  q('render').onclick=()=>this.#render();q('fixture').onchange=()=>this.#loadFixture();
  q('source').oninput=()=>{this.#manual=false;q('wgsl-pane').resetDraft();this.#invalidate();};q('source').onkeydown=e=>{if(e.key==='Enter'&&(e.metaKey||e.ctrlKey)){e.preventDefault();this.#render();}};
  q('open').onclick=()=>q('file').click();q('file').onchange=async()=>{
   const f=q('file').files[0];q('file').value='';if(!f)return;
   if(f.size>1048576){this.#fail('SVG files must be at most 1 MiB.');return;}
   try{q('source').value=await f.text();this.#invalidate();this.#render();}catch(e){this.#fail(e.message);}
  };
  q('download').onclick=()=>{if(!this.#hasFrame)return;q('canvas').toBlob(blob=>{if(!blob)return;const u=URL.createObjectURL(blob),a=document.createElement('a');a.href=u;a.download='factoidal-webgpu.png';a.click();setTimeout(()=>URL.revokeObjectURL(u),1000);});};
  this.#loadFixture();
 }
 disconnectedCallback(){this.#worker?.terminate();}
 #invalidate(){this.#serial++;this.#dirty=true;this.#hasFrame=false;this.q('download').disabled=true;this.q('canvas').hidden=true;this.q('placeholder').hidden=false;this.q('placeholder').textContent='Source changed. Render to show the new result.';this.q('status').textContent='Source changed — previous output cleared.';this.q('metrics').replaceChildren();this.q('shader').textContent='Render to inspect the current source.';this.q('evidence').textContent='';}
 #setBusy(value){this.#busy=value;for(const id of ['render','fixture','open','source'])this.q(id).disabled=value;this.q('render').textContent=value?'Rendering…':'Render SVG';}
 #fail(message){this.#hasFrame=false;this.q('download').disabled=true;this.q('canvas').hidden=true;this.q('placeholder').hidden=false;this.q('placeholder').textContent='No render produced';this.q('status').dataset.error='true';this.q('status').textContent=message;this.q('metrics').replaceChildren();this.q('wgsl-pane').fail(message);}
 async #loadFixture(){if(this.#busy)return;this.#manual=false;this.q('wgsl-pane').resetDraft();this.#setBusy(true);this.#invalidate();this.q('status').textContent='Loading scene…';try{const r=await fetch(new URL('./fixtures/'+this.q('fixture').value,import.meta.url));if(!r.ok)throw Error('Fixture unavailable: HTTP '+r.status);this.q('source').value=await r.text();this.#invalidate();}catch(e){this.#fail(e.message);this.#setBusy(false);return;}this.#setBusy(false);this.#render();}
 #render(manual=false){if(this.#busy){this.#queued=true;this.#manual=manual;return;}this.#manual=manual;if(!manual)this.q('wgsl-pane').resetDraft();if(!globalThis.isSecureContext||!navigator.gpu){this.#fail('WebGPU is unavailable. Open this localhost page in a current browser with WebGPU enabled.');return;}
  this.#invalidate();this.#dirty=false;this.#setBusy(true);this.q('status').dataset.error='false';this.q('status').textContent='Lean is compiling SVG and preparing the GPU…';this.q('placeholder').textContent='Rendering through Lean + WebGPU…';
  this.#running=++this.#serial;this.#worker.postMessage({type:'render',id:this.#running,source:this.q('source').value,...(manual?{shaderOverride:this.q('wgsl-pane').source}:{})});
 }
 #receive(d){
  if(d.type==='shader-submitted'){if(d.id===this.#serial)this.q('wgsl-pane').submitted(d.submission,d.id);return;}
  if(d.id!==this.#running)return;this.#setBusy(false);
  if(this.#queued){this.#queued=false;this.#render(this.#manual);return;}
  if(d.id!==this.#serial)return;if(d.type==='error'){this.#fail(d.error);return;}if(d.type!=='frame'||this.#dirty)return;
  const c=this.q('canvas');c.width=d.width;c.height=d.height;const context=c.getContext('2d');if(!context){this.#fail('Canvas pixel presentation unavailable.');return;}
  context.putImageData(new ImageData(new Uint8ClampedArray(d.rgba),d.width,d.height),0,0);c.hidden=false;this.q('placeholder').hidden=true;this.#hasFrame=true;this.q('download').disabled=false;
  this.q('status').dataset.error='false';this.q('status').textContent=`Rendered with ${d.adapter.vendor||'browser'} WebGPU · ${d.manualShader?'MANUAL WGSL — Lean pixel checks disabled':`${d.checks} sample pixels checked against Lean`}${d.adapter.isFallbackAdapter?' · fallback adapter':''}`;
  this.q('metrics').replaceChildren(...[`${d.width} × ${d.height} px`,`${d.primitives} primitives`,`${Math.round(d.time.compileMs)} ms compile`,`${Math.round(d.time.drawAndReadbackMs)} ms draw + readback`].map(text=>{const s=document.createElement('span');s.textContent=text;return s;}));
  this.q('wgsl-pane').setGenerated(d.generatedWGSL);this.q('wgsl-pane').markRendered(d.manualShader);
  this.q('shader').textContent=d.wgsl;const {rgba,wgsl,generatedWGSL,...facts}=d;this.q('evidence').textContent=JSON.stringify(facts,null,2);
 }
}
customElements.define('svg-gpu-lab',SvgGpuLab);
