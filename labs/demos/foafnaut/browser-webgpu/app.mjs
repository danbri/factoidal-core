import './shader-editor.mjs';
// UI/file/canvas transport only. No SVG geometry or drawing decisions here.
class SvgGpuLab extends HTMLElement{
 #worker;#serial=0;#busy=false;#dirty=false;#hasFrame=false;#running=0;#queued=false;#manual=false;
 connectedCallback(){
  this.innerHTML=`<main><header><div><p class="eyebrow">FACTOIDAL / SOLVING</p><h1>Solving<br><span>An SVG-scene rendering pipeline.</span></h1><p class="intro">One layered SVG scene, two rendering backends. Compare the browser renderer with Lean-generated WebGPU output.</p></div><span class="badge">LOCAL EXPERIMENT</span></header>
  <div class="flow" aria-label="Rendering pipeline"><span>One SVG scene</span><b>→</b><span>Web Platform SVG</span><b>│</b><span>Lean · WASM → WGSL → WebGPU</span></div>
  <section class="workspace"><div class="editor-panel"><div class="toolbar"><label>Scene <select id="fixture"><option value="solving-browser-scene.svg">Solving · layered browser view</option><option value="gallery.svg">Painted shapes</option><option value="affine.svg">Affine transformations</option><option value="linear-paths.svg">Paths & winding</option></select></label><button id="open">Open SVG</button><input id="file" type="file" accept=".svg,image/svg+xml" hidden></div><div class="editor-tabs" role="tablist" aria-label="Source editor"><button id="svg-tab" role="tab" aria-selected="true">SVG</button><button id="wgsl-tab" role="tab" aria-selected="false">WGSL / GPU</button></div><div id="svg-pane"><label class="sr-only" for="source">Editable SVG source</label><textarea id="source" spellcheck="false" aria-describedby="editor-hint"></textarea><div class="editor-footer"><small id="editor-hint">⌘ / Ctrl + Enter to render · local files stay on this machine</small><button class="primary" id="render">Render scene</button></div></div><shader-editor id="wgsl-pane" hidden></shader-editor></div>
  <div class="outputs"><div class="output-panel"><div class="output-title"><h2>Web Platform · SVG</h2><span class="backend-tag">same source</span></div><div class="canvas-wrap"><img id="platform" alt="Scene rendered by the browser SVG implementation" hidden><p id="platform-placeholder">Waiting for the first render…</p></div><p class="backend-caption">Browser SVG renderer · structured groups and paths</p></div><div class="output-panel"><div class="output-title"><h2>Solving · WebGPU</h2><button id="download" disabled>Save PNG</button></div><div class="canvas-wrap"><canvas id="canvas" width="640" height="420" aria-label="Rendered SVG pixels"></canvas><p id="placeholder">Loading the Lean renderer…</p></div><p id="status" role="status" aria-live="polite">Preparing the first scene…</p><div class="metrics" id="metrics"></div></div></div></section>
  <section class="notes"><article><h2>One scene model, two backends</h2><p>The layered document is SVG. The browser renders its groups directly. Lean parses that same document, computes geometry, generates WGSL and specifies GPU commands. The host transfers bytes and presents pixels; it does not reconstruct shapes.</p></article><article><h2>What this experiment establishes</h2><p>It compares two renderers from one source and exposes Lean’s submitted shader. Selected GPU pixels are checked against Lean’s sampler. This is a restricted SVG profile, not full SVG conformance or a proof of renderer equivalence.</p></article></section>
  <details><summary>Inspect the Lean scene tree, shader and runtime evidence</summary><div class="inspect"><section><h2>Retained scene tree from Lean</h2><p>Group transforms are local SVG matrices in [a, b, c, d, e, f] order. The current GPU path lowers these groups to paint items.</p><pre id="scene-tree">Render a scene to inspect its Lean display tree.</pre></section><section><h2>Rendered WGSL module</h2><pre id="shader">Render a scene to inspect its shader.</pre></section><section><h2>Frame evidence</h2><pre id="evidence"></pre><a href="./provenance.json" target="_blank" rel="noopener">Runtime/source hashes and artifact scope</a></section></div></details><footer>Experimental local build · Unsupported SVG features produce errors; no silent renderer fallback.</footer></main>`;
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
 disconnectedCallback(){this.#worker?.terminate();const url=this.q?.('platform')?.dataset.url;if(url)URL.revokeObjectURL(url);}
 #invalidate(){this.#serial++;this.#dirty=true;this.#hasFrame=false;this.q('download').disabled=true;this.q('canvas').hidden=true;this.q('placeholder').hidden=false;this.q('placeholder').textContent='Source changed. Render to show the new result.';this.q('platform').hidden=true;this.q('platform-placeholder').hidden=false;this.q('platform-placeholder').textContent='Render the scene to compare both backends.';this.q('status').textContent='Source changed — previous output cleared.';this.q('metrics').replaceChildren();this.q('scene-tree').textContent='Render to inspect the Lean scene tree.';this.q('shader').textContent='Render to inspect the current source.';this.q('evidence').textContent='';}
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
  const url=URL.createObjectURL(new Blob([this.q('source').value],{type:'image/svg+xml'}));const previous=this.q('platform').dataset.url;if(previous)URL.revokeObjectURL(previous);this.q('platform').dataset.url=url;this.q('platform').src=url;this.q('platform').hidden=false;this.q('platform-placeholder').hidden=true;
  context.putImageData(new ImageData(new Uint8ClampedArray(d.rgba),d.width,d.height),0,0);c.hidden=false;this.q('placeholder').hidden=true;this.#hasFrame=true;this.q('download').disabled=false;
  this.q('status').dataset.error='false';this.q('status').textContent=`Rendered with ${d.adapter.vendor||'browser'} WebGPU · ${d.manualShader?'MANUAL WGSL — Lean pixel checks disabled':`${d.checks} sample pixels checked against Lean`}${d.adapter.isFallbackAdapter?' · fallback adapter':''}`;
  this.q('metrics').replaceChildren(...[`${d.width} × ${d.height} px`,`${d.primitives} primitives`,`${Math.round(d.time.compileMs)} ms compile`,`${Math.round(d.time.drawAndReadbackMs)} ms draw + readback`].map(text=>{const s=document.createElement('span');s.textContent=text;return s;}));
  this.q('wgsl-pane').setGenerated(d.generatedWGSL);this.q('wgsl-pane').markRendered(d.manualShader);
  this.q('scene-tree').textContent=d.tree?JSON.stringify(d.tree,null,2):'No tree data in this artifact. Rebuild the SVG engine; trees above 16,384 nodes omit the optional inspector data.';this.q('shader').textContent=d.wgsl;const {rgba,wgsl,generatedWGSL,tree,...facts}=d;this.q('evidence').textContent=JSON.stringify(facts,null,2);
 }
}
customElements.define('svg-gpu-lab',SvgGpuLab);
