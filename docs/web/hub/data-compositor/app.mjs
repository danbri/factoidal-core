import { DEFAULTS } from './fixtures.mjs';
import '../assets/code-output.mjs';
import { nodeAssurance, wireAssurance, explainEvidence, PROOF_SOURCE } from './assurance.mjs';

const NODES = [
  {id:'turtle',title:'Turtle reader',kind:'INPUT · RDF',color:'#78dfb8',x:24,y:54,description:'People, projects and an RDFS vocabulary.',editable:['turtle']},
  {id:'csvw',title:'CSVW → RDF',kind:'INPUT · TABLE',color:'#b8a1f4',x:24,y:255,description:'CSV values + JSON-LD annotations → triples.',editable:['csv','metadata']},
  {id:'merge',title:'Merge graphs',kind:'COMBINE · RDF',color:'#78dfb8',x:234,y:154,description:'Bring the vocabulary and tabular data together.'},
  {id:'closure',title:'RDFS closure',kind:'INFER · RDF',color:'#78dfb8',x:444,y:154,description:'Domain and subclass rules infer new facts.'},
  {id:'graphs',title:'Named graphs',kind:'ORGANIZE · DATASET',color:'#8bbbf3',x:654,y:154,description:'Keep Turtle, CSV and derived facts addressable.'},
  {id:'query',title:'SPARQL join',kind:'QUERY · TABLE',color:'#edcf88',x:864,y:54,description:'Join names, projects, scores and inferred types.',editable:['query']},
  {id:'filter',title:'Score filter',kind:'FILTER · TABLE',color:'#edcf88',x:864,y:255,description:'An engine-evaluated FILTER controls the shortlist.',editable:['minScore']},
  {id:'xml',title:'Results → XML',kind:'SERIALIZE · XML',color:'#b8a1f4',x:1074,y:255,description:'Standard SPARQL Results XML from Lean.'},
  {id:'xslt',title:'XSLT transform',kind:'TRANSFORM · HTML',color:'#f5b591',x:1284,y:255,description:'A stylesheet turns result bindings into a page.',editable:['stylesheet']},
  {id:'diagnostic',title:'XML diagnostic',kind:'REFUSAL · TEXT',color:'#edcf88',x:1074,y:54,description:'An explicit refusal; the XML consumers do not run.'},
  {id:'report',title:'Pipeline report',kind:'OUTPUT · REPORT',color:'#8bbbf3',x:1494,y:154,description:'Either HTML or a diagnostic, with the selected path recorded.'},
  {id:'html',title:'HTML output',kind:'OUTPUT · VIEWER',color:'#f5b591',x:1284,y:54,description:'The actual stylesheet result, ready to export.'},
];
const EDGES = [['turtle','merge'],['csvw','merge'],['merge','closure'],['turtle','graphs'],['csvw','graphs'],['closure','graphs'],['graphs','query'],['query','filter'],['filter','xml'],['xml','xslt'],['xslt','html'],['xml','diagnostic'],['diagnostic','report'],['html','report']];
const LABELS = {turtle:'Turtle',csv:'CSV',metadata:'CSVW JSON-LD',query:'SPARQL',stylesheet:'XSLT',minScore:'Threshold'};
const escapeHTML = value => String(value).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const termText = value => value == null ? '' : typeof value === 'object' ? (value.value ?? JSON.stringify(value)) : String(value);

class FlowNode extends HTMLElement {
  configure(spec,index,onSelect,onMove){
    this.spec=spec; this.style.left=`${spec.x}px`;this.style.top=`${spec.y}px`;this.style.setProperty('--node-color',spec.color);
    this.innerHTML=`<article class="node" role="group" aria-label="${spec.title} node" data-state="idle"><div class="node-head"><span class="node-number">${String(index+1).padStart(2,'0')}</span><button class="node-title" aria-label="Inspect ${spec.title}">${spec.title}</button><span class="node-state">○</span></div><div class="node-body"><div class="node-description">${spec.description}</div><div class="node-summary">${spec.kind}</div><button class="assurance-badge" hidden></button></div>${index>1?'<i class="socket in"></i>':''}${spec.id!=='report'?'<i class="socket out"></i>':''}</article>`;
    this.onclick=()=>onSelect(spec.id);
    this.querySelector('.assurance-badge').onclick=e=>{e.stopPropagation();onSelect(spec.id,true);};
    this.querySelector('.node-head').onpointerdown=e=>{
      if(e.button!==0)return;e.stopPropagation(); const target=e.currentTarget;target.setPointerCapture(e.pointerId);
      const start={x:e.clientX,y:e.clientY,nx:spec.x,ny:spec.y};
      const move=ev=>onMove(spec,start,ev);
      const up=()=>{target.removeEventListener('pointermove',move);target.removeEventListener('pointerup',up);target.removeEventListener('pointercancel',up);};
      target.addEventListener('pointermove',move);target.addEventListener('pointerup',up);target.addEventListener('pointercancel',up);
    };
  }
  update(stage,selected,showEvidence=false){
    const node=this.querySelector('.node');node.classList.toggle('selected',selected);node.dataset.state=stage?.status??'idle';
    this.querySelector('.node-state').textContent=stage?.status==='done'?'✓':stage?.status==='running'?'◌':stage?.status==='error'?'!':stage?.status==='skipped'?'–':'○';
    const badge=this.querySelector('.assurance-badge');const assurance=nodeAssurance(stage);badge.textContent=assurance.badge;badge.hidden=!showEvidence;badge.dataset.status=assurance.status;badge.setAttribute('aria-label',`${assurance.badge}: explain evidence for ${this.spec.title}`);badge.title='Open the claim, assumptions and proof or test references';
    this.querySelector('.node-summary').textContent=stage?.status==='running'?'Computing…':stage?.summary??this.spec.kind;
  }
}
customElements.define('flow-node',FlowNode);

class DataflowStudio extends HTMLElement {
  connectedCallback(){
    this.inputs={...DEFAULTS};this.stages=new Map();this.selected='turtle';this.inspectTab='turtle';this.outputTab='preview';this.scale=1;this.pan={x:0,y:0};this.result=null;this.busy=false;this.logs=[];this.showEvidence=false;this.selectedWire=null;
    this.innerHTML=`
      <header class="topbar"><div class="identity"><span class="mark">◇</span><div><div class="eyebrow">Factoidal laboratory</div><h1>Data Compositor</h1></div></div><div class="actions"><span class="engine"><b>●</b> Lean → WASM · core 0.27.0</span><button id="reset">Reset inputs</button><button id="run" class="primary">▶ Run flow</button></div></header>
      <section class="intro"><p><strong>Think compositor nodes, with data in the sockets.</strong><br>Parse two sources, infer what follows, join named graphs, filter a table, then turn it into HTML.</p><div class="run-status" data-state="idle" role="status" aria-live="polite"><i class="status-dot"></i><span id="status-text">Ready to compose</span></div></section>
      <div class="toolbar"><label class="threshold">Keep score ≥ <output id="score-value">${escapeHTML(this.inputs.minScore)}</output><input id="score" aria-label="Minimum score" type="range" min="0" max="100" step="1" value="${escapeHTML(this.inputs.minScore)}"><span class="muted">Release to recompute</span></label><div class="view-controls"><label class="evidence-toggle"><input id="evidence-toggle" type="checkbox" aria-describedby="evidence-help"> Evidence <span class="evidence-state">off</span></label><span>NODE EDITOR</span><button class="icon" id="zoom-out" aria-label="Zoom out">−</button><button class="icon" id="zoom-in" aria-label="Zoom in">+</button><button class="icon" id="fit">Fit nodes</button></div></div>
      <section class="canvas" aria-label="Interactive dataflow graph"><div class="world"><svg class="wires" aria-hidden="true"></svg><div class="canvas-note">Two source branches. One reproducible flow.<br>Click a node to inspect its data and operation.</div></div><div class="legend"><span><i style="--c:var(--green)"></i>RDF</span><span><i style="--c:var(--blue)"></i>Dataset</span><span><i style="--c:var(--yellow)"></i>Table</span><span><i style="--c:var(--purple)"></i>XML</span><span><i style="--c:var(--orange)"></i>HTML</span></div><span class="canvas-hint">Drag headers to arrange · drag background to pan · Ctrl/⌘ + wheel to zoom</span></section>
      <div class="assurance-legend" id="evidence-help" hidden><strong>Evidence mode is on.</strong> Select a glowing label for the claim, its limits and source references. Select a dashed link for what is passed and which connection obligations remain open. A checked component is not a proof of the whole flow.</div>
      <div class="error-banner" role="alert"></div>
      <section class="lower"><aside class="inspector"><div class="section-head"><h2 id="inspect-title" tabindex="-1">Turtle reader</h2><span class="kicker">Node inspector</span></div><nav class="tabs inspect-tabs" aria-label="Node inspection"></nav><div class="inspect-body"></div></aside><section class="output-panel"><div class="output-head"><nav class="tabs output-tabs" aria-label="Output views"><button data-tab="preview" class="active">HTML viewer</button><button data-tab="rows">Results table</button><button data-tab="source">HTML source</button><button data-tab="log">Execution log</button></nav><button class="download" id="download" disabled>↓ Save HTML</button></div><div class="output-body"></div></section></section>
      <footer class="stats"><span><b id="done-count">0</b> completed stages</span><span><b id="row-count">—</b> result rows</span><span><b id="run-time">—</b> elapsed</span><span class="scope">Runs locally in a worker. Each node exposes its real operation and evidence; a successful run is not an end-to-end proof.</span></footer>`;
    this.$=s=>this.querySelector(s);this.world=this.$('.world');this.canvas=this.$('.canvas');
    for(const [i,spec] of NODES.entries()){
      const node=document.createElement('flow-node');node.configure({...spec},i,(id,evidence)=>{this.select(id);if(evidence){this.inspectTab='evidence';this.inspect();this.$('#inspect-title').focus();}},(spec,start,event)=>{spec.x=Math.max(0,start.nx+(event.clientX-start.x)/this.scale);spec.y=Math.max(0,start.ny+(event.clientY-start.y)/this.scale);node.style.left=`${spec.x}px`;node.style.top=`${spec.y}px`;this.drawWires();});
      this.world.append(node);
    }
    this.$('#run').onclick=()=>this.run();
    this.$('#evidence-toggle').onchange=e=>{this.showEvidence=e.target.checked;this.$('.evidence-state').textContent=this.showEvidence?'on':'off';this.canvas.classList.toggle('evidence-mode',this.showEvidence);this.$('.assurance-legend').hidden=!this.showEvidence;if(!this.showEvidence)this.selectedWire=null;this.updateNodes();this.fit();this.inspect();};
    this.$('#reset').onclick=()=>{this.inputs={...DEFAULTS};this.$('#score').value=this.inputs.minScore;this.$('#score-value').textContent=this.inputs.minScore;this.inspect();this.run();};
    this.$('#score').oninput=e=>{this.inputs.minScore=e.target.value;this.$('#score-value').textContent=e.target.value;};
    this.$('#score').onchange=()=>{if(this.selected==='filter')this.inspect();this.run();};
    this.$('#zoom-in').onclick=()=>this.zoom(1.16);this.$('#zoom-out').onclick=()=>this.zoom(1/1.16);this.$('#fit').onclick=()=>this.fit();
    this.canvas.onpointerdown=e=>{
      if(e.button!==0||e.target.closest('flow-node')||(this.showEvidence&&e.target.closest('.wire')))return;this.canvas.setPointerCapture(e.pointerId);const start={x:e.clientX,y:e.clientY,...{px:this.pan.x,py:this.pan.y}};
      const move=ev=>{this.pan={x:start.px+ev.clientX-start.x,y:start.py+ev.clientY-start.y};this.transform();};
      const up=()=>{this.canvas.removeEventListener('pointermove',move);this.canvas.removeEventListener('pointerup',up);this.canvas.removeEventListener('pointercancel',up);};
      this.canvas.addEventListener('pointermove',move);this.canvas.addEventListener('pointerup',up);this.canvas.addEventListener('pointercancel',up);
    };
    this.canvas.addEventListener('wheel',e=>{if(e.ctrlKey||e.metaKey){e.preventDefault();this.zoom(e.deltaY<0?1.08:1/1.08);}}, {passive:false});
    this.$('.output-tabs').onclick=e=>{const button=e.target.closest('button');if(button){this.outputTab=button.dataset.tab;this.output();}};
    this.$('#download').onclick=()=>{if(typeof this.result?.html!=='string')return;const url=URL.createObjectURL(new Blob([this.result.html],{type:'text/html'}));const a=document.createElement('a');a.href=url;a.download='factoidal-studio-roster.html';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);};
    this.resizeObserver=new ResizeObserver(()=>this.fit());this.resizeObserver.observe(this.canvas);
    this.select('turtle');this.output();this.drawWires();this.fit();this.makeWorker();
    this.run();
  }
  makeWorker(){
    const workerURL=new URL('./worker.mjs',import.meta.url);
    workerURL.searchParams.set('engine',new URL(this.getAttribute('data-engine-url')??'https://cdn.jsdelivr.net/npm/@factoidal/core@0.27.0/browser.js',document.baseURI).href);
    this.worker=new Worker(workerURL,{type:'module'});
    this.worker.onmessage=({data})=>{
      if(data.type==='stage'){
        const stage=data.stage;this.stages.set(stage.id,{...this.stages.get(stage.id),...stage});
        if(stage.status==='done'||stage.status==='skipped')this.logs.push(stage);
        this.updateNodes();this.$('#done-count').textContent=[...this.stages.values()].filter(s=>s.status==='done').length;
        if(stage.status==='running')this.status(`Running ${stage.label??stage.id}…`,'running');
        if(this.selected===stage.id&&!this.isEditing())this.inspect();
        if(this.outputTab==='log')this.output();
      }else if(data.type==='complete'){
        this.result=data.result;this.$('.engine').textContent=`Lean → WASM · core ${this.result.coreVersion}`;this.busy=false;this.$('#run').disabled=false;this.$('#reset').disabled=false;this.$('#download').disabled=typeof this.result.html!=='string';
        this.status(this.result.kind==='diagnostic'?'Flow complete · XML diagnostic (no HTML)':'Flow complete · HTML report','done');this.$('#row-count').textContent=this.result.kind==='diagnostic'?'—':this.result.rows?.length??0;this.$('#run-time').textContent=`${((performance.now()-this.started)/1000).toFixed(2)}s`;
        this.output();if(!this.isEditing())this.inspect();if(this.rerun){this.rerun=false;this.run();}
      }else if(data.type==='error')this.fail(data.message);
    };
    this.worker.onerror=event=>{event.preventDefault();this.fail(event.message||'The data worker could not start. See the local server log.');};
  }
  isEditing(){return this.$('.inspect-body').contains(document.activeElement)&&['TEXTAREA','INPUT'].includes(document.activeElement.tagName);}
  run(){
    if(this.busy){this.rerun=true;return;}
    this.busy=true;this.result=null;this.stages.clear();this.logs=[];this.started=performance.now();this.$('.error-banner').textContent='';this.$('#run').disabled=true;this.$('#reset').disabled=true;this.$('#download').disabled=true;this.$('#done-count').textContent='0';this.$('#row-count').textContent='—';this.$('#run-time').textContent='—';this.status('Loading engine…','running');this.updateNodes();this.output();
    this.worker.postMessage({type:'run',inputs:{...this.inputs}});
  }
  fail(message){this.busy=false;this.$('#run').disabled=false;this.$('#reset').disabled=false;this.status('Flow stopped · inspect the error below','error');this.$('.error-banner').textContent=message;this.updateNodes();}
  status(text,state){this.$('#status-text').textContent=text;this.$('.run-status').dataset.state=state;}
  select(id){this.selectedWire=null;this.selected=id;const spec=NODES.find(n=>n.id===id);this.inspectTab=spec.editable?.[0]??'output';this.updateNodes();this.inspect();}
  updateNodes(){for(const node of this.querySelectorAll('flow-node'))node.update(this.stages.get(node.spec.id),!this.selectedWire&&node.spec.id===this.selected,this.showEvidence);this.drawWires();}
  inspect(){
    if(this.selectedWire){this.inspectWire();return;}
    const spec=NODES.find(n=>n.id===this.selected),stage=this.stages.get(this.selected);this.$('#inspect-title').textContent=spec.title;
    const tabs=[...(spec.editable??[]),'output','evidence'];this.$('.inspect-tabs').innerHTML=tabs.map(key=>`<button data-key="${key}" class="${this.inspectTab===key?'active':''}">${LABELS[key]??(key==='output'?'Node output':'Operation & evidence')}</button>`).join('');
    this.$('.inspect-tabs').onclick=e=>{const b=e.target.closest('button');if(b){this.inspectTab=b.dataset.key;this.inspect();}};
    const body=this.$('.inspect-body');body.replaceChildren();const p=document.createElement('p');p.className='inspect-description';p.textContent=spec.description;body.append(p);
    if(this.showEvidence || this.inspectTab==='evidence')body.append(this.evidencePanel(stage));
    if(spec.editable?.includes(this.inspectTab)){
      if(this.inspectTab==='minScore'){
        const label=document.createElement('label');label.textContent='Minimum score ';const input=document.createElement('input');input.type='number';input.min='0';input.max='100';input.value=this.inputs.minScore;
        input.onchange=()=>{this.inputs.minScore=input.value;this.$('#score').value=input.value;this.$('#score-value').textContent=input.value;this.run();};label.append(input);body.append(label);
        const note=document.createElement('p');note.className='inspect-description';note.textContent='This parameter is bound into the SPARQL query and evaluated by Factoidal. The browser does not filter the result rows.';body.append(note);
      }else{
        const key=this.inspectTab,editor=document.createElement('textarea');editor.className='editor';editor.spellcheck=false;editor.setAttribute('aria-label',`${LABELS[key]} source`);editor.value=this.inputs[key];editor.oninput=()=>{this.inputs[key]=editor.value;this.status('Inputs changed · run to refresh outputs','idle');};body.append(editor);
        const note=document.createElement('p');note.className='edit-note';note.textContent='Editable source · press Run flow to recompute. Reset inputs restores the sample.';body.append(note);
      }
    }else if(this.inspectTab==='evidence'){
      const text=stage?JSON.stringify({operation:stage.operation??stage.kind,kind:stage.kind,evidence:stage.evidence??null,adapter:stage.adapter??null,membershipEvidence:stage.membershipEvidence??null,note:stage.note??null,details:stage.details??null,durationMs:stage.durationMs},null,2):'Run the flow to inspect the actual operation and its evidence.';const raw=document.createElement('details');const label=document.createElement('summary');label.textContent='Raw registry and runtime record';raw.append(label,this.codeOutput(text,'json'));body.append(raw);
      const note=document.createElement('p');note.className='edit-note';note.textContent='Registered dataflow nodes and public-API adapters are identified separately. Proof scope belongs to the engine evidence, not to the appearance of a wire.';body.append(note);
    }else{
      if(stage?.rows)body.append(this.rowsTable(stage.rows));else{const language=({turtle:'turtle',csvw:'turtle',merge:'trig',closure:'turtle',graphs:'trig',xml:'xml',xslt:'html',html:'html'})[spec.id]??'text';body.append(this.codeOutput(stage?.text??stage?.summary??'This output is populated by the real pipeline when you run it.',language));}
    }
  }
  evidencePanel(stage){
    const a=nodeAssurance(stage), info=explainEvidence(stage), box=document.createElement('section');box.className='evidence evidence-detail';
    const heading=document.createElement('h3');heading.textContent=info.title;box.append(heading);
    const paragraph=text=>{const p=document.createElement('p');p.textContent=text;box.append(p);};
    paragraph(info.claim);
    if(info.admission)paragraph(`Checked predicate: ${info.admission.predicate}. Source theorem: ${info.admission.theorem}. Proofs are checked at build time; the browser receives the engine result.`);
    if(a.checked)paragraph('“Applied” means the engine reports this registered contract as applicable to the bound component/settings. The browser does not re-run the Lean proof checker.');
    paragraph(info.scope);
    for(const boundary of info.boundaries)paragraph(boundary);
    if(a.assumptions.length)paragraph('Reported assumptions: '+a.assumptions.join('; '));
    else if(stage?.evidence)paragraph('No assumptions were listed in the runtime array. This is not evidence that the implementation has no assumptions; read the registry scope below.');
    if(info.source){const link=document.createElement('a');link.href=info.source;link.textContent=info.admission?'Read the XML producer theorem and its scope (development source)':'Read the formal contract and its scope (published 0.27.0 source)';box.append(link);}
    if(info.registry){
      const registry=info.registry;
      if(registry.note)paragraph('Registry scope: '+registry.note);
      for(const [label,values] of [['Theorem references',registry.theorems],['Test references (not a fresh test run)',registry.tests]]){
        if(!values?.length)continue;
        const title=document.createElement('h4');title.textContent=label;box.append(title);
        const list=document.createElement('ul');for(const value of values){const item=document.createElement('li');item.textContent=value;list.append(item);}box.append(list);
      }
      const link=document.createElement('a');link.href=PROOF_SOURCE+'docs/theorem-registry.md';link.textContent='Explore the theorem registry and assurance boundaries';box.append(link);
    }
    if(stage?.evidence?.projection){const p=document.createElement('p');p.textContent='The row projection is a separate component. Its evidence follows:';box.append(p,this.evidencePanel({evidence:stage.evidence.projection}));}
    return box;
  }
  inspectWire(){
    const {from,to}=this.selectedWire;
    this.$('#inspect-title').textContent=`${from} → ${to}`;
    this.$('.inspect-tabs').replaceChildren();
    const body=this.$('.inspect-body');body.replaceChildren();
    const report=wireAssurance(from,to,this.stages);
    const p=document.createElement('p');p.className='evidence';p.textContent=`${report.wireKind}. ${report.note} This display link does not carry a whole-wire or graph-wide proof.`;body.append(p);for(const text of ['What is connected: '+report.wireKind, 'What is established: '+(report.checkedSubcomposition?'The engine checks the tagged Dataset ports and merge contract inside this subgraph. The source graph-tagging adapters are outside that proof.':'This recipe records a dependency; no link-preservation proof is attached.'), 'What remains to prove: '+report.obligation]){const line=document.createElement('p');line.textContent=text;body.append(line);}const raw=document.createElement('details');const summary=document.createElement('summary');summary.textContent='Raw connection evidence';raw.append(summary,this.codeOutput(JSON.stringify(report,null,2),'json'));body.append(raw);
  }
  codeOutput(text,language='text'){
    const view=document.createElement('factoidal-code-output');
    view.setValue(text,{language});
    return view;
  }
  rowsTable(rows){
    if(!rows.length){const p=document.createElement('p');p.className='inspect-description';p.style.padding='20px';p.textContent='No rows match this filter. Lower the minimum score and run again.';return p;}
    const table=document.createElement('table');table.className='rows';const cols=Object.keys(rows[0]);const head=table.createTHead().insertRow();for(const col of cols){const th=document.createElement('th');th.textContent=col;head.append(th);}const body=table.createTBody();for(const row of rows){const tr=body.insertRow();for(const col of cols)tr.insertCell().textContent=termText(row[col]);}return table;
  }
  output(){
    for(const button of this.querySelectorAll('.output-tabs button'))button.classList.toggle('active',button.dataset.tab===this.outputTab);
    const body=this.$('.output-body');body.replaceChildren();
    if(this.outputTab==='log'){
      for(const stage of this.logs){const line=document.createElement('div');line.className='log-line';const b=document.createElement('b');b.textContent=stage.label??stage.id;const summary=document.createElement('span');summary.className='log-summary';summary.textContent=stage.summary;const time=document.createElement('time');time.textContent=`${Number(stage.durationMs??0).toFixed(1)} ms`;line.append(b,summary,time);body.append(line);}
      if(!this.logs.length)body.innerHTML='<div class="placeholder">The execution trace will appear here.</div>';return;
    }
    if(!this.result){body.innerHTML=`<div class="placeholder"><span class="large">${this.busy?'◌':'◇'}</span>${this.busy?'Composing the output…':'Your data becomes a document here.'}<br><span class="muted">Turtle + CSVW → RDF → SPARQL → XSLT → HTML</span></div>`;return;}
    if(this.result.kind==='diagnostic'){const box=document.createElement('div');box.className='diagnostic-report';const title=document.createElement('h3');title.textContent='XML admission refused';const detail=document.createElement('pre');detail.textContent=this.result.diagnostic.message;const note=document.createElement('p');note.textContent='The RDF result was not changed. XQuery projection and XSLT did not run. Edit the source or choose a representation that supports these values.';box.append(title,detail,note);body.append(box);return;}
    if(this.outputTab==='rows')body.append(this.rowsTable(this.result.rows??[]));
    else if(this.outputTab==='source')body.append(this.codeOutput(this.result.html,'html'));
    else{const iframe=document.createElement('iframe');iframe.title='HTML emitted by the Lean XSLT engine';iframe.setAttribute('sandbox','');iframe.srcdoc=`<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; img-src data:">`+this.result.html;body.append(iframe);}
  }
  drawWires(){
    if(!this.$)return;const specs=new Map([...this.querySelectorAll('flow-node')].map(n=>[n.spec.id,n.spec]));const svg=this.$('.wires');svg.replaceChildren();
    svg.setAttribute('aria-hidden',String(!this.showEvidence));
    for(const [from,to] of EDGES){const a=specs.get(from),b=specs.get(to);const x1=a.x+176,y1=a.y+61,x2=b.x,y2=b.y+61;let d;
      if(from==='query'&&to==='filter')d=`M ${x1} ${y1} C ${x1+50} ${y1}, ${x1+50} ${y2-75}, ${b.x+88} ${y2-75} S ${x2-30} ${y2}, ${x2} ${y2}`;
      else if(from==='xslt'&&to==='html')d=`M ${x1} ${y1} C ${x1+40} ${y1}, ${x1+40} ${y2-80}, ${x2+88} ${y2-80} S ${x2-30} ${y2}, ${x2} ${y2}`;
      else {const bend=Math.max(45,Math.abs(x2-x1)*.5);d=`M ${x1} ${y1} C ${x1+bend} ${y1}, ${x2-bend} ${y2}, ${x2} ${y2}`;}
      const path=document.createElementNS('http://www.w3.org/2000/svg','path');path.setAttribute('d',d);path.setAttribute('class',`wire ${this.stages.get(to)?.status??''}`);path.style.setProperty('--wire-color',a.color);if(this.showEvidence){path.setAttribute('tabindex','0');path.setAttribute('role','button');path.setAttribute('aria-label',`Inspect ${from} to ${to} wire assurance`);const select=()=>{this.selectedWire={from,to};this.updateNodes();this.inspect();this.$('#inspect-title').focus();};path.onclick=e=>{e.stopPropagation();select();};path.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();select();}};const title=document.createElementNS('http://www.w3.org/2000/svg','title');title.textContent=wireAssurance(from,to,this.stages).wireKind;path.append(title);}svg.append(path);
    }
  }
  transform(){this.world.style.transform=`translate(${this.pan.x}px,${this.pan.y}px) scale(${this.scale})`;}
  fit(){const w=this.canvas.clientWidth,h=this.canvas.clientHeight,nodes=[...this.querySelectorAll('flow-node')];const width=Math.max(1490,...nodes.map(n=>n.spec.x+n.offsetWidth+30)),height=Math.max(410,...nodes.map(n=>n.spec.y+n.offsetHeight+20));this.scale=Math.min(1,(w-32)/width,(h-64)/height);this.pan={x:(w-width*this.scale)/2,y:8};this.transform();}
  zoom(multiplier){const next=Math.max(.35,Math.min(1.8,this.scale*multiplier));const cx=this.canvas.clientWidth/2,cy=this.canvas.clientHeight/2;this.pan={x:cx-(cx-this.pan.x)*next/this.scale,y:cy-(cy-this.pan.y)*next/this.scale};this.scale=next;this.transform();}
  disconnectedCallback(){this.worker?.terminate();this.resizeObserver?.disconnect();}
}
customElements.define('dataflow-studio',DataflowStudio);
