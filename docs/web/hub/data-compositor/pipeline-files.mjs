import {decodePipelineDocument,encodePipelineDocument,MAX_PIPELINE_BYTES} from './pipeline-document.mjs';
import {loadKnownPods,rememberPods} from './pod-storage.mjs';

// Shared presentation/host IO for compositor recipes. Loading never executes a
// pipeline. The caller supplies snapshot/restore and the worker's LWS transport.
export class PipelineLibrary extends HTMLElement {
  connectedCallback(){
    if(this.initialized)return;this.initialized=true;
    this.innerHTML=`<div class="pipeline-library"><label>Pipeline name <input class="pipeline-title" value="Untitled pipeline" maxlength="160"></label><button class="open-file">Open pipeline…</button><button class="save-file">Save pipeline…</button><button class="open-pods">FOAF pods…</button><input class="pipeline-file" type="file" accept=".json,application/json" hidden><span class="file-status" role="status" aria-live="polite"></span></div>
    <dialog class="pod-dialog" aria-labelledby="pod-heading"><form method="dialog"><button class="close-dialog" aria-label="Close pod browser">×</button></form><h2 id="pod-heading">Pipeline library · FOAF pods</h2>
      <p>Discover storage declared in a bootstrap <code>foaf.ttl</code>. Only pod locations are remembered. Loading a pipeline does not run it.</p>
      <label>Bootstrap FOAF URL <input class="bootstrap-url" type="url" placeholder="https://example.org/foaf.ttl" autocomplete="url"></label><button class="discover-pods">Discover pods</button>
      <label>Known pod <select class="pod-choice"><option value="">Discover or select a pod</option></select></label>
      <details><summary>Access token (optional)</summary><p>Use a token issued for the selected pod. Kept in memory only and sent within that pod’s realm. Server authorization still applies.</p><label>Bearer token <input class="pod-token" type="password" autocomplete="off"></label><button class="forget-token">Forget token</button></details>
      <div class="pod-actions"><button class="list-pod">Browse pod</button><button class="parent-folder">Up one folder</button></div><p class="pod-location"></p>
      <label>Files and folders <select class="pod-files" size="7" aria-label="Pod files and folders"></select></label><button class="load-pod">Open selected</button>
      <hr><label>New filename <input class="pod-filename" value="pipeline.json" maxlength="200"></label><button class="create-pod">Save as new file</button><button class="update-pod" disabled>Update loaded file</button>
      <p class="pod-message" role="status" aria-live="polite"></p>
    </dialog>`;
    this.$=s=>this.querySelector(s);this.pods=loadKnownPods();this.renderPods();
    this.$('.open-file').onclick=()=>this.$('.pipeline-file').click();
    this.$('.pipeline-file').onchange=async e=>{const file=e.target.files?.[0];if(!file)return;try{if(file.size>MAX_PIPELINE_BYTES)throw Error('Pipeline file exceeds 2 MiB.');await this.loadText(await file.text(),file.name);this.loaded=null;this.$('.update-pod').disabled=true;}catch(error){this.message(error.message);}finally{e.target.value='';}};
    this.$('.save-file').onclick=()=>this.guarded(async()=>{
      const text=this.snapshotText();const url=URL.createObjectURL(new Blob([text],{type:'application/json'}));
      const a=document.createElement('a');a.href=url;a.download=this.downloadName();a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);this.message('Pipeline downloaded; inputs and node layout saved.');
    });
    this.$('.open-pods').onclick=()=>this.$('dialog').showModal();
    this.$('.discover-pods').onclick=()=>this.podAction(async()=>{
      const discovery=await this.transport('discover',{bootstrapUrl:this.$('.bootstrap-url').value.trim()});
      try{this.pods=rememberPods(discovery);}catch{this.pods=[...this.pods,...discovery.roots];}
      this.renderPods();if(discovery.roots.length){const index=this.pods.findIndex(p=>p.url===discovery.roots[0].url&&p.bootstrapUrl===discovery.bootstrapUrl);this.$('.pod-choice').value=String(index);this.selectPod();}
      return `${discovery.roots.length} storage declaration(s) found${discovery.rejected.length?`; ${discovery.rejected.length} unusable declaration(s)`:''}. Discovery does not grant access.`;
    });
    this.$('.pod-choice').onchange=()=>{if(this.$('.pod-choice').value!=='')this.selectPod();};
    this.$('.list-pod').onclick=()=>this.podAction(()=>this.browse());
    // The engine (storage worker, op containerPath) gives the folder above, never above the root.
    this.$('.parent-folder').onclick=()=>this.podAction(async()=>{const pod=this.selectedPod();const {url}=await this.transport('parent',{pod,url:this.folder??pod.url});return this.browse(url);});
    this.$('.load-pod').onclick=()=>this.podAction(async()=>{
      const url=this.$('.pod-files').value;if(!url)throw Error('Select a file or folder first.');
      if(url.endsWith('/'))return this.browse(url);
      const loaded=await this.transport('load',{pod:this.selectedPod(),url});
      await this.loadText(loaded.text,loaded.url);this.loaded=loaded;this.$('.update-pod').disabled=!loaded.etag;
      return loaded.etag?'Pipeline loaded. Edit it, then Run flow or Update loaded file.':'Pipeline loaded without an ETag. Save as a new file; an unguarded overwrite is not offered.';
    });
    this.$('.create-pod').onclick=()=>this.podAction(async()=>{
      // The storage worker forms the URL from the folder and the name (op containerPath).
      const pod=this.selectedPod(),folder=this.folder??pod.url,name=this.$('.pod-filename').value;
      const saved=await this.transport('save',{pod,folder,name,text:this.snapshotText(),create:true});
      // A subsequent overwrite requires an explicit load of the saved resource.
      return `Saved new pipeline: ${saved.url}. Open it before using Update loaded file.`;
    });
    this.$('.update-pod').onclick=()=>this.podAction(async()=>{
      if(!this.loaded?.etag)throw Error('Open a file with an ETag before updating.');
      const saved=await this.transport('save',{pod:this.selectedPod(),url:this.loaded.url,text:this.snapshotText(),etag:this.loaded.etag,create:false});
      this.loaded={url:saved.url,etag:saved.etag};this.$('.update-pod').disabled=!saved.etag;
      return `Updated ${saved.url}${saved.etag?'':'. Reopen it before another update'}.`;
    });
    this.$('.forget-token').onclick=()=>this.podAction(async()=>{this.$('.pod-token').value='';await this.transport('forget',{});return 'Credential session forgotten.';});
  }
  configure({recipe,capture,restore,request}){this.recipe=recipe;this.capture=capture;this.restore=restore;this.request=request;}
  get title(){return this.$('.pipeline-title').value;}
  set title(value){this.$('.pipeline-title').value=value;}
  snapshotText(){return encodePipelineDocument(this.capture(this.title),this.recipe);}
  async loadText(text,source='file'){
    const doc=decodePipelineDocument(text,this.recipe);await this.restore(doc);this.title=doc.title;
    this.message(`Loaded ${source}. Review the inputs, then run the flow.`);return doc;
  }
  downloadName(){return (this.title.replace(/[^\p{L}\p{N} ._-]/gu,'_').trim()||'pipeline')+'.pipeline.json';}
  message(text){this.$('.file-status').textContent=text;}
  async guarded(work){try{await work();}catch(error){this.message(error.message);}}
  async podAction(work){
    if(this.podBusy)return;this.podBusy=true;const buttons=[...this.$('dialog').querySelectorAll('button,input,select')].filter(b=>!b.classList.contains('close-dialog'));
    const states=buttons.map(b=>b.disabled);buttons.forEach(b=>b.disabled=true);this.$('.pod-message').textContent='Working…';
    try{this.$('.pod-message').textContent=await work();}catch(error){this.$('.pod-message').textContent=`${error.message} No automatic overwrite or retry was attempted.`;}
    finally{buttons.forEach((b,i)=>b.disabled=states[i]);this.$('.update-pod').disabled=!this.loaded?.etag;this.podBusy=false;}
  }
  selectedPod(){const value=this.$('.pod-choice').value;const pod=value===''?null:this.pods[Number(value)];if(!pod)throw Error('Discover and select a pod first.');return pod;}
  selectPod(){const pod=this.selectedPod();this.folder=pod.url;this.loaded=null;this.$('.pod-token').value='';this.$('.pod-files').replaceChildren();this.$('.update-pod').disabled=true;this.$('.pod-location').textContent=pod.url;}
  renderPods(){const select=this.$('.pod-choice');select.replaceChildren(new Option('Select a discovered pod',''));this.pods.forEach((pod,i)=>select.add(new Option(`${pod.url} — ${pod.bootstrapUrl}`,String(i))));}
  async browse(url){
    const pod=this.selectedPod(),folder=url??this.folder??pod.url;
    const listing=await this.transport('list',{pod,url:folder});
    const options=listing.items.map(item=>new Option(item.id,item.id));
    // Commit navigation only after a successful listing. A failed browse must
    // not change the destination used by Save as new while showing the old one.
    this.$('.pod-files').replaceChildren(...options);this.folder=folder;
    this.$('.pod-location').textContent=folder;
    return `${listing.items.length} item(s). Select a folder or pipeline JSON file to open.`;
  }
  async transport(operation,args){if(!this.request)throw Error('Pod transport is not ready.');const token=this.$('.pod-token').value;return this.request(operation,{...args,...(token&&args.pod?{bearer:{token,realm:args.pod.url}}:{})});}
}
customElements.define('pipeline-library',PipelineLibrary);
