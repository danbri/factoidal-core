// Foafnaut browser state: bookmarks, history, settings and open tabs.
// Design record: docs/designissues/2026-11-08-browser-state-lws.md
//
// Lean decides everything (labs/demos/foafnaut/WebState.lean): the path and the JSON-LD
// text of each resource, how two copies merge, what a sync sends each way, which origins
// a sync may reach, and the pages foafnaut:bookmarks and foafnaut:history. This file only
// moves the texts Lean wrote between Lean and a store. It reads no resource.
//
// One code path for both hosts. A store is {base, where, get(path), put(plan), list()}:
//   lwsStore       a Linked Web Storage server, through @factoidal/core's LWS client
//                  (the native browser: a local lws-serve on 127.0.0.1; a remote pod)
//   indexedDbStore the browser's own IndexedDB (the Hub: an https page cannot rely on
//                  reaching a loopback server)
//   memoryStore    a Map (tests, and a Hub with no IndexedDB)
// `call(op, request)` runs one Lean op and gives its parsed answer (or a promise of it).

/** The Lean ops of WebState. An engine without them answers "unknown op". */
export const STATE_OPS=['stateInfo','stateVisit','stateBookmark','stateUnbookmark','stateSettings','stateSession',
  'stateRead','statePage','stateMerge','stateSync','stateFetchAllowed'];

/** Whether the engine carries the state ops: {available, reason}. */
export async function stateAvailable(call){
  try{const info=await call('stateInfo',{});return {available:Array.isArray(info.ops),reason:'stateInfo answered',info};}
  catch(error){return {available:false,reason:'the engine has no browser-state ops (needs an engine built with WebState.lean): '+String(error?.message??error)};}
}

/** A fetch that asks Lean before each request: only the pod's origin and loopback. Each
 *  request gives one JSON line (method, origin, path, status, time, bytes); no header, no
 *  query and no body is logged, so no credential is. */
export function guardedFetch(call,pod,wire=globalThis.fetch,log=(_record)=>{}){
  return async(url,init={})=>{
    const href=String(url),verdict=await call('stateFetchAllowed',{url:href,pod});
    const where=(()=>{try{const u=new URL(href);return {origin:u.origin,path:u.pathname};}catch{return {origin:'',path:''};}})();
    if(!verdict.allow){log({type:'browser-state-fetch',method:init.method??'GET',...where,refused:verdict.reason});throw new Error(`browser state: request refused (${verdict.reason})`);}
    const start=performance.now();
    const reply=await wire(href,init);
    log({type:'browser-state-fetch',method:init.method??'GET',...where,status:reply.status,ms:Math.round(performance.now()-start),
      bytes:Number(reply.headers.get('content-length')??-1)});
    return reply;
  };
}

export function memoryStore(base='/',where='memory'){
  const items=new Map();
  return {base,where,items,
    async get(path){return items.has(path)?items.get(path):null;},
    async put(plan){items.set(plan.path,plan.body);},
    async list(){return [...items].map(([path,body])=>({path,body}));}};
}

/** The browser's IndexedDB: one object store of {path, body}. */
export async function indexedDbStore(name='foafnaut-state',base='/'){
  const db=await new Promise((resolve,reject)=>{
    const open=indexedDB.open(name,1);
    open.onupgradeneeded=()=>open.result.createObjectStore('resources',{keyPath:'path'});
    open.onsuccess=()=>resolve(open.result);open.onerror=()=>reject(open.error);
  });
  const run=(mode,act)=>new Promise((resolve,reject)=>{
    const tx=db.transaction('resources',mode),request=act(tx.objectStore('resources'));
    tx.oncomplete=()=>resolve(request.result);tx.onerror=()=>reject(tx.error);
  });
  return {base,where:'this browser (IndexedDB)',
    async get(path){const row=await run('readonly',s=>s.get(path));return row?row.body:null;},
    async put(plan){await run('readwrite',s=>s.put({path:plan.path,body:plan.body}));},
    async list(){return (await run('readonly',s=>s.getAll())).map(({path,body})=>({path,body}));}};
}

const status=error=>error?.detail?.status??0;

/** A Linked Web Storage server, through a client from createLwsClient. `base` is the
 *  storage root URL (ending in /); `containers` are Lean's (stateInfo). */
export function lwsStore(client,base,containers,where=base){
  const url=path=>base+path.slice(1);
  return {base,where,
    async get(path){
      try{const r=await client.read(url(path));return typeof r.body==='string'?r.body:new TextDecoder().decode(r.body);}
      catch(error){if(status(error)===404)return null;throw error;}
    },
    async put(plan){
      try{await client.update(plan.url,{body:plan.body,mediaType:plan.mediaType});return;}
      catch(error){if(status(error)!==404)throw error;}
      // Missing: make the containers Lean named, from the top down, then create it.
      // A container that is there is left alone: a second create could get another name.
      for(const c of plan.containers){
        try{await client.head(c.url);continue;}catch(error){if(status(error)!==404)throw error;}
        const madeDir=await client.create(c.parent,{slug:c.slug,container:true});
        if(madeDir.location!==c.url)throw new Error(`browser state: the server made the container ${madeDir.location}, not ${c.url}`);
      }
      const made=await client.create(plan.parent,{slug:plan.slug,body:plan.body,mediaType:plan.mediaType});
      if(made.location!==plan.url){
        // The server chose another name: remove it, so the storage never holds a copy at a path Lean did not name.
        try{await client.delete(made.location);}catch{}
        throw new Error(`browser state: the server created ${made.location}, not ${plan.url}`);
      }
    },
    async list(){
      const out=[];
      for(const container of containers){
        let listing;
        try{listing=await client.list(url(container));}catch(error){if(status(error)===404)continue;throw error;}
        for(const member of listing.members??[]){
          if(member.type!=='DataResource'||!member.id.startsWith(base))continue;
          const path='/'+member.id.slice(base.length);
          // Only the members directly in this container: deeper ones are listed by their own.
          if(path.slice(container.length).includes('/'))continue;
          const body=await this.get(path);
          if(body!==null)out.push({path,body});
        }
      }
      return out;
    }};
}

/** The browser-state API over one store. `now` gives milliseconds since 1970. */
export function createBrowserState({call,store,now=()=>Date.now(),log=(_record)=>{}}){
  // Lean names the path from the request; when a copy is there, Lean is asked again with it.
  const record=async(op,request)=>{
    const at=now();
    let plan=await call(op,{...request,base:store.base,now:at});
    if(plan.skip)return null;
    const current=await store.get(plan.path);
    if(current!==null)plan=await call(op,{...request,base:store.base,now:at,current});
    await store.put(plan);
    log({type:'browser-state-write',op,path:plan.path,bytes:plan.body.length});
    return plan;
  };
  return {
    store,
    visit:(url,title='',from='')=>record('stateVisit',{url,title,from}),
    bookmark:(url,title='',tags)=>record('stateBookmark',{url,title,...(tags?{tags}:{})}),
    unbookmark:url=>record('stateUnbookmark',{url}),
    settings:changes=>record('stateSettings',changes),
    session:(tabs,active)=>record('stateSession',{tabs,active}),
    async read(){return await call('stateRead',{resources:await store.list()});},
    async page(page){return await call('statePage',{page,resources:await store.list(),where:store.where});},
    /** Push local changes and pull remote ones, merged by Lean. */
    async sync(remote){
      const start=performance.now();
      const [localSide,remoteSide]=await Promise.all([store.list(),remote.list()]);
      const plan=await call('stateSync',{local:localSide,remote:remoteSide,base:store.base,remoteBase:remote.base});
      for(const item of plan.toRemote)await remote.put(item);
      for(const item of plan.toLocal)await store.put(item);
      const result={pushed:plan.toRemote.length,pulled:plan.toLocal.length,ms:Math.round(performance.now()-start)};
      log({type:'browser-state-sync',...result});
      return result;
    }
  };
}
