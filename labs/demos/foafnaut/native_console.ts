// The console of a page (foafnaut:console). The host keeps the entries of each page it
// shows; Lean writes the console page from them (WebConsole.lean, op consolePage) and
// draws it as any page. Entries: what the page's scripts wrote (logs and errors of the
// script session), and System entries: Lean's diagnostics of liberal mode (WebAccept),
// refusals, and fetches that failed. Nothing here decides what is skipped: the System
// entries of skips are Lean's diagnostics as Lean gave them.

export type ConsoleEntry={source:"System"|"page";severity:string;message:string;feature?:string;where?:string;action?:string};

/** The most entries a page keeps: the first ones of a long run stay out. */
export const MAX_CONSOLE_ENTRIES=1000;

const entries=new WeakMap<object,ConsoleEntry[]>();
const seen=new WeakMap<object,Set<string>>();

/** The entries of a page, oldest first. */
export function consoleOf(page:object):ConsoleEntry[]{
  let list=entries.get(page);
  if(!list){list=[];entries.set(page,list);}
  return list;
}

/** Add entries. A System entry is kept once: each render of a page in liberal mode gives
the same diagnostics again. */
export function addEntries(page:object,list:ConsoleEntry[]){
  const kept=consoleOf(page);
  let keys=seen.get(page);
  if(!keys){keys=new Set();seen.set(page,keys);}
  for(const entry of list){
    if(kept.length>=MAX_CONSOLE_ENTRIES)return;
    if(entry.source==="System"){
      const key=JSON.stringify([entry.feature,entry.where,entry.message]);
      if(keys.has(key))continue;
      keys.add(key);
    }
    kept.push(entry);
  }
}

/** The diagnostics of an inspect or render answer (WebAccept.Diagnostic.json). Lean puts them
in a render answer only when the request asks (`diagnostics:true`), which a host does for the
first frame of a liberal page: later frames carry and cost nothing. */
export function noteDiagnostics(page:object,answer:unknown,render=true){
  const list=(answer as {diagnostics?:unknown})?.diagnostics;
  if(render)(page as {diagnosticsSeen?:()=>void}).diagnosticsSeen?.();
  if(!Array.isArray(list))return;
  addEntries(page,list.filter(d=>d&&typeof d==="object").map(d=>{
    const x=d as Record<string,unknown>,text=(k:string)=>typeof x[k]==="string"?x[k] as string:undefined;
    return {source:"System",severity:text("severity")??"warning",message:text("message")??"",feature:text("feature"),where:text("where"),action:text("action")};
  }));
}

/** The lines of a script turn: logs (every console method of the QuickJS-NG prelude writes
one kind of line) and uncaught errors. */
export function noteTurn(page:object,turn:{logs?:string[];errors?:string[]}){
  addEntries(page,[...(turn.logs??[]).map(message=>({source:"page" as const,severity:"log",message})),
    ...(turn.errors??[]).map(message=>({source:"page" as const,severity:"error",message}))]);
}

/** The request of the op consolePage for the page of tab `tab` (0-based). */
export function consoleRequest(page:{url:string;title?:string},tab:number,tabs:{url:string;title?:string}[]){
  return {tab:tab+1,title:page.title??"",url:page.url,entries:consoleOf(page),
    tabs:tabs.map(t=>({url:t.url,title:t.title??""}))};
}
