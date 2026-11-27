// page-load.mjs: the steps every host takes for a page between the engine's `inspect`
// answer and its requests (record: docs/designissues/2026-11-14-engine-integration.md).
//
// A host moves bytes: the engine says what to fetch (op `inspect`) and decides what the
// bytes mean. Each host used to write these steps for itself, and they drifted: the Hub
// fetched no linked style sheet, its hit test was asked with fewer layout fields than its
// render, and two hosts answered a script fetch with no Content-Type. The steps are here
// once, with the host's `fetch` given as a function. Nothing here reads a page: no markup,
// no CSS, no URL is parsed in this file.
//
// Hosts: docs/web/hub/foafnaut/browser-worker.mjs (the Hub), labs/demos/foafnaut/run_html.ts
// and native_html_document.ts (the window and Textnaut), tests/browser-wpt/testharness-run.ts
// (the WPT runner). labs/demos/foafnaut/host_parity_test.ts fails when one of them builds
// these requests by hand again.

/** The engine's bound on the supplied sheets of one request (WebDocument.validateResources). */
export const MAX_SHEETS=64;

/** The reason of an error, as one line for the console. */
const reasonOf=error=>String(error instanceof Error?error.message:error);

/** The linked style sheets of a page: every sheet the engine listed (`inspect.stylesheets`,
each `{nodeId, url}` chosen and resolved by the engine), fetched with `fetchText(url)`, which
answers `{url, source}` or throws. A sheet that is not read is a failure with its reason: the
engine draws the page without it in liberal mode and refuses the page in strict mode
(WebAccept.Skip.stylesheetMissing). Sheets past `limit` are failures too.
Answer: `{resources:[{nodeId,url,source}], resourceFailures:[{nodeId,url,reason}]}`. */
export async function loadStyleSheets(stylesheets,fetchText,limit=MAX_SHEETS) {
  const resources=[],resourceFailures=[];
  for(const [index,sheet] of (stylesheets??[]).entries()) {
    if(index>=limit){resourceFailures.push({nodeId:sheet.nodeId,url:sheet.url,reason:`more than ${limit} linked style sheets`});continue;}
    try{
      const got=await fetchText(sheet.url);
      resources.push({nodeId:sheet.nodeId,url:got.url??sheet.url,source:got.source});
    }catch(error){
      if(error?.name==='AbortError')throw error;
      resourceFailures.push({nodeId:sheet.nodeId,url:sheet.url,reason:reasonOf(error)});
    }
  }
  return {resources,resourceFailures};
}

/** What a page's elements ask for now that they did not ask for before: the style sheets and
images of an `inspect` answer (`inspection`) that are not in `listed` (`{sheets, images}`:
sets this function fills). A host calls it with the first inspection of a page and, after a
turn of the page's scripts changed the tree, with an inspection made with the scripts'
commands: an element a script made, or a link whose `rel` or `href` a script set, is then
listed by the engine as any other, and the host fetches what is new. A sheet is known by its
node and URL, an image by its key. */
export function newlyListed(listed,inspection) {
  const stylesheets=(inspection?.stylesheets??[]).filter(sheet=>!listed.sheets.has(`${sheet.nodeId} ${sheet.url}`));
  const images=(inspection?.images??[]).filter(image=>!listed.images.has(image.key));
  for(const sheet of stylesheets)listed.sheets.add(`${sheet.nodeId} ${sheet.url}`);
  for(const image of images)listed.images.add(image.key);
  return {stylesheets,images};
}

/** The sheets that a page's sheets import (`@import`): the engine names them (`inspect`
with the page's fetched sheets and the imported sheets so far gives `imports`, the URLs it
lacks; it finds an import's own imports once that sheet is given), and the host fetches
each with `fetchText(url)`, which answers `{url, source}` or throws. `inspect(imported)`
asks the engine with the list so far. A sheet that is not read is asked for no more and
reported to `failed(url, reason)`; the page is drawn without it. At most `rounds` rounds of
asking (the engine follows imports 8 deep) and `limit` sheets. Answer: the list for the
request field `imported`, `[{url, source}]` under the URLs the engine named. */
export async function loadImports(inspect,fetchText,imported=[],failed=(_url,_reason)=>{},limit=MAX_SHEETS,rounds=9) {
  const tried=new Set(imported.map(sheet=>sheet.url));
  for(let round=0;round<rounds;round++) {
    const wanted=((await inspect(imported))?.imports??[]).map(entry=>entry.url).filter(url=>!tried.has(url));
    if(!wanted.length)break;
    for(const url of wanted) {
      tried.add(url);
      if(imported.length>=limit){failed(url,`more than ${limit} imported style sheets`);continue;}
      try{imported.push({url,source:(await fetchText(url)).source});}
      catch(error){
        if(error?.name==='AbortError')throw error;
        failed(url,reasonOf(error));
      }
    }
  }
  return imported;
}

/** One subresource of a page, of any origin (an image, a style sheet, a font, a script): the
engine decides every step (`step`: its op `subresource`, Net.Subresource: the request to make,
the address of a name, each redirect, CORS or no CORS, whether the answer is used), and the
host makes each request it is told to (`wire`: native_net.ts `netAnswer`; on the Hub, the
page's own fetch). `page` is `{url, address?, hostCors?, referrerPolicy?}`: the document's
URL, the address the host loaded it from when it knows it, whether the host's own network
rules apply (the Hub), and the document's referrer policy. `crossorigin` is the element's
attribute ("" for none). Answer: `{url, status, contentType, opaque, base64}`: the final
URL, the type as sent, whether a script may never read the bytes, and the body of the answer
the engine accepted (for a `data:` URL, the body the engine made). A refusal is a throw with
the engine's reason. No URL is read here, and the engine's decision never gets a body. */
export async function loadSubresource(step,wire,page,kind,url,signal,crossorigin='') {
  let answer=await step({action:'start',kind,url,documentURL:page.url,referrerPolicy:page.referrerPolicy??'',crossorigin,
    ...(page.hostCors?{hostCors:true}:{}),...(page.address?{address:page.address}:{}),...(page.tor?{tor:true}:{})}),body='';
  // 20 redirects at most, each a name to resolve and a request: under 64 steps.
  for(let steps=0;steps<64;steps++) {
    if(answer?.done)return {url:answer.done.url,status:answer.done.status,contentType:answer.done.type??'',
      opaque:answer.done.opaque===true,base64:answer.done.bodyBase64??body};
    if(!answer?.wire)throw new Error(String(answer?.fail??'subresource refused'));
    if(signal?.aborted){await step({action:'cancel',id:answer.id});signal.throwIfAborted();}
    const {bodyBase64,...head}=await wire(answer.wire);
    body=bodyBase64??'';
    answer=await step({action:'answer',id:answer.id,answer:head});
  }
  if(answer?.id!==undefined)await step({action:'cancel',id:answer.id});
  throw new Error('subresource: too many steps');
}

/** The fields of a page that every request which lays the page out must carry, the same in
each: a render, a hit test (`nodeAt`), the selection, find in page, a print layout, and the
`layout` request of the page's script session (WebDocument.layoutFields). A request that
leaves one out is laid out again, as another page: its answer is not of the frame on screen.
`page` is the host's record of the page: `url`, and what it fetched and was told
(`resources`, `resourceFailures`, `imported`, `images`, `heldImages`, `webFonts`, `commands`, `animated`,
`liberal`, `scripting`). The view (text size, zoom unit, media) is the host's to add. */
export function pageLayoutFields(page) {
  const out={url:page.url};
  if(page.liberal)out.liberal=true;
  if(page.scripting===false)out.scripting=false;
  if(page.syntax)out.syntax=page.syntax;
  for(const key of ['resources','resourceFailures','imported','images','heldImages','webFonts','commands','animated']) {
    const value=page[key];
    if(Array.isArray(value)&&value.length)out[key]=value;
  }
  return out;
}

/** The animated values of a script turn, kept on the host's record of the page for its next
requests. `turn.animated` is `[[node, longhand, computed text, isTransition], ...]`: the
values of the page's running animations and transitions at the turn's time, by the nodes
of the session's arena, which are the nodes of a render (a render replays the session's
commands). The engine decides them and when another frame is due (`turn.nextWake`); a host
only carries the list from the turn to its requests (`pageLayoutFields`). The answer is
whether the list changed, so that the host draws again: a turn with no `animated` field
(a page with no animation, an engine from before the field) and a turn whose list is the
last one change nothing and cost no frame; an empty list removes the field. */
export function takeAnimated(page,turn) {
  if(!Array.isArray(turn?.animated))return false;
  const next=turn.animated,last=page.animated??[];
  if(next.length===last.length&&JSON.stringify(next)===JSON.stringify(last))return false;
  if(next.length)page.animated=next;else delete page.animated;
  return true;
}

/** A script turn on the host's record of the page, the same in every host: the DOM commands
of a turn that changed the page and its animated values (takeAnimated) go into the page's next
requests. The answer is whether the page is drawn again; that frame is a layered frame (a render
with `layers:true`) wherever the engine makes layers, as for an animation value. The engine then
decides the cost: a layout only when the layout key (which holds the commands) is one it has not
laid out, and otherwise the kept layout painted with the new values, the primitives whose keys
changed compiled again and their damage named, so that a script that moves or fades an element
(transform, opacity) costs a paint-only frame (FrameCost.run_paints_never_layout) and a draw of the
damage, not a whole-page frame. */
export function takeTurn(page,turn) {
  const changed=!!(turn?.changed&&turn.commands);
  if(changed)page.commands=turn.commands;
  const moved=takeAnimated(page,turn);
  return changed||moved;
}

/** The steps of a page's scripts in one timer turn of a host that takes input between turns
(WebScripts action `advance` with `sliceSteps`): the engine stops between two tasks past it,
and the rest is due at once (`nextWake`). About 50 ms of BubblePopJS on the native engine
(LeanJS.stepsPerMs, 500 steps a millisecond); an engine without slices ignores the field. */
export const turnSliceSteps=25000;

/** How long a scroll, key or press holds the next timer turn back (ms), and the most a due
timer turn waits for input (ms): input comes first, timers are never starved. */
export const INPUT_FIRST_MS=50,TIMER_HOLD_MAX_MS=250;

/** Input first, the rule of every host: whether a due timer turn waits, because input is
waiting for its frame (`waiting`) or came in the last INPUT_FIRST_MS (`inputAt`), unless the
turn has already waited TIMER_HOLD_MAX_MS (`heldSince`, undefined when it has not waited). */
/** @param {{now:number,inputAt:number,waiting?:boolean,heldSince?:number}} o */
export function inputFirst({now,inputAt,waiting,heldSince}) {
  if(heldSince!==undefined&&now-heldSince>=TIMER_HOLD_MAX_MS)return false;
  return !!waiting||now-inputAt<INPUT_FIRST_MS;
}

/** How long after the last scroll event a change of the page waits (ms), and the most it
waits (ms). */
export const SCROLL_QUIET_MS=150,SCROLL_HOLD_MAX_MS=1000;

/** Scroll first, the rule of every host that scrolls bands of a kept layout: whether a change
of the page by its scripts or by a late resource (`changedAt`, undefined when none waits yet)
waits, because the user scrolled in the last SCROLL_QUIET_MS (`scrollAt`). Meanwhile the host
shows, and makes the bands of, the page as it is on screen, so a scroll never waits for a
layout of the new page; the change is drawn when the scroll pauses, or after
SCROLL_HOLD_MAX_MS. Just after a page is first shown (`shownAt`) a change waits SCROLL_QUIET_MS
too: a reader who scrolls at once scrolls the page as shown, not behind its next layout. */
/** @param {{now:number,scrollAt:number,changedAt?:number,shownAt?:number}} o */
export function scrollFirst({now,scrollAt,changedAt,shownAt}) {
  if(changedAt!==undefined&&now-changedAt>=SCROLL_HOLD_MAX_MS)return false;
  return now-scrollAt<SCROLL_QUIET_MS||(shownAt!==undefined&&now-shownAt<SCROLL_QUIET_MS);
}

/** A start in slices (WebScripts action `start` with `sliceSteps`): the steps of the page's
scripts before the first turn's answer. The classic scripts run whole; the module scripts, the
events and the tasks due at once then stop between two of them past this, the turn says
`startMore`, and each timer turn (`advance` with `sliceSteps`) goes on, so the page is shown
after its classic scripts and its first slice, not after every script it has
(LeanJS.startSome; theorems startSome_never, startSome_resume). */
export const startSliceSteps=turnSliceSteps;

/** Scripts first: the fewest and the most a change of the page waits while its start has not
finished (ms), and how many times the last layout's time it waits. */
export const SCRIPTS_HOLD_MIN_MS=30,SCRIPTS_HOLD_MAX_MS=5000,SCRIPTS_HOLD_LAYOUTS=3;

/** Scripts first, the rule of every host that starts a page in slices: whether a change of the
page by its scripts (`changedAt`, undefined when none waits yet) waits, because the page's start
has not finished (`more`: the last turn's `startMore`). A layout of a large page takes a second
or more, and a start makes many small changes: drawn after each slice, the page would spend its
time in layouts of states nobody reads. The change is drawn when the start ends, or after
SCRIPTS_HOLD_LAYOUTS times the last layout (`layoutMs`), at least SCRIPTS_HOLD_MIN_MS and at
most SCRIPTS_HOLD_MAX_MS: at most a quarter of a long start goes to layouts, and a page whose
layout takes a few milliseconds is still drawn thirty times a second. */
/** @param {{now:number,more:boolean,changedAt?:number,layoutMs?:number}} o */
export function scriptsFirst({now,more,changedAt,layoutMs}) {
  if(!more)return false;
  if(changedAt===undefined)return true;
  return now-changedAt<Math.min(SCRIPTS_HOLD_MAX_MS,Math.max(SCRIPTS_HOLD_MIN_MS,SCRIPTS_HOLD_LAYOUTS*(layoutMs??0)));
}

/** Whether an engine's error says the page's script session is gone: the engine holds no
session (`no session`), holds another page's (`not the current session`), or ended this one
(`session ended`, WebScripts.sealAnswer). Asking that session again can only fail again. */
export function scriptSessionGone(message) {
  return /scriptSession: (no session|not the current session|session ended)/.test(String(message));
}

/** A failed action of a page's script session, the rule of every host: an answer that says the
session is gone ends the page's scripts in the host (no timer, frame, input or request asks it
again) with one line; a failed timer turn stops the page's timers; any other failure is logged
once for each page and message, never once for each retry. `log` takes the line. Answers
`ended`, `stopped`, `logged`, `repeated` (not logged again) or `none` (the page has no scripts). */
export function scriptFailure(page,error,what,log) {
  const message=String(error?.message??error);
  if(!page?.script)return 'none';
  if(scriptSessionGone(message)){
    page.script=undefined;page.scriptStopped=true;
    log(`page scripts stopped (${what}): the engine no longer holds this page's script session (${message})`);
    return 'ended';
  }
  if(what==='timers'&&page.script.turn){
    page.script.turn.nextWake=null;
    log(`page script timers stopped: ${message}`);
    return 'stopped';
  }
  const seen=page.scriptFailures??=new Set();
  if(seen.has(message))return 'repeated';
  seen.add(message);
  log(`page script ${what} failed: ${message}`);
  return 'logged';
}

/** The embedder's answer to one script fetch of a turn (`fetches`: a worker's script, an
imported script): the status, the final URL, and the Content-Type and X-Content-Type-Options
as the server sent them, with the text. The engine decides whether it is a script
(LeanJSWorkers.scriptAccepted: `nosniff` with a type that is not JavaScript is refused), so
the two header values must reach it. `fetchRaw(url)` answers
`{status, url, contentType, contentTypeOptions, source}` or throws; a throw is a network
error (status 0). */
export async function fetchedAnswer(wanted,fetchRaw) {
  try{
    const got=await fetchRaw(wanted.url);
    return {id:wanted.id,status:got.status??200,url:got.url??wanted.url,contentType:got.contentType??'',
      contentTypeOptions:got.contentTypeOptions??'',source:got.source??''};
  }catch{
    return {id:wanted.id,status:0,url:wanted.url,contentType:'',contentTypeOptions:'',source:''};
  }
}

/** `fetchRaw` over a `fetch`-like function, for a host whose pages are HTTP(S). */
export const rawOverFetch=fetchLike=>async url=>{
  const response=await fetchLike(url);
  return {status:response.status,url:response.url||url,contentType:response.headers.get('content-type')??'',
    contentTypeOptions:response.headers.get('x-content-type-options')??'',source:await response.text()};
};

/** How far a page scrolls: the engine's limit for the layers on screen (`layers.scrollLimit`,
WebDocument.scrollLimit, with `scrollLimit_reaches`: the view then ends at the last page row).
An answer without layers (a single frame, an older engine) ends at the bottom of the lowest box
plus 60 CSS pixels. The window and the Hub used to decide this each for itself, and the Hub
never read the engine's limit. `boxes` are the frame's `webRender.boxes` (`[node, x, y, w, h]`
rows: y at 2, height at 4). */
export function scrollLimitOf(layers,boxes,view,scale) {
  if(typeof layers?.scrollLimit==='number')return layers.scrollLimit;
  const bottom=Math.max(0,...(boxes??[]).map(box=>box[2]+box[4]));
  return Math.max(0,bottom-view+Math.round(60*scale));
}
