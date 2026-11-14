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
    ...(page.hostCors?{hostCors:true}:{}),...(page.address?{address:page.address}:{})}),body='';
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
(`resources`, `resourceFailures`, `images`, `heldImages`, `webFonts`, `commands`, `animated`,
`liberal`, `scripting`). The view (text size, zoom unit, media) is the host's to add. */
export function pageLayoutFields(page) {
  const out={url:page.url};
  if(page.liberal)out.liberal=true;
  if(page.scripting===false)out.scripting=false;
  for(const key of ['resources','resourceFailures','images','heldImages','webFonts','commands','animated']) {
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
