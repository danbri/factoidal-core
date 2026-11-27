// WebDriver BiDi transport for Foafnaut's WebDriver endpoint (WebSocket, W3C WebDriver BiDi section 4).
//
// The host moves bytes only. Lean decides everything (L4Factoidal.WebDriver.BiDi, through the engine's
// session actions in labs/demos/foafnaut/WebScripts.lean):
//   bidiConnect: the upgrade request (the gate: secret, Origin, Host, lock; then the resource)
//   bidi:        one frame; Lean answers the text to send, a URL to load first, connections to close
//   bidiClose:   the socket closed
// Design record: docs/designissues/2026-11-27-foafnaut-webdriver-bidi.md. The endpoint exists only when the
// user passed --dangerously-enable-webdriver-endpoint (L4Factoidal.WebDriver.Gate, Risk.webdriverEndpoint).

export type BidiEngine = {scriptSession:(source:string,request:Record<string,unknown>)=>unknown};

/** The experimental code notice (CLAUDE.md, "Experimental code notice"), printed when the endpoint starts. */
export const REVIEW_WARNING = "EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.";

const sockets = new Map<number, WebSocket>();

/** A WebSocket upgrade request on the endpoint's port: the Response to give, or undefined when the request is
 * not an upgrade (the caller handles it as a classic WebDriver request). `loadPage` loads a URL in the session's
 * page, as classic Navigate To does. */
export function bidiUpgrade(engine:BidiEngine, request:Request, loadPage:((url:string)=>Promise<unknown>)|undefined):Response|undefined {
  if ((request.headers.get("upgrade") ?? "").toLowerCase() !== "websocket") return undefined;
  const url = new URL(request.url);
  const answer = engine.scriptSession("", {action:"bidiConnect", path:url.pathname + url.search, host:request.headers.get("host") ?? "",
    ...(request.headers.has("origin") ? {origin:request.headers.get("origin")} : {})}) as {connection?:number; status?:number};
  if (answer.connection === undefined) return new Response(null, {status:answer.status ?? 403});
  const id = answer.connection;
  const {socket, response} = Deno.upgradeWebSocket(request);
  sockets.set(id, socket);
  // One frame at a time, in order: a navigation finishes before the next frame is handled.
  let queue = Promise.resolve();
  socket.onmessage = (event) => {
    const frame = typeof event.data === "string" ? {text:event.data} : {binary:true};
    queue = queue.then(async () => {
      const out = engine.scriptSession("", {action:"bidi", connection:id, ...frame}) as {reply?:string; navigate?:string; close?:number[]};
      if (out.navigate !== undefined && loadPage) {
        try { await loadPage(out.navigate); } catch (e) { console.error(`webdriver bidi: navigation failed: ${e}`); }
      }
      if (out.reply !== undefined && socket.readyState === WebSocket.OPEN) socket.send(out.reply);
      for (const k of out.close ?? []) { sockets.get(k)?.close(1000, "session ended"); sockets.delete(k); }
    }).catch((e) => console.error(`webdriver bidi: ${e}`));
  };
  socket.onclose = () => {
    sockets.delete(id);
    engine.scriptSession("", {action:"bidiClose", connection:id});
  };
  return response;
}
