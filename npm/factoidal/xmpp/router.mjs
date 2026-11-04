// factoidal/xmpp/router.mjs — the routing table of an XMPP host, with no
// transport: the Node host (`server.mjs`, TCP, TLS, WebSocket) and the
// in-page host (`inpage.mjs`, whole messages over a MessagePort or a
// function call) share it. No Node or browser API is used here.
//
// A connection is any object with `bare`, `full` (the last values the
// engine reported, or null) and `deliver(text) → boolean` (hand it a stanza
// another session routed to it; false when its session refused). The engine
// decides where every stanza goes (`route`, `routeFull` of a feed answer);
// this file only finds the connections and calls `deliver`.

/**
 * @param {object} [options]
 * @param {Function} [options.onError]
 * @param {number} [options.pendingLimit] stanzas kept per bare JID for the
 *   race where a session closed between the engine's decision and the
 *   delivery (default 100)
 */
export function createXmppRouter (options = {}) {
  const onError = typeof options.onError === 'function' ? options.onError : () => {}
  const pendingLimit = typeof options.pendingLimit === 'number' ? options.pendingLimit : 100
  /** Every live connection. */
  const connections = new Set()
  /** bare JID → stanzas routed to it while no session was bound. */
  const pending = new Map()

  function boundTo (bare) {
    const found = []
    for (const c of connections) if (c.full !== null && c.bare === bare) found.push(c)
    return found
  }

  function hold (bare, text) {
    if (!pending.has(bare)) pending.set(bare, [])
    const q = pending.get(bare)
    if (q.length < pendingLimit) q.push(text)
    else onError(new Error(`dropped a stanza for ${bare}: the host fallback queue is full`))
  }

  /**
   * Deliver one stanza to every session bound to `bare`. The engine holds
   * stanzas for accounts with no bound session (L4Factoidal/XMPP/Held.lean,
   * bounded; issue 1235), so a route reaches here only for a bound account.
   * `pending` covers the race where that session closed between the
   * engine's decision and this delivery; it is bounded too.
   */
  function routeStanza (bare, text) {
    const targets = boundTo(bare)
    if (targets.length === 0) { hold(bare, text); return }
    for (const t of targets) {
      let delivered = false
      try { delivered = t.deliver(text) } catch (error) { onError(error); continue }
      if (!delivered) hold(bare, text)
    }
  }

  /**
   * `Out.routeFull`: deliver to the ONE session bound to `full`, now. With no
   * such session (or one that refuses), deliver the engine's bounce, if it
   * gave one, back to the sending session. Never held (RFC 6120 section
   * 10.5.3.2; https://github.com/danbri/factoidal/issues/1234).
   */
  function routeFull (sender, full, text, bounce) {
    for (const t of connections) {
      if (t.full !== full) continue
      try { if (t.deliver(text)) return } catch (error) { onError(error) }
    }
    if (typeof bounce === 'string' && sender !== null) {
      try { sender.deliver(bounce) } catch (error) { onError(error) }
    }
  }

  /** A session just bound: hand it what was waiting. */
  function flushPending (c) {
    const queue = pending.get(c.bare)
    if (!queue || queue.length === 0) return
    pending.delete(c.bare)
    for (const text of queue) routeStanza(c.bare, text)
  }

  /**
   * The routing part of one feed answer: the session's JIDs as the engine
   * reports them, then `route` and `routeFull`, then what waited for a
   * session that has just bound.
   */
  function apply (c, answer) {
    const wasBound = c.full !== null
    c.bare = typeof answer.bare === 'string' ? answer.bare : null
    c.full = typeof answer.full === 'string' ? answer.full : null
    for (const r of answer.route || []) routeStanza(r.to, r.text)
    for (const r of answer.routeFull || []) routeFull(c, r.to, r.text, r.bounce)
    if (!wasBound && c.full !== null) flushPending(c)
  }

  return { connections, pending, boundTo, routeStanza, routeFull, flushPending, apply }
}
