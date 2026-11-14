// Foafnaut's testdriver-vendor.js (this repository's own file; a WPT runner supplies its
// own, as wptrunner does). The runner (testharness-run.ts) serves it in place of
// /resources/testdriver-vendor.js.
//
// A request of test_driver leaves the page as a console line, as results do. The runner
// gives it to the engine as input of the user (scriptSession action `actions`: WebDriver's
// Perform Actions, decided in L4Factoidal.WebDriver.Actions and dispatched as trusted
// events by Hosts.PageEvents), and answers with a `message` event at the window, as
// wptrunner's own vendor file is answered. Nothing about the input is decided here: this
// file names the element of a request (its tree path from the document) and passes the
// request on. A console line does this in the WPT runner only; no browser host reads it.
//
// Done: click, send_keys, action_sequence (key, pointer, wheel and none sources),
// delete_all_cookies (scriptSession action `cookies`: WebDriver's Delete All Cookies),
// get_computed_role and get_computed_label (scriptSession action `computed`).
// Not done (each rejects with "not implemented"): the other hooks of test_driver_internal.
(function () {
  'use strict';
  if (!window.test_driver_internal) return;
  const ELEMENT = 'element-6066-11e4-a52e-4f735466cecf';
  // The tree path of a node from this document: child indices, `s` into a shadow root.
  const pathOf = node => {
    const steps = [];
    while (node && node !== document) {
      const parent = node.parentNode;
      if (parent) { steps.unshift(Array.prototype.indexOf.call(parent.childNodes, node)); node = parent; }
      else if (typeof ShadowRoot === 'function' && node instanceof ShadowRoot && node.host) { steps.unshift('s'); node = node.host; }
      else return null;
    }
    return node === document ? 'path:' + steps.join('/') : null;
  };
  const refOf = element => {
    const path = pathOf(element);
    if (path === null) throw new Error('the element is not in the document of the test');
    return { [ELEMENT]: path };
  };
  let serial = 0;
  const pending = new Map();
  window.addEventListener('message', e => {
    const d = e.data;
    if (!d || d.type !== 'testdriver-complete' || !pending.has(d.id)) return;
    const [resolve, reject] = pending.get(d.id);
    pending.delete(d.id);
    if (d.status === 'success') resolve(d.value); else reject(new Error(d.message));
  });
  // Ask the runner; the promise settles when the page has seen every event of the request.
  const request = body => new Promise((resolve, reject) => {
    const id = ++serial;
    pending.set(id, [resolve, reject]);
    console.log('__wpt_driver ' + JSON.stringify(Object.assign({ id }, body)));
  });
  // "Delete All Cookies" (WebDriver §14.5): the engine empties the page session's jar.
  window.test_driver_internal.delete_all_cookies = function () { return request({ cookies: 'delete' }); };
  const attempt = f => { try { return f(); } catch (e) { return Promise.reject(e); } };
  // "Element Click" (WebDriver §12.5.1): a mouse moves to the element's in-view centre
  // point, and its primary button goes down and up.
  window.test_driver_internal.click = function (element) {
    return attempt(() => request({ actions: [{ type: 'pointer', id: 'testdriver click', parameters: { pointerType: 'mouse' },
      actions: [{ type: 'pointerMove', x: 0, y: 0, origin: refOf(element) }, { type: 'pointerDown', button: 0 }, { type: 'pointerUp', button: 0 }] }] }));
  };
  // "Element Send Keys" (WebDriver §12.5.3): the element is focused; the text is typed.
  window.test_driver_internal.send_keys = function (element, keys) {
    if (element && typeof element.focus === 'function' && document.activeElement !== element) element.focus();
    return request({ text: String(keys) });
  };
  // "Get Computed Role" (WebDriver §12.4.9): the engine's computed role of the element.
  window.test_driver_internal.get_computed_role = function (element) {
    return attempt(() => request({ computed: 'role', element: refOf(element)[ELEMENT] }));
  };
  // "Get Computed Label" (WebDriver §12.4.10): the engine's accessible name of the element.
  window.test_driver_internal.get_computed_label = function (element) {
    return attempt(() => request({ computed: 'label', element: refOf(element)[ELEMENT] }));
  };
  // "Perform Actions" (WebDriver §15.7): an element origin is named by its path.
  window.test_driver_internal.action_sequence = function (actions) {
    return attempt(() => request({ actions: actions.map(source => Object.assign({}, source, {
      actions: (source.actions || []).map(a => a && a.origin instanceof Element ? Object.assign({}, a, { origin: refOf(a.origin) }) : a) })) }));
  };
})();
