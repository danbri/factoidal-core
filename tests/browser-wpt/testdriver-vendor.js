// Foafnaut's testdriver-vendor.js (this repository's own file; a WPT runner supplies its
// own, as wptrunner does). The runner (testharness-run.ts) serves it in place of
// /resources/testdriver-vendor.js. A request of test_driver leaves the page as a console
// line, as results do; the runner then gives the engine the input of the user it asks for
// (scriptSession action `key`), and the page sees trusted events. What a key does is the
// engine's decision (DOM.Editing.keyCommand); this file only names the keys of WebDriver.
// Done: send_keys and the key actions of action_sequence. Not done: pointer actions, click.
(function () {
  'use strict';
  if (!window.test_driver_internal) return;
  // WebDriver's key code points (WebDriver §17.4.2) as KeyboardEvent key values.
  const KEYS = { '': null, '': 'Backspace', '': 'Tab', '': 'Enter', '': 'Enter', '': 'Shift',
    '': 'Control', '': 'Alt', '': 'Escape', '': ' ', '': 'PageUp', '': 'PageDown',
    '': 'End', '': 'Home', '': 'ArrowLeft', '': 'ArrowUp', '': 'ArrowRight', '': 'ArrowDown',
    '': 'Insert', '': 'Delete', '': 'Meta', '': 'Shift', '': 'Control', '': 'Alt', '': 'Meta' };
  const MODS = { Shift: 'shiftKey', Control: 'ctrlKey', Alt: 'altKey', Meta: 'metaKey' };
  const KEYCODES = { Backspace: 8, Tab: 9, Enter: 13, Shift: 16, Control: 17, Alt: 18, Escape: 27, ' ': 32, PageUp: 33, PageDown: 34,
    End: 35, Home: 36, ArrowLeft: 37, ArrowUp: 38, ArrowRight: 39, ArrowDown: 40, Insert: 45, Delete: 46, Meta: 91 };
  const held = { shiftKey: false, ctrlKey: false, altKey: false, metaKey: false };
  const codeOf = key => /^[a-z]$/i.test(key) ? 'Key' + key.toUpperCase() : /^[0-9]$/.test(key) ? 'Digit' + key : key === ' ' ? 'Space'
    : key in MODS ? key + 'Left' : key.length === 1 ? '' : key;
  const keyCodeOf = key => KEYCODES[key] ?? (/^[a-z0-9]$/i.test(key) ? key.toUpperCase().charCodeAt(0) : 0);
  // One low-level key event of the user: the modifiers are those held when it happens.
  const keyEvent = (kind, raw) => {
    const key = raw in KEYS ? KEYS[raw] : raw;
    if (key === null) return null;
    if (key in MODS) held[MODS[key]] = kind === 'down';
    return Object.assign({ kind, key, code: codeOf(key), keyCode: keyCodeOf(key) }, held);
  };
  let serial = 0;
  // Ask the runner for the events; the promise resolves when the page has seen them all.
  const run = events => new Promise(resolve => {
    events = events.filter(e => e !== null);
    if (events.length === 0) { resolve(); return; }
    let left = events.length;
    const seen = e => {
      if (!e.isTrusted || --left > 0) return;
      window.removeEventListener('keydown', seen, true);
      window.removeEventListener('keyup', seen, true);
      setTimeout(resolve, 0);
    };
    window.addEventListener('keydown', seen, true);
    window.addEventListener('keyup', seen, true);
    console.log('__wpt_driver ' + JSON.stringify({ id: ++serial, keys: events }));
  });
  // "Element Send Keys" (WebDriver §12.5.3): the element is focused; a modifier in the text
  // stays down until the end of the text or the null key.
  window.test_driver_internal.send_keys = function (element, keys) {
    if (element && typeof element.focus === 'function') element.focus();
    const events = [], down = [];
    const release = () => { while (down.length) events.push(keyEvent('up', down.pop())); };
    for (const ch of String(keys)) {
      if (ch === '') { release(); continue; }
      const key = ch in KEYS ? KEYS[ch] : ch;
      if (key in MODS) { if (!down.includes(ch)) { down.push(ch); events.push(keyEvent('down', ch)); } continue; }
      events.push(keyEvent('down', ch));
      events.push(keyEvent('up', ch));
    }
    release();
    return run(events);
  };
  // "Perform Actions" (WebDriver §15.7) for key sources: tick by tick, each source's action.
  window.test_driver_internal.action_sequence = function (actions) {
    const events = [];
    const ticks = Math.max(0, ...actions.map(a => (a.actions || []).length));
    for (let i = 0; i < ticks; i++) {
      for (const source of actions) {
        const a = (source.actions || [])[i];
        if (!a || a.type === 'pause') continue;
        if (source.type === 'key' && (a.type === 'keyDown' || a.type === 'keyUp')) events.push(keyEvent(a.type === 'keyDown' ? 'down' : 'up', a.value));
        else return Promise.reject(new Error('action_sequence: ' + source.type + ' ' + a.type + ' is not implemented by testdriver-vendor.js'));
      }
    }
    return run(events);
  };
})();
