import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';

// Exercise the actual IDL property implementation without building an engine. The
// native-query stub records the ABI boundary; Lean guards and WPT test DOM state.
const prelude = readFileSync(new URL('../../tools/wasmvm/quickjs/prelude.js', import.meta.url), 'utf8');
const start = prelude.indexOf("    prop(T, 'value',");
const end = prelude.indexOf("    prop(T, 'defaultValue',", start);
assert.ok(start >= 0 && end > start);
const install = new Function('prop', 'T', 'selOf', 'n', 'nodeId', 'chk', prelude.slice(start, end));

function control(raw = '') {
  function T() {}
  const calls = [], selection = { start: 1, end: 2, dir: 'backward' };
  const n = { query(id, op, q) {
    calls.push([id, op, q]);
    if (q === 'v') return raw;
    assert.ok(q.startsWith('s'));
    raw = q.slice(1);
    return '';
  } };
  install((C, name, get, set) => Object.defineProperty(C.prototype, name, { get, set }),
    T, () => selection, n, () => 42, v => v);
  const el = new T();
  Object.defineProperty(el, 'textContent', {
    get() { throw new Error('value must read the live state, not default child text'); },
    set() { throw new Error('value must not mutate child nodes'); },
  });
  return { el, calls, selection };
}

test('getter reads native raw state and normalizes CRLF and CR', () => {
  const { el, calls } = control('a\r\nb\rc');
  assert.equal(el.value, 'a\nb\nc');
  assert.deepEqual(calls, [[42, 169, 'v']]);
});

test('setter forwards raw text unchanged and uses API length for selection', () => {
  const { el, calls, selection } = control();
  el.value = 'a\r\nb';
  assert.ok(calls.some(c => c[2] === 'sa\r\nb'));
  assert.equal(el.value, 'a\nb');
  assert.deepEqual(selection, { start: 3, end: 3, dir: 'none' });
});

test('equal API value still reaches Lean to set dirty flag and preserves selection', () => {
  const { el, calls, selection } = control('a\nb');
  el.value = 'a\r\nb';
  assert.ok(calls.some(c => c[2] === 'sa\r\nb'));
  assert.deepEqual(selection, { start: 1, end: 2, dir: 'backward' });
});

test('null becomes empty and other values use DOMString conversion', () => {
  const { el, calls } = control('old');
  el.value = null;
  assert.equal(el.value, '');
  el.value = undefined;
  assert.equal(el.value, 'undefined');
  assert.ok(calls.some(c => c[2] === 's'));
  assert.ok(calls.some(c => c[2] === 'sundefined'));
});

test('empty setter still reaches Lean when the API value is already empty', () => {
  const { el, calls } = control();
  el.value = '';
  assert.ok(calls.some(c => c[2] === 's'));
});

test('input value implementation remains separate from textarea raw-value handling', () => {
  const original = readFileSync(new URL('../../formal/lean4/L4Factoidal/WasmVM/Hosts/DomOps.lean', import.meta.url), 'utf8');
  const valueOp = original.slice(original.indexOf('  | 169 =>'), original.indexOf('  -- 189:'));
  assert.match(valueOp, /\["textarea"\][\s\S]*return d\.textareaRawValue n/);
  assert.match(valueOp, /\["input"\][\s\S]*Forms\.valueModeOf[\s\S]*Forms\.inputValue d n/);
  assert.match(valueOp, /\.filename => if rest\.isEmpty then return "" else throw \(-16\)/);
});
