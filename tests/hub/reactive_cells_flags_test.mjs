import test from 'node:test';
import assert from 'node:assert/strict';

import { parseCellFlags } from '../../docs/web/hub/reactive-cells.mjs';

// parseCellFlags() reads the fence-line text after the `observable-js`
// language word (docs/.eleventy.js passes it the raw fence info string
// minus the language; docs/_includes/hub.njk and
// tests/hub/_helpers.mjs's extractObservableCellsWithFlags() pass it
// the same text back from the built `data-hub-cell-flags` attribute or
// the Markdown source). All three callers share one parser so they can
// never disagree about what a fence line's flags mean
// (https://github.com/danbri/factoidal/issues/686).

test('parseCellFlags: no flags text', () => {
  assert.deepEqual(parseCellFlags(''), { closed: false, title: null });
  assert.deepEqual(parseCellFlags(undefined), { closed: false, title: null });
  assert.deepEqual(parseCellFlags(null), { closed: false, title: null });
});

test('parseCellFlags: bare closed flag', () => {
  assert.deepEqual(parseCellFlags('closed'), { closed: true, title: null });
});

test('parseCellFlags: title only, value may contain spaces', () => {
  assert.deepEqual(parseCellFlags('title="Library: circuit helpers"'), {
    closed: false,
    title: 'Library: circuit helpers',
  });
});

test('parseCellFlags: closed and title together, either order', () => {
  assert.deepEqual(parseCellFlags('closed title="Library: circuit helpers"'), {
    closed: true,
    title: 'Library: circuit helpers',
  });
  assert.deepEqual(parseCellFlags('title="Library: circuit helpers" closed'), {
    closed: true,
    title: 'Library: circuit helpers',
  });
});

test('parseCellFlags: surrounding and repeated whitespace is ignored', () => {
  assert.deepEqual(parseCellFlags('   closed    title="X Y"   '), {
    closed: true,
    title: 'X Y',
  });
});

test('parseCellFlags: an unrecognized bare word or key="value" pair is ignored', () => {
  assert.deepEqual(parseCellFlags('closed experimental'), { closed: true, title: null });
  assert.deepEqual(parseCellFlags('foo="bar" closed'), { closed: true, title: null });
  assert.deepEqual(parseCellFlags('unknown'), { closed: false, title: null });
});

test('parseCellFlags: an empty title value is a real, non-null title', () => {
  assert.deepEqual(parseCellFlags('title=""'), { closed: false, title: '' });
});

// ---------------------------------------------------------------------
// https://github.com/danbri/factoidal/issues/690: the local-binding scan
// took a nested call's argument list for an arrow parameter list, so `model`
// below was recorded as a local and not wired as a reactive input (in the
// browser: ReferenceError). Fixed 2026-10-25; this case was an xfail.
// ---------------------------------------------------------------------
import { analyzeCell } from '../../docs/web/hub/reactive-cells.mjs';

test('analyzeCell: an arrow function inside a nested call keeps the outer argument as a reference, not a local', () => {
  const info = analyzeCell('return pretty(model.elements.map((el) => el.local));');
  assert.ok(info.refs.includes('model'), 'model must be a reference of the cell');
  assert.ok(!info.locals.has('model'), 'model must not be recorded as a local');
  assert.ok(info.locals.has('el'), 'el is the arrow parameter');
});

test('analyzeCell: the arrow parameters of nested and destructured forms are locals', () => {
  const a = analyzeCell('x = f(g((a, b) => a + b), ({ c }) => c, (d = 1) => d)');
  for (const v of ['a', 'b', 'c', 'd']) assert.ok(a.locals.has(v), v);
  assert.ok(!a.locals.has('f') && !a.locals.has('g'), 'f and g are references');
  assert.ok(a.refs.includes('f') && a.refs.includes('g'));
});
