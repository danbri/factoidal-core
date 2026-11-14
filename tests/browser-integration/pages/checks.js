// Helpers of the integration fixtures, over testharness.js (a classic script).
'use strict';
function rectOf(id) {
  const r = document.getElementById(id).getBoundingClientRect();
  return [r.x, r.y, r.width, r.height];
}
// The border box of an element, each number within `tolerance` CSS pixels.
function assert_rect(id, expected, tolerance) {
  const got = rectOf(id), names = ['x', 'y', 'width', 'height'];
  const shown = '[' + got.map(function (v) { return Math.round(v * 100) / 100; }).join(', ') + ']';
  for (let i = 0; i < 4; i++) assert_approx_equals(got[i], expected[i], tolerance === undefined ? 0.5 : tolerance, id + ' ' + names[i] + ' of ' + shown);
}
function styleOf(id, property) {
  return getComputedStyle(document.getElementById(id)).getPropertyValue(property);
}
// The checks that every fixture shares: the external sheet, the cascade's selectors and
// values, and the layout modes. Each is one subtest, so a result names what failed.
function sharedChecks() {
  test(function () { assert_equals(styleOf('header', 'background-color'), 'rgb(0, 102, 204)'); },
    'external sheet: the header colour comes through a custom property');
  test(function () { assert_equals(getComputedStyle(document.documentElement).getPropertyValue('--gap').trim(), '10px'); },
    'custom property: a script reads --gap');
  test(function () { assert_rect('header', [0, 10, 600, 40]); }, 'block: the header box');
  test(function () { assert_equals(rectOf('n1')[3], 26); }, 'selector: a child combinator rule sets a height');
  test(function () {
    assert_rect('n1', [0, 50, 193.33, 26]); assert_rect('n2', [203.33, 50, 193.33, 26]); assert_rect('n3', [406.67, 50, 193.33, 26]);
  }, 'flex: three equal items in a row with a gap');
  test(function () {
    assert_rect('c1', [0, 80, 193.33, 50]); assert_rect('c2', [203.33, 80, 193.33, 50]); assert_rect('c3', [406.67, 80, 193.33, 50]);
    assert_rect('c4', [0, 140, 193.33, 50]); assert_rect('c5', [203.33, 140, 193.33, 50]);
  }, 'grid: three columns, two rows');
  test(function () { assert_equals(styleOf('wide', 'display'), 'block'); assert_rect('wide', [0, 200, 600, 10]); },
    'media query: a block that holds applies');
  test(function () { assert_equals(styleOf('never', 'display'), 'none'); }, 'media query: a block that does not hold does not apply');
  test(function () {
    assert_true(matchMedia('(min-width: 300px)').matches, 'min-width: 300px'); assert_false(matchMedia('(min-width: 100000px)').matches, 'min-width: 100000px');
  }, 'media query: matchMedia agrees with the sheet');
  test(function () { assert_rect('abs', [550, 350, 50, 20]); }, 'position: absolute in a relative box');
  test(function () { assert_rect('bb', [0, 380, 100, 30]); }, 'box-sizing: border-box');
  test(function () { assert_rect('units', [32, 410, 280, 20]); }, 'values: calc(), rem and em lengths');
  const probes = [['s-child', 'child combinator'], ['s-next', 'next-sibling combinator'], ['s-attr', 'attribute selector'],
    ['s-not', ':not()'], ['s-first', ':first-child'], ['s-nth', ':nth-child()'], ['s-is', ':is()']];
  probes.forEach(function (p) {
    test(function () { assert_equals(rectOf(p[0])[3], 4); }, 'selector in the cascade: ' + p[1]);
  });
  test(function () {
    assert_equals(document.querySelectorAll('#selbox > .child, #selbox .first + .next, #selbox [data-k="v"], #selbox .plain:not(.other), #selbox :is(.one, .two)').length, 5);
  }, 'selector in querySelectorAll: the same selectors match');
}
// When the page's tests have ended: the boxes its scripts read and the tree its scripts see,
// as console lines. A host that draws the page compares them with what it drew.
add_completion_callback(function () {
  const rects = {}, tree = [];
  document.querySelectorAll('*').forEach(function (el) {
    tree.push([el.localName, el.id, el.getAttribute('class') || '']);
    if (el.id) rects[el.id] = rectOf(el.id).map(function (v) { return Math.round(v * 100) / 100; });
  });
  console.log('__rects ' + JSON.stringify(rects));
  console.log('__dom ' + JSON.stringify(tree));
});
