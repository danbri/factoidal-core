// acorn: parse a generated program N times and count the nodes of the tree.
(function () {
  var acorn = module.exports;
  if (N === 0) { console.log('RESULT 0'); return; }
  var parts = [];
  for (var f = 0; f < 40; f++) {
    parts.push('function f' + f + '(a, b) {\n  var s = 0;\n  for (var i = 0; i < a.length; i++) {\n    if (a[i] > b && a[i] !== ' + f +
      ') { s += a[i] * ' + (f + 1) + '; } else { s -= b ? 1 : 2; }\n  }\n  try { s = g(s, { k: "v' + f + '", n: [1, 2, ' + f +
      '] }); } catch (e) { s = -1; }\n  return s + (a.length ? f' + (f ? f - 1 : 0) + '.name.length : 0);\n}\n');
  }
  var src = parts.join('');
  function count(node) {
    var n = 1;
    for (var k in node) {
      var v = node[k];
      if (v && typeof v === 'object') {
        if (Array.isArray(v)) { for (var i = 0; i < v.length; i++) if (v[i] && typeof v[i].type === 'string') n += count(v[i]); }
        else if (typeof v.type === 'string') n += count(v);
      }
    }
    return n;
  }
  var h = src.length;
  for (var r = 0; r < N; r++) h = mix(h, count(acorn.parse(src, { ecmaVersion: 2020 })));
  console.log('RESULT ' + h);
})();
