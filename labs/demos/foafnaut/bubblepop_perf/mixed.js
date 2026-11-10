// A small program: Map, sort with a comparator, array methods, string keys.
var m = new Map();
for (var i = 0; i < 20000; i++) m.set("k" + (i % 500), i);
var a = [];
m.forEach(function (v, k) { a.push({ k: k, v: v }); });
a.sort(function (x, y) { return y.v - x.v; });
var t = a.map(function (e) { return e.v * 2; }).filter(function (v) { return v % 3 == 0; }).reduce(function (s, v) { return s + v; }, 0);
var o = {};
for (var i = 0; i < 20000; i++) { var k = "p" + (i % 100); o[k] = (o[k] | 0) + i; }
var c = 0;
for (var k in o) c += o[k];
print(t, c);
