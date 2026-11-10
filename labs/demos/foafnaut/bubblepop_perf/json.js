// JSON.stringify and JSON.parse of an array of small records.
var o = [];
for (var i = 0; i < 2000; i++) o.push({ id: i, name: "name" + i, tags: ["a", "b", i], ok: i % 2 == 0 });
var n = 0;
for (var r = 0; r < 10; r++) {
  var s = JSON.stringify(o);
  var v = JSON.parse(s);
  n += s.length + v[r].id;
}
print(n);
