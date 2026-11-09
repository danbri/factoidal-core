// Short-lived small objects and arrays.
var keep = null, n = 0;
for (var i = 0; i < 200000; i++) {
  var p = { x: i, y: i + 1, next: keep };
  if (i % 16 == 0) keep = { v: [i, p.y] }; else keep = p.next;
  n += p.x & 1;
}
print(n);
