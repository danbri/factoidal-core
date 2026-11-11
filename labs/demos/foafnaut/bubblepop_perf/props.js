// Named property reads and writes on one object, in a loop.
var o = { a: 1, b: 2, c: 3, d: 4 };
var s = 0;
for (var i = 0; i < 300000; i++) { s += o.a + o.b; o.c = i; o.d = o.c; }
print(s + o.d);
