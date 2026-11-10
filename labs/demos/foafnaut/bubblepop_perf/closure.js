// Closures: creation, captured variable reads and writes, calls.
function counter(k) { var c = 0; return function (d) { c += d * k; return c; }; }
var fs = [];
for (var i = 0; i < 1000; i++) fs.push(counter(i));
var s = 0;
for (var r = 0; r < 300; r++) for (var i = 0; i < fs.length; i++) s = (s + fs[i](1)) % 65536;
print(s);
