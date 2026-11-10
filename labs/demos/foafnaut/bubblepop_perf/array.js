// Array push, index read, index write.
var a = [];
for (var i = 0; i < 200000; i++) a.push(i);
var s = 0;
for (var i = 0; i < a.length; i++) s += a[i];
for (var i = 0; i < a.length; i++) a[i] = s - a[i];
for (var i = 0; i < a.length; i += 3) s -= a[i];
print(s);
