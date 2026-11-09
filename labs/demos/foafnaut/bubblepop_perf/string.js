// String concatenation in a loop, charCodeAt, indexing, slice.
var t = "";
for (var i = 0; i < 40000; i++) t += String.fromCharCode(97 + i % 26);
var h = 0;
for (var i = 0; i < t.length; i++) h = (h * 31 + t.charCodeAt(i)) | 0;
var n = 0;
for (var i = 0; i + 8 < t.length; i += 8) if (t.slice(i, i + 4) === "abcd" || t[i] === "z") n++;
print(h, n);
