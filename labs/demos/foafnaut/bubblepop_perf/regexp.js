// Regular expression exec over a long text, and replace.
var parts = [];
for (var i = 0; i < 4000; i++) parts.push("item" + i + "-" + (i % 7) + " ");
var t = parts.join(""), re = /item(\d+)-(\d)/g, m, n = 0;
while ((m = re.exec(t)) !== null) n += m[2].length;
print(n, t.replace(/\d+/g, "#").length);
