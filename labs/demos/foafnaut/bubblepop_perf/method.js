// Method calls through the prototype chain, `this`, field updates.
class Vec {
  constructor(x, y) { this.x = x; this.y = y; }
  dot(o) { return this.x * o.x + this.y * o.y; }
  bump(d) { this.x += d; return this; }
}
var a = new Vec(1, 2), b = new Vec(3, 4), s = 0;
for (var i = 0; i < 300000; i++) { s = (s + a.dot(b)) % 1000; a.bump(1); }
print(s);
