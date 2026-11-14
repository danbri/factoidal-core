// Property-heavy object code: constructors, prototype methods, object literals, getters,
// optional chaining and `in`. Typical of model and state code in page bundles.
function Point(x, y) { this.x = x; this.y = y; }
Point.prototype.add = function (o) { return new Point(this.x + o.x, this.y + o.y); };
Point.prototype.len2 = function () { return this.x * this.x + this.y * this.y; };
class Box {
  constructor(id, w, h) { this.id = id; this.w = w; this.h = h; this.meta = { tag: "b" + (id % 7), seen: 0 }; }
  get area() { return this.w * this.h; }
  grow(d) { this.w += d; this.h += d; this.meta.seen++; return this; }
}
function run(n) {
  let acc = 0, p = new Point(0, 0);
  const boxes = [];
  for (let i = 0; i < n; i++) {
    p = p.add(new Point(i & 3, 1));
    const b = new Box(i, i % 5, 3);
    b.grow(1).grow(2);
    boxes.push(b);
    const cfg = { width: b.w, height: b.h, label: b.meta.tag, opts: { dense: (i & 1) === 0 } };
    acc += cfg.opts?.dense ? cfg.width : cfg.height;
    if ("label" in cfg) acc += cfg.label.length;
    acc += b.area % 11;
  }
  for (const b of boxes) acc += b.meta.seen;
  return acc + p.len2() % 1000;
}
RESULT = run(SCALE * 4000);
