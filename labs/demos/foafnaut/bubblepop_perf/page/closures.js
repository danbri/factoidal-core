// Closures and array methods: map, filter, reduce, forEach, some, find, sort with a comparator,
// a small event-emitter and memoised selectors, as UI libraries write them.
function emitter() {
  const subs = {};
  return {
    on(t, f) { (subs[t] || (subs[t] = [])).push(f); return () => { subs[t] = subs[t].filter(g => g !== f); }; },
    emit(t, x) { let r = 0; (subs[t] || []).forEach(f => { r += f(x); }); return r; },
  };
}
function memo(f) { let lastA, lastR; return a => (a === lastA ? lastR : (lastA = a, lastR = f(a))); }
function run(n) {
  const items = [];
  for (let i = 0; i < n; i++) items.push({ id: i, price: (i * 37) % 101, tags: ["t" + (i % 5), "u" + (i % 3)] });
  const e = emitter();
  let total = 0;
  const off = e.on("x", v => v * 2);
  e.on("x", v => v + 1);
  const cheap = memo(list => list.filter(it => it.price < 30).map(it => it.id));
  for (let r = 0; r < 20; r++) {
    const ids = cheap(r % 2 ? items : items);
    total += ids.length;
    total += items.map(it => it.price).reduce((a, b) => a + b, 0);
    total += items.filter(it => it.tags.some(t => t === "t1")).length;
    const f = items.find(it => it.price === 100 - r);
    total += f ? f.id : 0;
    total += e.emit("x", r);
  }
  off();
  total += e.emit("x", 1);
  const sorted = items.slice(0, 2000).sort((a, b) => a.price - b.price || b.id - a.id);
  total += sorted[0].id + sorted[sorted.length - 1].id;
  return total;
}
RESULT = run(SCALE * 1000);
