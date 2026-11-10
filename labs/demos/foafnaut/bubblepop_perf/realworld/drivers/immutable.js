// immutable: persistent Map and List, N inserts, N updates, N pushes, then folds.
(function () {
  var I = module.exports;
  if (N === 0) { console.log('RESULT 0'); return; }
  var m = I.Map(), i;
  for (i = 0; i < N; i++) m = m.set('k' + i, i);
  for (i = 0; i < N; i++) m = m.update('k' + ((i * 7) % N), function (v) { return v + 1; });
  var l = I.List();
  for (i = 0; i < N; i++) l = l.push(i * 3);
  for (i = 0; i < N; i += 5) l = l.set(i, i);
  var h = mix(m.size, l.size);
  h = mix(h, m.reduce(function (a, v) { return (a + v) | 0; }, 0));
  h = mix(h, l.reduce(function (a, v) { return (a ^ v) | 0; }, 0));
  h = mix(h, m.filter(function (v) { return v % 2 === 0; }).size);
  h = mix(h, l.map(function (v) { return v + 1; }).filter(function (v) { return v % 3 === 0; }).size);
  h = mix(h, I.is(m, m.set('k0', m.get('k0'))) ? 1 : 2);
  console.log('RESULT ' + h);
})();
