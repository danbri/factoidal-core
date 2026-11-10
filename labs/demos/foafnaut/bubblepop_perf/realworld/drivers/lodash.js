// lodash: filter, map, groupBy, sumBy, sortBy, uniqBy, keyBy over N generated records.
(function () {
  var _ = module.exports;
  if (N === 0) { console.log('RESULT 0'); return; }
  var next = lcg(7), rows = [];
  for (var i = 0; i < N; i++) rows.push({ id: i, group: next() % 17, score: next() % 1000, name: 'n' + (next() % 5000) });
  var h = 0;
  var sums = _.chain(rows).filter(function (o) { return o.score % 3 !== 0; })
    .map(function (o) { return { g: o.group, s: o.score * 2, n: o.name }; })
    .groupBy('g').mapValues(function (v) { return _.sumBy(v, 's'); }).value();
  _.forEach(_.sortBy(_.keys(sums)), function (k) { h = mix(mixStr(h, k), sums[k]); });
  var sorted = _.sortBy(rows, ['group', 'score', 'id']);
  for (var j = 0; j < sorted.length; j += 7) h = mix(h, sorted[j].id);
  h = mix(h, _.uniqBy(rows, 'name').length);
  var byId = _.keyBy(rows, 'id');
  h = mix(h, byId[N >> 1].score);
  h = mix(h, _.reduce(_.range(N), function (a, x) { return (a + (x % 13)) | 0; }, 0));
  h = mixStr(h, _.map(_.take(_.orderBy(rows, ['score', 'id'], ['desc', 'asc']), 5), 'name').join(','));
  console.log('RESULT ' + h);
})();
