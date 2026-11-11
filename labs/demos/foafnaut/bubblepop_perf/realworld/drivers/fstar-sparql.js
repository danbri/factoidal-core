// The F*-extracted RDF and SPARQL engine (js_of_ocaml output): parse N subjects of Turtle,
// run one SELECT with a join and a FILTER, count and hash the rows.
(function () {
  var e = (module.exports && module.exports.factoidalNpmEntry) || globalThis.factoidalNpmEntry;
  if (N === 0) { console.log('RESULT 0'); return; }
  var parts = ['@prefix ex: <http://example.org/> .\n'];
  for (var i = 0; i < N; i++) {
    parts.push('ex:s' + i + ' ex:p ' + (i * 3 % 1000) + ' ; ex:q ex:s' + ((i + 1) % N) + ' ; ex:name "name ' + i + '" .\n');
  }
  var opened = JSON.parse(e.datasetOpen(parts.join(''), 'turtle', 'http://example.org/'));
  var h = mix(opened.ok ? 1 : 0, opened.count | 0);
  var q = 'PREFIX ex: <http://example.org/> SELECT ?s ?v ?n WHERE { ?s ex:q ?o . ?o ex:p ?v . ?s ex:name ?n . FILTER(?v > 500) } ORDER BY ?v ?n';
  var res = JSON.parse(e.datasetQuery(opened.handle, q));
  var rows = res.ok ? res.srj.results.bindings : [];
  h = mix(h, rows.length);
  for (var r = 0; r < rows.length; r++) h = mixStr(mixStr(h, rows[r].v.value), rows[r].n.value);
  e.datasetClose(opened.handle);
  console.log('RESULT ' + h);
})();
