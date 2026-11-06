import test from 'node:test';
import assert from 'node:assert/strict';
const core = await import(process.env.FACTOIDAL_COMPOSITOR_TEST_ENGINE || '@factoidal/core');
import { DEFAULTS, runPipeline } from '../../docs/web/hub/data-compositor/pipeline.mjs';

const ids = ['turtle', 'csvw', 'merge', 'closure', 'graphs', 'query', 'filter', 'diagnostic', 'xml', 'xslt', 'html', 'report'];

test('engine runs source stages, graph joins, inference, XML and HTML report', async () => {
  const events = [];
  const result = await runPipeline(core, DEFAULTS, event => events.push(structuredClone(event)));
  assert.deepEqual(result.stages.map(stage => stage.id), ids);
  assert.deepEqual(events.map(event => `${event.id}:${event.status}`), ids.flatMap(id => id === 'diagnostic' ? [`${id}:skipped`] : [`${id}:running`, `${id}:done`]));
  assert.deepEqual(result.rows.map(row => row.name), ['Mina Chen', 'Luz Silva', 'Nora Patel']);
  assert.deepEqual(result.rows.map(row => row.project), ['Aurora / short film', 'Pulse / music video', 'Aurora / short film']);
  assert.equal(result.inferredPeople.length, 5);
  assert.equal(result.counts.merged, 29);
  assert.equal(result.stages.find(stage => stage.id === 'query').count, 5);
  assert.ok(result.counts.derived > result.inferredPeople.length, 'closure total must not be presented as just Person memberships');
  const graphs = result.stages.find(stage => stage.id === 'graphs');
  for (const graph of result.graphNames) assert.ok(graphs.text.includes(graph));
  const xml = result.stages.find(stage => stage.id === 'xml').text;
  assert.match(xml, /http:\/\/www.w3.org\/2005\/sparql-results#/);
  assert.match(xml, /Mina Chen/);
  assert.doesNotMatch(xml, /Jonah Reed/);
  assert.match(result.html, /People behind the pixels/);
  assert.match(result.html, /Mina Chen/);
  assert.doesNotMatch(result.html, /Jonah Reed/);
  assert.equal(result.stages.find(stage => stage.id === 'xslt').evidence.checked, false);
  assert.equal(result.stages.find(stage => stage.id === 'csvw').evidence.checked, false);
  assert.equal(result.proved, false);
  assert.doesNotThrow(() => structuredClone(result));
  assert.doesNotThrow(() => JSON.stringify(result));
});

test('numeric slider and CSV edits change the real SPARQL rows and XSLT output', async () => {
  const high = await runPipeline(core, { minScore: '90' });
  assert.deepEqual(high.rows.map(row => row.name), ['Mina Chen']);
  const edited = await runPipeline(core, { csv: DEFAULTS.csv.replace('jonah,atlas,67', 'jonah,atlas,97') });
  assert.deepEqual(edited.rows.map(row => row.name), ['Jonah Reed', 'Mina Chen', 'Luz Silva', 'Nora Patel']);
  assert.match(edited.html, /Jonah Reed/);
  const none = await runPipeline(core, { minScore: '100' });
  assert.equal(none.rows.length, 0);
  assert.match(none.html, /0 artists in this cut/);
});

test('Person membership depends on the schema and team selection is evaluated in SPARQL', async () => {
  const noSubclass = await runPipeline(core, { turtle: DEFAULTS.turtle.replace('ex:Contributor rdfs:subClassOf foaf:Person .', '') });
  assert.equal(noSubclass.inferredPeople.length, 0);
  assert.equal(noSubclass.rows.length, 0);
  const team = await runPipeline(core, {
    query: DEFAULTS.query.replace('FILTER (?score >= {{MIN_SCORE}})', 'FILTER (?score >= {{MIN_SCORE}}) FILTER (?team = "Compositing")'),
    stylesheet: DEFAULTS.stylesheet.replace('People behind the pixels', 'Compositing crew'),
  });
  assert.deepEqual(team.rows.map(row => row.name), ['Luz Silva', 'Nora Patel']);
  assert.match(team.html, /Compositing crew/);
});

test('CSVW numeric fallback remains visible in the trace and the engine filters it', async () => {
  const result = await runPipeline(core, { csv: DEFAULTS.csv.replace('mina,aurora,94', 'mina,aurora,oops') });
  assert.match(result.stages.find(stage => stage.id === 'csvw').text, /"oops"/);
  assert.deepEqual(result.rows.map(row => row.name), ['Luz Silva', 'Nora Patel']);
});

test('empty edited sources report actual nonempty graphs instead of a hardcoded three', async () => {
  const result = await runPipeline(core, { turtle: '', csv: 'id,project,score,team\n' });
  assert.equal(result.rows.length, 0);
  assert.equal(result.designatedGraphNames.length, 3);
  assert.ok(result.graphNames.length < 3);
  assert.equal(result.stages.find(stage => stage.id === 'graphs').graphNames.length, result.graphNames.length);
});

test('filtered table, XML and HTML share one execution even with volatile UUID bindings', async () => {
  const query = DEFAULTS.query.replace('SELECT ?person ?name ?project ?score ?team', 'SELECT ?person ?name ?project ?score ?team ?ticket')
    .replace('FILTER (?score', 'BIND(STR(UUID()) AS ?ticket) FILTER (?score');
  const stylesheet = DEFAULTS.stylesheet.replace('</body>', `<p><xsl:for-each select="s:sparql/s:results/s:result"><xsl:value-of select="s:binding[@name='ticket']/*"/><xsl:text> </xsl:text></xsl:for-each></p></body>`);
  let filteredExecutions = 0;
  const observedCore = {
    ...core,
    run(node, ...args) {
      if (node.stage === 'shippedEvaluator' && node.params.query.includes('UUID()') && node.params.query.includes('>= 70')) filteredExecutions++;
      return core.run(node, ...args);
    },
    queryRaw(data, text, options) {
      if (text.includes('UUID()') && text.includes('>= 70')) filteredExecutions++;
      return core.queryRaw(data, text, options);
    },
  };
  const result = await runPipeline(observedCore, { query, stylesheet });
  assert.equal(filteredExecutions, 1);
  const xml = result.stages.find(stage => stage.id === 'xml').text;
  for (const row of result.rows) {
    assert.ok(row.ticket.startsWith('urn:uuid:'));
    assert.ok(xml.includes(row.ticket));
    assert.ok(result.html.includes(row.ticket));
  }
});

test('Lean XML-to-JSON projection preserves quoted names, Unicode and XML characters', async () => {
  const name = 'Mina "Q" & <light> Ω';
  const result = await runPipeline(core, { turtle: DEFAULTS.turtle.replace('"Mina Chen"', JSON.stringify(name)) });
  assert.equal(result.rows.find(row => row.score === '94').name, name);
  assert.match(result.html, /Mina "Q" &amp; &lt;light&gt; Ω/);
});

test('malformed inputs surface the failing stage and never produce a successful final frame', async () => {
  for (const [input, expectedStage] of [
    [{ turtle: '@prefix ex: <https://studio.example/> . this is not Turtle' }, 'turtle'],
    [{ metadata: '{broken JSON' }, 'csvw'],
    [{ query: 'SELECT WHERE { {{MIN_SCORE}}' }, 'query'],
    [{ minScore: 'NaN' }, 'filter'],
    [{ minScore: '101' }, 'filter'],
    [{ stylesheet: '<not-a-stylesheet/>' }, 'xslt'],
  ]) {
    const events = [];
    await assert.rejects(runPipeline(core, input, event => events.push(event)), error => error.stageId === expectedStage);
    assert.equal(events.at(-1).status, 'error');
    assert.equal(events.at(-1).id, expectedStage);
    assert.ok(!events.some(event => event.id === 'html' && event.status === 'done'));
  }
});
