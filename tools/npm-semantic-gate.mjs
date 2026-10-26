#!/usr/bin/env node
// Selected product regressions, not an all-suites conformance runner.
// Run each case in another process: synchronous wasm cannot block the timer.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { mkdtemp, readFile, realpath, rm, stat, writeFile } from 'node:fs/promises';
import { fork, spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { basename, join, resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const SELF = fileURLToPath(import.meta.url);
const RDF = 'http://www.w3.org/1999/02/22-rdf-syntax-ns#';
const RDFS = 'http://www.w3.org/2000/01/rdf-schema#';
const OWL = 'http://www.w3.org/2002/07/owl#';
const XSD = 'http://www.w3.org/2001/XMLSchema#';
const DEFAULT_CASE_MS = 10_000;
const DEFAULT_TOTAL_MS = 120_000;
const REQUIRED_EXPORTS = ['loadEngine', 'parse', 'query', 'jsonldToRdf',
  'registerServiceEndpoint', 'clearServiceEndpoints', 'owlIsConsistent',
  'owlEntails', 'xsltTransform'];
const REQUIRED_OPS = ['datasetOpen', 'datasetQuery', 'datasetQueryRaw',
  'datasetQuery12', 'datasetUpdate', 'registerServiceEndpoint',
  'clearServiceEndpoints', 'owlIsConsistent', 'owlEntails', 'xsltTransform',
  'solidOpen', 'solidStep', 'solidClose'];
const UNCOVERED = [
  { finding: 'R07', obligation: 'Resource budgets for public operations and adversarial inputs.' },
  { finding: 'R11', obligation: 'CSVW external tables and metadata interoperability.' },
  { finding: 'R12', obligation: 'Published TypeScript declaration and implementation agreement.' },
  { finding: 'R13', obligation: 'RML source/iterator and logical-table interoperability.' },
];

function required(object, name) {
  if (typeof object?.[name] !== 'function') throw new Error(`Required public operation is missing: ${name}`);
  return object[name];
}

async function cardinality(ds, expected, observed, named = false) {
  observed.size = ds.size;
  observed.iterated = [...ds].length;
  observed.objects = [...ds].map(q => ({ termType: q.object.termType,
    value: q.object.value, datatype: q.object.datatype?.value, language: q.object.language }));
  const body = named ? 'GRAPH ?g { ?s ?p ?o }' : '?s ?p ?o';
  observed.count = (await ds.query(`SELECT (COUNT(*) AS ?n) WHERE { ${body} }`))[0]?.get('n')?.value;
  if (named) observed.defaultCount = (await ds.query('SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'))[0]?.get('n')?.value;
  assert.equal(observed.size, expected, 'Dataset.size');
  assert.equal(observed.iterated, expected, 'dataset iteration cardinality');
  assert.equal(observed.count, String(expected), 'SPARQL COUNT');
  if (named) assert.equal(observed.defaultCount, '0', 'named triples must not enter the default graph');
}

function catalog() {
  const entries = [];
  const add = (id, category, expected, run) => entries.push({ id, category, expected, run });
  const duplicate = '<urn:s> <urn:p> "x" .\n';
  for (const [format, input] of [
    ['turtle', '<urn:s> <urn:p> "x", "x" .'],
    ['ntriples', duplicate + duplicate],
    ['nquads', duplicate + duplicate],
    ['jsonld', '{"@id":"urn:s","urn:p":[{"@value":"x"},{"@value":"x"}]}'],
    ['rdfxml', '<rdf:RDF xmlns:rdf="' + RDF + '" xmlns:e="urn:"><rdf:Description rdf:about="urn:s"><e:p>x</e:p><e:p>x</e:p></rdf:Description></rdf:RDF>'],
  ]) {
    add(`R02.duplicate-default.${format}`, 'rdf-term-identity', { size: 1, iterated: 1, count: '1' }, async (f, o) => {
      const ds = format === 'jsonld' ? await f.jsonldToRdf(input) : await f.parse(input, { format });
      try { await cardinality(ds, 1, o); } finally { ds.dispose(); }
    });
  }
  for (const [name, text, size] of [
    ['one-named-graph', `<urn:g1> { ${duplicate}${duplicate} }`, 1],
    ['distinct-named-graphs', `<urn:g1> { ${duplicate} } <urn:g2> { ${duplicate} }`, 2],
  ]) {
    add(`R02.${name}`, 'rdf-term-identity', { size, iterated: size, count: String(size), defaultCount: '0' }, async (f, o) => {
      const ds = await f.parse(text, { format: 'trig' });
      try { await cardinality(ds, size, o, true); } finally { ds.dispose(); }
    });
  }
  for (const [name, objects, size] of [
    ['identical-iri', '<urn:o>, <urn:o>', 1],
    ['numeric-lexical', `"1"^^<${XSD}integer>, "01"^^<${XSD}integer>`, 2],
    ['different-datatype', `"1"^^<${XSD}string>, "1"^^<${XSD}integer>`, 2],
    ['different-language', '"x"@en, "x"@fr', 2],
  ]) {
    for (const format of ['turtle', 'nquads-roundtrip']) {
      add(`R02.${name}.${format}`, 'rdf-term-identity', { size, iterated: size, count: String(size) }, async (f, o) => {
        let ds = await f.parse(`<urn:s> <urn:p> ${objects} .`, { format: 'turtle' });
        try {
          if (format === 'nquads-roundtrip') {
            const nq = ds.toNQuads();
            ds.dispose();
            ds = await f.parse(nq, { format: 'nquads' });
          }
          await cardinality(ds, size, o);
        } finally { ds.dispose(); }
      });
    }
  }
  add('R14.xmlliteral-lexical.nquads', 'rdf-term-identity', { size: 2, iterated: 2, count: '2' }, async (f, o) => {
    const ds = await f.parse(`<urn:s> <urn:p> "<x a='1' b='2'/>"^^<${RDF}XMLLiteral> .\n` +
      `<urn:s> <urn:p> "<x b='2' a='1'/>"^^<${RDF}XMLLiteral> .`, { format: 'nquads' });
    try { await cardinality(ds, 2, o); } finally { ds.dispose(); }
  });

  const endpoint = 'https://service-options.example/sparql';
  const local = `@prefix ex: <https://service-options.example/> . ex:alice a ex:Student . ex:Student <${RDFS}subClassOf> ex:Person .`;
  const remote = '<https://service-options.example/alice> <https://service-options.example/name> "Alice" .';
  const serviceQuery = (options, iri = endpoint) => `SELECT ?name WHERE {
    <https://service-options.example/alice> a <https://service-options.example/${options.entail ? 'Person' : 'Student'}> .
    SERVICE <${iri}> { <https://service-options.example/alice> <https://service-options.example/name> ?name }
  }`;
  const answer = (value, options, o) => {
    if (options.output === 'csv') {
      o.answer = value;
      assert.equal(value, 'name\r\nAlice\r\n');
    } else if (options.output === 'json') {
      o.answer = value;
      assert.deepEqual(value.head.vars, ['name']);
      assert.deepEqual(value.results.bindings, [{ name: { type: 'literal', value: 'Alice' } }]);
    } else {
      o.answer = value.map(row => [...row].map(([key, term]) => [key, term.value]));
      assert.deepEqual(o.answer, [[['name', 'Alice']]]);
    }
  };
  for (const [name, options] of [
    ['ordinary', {}], ['json', { output: 'json' }], ['csv', { output: 'csv' }],
    ['rdfs', { entail: 'RDFS' }], ['rdfs-json', { entail: 'RDFS', output: 'json' }],
    ['rdfs-csv', { entail: 'RDFS', output: 'csv' }],
  ]) {
    for (const state of ['registered', 'missing', 'cleared']) {
      add(`R03.${state}.${name}`, 'query-execution-environment',
        state === 'registered' ? { name: 'Alice', inferredLocalTypeRequired: Boolean(options.entail) } : { rejects: 'SERVICE endpoint unavailable' },
        async (f, o) => {
          const ds = await f.parse(local, { format: 'turtle' });
          try {
            await f.clearServiceEndpoints();
            await f.registerServiceEndpoint(endpoint, remote, { format: 'ntriples' });
            if (state === 'cleared') {
              answer(await ds.query(serviceQuery({})), {}, o);
              await f.clearServiceEndpoints();
            }
            if (state === 'registered') answer(await f.query(ds, serviceQuery(options), options), options, o);
            else {
              let error;
              try { await ds.query(serviceQuery(options, state === 'missing' ? `${endpoint}/missing` : endpoint), options); }
              catch (caught) { error = caught; }
              o.error = error?.message;
              assert.match(error?.message ?? '', /SERVICE.*no endpoint is available/i);
            }
          } finally { await f.clearServiceEndpoints(); ds.dispose(); }
        });
    }
  }
  add('R04.variable-service', 'product-interoperability', { values: ['x'] }, async (f, o) => {
    const ds = await f.parse('');
    try {
      await f.registerServiceEndpoint('urn:svc', '<urn:s> <urn:p> "x" .');
      const rows = await ds.query('SELECT ?o WHERE { VALUES ?service { <urn:svc> } SERVICE ?service { ?s ?p ?o } }');
      o.values = rows.map(row => row.get('o')?.value);
      assert.deepEqual(o.values, ['x']);
    } finally { await f.clearServiceEndpoints(); ds.dispose(); }
  });
  add('R08.shared-blank-in-triple-term', 'rdf12-term-identity', { sameBlankNode: true }, async (f, o) => {
    const ds = await f.parse('_:b <urn:p> <urn:o> . <urn:s> <urn:q> <<( _:b <urn:p> <urn:o> )>> .', { format: 'turtle12' });
    try {
      const quads = ds.toArray();
      const outer = quads.find(q => q.predicate.value === 'urn:p');
      const inner = quads.find(q => q.predicate.value === 'urn:q')?.object?.subject;
      o.outerBlank = outer?.subject?.value;
      o.innerBlank = inner?.value;
      o.sameBlankNode = Boolean(inner && outer?.subject?.equals(inner));
      assert.equal(o.sameBlankNode, true);
    } finally { ds.dispose(); }
  });
  for (const operation of ['construct', 'insert']) {
    add(`R09.sparql12-${operation}`, 'public-api-version-routing', { size: 1, tripleTerm: true }, async (f, o) => {
      const ds = await f.parse('');
      let result;
      try {
        if (operation === 'construct') result = await ds.query('CONSTRUCT { <urn:s> <urn:q> <<( <urn:a> <urn:p> <urn:b> )>> } WHERE {}', { sparql12: true });
        else { await ds.update('INSERT DATA { <urn:s> <urn:q> <<( <urn:a> <urn:p> <urn:b> )>> }', { sparql12: true }); result = ds; }
        o.size = result.size;
        const object = [...result][0]?.object;
        o.tripleTerm = object?.termType === 'Quad' && object?.subject?.value === 'urn:a' &&
          object?.predicate?.value === 'urn:p' && object?.object?.value === 'urn:b';
        assert.equal(o.size, 1);
        assert.equal(o.tripleTerm, true);
      } finally { if (result && result !== ds) result.dispose(); ds.dispose(); }
    });
  }
  const same = `<urn:a> <${OWL}sameAs> <urn:b> .`;
  const different = `<urn:a> <${OWL}differentFrom> <urn:b> .`;
  add('R10.same-and-different', 'owl-verdict-soundness', { consistent: false }, async (f, o) => {
    o.answer = await f.owlIsConsistent(same + different, { format: 'ntriples' });
    assert.equal(o.answer.consistent, false);
  });
  for (const [name, input] of [['same-only', same], ['different-only', different]]) {
    add(`R10.${name}`, 'owl-verdict-soundness', { consistentIsNotFalse: true }, async (f, o) => {
      o.answer = await f.owlIsConsistent(input, { format: 'ntriples' });
      assert.ok(o.answer.consistent === true || o.answer.consistent === null, 'must not invent an inconsistency');
    });
  }
  add('R10.checked-model', 'owl-assurance-policy', { consistent: true }, async (f, o) => {
    o.answer = await f.owlIsConsistent(`<urn:a> <${RDF}type> <urn:C> .`, { format: 'ntriples' });
    // A checked finite model (AtomicModel.checkModel_sound,
    // https://github.com/danbri/factoidal/issues/960).
    assert.equal(o.answer.consistent, true);
  });
  add('R10.truncated-search', 'owl-verdict-soundness', { consistent: null }, async (f, o) => {
    const premise = `<urn:i> <${RDF}type> <urn:A> . <urn:A> <${RDFS}subClassOf> _:r . ` +
      `_:r <${OWL}onProperty> <urn:p> . _:r <${OWL}someValuesFrom> <urn:A> .`;
    o.answer = await f.owlIsConsistent(premise, { format: 'ntriples', fuel: 1 });
    assert.equal(o.answer.consistent, null);
  });
  add('R10.unsupported-negation', 'owl-verdict-soundness', { entailed: null }, async (f, o) => {
    o.answer = await f.owlEntails('', '<urn:a> <urn:p> "value" .', { format: 'ntriples' });
    assert.equal(o.answer.entailed, null, 'unsupported negation must not establish a countermodel');
  });
  // These fixtures have Direct Semantics models. RDF-based closure must not
  // turn annotations or equality of punned individuals into class constraints.
  // Sources and explicit models: docs/20261021-npm-semantic-gate.md.
  for (const [name, input] of [
    ['annotation-property-domain', `@prefix owl: <${OWL}> . @prefix rdfs: <${RDFS}> .
      <urn:p> a owl:AnnotationProperty; rdfs:domain owl:Nothing .
      <urn:a> <urn:p> "note" .`],
    ['class-individual-punning', `@prefix owl: <${OWL}> .
      <urn:C> a owl:Class, owl:NamedIndividual; owl:sameAs <urn:D>; owl:disjointWith <urn:D> .
      <urn:D> a owl:Class, owl:NamedIndividual .
      <urn:x> a owl:NamedIndividual, <urn:C> .`],
  ]) {
    add(`R10.direct.${name}`, 'owl-regime',
      { semanticRegime: 'OWL 2 Direct Semantics', consistentIsNotFalse: true }, async (f, o) => {
        o.answer = await f.owlIsConsistent(input, { format: 'turtle' });
        assert.ok(o.answer.consistent === true || o.answer.consistent === null,
          'a graph with a Direct Semantics model must not be reported inconsistent');
      });
  }
  add('R05.xslt-attribute-set', 'xslt-behavior', { color: 'black' }, async (f, o) => {
    o.xml = await f.xsltTransform('<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:attribute-set name="a"><xsl:attribute name="color">black</xsl:attribute></xsl:attribute-set><xsl:template match="/"><out xsl:use-attribute-sets="a"/></xsl:template></xsl:stylesheet>', '<in/>');
    assert.match(o.xml, /color=["']black["']/);
  });
  for (const [name, options] of [['default', {}], ['explicit-secure', { insecureNoAuth: false }]]) {
    add(`R06.solid-anonymous-put.${name}`, 'secure-library-default', { status: 401 }, async (f, o, pkg) => {
      const solid = await import(pathToFileURL(join(pkg, 'solid/server/index.mjs')).href);
      const storage = await required(solid, 'openSolidStorage')({ baseIri: 'http://example.test/', ...options });
      try {
        o.status = (await storage.step({ method: 'PUT', target: '/gate.txt',
          headers: [['content-type', 'text/plain']], body: 'hello' })).status;
        assert.equal(o.status, 401);
      } finally { storage.close(); }
    });
  }
  add('R01.reject-nonexistent-package', 'gate-control', { exitCode: 1, reportErrors: true }, async (_f, o) => {
    const temp = await mkdtemp(join(tmpdir(), 'factoidal-gate-missing-'));
    try {
      const report = join(temp, 'missing.json');
      const result = spawnSync(process.execPath, [SELF, '--package', join(temp, 'absent'), '--json', report],
        { timeout: 3_000, encoding: 'utf8', env: cleanEnvironment() });
      o.exitCode = result.status;
      o.spawnError = result.error?.message;
      assert.equal(result.status, 1);
      const written = JSON.parse(await readFile(report, 'utf8'));
      o.counts = written.counts;
      assert.ok(written.counts.error > 0);
      assert.equal(written.selectedRegressionsPassed, false);
    } finally { await rm(temp, { recursive: true, force: true }); }
  });
  return entries;
}

function validateCatalog(entries) {
  assert.ok(entries.length > 0, 'zero discovered cases is a gate failure');
  const ids = entries.map(c => c.id);
  assert.equal(new Set(ids).size, ids.length, 'case IDs must be unique');
  for (const c of entries) assert.equal(typeof c.run, 'function', `missing implementation: ${c.id}`);
}

function cleanEnvironment(pkg) {
  const env = { ...process.env };
  delete env.NODE_OPTIONS;
  delete env.FACTOIDAL_L4_ASSETS;
  if (pkg) env.FACTOIDAL_L4_ASSETS = join(pkg, 'l4-assets');
  return env;
}

async function worker(pkg, id) {
  const observed = {};
  try {
    // An actual synchronous block tests the parent deadline, not Promise.race.
    if (id === '@selftest-block') for (;;) { /* killed by parent */ }
    if (id === '@selftest-exit') process.exit(7);
    if (id === '@selftest-error') throw new Error('deliberate worker error');
    const entries = catalog();
    const entry = entries.find(c => c.id === id);
    if (!entry && id !== '@metadata') throw new Error(`Unknown worker case: ${id}`);
    const f = id === 'R01.reject-nonexistent-package' ? null : await import(pathToFileURL(join(pkg, 'index.mjs')).href);
    if (id === '@metadata') {
      for (const name of REQUIRED_EXPORTS) required(f, name);
      const engine = await f.loadEngine();
      required(engine, 'call');
      const reflection = engine.call('ops', []);
      assert.ok(Array.isArray(reflection.ops) && reflection.ops.length > 0, 'engine returned zero operations');
      const absent = REQUIRED_OPS.filter(op => !reflection.ops.includes(op));
      if (absent.length) throw new Error(`Required engine operations are missing: ${absent.join(', ')}`);
      observed.engine = f.engine ?? null;
      observed.packageApiVersion = f.version ?? null;
      observed.engineVersion = typeof engine.version === 'function' ? engine.version() : null;
      observed.abiVersion = reflection.abiVersion ?? null;
      observed.opCount = reflection.ops.length;
      observed.requiredOps = REQUIRED_OPS;
    } else await entry.run(f, observed, pkg);
    return { status: 'pass', observed };
  } catch (error) {
    return { status: error?.code === 'ERR_ASSERTION' ? 'fail' : 'error', observed,
      error: { name: error?.name ?? 'Error', message: String(error?.message ?? error),
        stack: String(error?.stack ?? '').slice(0, 4_000) } };
  }
}

function runWorker(pkg, id, limitMs, signal) {
  return new Promise(resolveResult => {
    const started = performance.now();
    if (signal?.aborted || limitMs <= 0) return resolveResult({ status: 'timeout', elapsedMs: 0, reason: 'whole-execution deadline reached before start' });
    const child = fork(SELF, ['--worker', id, '--package', pkg],
      { silent: true, execArgv: [], env: cleanEnvironment(pkg) });
    let message, timedOut = false, spawnError, stdout = '', stderr = '';
    const trim = (text, next) => (text + next).slice(0, 16_384);
    child.stdout.on('data', bytes => { stdout = trim(stdout, bytes); });
    child.stderr.on('data', bytes => { stderr = trim(stderr, bytes); });
    child.on('message', value => { message = value; });
    child.on('error', error => { spawnError = error.message; });
    const stop = () => { timedOut = true; child.kill('SIGKILL'); };
    const timer = setTimeout(stop, limitMs);
    signal?.addEventListener('abort', stop, { once: true });
    child.on('close', (code, terminationSignal) => {
      clearTimeout(timer);
      signal?.removeEventListener('abort', stop);
      const elapsedMs = Math.round(performance.now() - started);
      const logs = { ...(stdout ? { stdout } : {}), ...(stderr ? { stderr } : {}) };
      if (timedOut) resolveResult({ status: 'timeout', elapsedMs, limitMs, terminationSignal, ...logs });
      else if (code !== 0 || !message || !['pass', 'fail', 'error'].includes(message.status))
        resolveResult({ status: 'error', elapsedMs, exitCode: code, terminationSignal,
          error: { message: spawnError ?? 'Worker exited without a valid successful protocol response' }, ...logs });
      else resolveResult({ ...message, elapsedMs, ...logs });
    });
  });
}

async function hashFile(path, signal) {
  const hash = createHash('sha256');
  let bytes = 0;
  for await (const chunk of createReadStream(path, { signal })) { hash.update(chunk); bytes += chunk.length; }
  return { path, bytes, sha256: hash.digest('hex') };
}

function countsOf(rows) {
  const counts = { discovered: rows.length, pass: 0, fail: 0, error: 0, timeout: 0, skipped: 0 };
  for (const row of rows) {
    if (!['pass', 'fail', 'error', 'timeout', 'skipped'].includes(row.status)) throw new Error(`Invalid status: ${row.status}`);
    counts[row.status]++;
  }
  return counts;
}

function verdict(entries, rows, errors) {
  validateCatalog(entries);
  assert.deepEqual(rows.map(c => c.id), entries.map(c => c.id), 'every discovered case needs exactly one result');
  const counts = countsOf(rows);
  return errors.length === 0 && counts.pass === counts.discovered && counts.discovered > 0 &&
    counts.fail === 0 && counts.error === 0 && counts.timeout === 0 && counts.skipped === 0;
}

async function gate(options) {
  const entries = catalog();
  validateCatalog(entries);
  const started = performance.now();
  const controller = new AbortController();
  const deadline = setTimeout(() => controller.abort(), options.totalMs);
  const report = {
    schemaVersion: 1, gate: 'selected-npm-semantic-regressions',
    startedAt: new Date().toISOString(), nodeVersion: process.version,
    packageDirectory: resolve(options.pkg), reportPath: resolve(options.json),
    limits: { caseMs: options.caseMs, wholeExecutionMs: options.totalMs, mechanism: 'parent process kills isolated synchronous-wasm workers with SIGKILL' },
    scope: { allSuitesConformance: false, completeAuditCoverage: false,
      unimplementedObligations: UNCOVERED,
      notes: ['Self-contained product regressions only; no external corpus or network.',
        'R04 variable SERVICE is a product interoperability obligation, not a normative W3C claim.',
        'R10 consistency answers true only with a checked finite model (issue 960).',
        'Runner timeouts bound execution; they do not implement or certify R07 engine resource budgets.'] },
    artifacts: {}, engineMetadata: null, fatalErrors: [], rows: [],
  };
  let preflightError;
  try {
    const pkg = await realpath(options.pkg);
    report.packageDirectory = pkg;
    for (const file of ['package.json', 'index.mjs', 'l4-assets/l4factoidal.js',
      'l4-assets/l4factoidal.mjs', 'l4-assets/l4factoidal.wasm']) {
      const path = join(pkg, file);
      if (!(await stat(path)).isFile()) throw new Error(`Not a regular package file: ${path}`);
      report.artifacts[file] = await hashFile(path, controller.signal);
    }
    const metadata = JSON.parse(await readFile(join(pkg, 'package.json'), 'utf8'));
    report.package = { name: metadata.name ?? null, version: metadata.version ?? null };
  } catch (error) {
    preflightError = String(error.message);
    report.fatalErrors.push({ stage: 'package-preflight', message: preflightError });
  }
  const remaining = () => Math.max(0, options.totalMs - (performance.now() - started));
  try {
    if (!preflightError) {
      report.engineMetadata = await runWorker(report.packageDirectory, '@metadata', Math.min(options.caseMs, remaining()), controller.signal);
      if (report.engineMetadata.status !== 'pass') report.fatalErrors.push({ stage: 'engine-metadata', message: 'Engine identity or required operations could not be verified' });
    }
    for (const entry of entries) {
      let result;
      if (preflightError) result = { status: controller.signal.aborted ? 'timeout' : 'error',
        reason: `Not run: package preflight failed: ${preflightError}` };
      else result = await runWorker(report.packageDirectory, entry.id, Math.min(options.caseMs, remaining()), controller.signal);
      const row = { id: entry.id, category: entry.category, expected: entry.expected, ...result };
      report.rows.push(row);
      console.log(`${row.status.toUpperCase()} ${row.id}`);
    }
  } finally { clearTimeout(deadline); }
  report.counts = countsOf(report.rows);
  report.selectedRegressionsPassed = verdict(entries, report.rows, report.fatalErrors);
  report.elapsedMs = Math.round(performance.now() - started);
  report.finishedAt = new Date().toISOString();
  // Refuse to overwrite prior evidence, including audit originals.
  await writeFile(options.json, JSON.stringify(report, null, 2) + '\n', { flag: 'wx' });
  const c = report.counts;
  console.log(`${c.discovered} discovered; ${c.pass} pass, ${c.fail} fail, ${c.error} error, ${c.timeout} timeout, ${c.skipped} skipped`);
  console.log(`Report: ${resolve(options.json)}`);
  return report.selectedRegressionsPassed ? 0 : 1;
}

async function selfTest() {
  const temp = await mkdtemp(join(tmpdir(), 'factoidal-gate-selftest-'));
  const checks = [];
  const check = async (id, action) => { await action(); checks.push(id); console.log(`PASS ${id}`); };
  try {
    await check('zero-cases-rejected', () => assert.throws(() => validateCatalog([]), /zero discovered/));
    await check('duplicate-ids-rejected', () => assert.throws(() => validateCatalog([{ id: 'x', run() {} }, { id: 'x', run() {} }]), /unique/));
    const one = [{ id: 'x', run() {} }];
    await check('skips-rejected', () => assert.equal(verdict(one, [{ id: 'x', status: 'skipped' }], []), false));
    await check('missing-results-rejected', () => assert.throws(() => verdict(one, [], []), /exactly one result/));
    await check('nonzero-worker-rejected', async () => assert.equal((await runWorker(temp, '@selftest-exit', 2_000)).status, 'error'));
    await check('worker-errors-rejected', async () => assert.equal((await runWorker(temp, '@selftest-error', 2_000)).status, 'error'));
    await check('synchronous-worker-killed', async () => {
      const result = await runWorker(temp, '@selftest-block', 200);
      assert.equal(result.status, 'timeout');
      assert.ok(result.elapsedMs < 2_000);
    });
    await check('whole-execution-kills-worker', async () => {
      const controller = new AbortController();
      const timer = setTimeout(() => controller.abort(), 200);
      try {
        const result = await runWorker(temp, '@selftest-block', 10_000, controller.signal);
        assert.equal(result.status, 'timeout');
        assert.ok(result.elapsedMs < 2_000);
      } finally { clearTimeout(timer); }
    });
    await check('nonexistent-package-fails-nonzero', async () => {
      const result = await worker(temp, 'R01.reject-nonexistent-package');
      assert.equal(result.status, 'pass', JSON.stringify(result));
    });
    await check('missing-public-operation-rejected', () => assert.throws(() => required({}, 'query'), /missing/));
    await check('missing-engine-operation-rejected', async () => {
      const ops = REQUIRED_OPS.filter(name => name !== 'datasetQueryRaw');
      const stub = REQUIRED_EXPORTS.map(name => name === 'loadEngine'
        ? `export async function loadEngine() { return {call() { return {ops: ${JSON.stringify(ops)}}; }}; }`
        : `export function ${name}() {}`).join('\n');
      await writeFile(join(temp, 'index.mjs'), stub);
      const result = await runWorker(temp, '@metadata', 2_000);
      assert.equal(result.status, 'error');
      assert.match(result.error.message, /Required engine operations are missing: datasetQueryRaw/);
    });
    await check('report-overwrite-refused', async () => {
      const path = join(temp, 'evidence.json');
      await writeFile(path, 'original');
      await assert.rejects(() => writeFile(path, 'replacement', { flag: 'wx' }), { code: 'EEXIST' });
      assert.equal(await readFile(path, 'utf8'), 'original');
    });
    console.log(`Gate self-test: ${checks.length} pass, 0 fail; no package conformance claim.`);
    return 0;
  } finally { await rm(temp, { recursive: true, force: true }); }
}

function argumentsOf(args) {
  const out = { caseMs: DEFAULT_CASE_MS, totalMs: DEFAULT_TOTAL_MS };
  for (let i = 0; i < args.length; i++) {
    const key = args[i];
    if (key === '--self-test') out.selfTest = true;
    else if (key === '--help') out.help = true;
    else if (['--package', '--json', '--case-timeout-ms', '--timeout-ms', '--worker'].includes(key)) {
      const value = args[++i];
      if (!value || value.startsWith('--')) throw new Error(`Missing value for ${key}`);
      const field = { '--package': 'pkg', '--json': 'json', '--case-timeout-ms': 'caseMs', '--timeout-ms': 'totalMs', '--worker': 'worker' }[key];
      if (Object.hasOwn(out, field) && !['caseMs', 'totalMs'].includes(field)) throw new Error(`Repeated option: ${key}`);
      out[field] = ['caseMs', 'totalMs'].includes(field) ? Number(value) : value;
    } else throw new Error(`Unknown option: ${key}`);
  }
  for (const key of ['caseMs', 'totalMs']) if (!Number.isSafeInteger(out[key]) || out[key] <= 0 || out[key] > 3_600_000)
    throw new Error(`${key} must be an integer from 1 to 3600000`);
  if (!out.help && !out.selfTest && (!out.pkg || (!out.worker && !out.json))) throw new Error('--package DIR and --json REPORT are required');
  return out;
}

try {
  const options = argumentsOf(process.argv.slice(2));
  if (options.worker) {
    if (!process.send) throw new Error('Worker mode requires an IPC parent');
    const result = await worker(resolve(options.pkg), options.worker);
    process.send(result, error => process.exit(error ? 1 : 0));
  } else if (options.help) {
    console.log(`Usage: node ${basename(SELF)} --package DIR --json NEW_REPORT [--case-timeout-ms 10000] [--timeout-ms 120000]\n       node ${basename(SELF)} --self-test\nReports are never overwritten. This is a selected regression gate, not all-suites conformance.`);
  } else process.exitCode = options.selfTest ? await selfTest() : await gate(options);
} catch (error) {
  console.error(`npm-semantic-gate: ${error.message}`);
  process.exitCode = 1;
}
