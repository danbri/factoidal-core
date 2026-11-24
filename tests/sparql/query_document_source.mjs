import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';

// Native: node tests/sparql/query_document_source.mjs --native PATH
// Wasm:   node tests/sparql/query_document_source.mjs

function* astNodes(value) {
  if (Array.isArray(value)) {
    for (const item of value) yield* astNodes(item);
  } else if (value && typeof value === 'object') {
    if (typeof value.kind === 'string') yield value;
    for (const [key, child] of Object.entries(value)) {
      if (key !== 'source') yield* astNodes(child);
    }
  }
}

function ofKind(value, kind) {
  return [...astNodes(value)].filter(node => node.kind === kind);
}

function one(value, kind) {
  const matches = ofKind(value, kind);
  assert.equal(matches.length, 1, `expected one ${kind} node`);
  return matches[0];
}

function slice(query, { start, end }) {
  return Array.from(query).slice(start, end).join('');
}

function occurrence(query, text, index = 0) {
  let start = -text.length;
  for (let i = 0; i <= index; i++) {
    start = query.indexOf(text, start + text.length);
    assert.notEqual(start, -1, `missing fixture occurrence ${index} of ${text}`);
  }
  const offset = Array.from(query.slice(0, start)).length;
  return { start: offset, end: offset + Array.from(text).length };
}

function exact(node, query, text, index = 0) {
  assert.equal(node.source.origin, 'exact', `${node.kind} → ${text}`);
  assert.deepEqual(node.source.span, occurrence(query, text, index), node.kind);
  assert.equal(slice(query, node.source.span), text, node.kind);
}

function derived(node, query, parts) {
  assert.equal(node.source.origin, 'derived', node.kind);
  assert.deepEqual(node.source.spans.map(span => slice(query, span)), parts, node.kind);
}

function assertSpan(span, length, label) {
  assert.ok(span && Number.isInteger(span.start) && Number.isInteger(span.end), `${label} span`);
  assert.ok(0 <= span.start && span.start < span.end && span.end <= length, `${label} span bounds`);
}

function verifyNode(node, length, counts) {
  assert.ok(node.source && typeof node.source === 'object', `missing source on ${node.kind}`);
  const { origin, span, spans, reason } = node.source;
  assert.ok(Object.hasOwn(counts, origin), `unexpected ${node.kind} origin ${origin}`);
  counts[origin]++;
  if (reason !== undefined) assert.equal(typeof reason, 'string');
  if (origin === 'exact') {
    assertSpan(span, length, node.kind);
    assert.ok(!Object.hasOwn(node.source, 'spans'), `${node.kind} has extra spans`);
  } else if (origin === 'derived') {
    assert.ok(Array.isArray(spans) && spans.length > 0, `${node.kind} has no derived spans`);
    assert.ok(!Object.hasOwn(node.source, 'span'), `${node.kind} has an extra span`);
    for (const part of spans) assertSpan(part, length, node.kind);
  } else {
    assert.ok(!Object.hasOwn(node.source, 'span') && !Object.hasOwn(node.source, 'spans'),
      `${node.kind} has a source range (${origin})`);
  }
}

function verifyDocument(document, query, counts) {
  const length = Array.from(query).length;
  assert.equal(document.schema_version, 1);
  assert.equal(typeof document.parser_version, 'string');
  assert.equal(document.source.text, query);
  assert.equal(document.source.offsetEncoding, 'unicode-code-points');
  assert.deepEqual(document.source.span, { start: 0, end: length });
  for (const token of document.source.tokens) {
    assertSpan(token.span, length, 'token');
    assert.equal(slice(query, token.span), token.text);
  }
  for (const node of astNodes(document.ast)) verifyNode(node, length, counts);
  for (const { span, ast } of document.namedSubqueries) {
    assertSpan(span, length, 'named subquery');
    for (const node of astNodes(ast)) verifyNode(node, length, counts);
  }
  if (document.ast !== null) {
    assert.deepEqual(document.diagnostics, []);
    exact(document.ast, query, query);
  }
}

function eraseSource(value) {
  if (Array.isArray(value)) return value.map(eraseSource);
  if (value && typeof value === 'object') {
    return Object.fromEntries(Object.entries(value).filter(([key]) => key !== 'source')
      .map(([key, child]) => [key, eraseSource(child)]));
  }
  return value;
}

function optionalCase(name, body, check) {
  const clause = `OPTIONAL { ?x <urn:q> ?z ${body}}`;
  return {
    name,
    query: `SELECT * WHERE { ?x <urn:p> ?y . ${clause} }`,
    check(document, query) {
      const optional = one(document.ast, 'leftJoin');
      exact(optional, query, clause);
      check(optional.condition, query);
    },
  };
}

const triple = '?x <urn:p> ?o';
const nestedSelect = `SELECT ?x (<urn:fn>(?x) AS ?alias) WHERE { ${triple} }`;
const cases = [
  {
    name: 'repeated triples, projection, and Unicode code-point offsets',
    query: `# 🪴 author note\nSELECT ?x WHERE { ${triple} . ${triple} # inside\n} # tail 🐈`,
    check(document, query) {
      exact(document.ast.form.projection[0], query, '?x');
      const triples = ofKind(document.ast, 'triple');
      assert.equal(triples.length, 2);
      const [first, second] = triples;
      exact(first, query, triple);
      exact(second, query, triple, 1);
      exact(first.subject, query, '?x', 1);
      exact(second.subject, query, '?x', 2);
      assert.equal(one(document.ast, 'bgp').source.origin, 'derived');
      assert.deepEqual(document.source.comments.map(comment => comment.text),
        ['# 🪴 author note', '# inside', '# tail 🐈']);
    },
  },
  {
    name: 'predicate and object list expansion across comments',
    query: 'SELECT * WHERE { ?x <urn:p> ?a ; # predicate\n<urn:q> ?b , # object\n?c . }',
    check(document, query) {
      const triples = ofKind(document.ast, 'triple');
      assert.equal(triples.length, 3);
      exact(triples[0], query, '?x <urn:p> ?a');
      derived(triples[1], query, ['?x', '<urn:q>', '?b']);
      derived(triples[2], query, ['?x', '<urn:q>', '?c']);
      exact(triples[1].subject, query, '?x');
      exact(triples[2].predicate, query, '<urn:q>');
      exact(triples[2].object, query, '?c');
    },
  },
  {
    name: 'predicate list following a blank node property list',
    query: 'SELECT * WHERE { ?s <urn:p> [ <urn:q> ?x ] ; <urn:r> ?y ; <urn:t> ?z }',
    check(document, query) {
      const triples = ofKind(document.ast, 'triple');
      assert.equal(triples.length, 4);
      const forPredicate = iri => triples.find(node => node.predicate.iri === iri);
      derived(forPredicate('urn:p').object, query, ['[ <urn:q> ?x ]']);
      derived(forPredicate('urn:r'), query, ['?s', '<urn:r>', '?y']);
      derived(forPredicate('urn:t'), query, ['?s', '<urn:t>', '?z']);
    },
  },
  {
    name: 'FILTER before and after a triple',
    query: `SELECT ?x WHERE { FILTER(?x > 1) ${triple} . FILTER(?x > 1) }`,
    check(document, query) {
      const filters = ofKind(document.ast, 'filter').sort((a, b) =>
        (a.source.span?.start ?? -1) - (b.source.span?.start ?? -1));
      assert.equal(filters.length, 2);
      for (const [index, filter] of filters.entries()) {
        exact(filter, query, 'FILTER(?x > 1)', index);
        exact(filter.condition, query, '?x > 1', index);
      }
      exact(one(document.ast, 'triple'), query, triple);
    },
  },
  optionalCase('OPTIONAL without FILTER', '', condition => {
    assert.deepEqual(eraseSource(condition), { kind: 'boolLit', value: true });
    assert.equal(condition.source.origin, 'synthetic');
  }),
  optionalCase('OPTIONAL with explicit true', 'FILTER(true) ', (condition, query) => {
    assert.deepEqual(eraseSource(condition), { kind: 'boolLit', value: true });
    exact(condition, query, 'true');
  }),
  optionalCase('OPTIONAL with two filters', 'FILTER(?z > 1) FILTER(?z < 3) ', (condition, query) => {
    assert.equal(condition.kind, 'and');
    assert.equal(condition.source.origin, 'derived');
    const parts = condition.source.spans.map(span => slice(query, span));
    for (const text of ['?z > 1', '?z < 3']) {
      assert.ok(parts.some(part => part.includes(text)), `OPTIONAL condition missing ${text}`);
    }
    const comparisons = ofKind(condition, 'compare');
    exact(comparisons.find(node => node.operator === '>'), query, '?z > 1');
    exact(comparisons.find(node => node.operator === '<'), query, '?z < 3');
  }),
  {
    name: 'nested SELECT with repeated terms and an aliased full IRI function',
    query: `SELECT ?x WHERE { { ${triple} } { ${nestedSelect} } }`,
    check(document, query) {
      assert.equal(one(document.ast, 'join').source.origin, 'synthetic');
      const nested = one(document.ast, 'subSelect');
      exact(nested, query, `{ ${nestedSelect} }`);
      exact(nested.query, query, nestedSelect);
      exact(nested.query.form.projection[0], query, '?x', 2);
      const alias = one(nested.query.form, 'alias');
      assert.equal(alias.variable, 'alias');
      exact(alias, query, '(<urn:fn>(?x) AS ?alias)');
      const call = one(alias, 'functionCall');
      assert.equal(call.iri, 'urn:fn');
      exact(call, query, '<urn:fn>(?x)');
      exact(call.args[0], query, '?x', 3);
      const triples = ofKind(document.ast, 'triple');
      assert.equal(triples.length, 2);
      const [outerTriple, innerTriple] = triples;
      exact(outerTriple, query, triple);
      exact(innerTriple, query, triple, 1);
      exact(innerTriple.subject, query, '?x', 4);
    },
  },
  {
    name: 'property path and its components',
    query: 'SELECT * WHERE { ?x <urn:p>/^<urn:q>+ ?o }',
    check(document, query) {
      const path = one(document.ast, 'propertyPath');
      exact(path, query, '?x <urn:p>/^<urn:q>+ ?o');
      exact(path.path, query, '<urn:p>/^<urn:q>+');
      exact(one(path.path, 'inverse'), query, '^<urn:q>+');
      exact(one(path.path, 'oneOrMore'), query, '<urn:q>+');
      exact(path.path.left, query, '<urn:p>');
      exact(path.path.right.path.path, query, '<urn:q>');
      exact(document.ast.form.projection, query, '*');
    },
  },
  {
    name: 'anonymous blank node, property list, and collection',
    query: 'SELECT * WHERE { ?x <urn:p> [] . ?x <urn:p> [ <urn:q> ?o ] . ?x <urn:p> (?a ?b) . }',
    check(document, query) {
      const triples = ofKind(document.ast, 'triple');
      const outer = triples.filter(node => node.predicate.iri === 'urn:p');
      assert.equal(outer.length, 3);
      exact(outer[0].object, query, '[]');
      derived(outer[1].object, query, ['[ <urn:q> ?o ]']);
      assert.equal(outer[2].object.source.origin, 'derived');
      const listTriples = triples.filter(node => node.predicate.iri?.endsWith('#first') ||
        node.predicate.iri?.endsWith('#rest'));
      assert.equal(listTriples.length, 4);
      for (const listTriple of listTriples) {
        assert.equal(listTriple.source.origin, 'derived');
        assert.equal(listTriple.predicate.source.origin, 'derived');
      }
      assert.deepEqual(document.source.blankNodes.map(node => [node.kind, slice(query, node.span)]),
        [['anonymous', '[]'], ['propertyList', '[ <urn:q> ?o ]']]);
    },
  },
  {
    name: 'CONSTRUCT WHERE shorthand derives its template from the graph pattern',
    query: `CONSTRUCT WHERE { ${triple} }`,
    check(document, query) {
      assert.equal(document.ast.form.kind, 'construct');
      const whereTriple = one(document.ast.pattern, 'triple');
      exact(whereTriple, query, triple);
      const templateTriple = one(document.ast.form, 'triple');
      assert.deepEqual(eraseSource(templateTriple), eraseSource(whereTriple));
      derived(templateTriple, query, [triple]);
    },
  },
  {
    name: 'named WITH and INCLUDE',
    query: '# 🪴\nWITH { SELECT ?x WHERE { ?x <urn:p> ?o } } AS %rows\n' +
      'SELECT ?y WHERE { INCLUDE %rows . ?y <urn:q> ?o }',
    options: { wdqs: true },
    canonical: false,
    check(document, query) {
      assert.equal(document.namedSubqueries.length, 1);
      const [{ name, span, ast }] = document.namedSubqueries;
      assert.equal(name, 'rows');
      assert.equal(slice(query, span), 'WITH { SELECT ?x WHERE { ?x <urn:p> ?o } } AS %rows');
      const include = one(document.ast, 'include');
      assert.deepEqual(eraseSource(include), { kind: 'include', name: 'rows', variables: ['x'] });
      for (const [node, text] of [
        [include, 'INCLUDE %rows'],
        [one(document.ast, 'triple'), '?y <urn:q> ?o'],
        [one(ast, 'triple'), '?x <urn:p> ?o'],
      ]) {
        if (node.source.origin !== 'unmapped') exact(node, query, text);
      }
    },
  },
  {
    name: 'named projection alias is visible but an unused projected variable remains free for BIND',
    query: 'SELECT ?x ?label ?alias WITH { SELECT ?x ?label (STR(?x) AS ?alias) ' +
      'WHERE { ?x wdt:P31 wd:Q5 } } AS %rows WHERE { INCLUDE %rows . BIND("unknown" AS ?label) }',
    options: { wdqs: true },
    canonical: false,
    check(document) {
      assert.deepEqual(document.diagnostics, []);
      const include = one(document.ast, 'include');
      assert.deepEqual(eraseSource(include), { kind: 'include', name: 'rows', variables: ['x', 'alias'] });
      assert.equal(one(document.ast, 'bind').variable, 'label');
      assert.ok(ofKind(document.namedSubqueries[0].ast.form, 'var').some(node => node.name === 'label'));
    },
  },
  {
    name: 'a variable mentioned inside OPTIONAL is still in scope after INCLUDE',
    query: 'SELECT ?x ?label WITH { SELECT ?x ?label WHERE { ?x wdt:P31 wd:Q5 . ' +
      'OPTIONAL { ?x rdfs:label ?label } } } AS %rows WHERE { INCLUDE %rows . BIND("unknown" AS ?label) }',
    options: { wdqs: true },
    canonical: false,
    check(document) {
      assert.equal(document.ast, null);
      assert.equal(document.diagnostics[0].code, 'named_subquery_outer_parse_error');
      assert.match(document.diagnostics[0].message, /BIND variable already in scope/);
    },
  },
  {
    name: 'COUNT(*) and COUNT(true) keep distinct arguments',
    query: 'SELECT (COUNT(*) AS ?a) (COUNT(true) AS ?b) WHERE { ?x <urn:p> ?o }',
    check(document, query) {
      const counts = ofKind(document.ast, 'aggregate');
      assert.equal(counts.length, 2);
      assert.equal(counts[0].arg.kind, 'wildcard');
      assert.equal(counts[1].arg.kind, 'literal');
      assert.equal(counts[1].arg.value, 'true');
      assert.equal(counts[1].arg.datatype, 'http://www.w3.org/2001/XMLSchema#boolean');
      exact(counts[0].arg, query, '*');
      exact(counts[1].arg, query, 'true');
    },
  },
  {
    name: 'dataset, group, HAVING and order clauses',
    query: 'SELECT ?x (COUNT(?o) AS ?count) FROM <graph> FROM NAMED <named> ' +
      'WHERE { ?x <urn:p> ?o } GROUP BY ?x HAVING(COUNT(?o) > 0) ORDER BY DESC(?count)',
    options: { base: 'https://example.org/' },
    check(document) {
      const { dataset, groupBy, having, modifier } = document.ast;
      assert.equal(dataset[0].iri, 'https://example.org/graph');
      assert.equal(dataset[1].iri, 'https://example.org/named');
      assert.equal(groupBy[0].kind, 'var');
      assert.equal(having[0].kind, 'compare');
      assert.equal(modifier.orderBy[0].kind, 'desc');
    },
  },
  {
    name: 'provenance replay limit preserves the canonical query with unmapped ranges',
    query: `SELECT * WHERE { ${Array.from({ length: 1100 }, (_, i) => `?s <urn:p${i}> ?o .`).join(' ')} }`,
    check(document) {
      assert.equal(ofKind(document.ast, 'triple').length, 1100);
      for (const node of astNodes(document.ast.pattern)) {
        assert.equal(node.source.origin, 'unmapped');
        assert.equal(node.source.reason, 'provenance-trace-incomplete');
      }
    },
  },
  {
    name: 'invalid query keeps diagnostics and source',
    query: '# 🪴\nSELECT WHERE {',
    check(document) {
      assert.equal(document.ast, null);
      assert.equal(document.diagnostics.length, 1);
      assert.equal(document.diagnostics[0].code, 'sparql_parse_error');
    },
  },
];

function nativeReplies(binary, requests) {
  const child = spawnSync(binary, [], {
    input: requests.map(request => JSON.stringify(request)).join('\n') + '\n',
    encoding: 'utf8',
    timeout: 30_000,
    maxBuffer: 4 * 1024 * 1024,
  });
  if (child.error) throw child.error;
  assert.equal(child.status, 0, child.stderr || child.signal);
  const replies = child.stdout.trimEnd().split('\n').map(line => JSON.parse(line));
  assert.equal(replies.length, requests.length, 'native reply count');
  return replies;
}

const args = process.argv.slice(2);
assert.ok(args.length === 0 || (args.length === 2 && args[0] === '--native'),
  'Usage: node tests/sparql/query_document_source.mjs [--native PATH]');
const native = args[1];
const requests = cases.map(({ query, options }) => ({ query, ...options }));
const canonicalRequests = requests.filter((_, i) => cases[i].canonical !== false);
let documents;
let canonicalReplies = [];
if (native) {
  const replies = nativeReplies(native, [...requests, ...canonicalRequests.map(request => ({ ...request, canonical: true }))]);
  documents = replies.slice(0, requests.length);
  canonicalReplies = replies.slice(requests.length);
} else {
  const { parseSparqlAst } = await import('../../npm/factoidal/index.mjs');
  documents = [];
  for (const { query, options } of cases) documents.push(await parseSparqlAst(query, options));
}

const origins = { exact: 0, derived: 0, synthetic: 0, unmapped: 0 };
const failures = [];
let canonicalIndex = 0;
for (const [i, { name, query, check, canonical }] of cases.entries()) {
  const document = documents[i];
  const compare = native && canonical !== false;
  const reference = compare ? canonicalReplies[canonicalIndex++] : undefined;
  try {
    verifyDocument(document, query, origins);
    if (compare) assert.deepEqual(eraseSource(document.ast), reference, 'canonical AST mismatch');
    check(document, query);
  } catch (error) {
    failures.push(name);
    console.error(`${name}: ${error.stack}`);
  }
}

console.log(JSON.stringify({
  backend: native ? 'native' : 'wasm',
  passed: cases.length - failures.length,
  failed: failures.length,
  canonical: canonicalIndex,
  origins,
}));
if (failures.length > 0) process.exitCode = 1;
