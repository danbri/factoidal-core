// Sample hand port of three Apache Jena test classes to node:test, against a
// HYPOTHETICAL facade package "@factoidal/echochamber". Not run: the facade
// does not exist. Each test notes the engine op it needs; "NEW OP" marks a
// semantic decision that must be added to Lean first (iron rules 1, 2, 7;
// anti-pattern 36).
//
// Derived from Apache Jena (Apache License 2.0), files
//   jena-core/src/test/java/org/apache/jena/rdf/model/TestLiteralsInModel.java
//   jena-arq/src/test/java/org/apache/jena/sparql/api/TestAPI.java
//   jena-arq/src/test/java/org/apache/jena/riot/TestRDFParser.java
// at apache/jena a1164c5dc5c9e1a9c58d94766c13d870e0a8ba98. Changed: translated
// from Java/JUnit 5 to JavaScript/node:test.

import { test, describe, beforeEach } from 'node:test';
import assert from 'node:assert/strict';
import {
  ModelFactory, ResourceFactory, QueryExecution, QuerySolutionMap,
  RDFParser, Lang, GraphFactory, RiotException, XSD,
} from '@factoidal/echochamber';

// ---------------------------------------------------------------------------
// 1. jena-core TestLiteralsInModel (7 methods; parameterized over
//    ModelCreators, so each runs once per model kind).
describe('TestLiteralsInModel', () => {
  let model, X, P;
  beforeEach(() => {
    model = ModelFactory.createDefaultModel();      // op: datasetOpen('')
    X = ResourceFactory.createResource('eh:/X');      // JS: term object only
    P = ResourceFactory.createProperty('eh:/P');
  });

  test('testAddWithBooleanObject', () => {
    model.addLiteral(X, P, true);                     // NEW OP: JS value -> RDF literal mapping
    assert.ok(model.contains(X, P, model.createTypedLiteral(true)));
    assert.ok(model.containsLiteral(X, P, true));
  });

  test('testAddWithIntObject', () => {
    // Java: addLiteral(X, P, 99) gives xsd:int; addLiteral(X, P, 99L) gives
    // xsd:long. A JS number cannot carry that distinction. The facade needs an
    // explicit type: a BigInt, or a typed wrapper whose datatype the ENGINE
    // chooses from a fixed table (NEW OP), never a JS rule such as
    // Number.isInteger (the bin/ext.mjs 1e21 defect, anti-pattern 36).
    model.addLiteral(X, P, XSD.int(99));
    assert.ok(model.contains(X, P, model.createTypedLiteral(XSD.int(99))));
    assert.ok(model.containsLiteral(X, P, XSD.int(99)));
  });

  test('testAddWithLongObject', () => {
    model.addLiteral(X, P, 99n);                      // BigInt -> xsd:long (engine table)
    assert.ok(model.contains(X, P, model.createTypedLiteral(99n)));
    assert.ok(model.containsLiteral(X, P, 99n));
  });
});

// ---------------------------------------------------------------------------
// 2. jena-arq TestAPI (36 methods).
describe('TestAPI', () => {
  const ns = 'http://example/ns#';
  const m = ModelFactory.createDefaultModel();
  const r1 = m.createResource();                      // fresh blank node: engine label supply
  const p1 = m.createProperty(ns + 'p1');
  const p2 = m.createProperty(ns + 'p2');
  const p3 = m.createProperty(ns + 'p3');
  m.add(r1, p1, 'x1');                                // op: datasetAddQuads
  m.add(r1, p2, 'X2');
  m.add(r1, p3, 'y1');

  test('testSelect1', () => {
    using qExec = QueryExecution.model(m).query('SELECT * {?s ?p ?o}').build();
    const rs = qExec.execSelect();                    // op: datasetQuery
    assert.ok(rs.hasNext(), 'No results');
    const qr = rs.nextSolution().getResource('s');
    // Jena: a Resource from a result keeps a link to its Model. The facade
    // keeps the dataset handle on each result term (JS only).
    assert.deepEqual(new Set(qr.getModel().listStatements().toArray().map(String)),
                     new Set(m.listStatements().toArray().map(String)));
  });

  test('testConstruct1', () => {
    using qExec = QueryExecution.model(m)
      .query('CONSTRUCT {?s ?p ?o} WHERE { ?s ?p ?o }').build();
    const m2 = qExec.execConstruct();                 // op: datasetQuery (CONSTRUCT -> new handle)
    assert.ok(!m2.isEmpty());
    assert.ok(m.isIsomorphicWith(m2));                // op: datasetIsomorphic
  });

  test('testConstructBad1', () => {
    // RDF 1.2 CONSTRUCT template with a literal in subject position: the
    // ill-formed triples are dropped (SPARQL 1.1 section 16.2). No JS logic.
    const qs = `PREFIX : <http://example/>
      CONSTRUCT { << 456 :p :o >> . ?x :p :o . :s ?x :o .
                  :tt1 :p <<( ?x :c2 :c3 )>> . } WHERE { BIND(123 AS ?x) }`;
    using qExec = QueryExecution.model(m).query(qs).build();
    assert.ok(qExec.execConstruct().isEmpty());      // op: datasetQuery12
  });

  test('testSubstitutionConstruct1', () => {
    const init = new QuerySolutionMap();
    init.add('z', m.createLiteral('zzz'));
    using qExec = QueryExecution.model(m)
      .query("CONSTRUCT {?s ?p ?z} {?s ?p 'x1'}")
      .substitution(init).build();                    // NEW OP: query substitution (syntactic, Lean)
    const r = qExec.execConstruct();
    assert.ok(r.size() > 0);
    assert.ok(r.contains(null, p1, init.get('z')));
  });
});

// ---------------------------------------------------------------------------
// 3. jena-arq TestRDFParser (38 methods).
describe('TestRDFParser', () => {
  const DIR = 'testing/RIOT/Parser/';                 // copied Jena fixtures, with NOTICE
  const testdata = '@prefix : <http://example/ns#> . :x :x _:b .';

  test('source_not_uri_01', () => {
    const graph = GraphFactory.createGraphMem();
    RDFParser.create().lang(Lang.TTL).fromString(testdata).parse(graph); // op: parseDocument + datasetAddQuads
    assert.equal(graph.size(), 1);
  });

  test('source_uri_02', () => {
    // Jena picks the syntax from the file name suffix and fails on
    // ".unknown". The suffix table is an RDF syntax decision: NEW OP
    // (formatOfFileName), not a JS table (host-purity lint group 3).
    const graph = GraphFactory.createGraphMem();
    assert.throws(() => RDFParser.create().source('file:' + DIR + 'data.unknown').parse(graph),
                  RiotException);
  });

  test('source_uri_03', () => {
    const graph = GraphFactory.createGraphMem();
    RDFParser.create().source('file:' + DIR + 'data.unknown').lang(Lang.TTL).parse(graph);
    assert.equal(graph.size(), 3);
  });

  test('source_shortcut_01', () => {
    const graph = GraphFactory.createGraphMem();
    RDFParser.fromString(testdata, Lang.TTL).parse(graph);
    assert.equal(graph.size(), 1);
  });
});

// Notes on the shape:
// * Java's synchronous API is kept synchronous. This needs the engine loaded
//   before first use (await echochamber.ready()), because @factoidal/core
//   loads its wasm asynchronously. Every op call after that is synchronous.
// * try-with-resources maps to the JS `using` declaration (explicit resource
//   management; Node 24+, or a try/finally with close() on Node 22).
// * Iterators (StmtIterator, ResultSet) implement both the Java methods
//   (hasNext/next/close/toList) and [Symbol.iterator].
