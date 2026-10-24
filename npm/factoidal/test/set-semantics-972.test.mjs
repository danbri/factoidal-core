// The three defects of @factoidal/core 0.12.0 recorded in
// https://github.com/danbri/factoidal/issues/972, run against this package's
// own entry and wasm. The package suite runs inside `npm publish`
// (prepublishOnly), so a release that brings one back fails to publish.
//
// R1: an RDF graph is a set of triples (RDF 1.1 Concepts §3); a document
//     that states one triple twice gives one triple.
// R2: "01"^^xsd:integer and "1"^^xsd:integer are different RDF terms, so
//     DISTINCT keeps both (SPARQL 1.1 §18.5, Distinct uses RDF term identity).
// R3: STR of a typed literal is its lexical form (SPARQL 1.1 §17.4.2.5).
import test from 'node:test'
import assert from 'node:assert/strict'
import { parse, query } from '../index.mjs'

const XSD_INTEGER = 'http://www.w3.org/2001/XMLSchema#integer'

test('R1: a repeated triple is stored once (size and COUNT)', async () => {
  const ds = await parse(
    '<http://e/a> <http://e/p> <http://e/o> .\n<http://e/a> <http://e/p> <http://e/o> .\n',
    { format: 'ntriples' })
  assert.equal(ds.size, 1)
  const rows = await query(ds, 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }')
  assert.equal(rows[0].get('n').value, '1')
})

test('R2: COUNT(DISTINCT) keeps "01" and "1" as two integer terms', async () => {
  const ds = await parse('', { format: 'ntriples' })
  const rows = await query(ds,
    `SELECT (COUNT(DISTINCT ?v) AS ?n) WHERE { VALUES ?v { "01"^^<${XSD_INTEGER}> "1"^^<${XSD_INTEGER}> "1"^^<${XSD_INTEGER}> } }`)
  assert.equal(rows[0].get('n').value, '2')
})

test('R3: STR of a VALUES "01"^^xsd:integer is "01"', async () => {
  const ds = await parse('', { format: 'ntriples' })
  const rows = await query(ds,
    `SELECT (STR(?v) AS ?s) WHERE { VALUES ?v { "01"^^<${XSD_INTEGER}> } }`)
  assert.equal(rows[0].get('s').value, '01')
})
