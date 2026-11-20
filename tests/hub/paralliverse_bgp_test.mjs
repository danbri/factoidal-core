import test from "node:test";
import assert from "node:assert/strict";
import {BASE, SIZES, QUERY, PATTERN_KNOWS, PATTERN_ATLAS,
  makeFixture, personIri, personWord, packBindingPairs, shortTerm} from "../../docs/web/hub/paralliverse/bgp-fixtures.mjs";

test("BGP lexical syntax retains the shared variable and full SPARQL terms", () => {
  assert.match(QUERY, /SELECT \?person \?colleague WHERE/);
  assert.match(QUERY, /\?person ex:knows \?colleague/);
  assert.match(QUERY, /\?colleague ex:worksOn ex:Atlas/);
  assert.match(QUERY, /ORDER BY \?person \?colleague/);
  assert.match(PATTERN_KNOWS, /SELECT \?person \?colleague/);
  assert.match(PATTERN_ATLAS, /SELECT \?colleague/);
  assert.equal(shortTerm(personIri(7)), "ex:person/0007");
});
for (const n of SIZES) {
  test("fixture " + n + " people: 4n unique lexical RDF triples in three predicate scopes", () => {
    const data = makeFixture(n);
    const sources = Object.values(data.blocks);
    const triples = sources.flatMap(x => x.trim().split("\n"));
    assert.equal(data.triples, 4 * n);
    assert.equal(triples.length, 4 * n);
    assert.equal(new Set(triples).size, triples.length);
    assert.deepEqual(data.sourceCounts, {knows: 2 * n, projects: n, labels: n});
    assert.ok(triples.every(x => x.startsWith("<" + BASE) && x.endsWith(" .")));
    assert.equal((data.blocks.projects.match(new RegExp("<" + BASE + "Atlas>", "g")) ?? []).length, n / 4);
  });
}

test("fixture person dictionary is injective, finite, and not a claimed SBM11 term ID", () => {
  const ids = new Set(Array.from({length: 1024}, (_, i) => personWord(personIri(i), 1024)));
  assert.equal(ids.size, 1024);
  assert.equal(Math.min(...ids), 1);
  assert.equal(Math.max(...ids), 1024);
  assert.throws(() => personWord(BASE + "object", 1024), /fixture person IRI/);
  assert.throws(() => personWord(personIri(2048), 1024), /outside the fixture/);
  assert.throws(() => personWord(personIri(65), 64), /outside the fixture/);
});

test("512 BGP bindings fit the existing 128-row/1024-u32 packing profile", () => {
  const rows = Array.from({length: 512}, (_, i) => ({
    person: {type: "uri", value: personIri(i)},
    colleague: {type: "uri", value: personIri((i + 7) % 1024)},
  }));
  const result = packBindingPairs(rows, 1024);
  assert.equal(result.sourcePairs, 512);
  assert.equal(result.words, 1024);
  assert.equal(result.packedRows.length, 128);
  assert.deepEqual(result.packedRows[0], [1, 8, 2, 9, 3, 10, 4, 11]);
  assert.deepEqual(result.packedRows.at(-1), [509, 516, 510, 517, 511, 518, 512, 519]);
  assert.throws(() => packBindingPairs([...rows, rows[0]], 1024), /Too many query results/);
  assert.throws(() => packBindingPairs([{person: rows[0].person}], 1024), /must be bound/);
});

test("empty binding result remains an admitted empty packing input", () => {
  const result = packBindingPairs([], 64);
  assert.equal(result.words, 0);
  assert.deepEqual(result.packedRows, []);
});
