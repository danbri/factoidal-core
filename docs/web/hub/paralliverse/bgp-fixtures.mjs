// Deterministic RDF fixture, presentation vocabulary and bounded u32 bridge.
// This module generates *input data*; it never evaluates a SPARQL query.
// The browser worker executes each pattern and the joined BGP in Lean/Wasm.
export const BASE = "https://example.org/paralliverse/";
export const SIZES = Object.freeze([64, 256, 1024]);
export const TERM_IDS = Object.freeze({
  knows: 0xff000001,
  worksOn: 0xff000002,
  Atlas: 0xff000003,
  Orion: 0xff000004,
  label: 0xff000005,
});
export const LABEL_BASE = 0x80000000;
// Person IRIs: [1..n]. Predicates and project IRIs: [0xff000001..5].
// Person label literals: 0x80000000+i. The ranges are disjoint and
// the graph, including all literal identities, is a true RDF set.
export const QUERY = [
  "PREFIX ex: <" + BASE + ">",
  "SELECT ?person ?colleague WHERE {",
  "  ?person ex:knows ?colleague .",
  "  ?colleague ex:worksOn ex:Atlas .",
  "}",
  "ORDER BY ?person ?colleague",
].join("\n");
export const PATTERN_KNOWS = [
  "PREFIX ex: <" + BASE + ">",
  "SELECT ?person ?colleague WHERE { ?person ex:knows ?colleague . }",
].join("\n");
export const PATTERN_ATLAS = [
  "PREFIX ex: <" + BASE + ">",
  "SELECT ?colleague WHERE { ?colleague ex:worksOn ex:Atlas . }",
].join("\n");

export function checkScale(n) {
  if (!SIZES.includes(n)) throw new RangeError("Choose 64, 256 or 1024 people.");
  return n;
}

export function personIri(i) {
  return BASE + "person/" + String(i).padStart(4, "0");
}

export function shortTerm(iri) {
  return typeof iri === "string" && iri.startsWith(BASE)
    ? "ex:" + iri.slice(BASE.length) : String(iri);
}

export function makeFixture(n) {
  checkScale(n);
  const knows = [], projects = [], labels = [];
  const knowsIds = [], projectsIds = [], labelIds = [];
  const e = iri => "<" + iri + ">";
  const predKnows = e(BASE + "knows"), predProject = e(BASE + "worksOn");
  const predLabel = e(BASE + "label");
  const atlas = e(BASE + "Atlas"), orion = e(BASE + "Orion");
  for (let i = 0; i < n; i++) {
    const person = e(personIri(i));
    knows.push(person + " " + predKnows + " " + e(personIri((i + 1) % n)) + " .");
    knowsIds.push([i+1, TERM_IDS.knows, ((i+1)%n)+1]);
    knows.push(person + " " + predKnows + " " + e(personIri((i + 7) % n)) + " .");
    knowsIds.push([i+1, TERM_IDS.knows, ((i+7)%n)+1]);
    projects.push(person + " " + predProject + " " + (i % 4 === 0 ? atlas : orion) + " .");
    projectsIds.push([i+1, TERM_IDS.worksOn, i%4===0 ? TERM_IDS.Atlas : TERM_IDS.Orion]);
    labels.push(person + " " + predLabel + ' "Person ' + i + '" .');
    labelIds.push([i+1, TERM_IDS.label, LABEL_BASE+i]);
  }
  return {
    people: n,
    triples: 4 * n,
    sourceCounts: {knows: knows.length, projects: projects.length, labels: labels.length},
    blocks: {
      knows: knows.join("\n") + "\n",
      projects: projects.join("\n") + "\n",
      labels: labels.join("\n") + "\n",
    },
    example: [...knows.slice(0, 3), projects[0], projects[1], labels[0]],
    // Same iteration produces lexical and integer triple representations.
    integerGraph: [...knowsIds, ...projectsIds, ...labelIds],
    queryConstants: {knows: TERM_IDS.knows, works: TERM_IDS.worksOn, atlas: TERM_IDS.Atlas},
  };
}

// A teaching dictionary only, NOT the internal SBM11 UInt64 term dictionary.
// The current packing shader admits u32; no lossy narrowing is performed.
export function personWord(iri, n) {
  if (typeof iri !== "string" || !iri.startsWith(BASE + "person/"))
    throw new TypeError("The query result must contain a fixture person IRI.");
  const suffix = iri.slice((BASE + "person/").length);
  if (!/^[0-9]{4}$/.test(suffix)) throw new TypeError("Unrecognised person identifier.");
  const index = Number(suffix);
  if (index >= n) throw new RangeError("Query result ID falls outside the fixture.");
  return index + 1;
}

export function packBindingPairs(rows, n) {
  checkScale(n);
  if (!Array.isArray(rows) || rows.length > 512)
    throw new RangeError("Too many query results for the bounded packing bridge.");
  const pairs = rows.map(row => {
    const person = row?.person, colleague = row?.colleague;
    if (person?.type !== "uri" || colleague?.type !== "uri")
      throw new TypeError("Both projected variables must be bound to fixture IRIs.");
    return [personWord(person.value, n), personWord(colleague.value, n)];
  });
  if (pairs.length * 2 > 1024)
    throw new RangeError("The BGP result exceeds the existing GPU word limit.");
  const groupSize = Math.max(1, Math.ceil(pairs.length / 128));
  const packedRows = [];
  for (let i = 0; i < pairs.length; i += groupSize)
    packedRows.push(pairs.slice(i, i + groupSize).flat());
  if (packedRows.length > 128) throw new Error("Row packing admission failed.");
  return {packedRows, sourcePairs: pairs.length, words: pairs.length * 2,
    mapping: "ex:person/0000 = 1; ex:person/0001 = 2; …; ex:person/" +
      String(n - 1).padStart(4, "0") + " = " + n};
}
