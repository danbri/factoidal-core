// A genuine Lean SPARQL 1.1 BGP experiment in a browser Web Worker.
// Independent predicate-scoped N-Quads datasets and their union are all
// parsed and queried by the published Lean l4factoidal.wasm runtime.
// No SPARQL algebra, graph matching or joins are implemented in JavaScript.
// NOT an SBM11 block worker, GPU query, remote process or Kubernetes cluster.
import {makeFixture, packBindingPairs, QUERY, PATTERN_KNOWS, PATTERN_ATLAS,
  shortTerm, personWord, checkScale} from "./bgp-fixtures.mjs";
import {loadL4} from "../assets/l4/l4factoidal.js";

let enginePromise;
function engine() {
  return enginePromise ??= loadL4();
}

function selected(answer, stage) {
  if (answer?.kind !== "select" || !Array.isArray(answer.srj?.results?.bindings)) {
    throw new Error(stage + ": Lean did not return SPARQL SELECT bindings.");
  }
  return answer.srj.results.bindings;
}

function summarize(rows, variables) {
  return {
    count: rows.length,
    preview: rows.slice(0, 10).map(row => Object.fromEntries(variables.map(name => {
      const term = row[name];
      return [name, term?.value == null ? null : shortTerm(term.value)];
    }))),
  };
}

async function execute(size, requestId) {
  checkScale(size);
  const start = performance.now();
  const fixture = makeFixture(size);
  self.postMessage({type: "bgp-phase", id: requestId,
    detail: "Generated " + fixture.triples + " RDF triples in three predicate-scoped source sets."});
  const l4 = await engine();
  const handles = [];
  const open = text => {
    // The established Hub notebook 51 uses exactly this Lean dispatch
    // operation and the same nquads format for complete N-Triples fragments.
    const result = l4.call("datasetOpen", [text, "nquads", ""]);
    if (!result?.handle) throw new Error("Lean did not return a dataset handle.");
    handles.push(result.handle);
    return result;
  };
  const query = (handle, text, stage) => selected(l4.call("datasetQuery", [handle, text]), stage);
  try {
    const sourcesStarted = performance.now();
    const knows = open(fixture.blocks.knows);
    const projects = open(fixture.blocks.projects);
    self.postMessage({type: "bgp-phase", id: requestId,
      detail: "Lean opened and validated predicate-scoped RDF sources. Evaluating each triple pattern."});

    const left = query(knows.handle, PATTERN_KNOWS, "knows pattern");
    const right = query(projects.handle, PATTERN_ATLAS, "Atlas pattern");
    const scansMs = performance.now() - sourcesStarted;
    self.postMessage({type: "bgp-phase", id: requestId,
      detail: "Lean returned " + left.length + " knows bindings and " + right.length +
        " Atlas bindings. Evaluating the complete BGP in Lean."});

    // A separate Lean call over the complete input dataset is the semantic
    // authority for the join, including SPARQL solution multiplicity.
    // Host JavaScript deliberately does not join the two binding lists.
    const fullStart = performance.now();
    const merged = open(fixture.blocks.knows + fixture.blocks.projects + fixture.blocks.labels);
    const matches = query(merged.handle, QUERY, "joined BGP");
    const joinMs = performance.now() - fullStart;
    const packed = packBindingPairs(matches, size);
    const bindings = matches.map((row, index) => ({
      ordinal: index + 1,
      person: shortTerm(row.person.value),
      colleague: shortTerm(row.colleague.value),
      personId: personWord(row.person.value, size),
      colleagueId: personWord(row.colleague.value, size),
    }));

    return {
      schemaVersion: 1,
      engine: "Lean l4factoidal.wasm; local browser Web Worker",
      execution: "3 actual Lean dataset opens, two individual-pattern queries, and one complete BGP query",
      noRemoteWorkers: true,
      gpuBgpSupported: "separate bounded integer-query profile; check actual GPU availability",
      query: QUERY,
      input: {
        people: size,
        tripleCount: fixture.triples,
        integerGraph: fixture.integerGraph,
        queryConstants: fixture.queryConstants,
        blocks: [
          {name: "knows", triples: fixture.sourceCounts.knows},
          {name: "worksOn", triples: fixture.sourceCounts.projects},
          {name: "label", triples: fixture.sourceCounts.labels},
        ],
        sample: fixture.example,
      },
      scans: {
        knows: summarize(left, ["person", "colleague"]),
        atlas: summarize(right, ["colleague"]),
      },
      bgp: summarize(matches, ["person", "colleague"]),
      bindings,
      preview: bindings.slice(0, 16),
      pack: packed,
      timing: {
        openAndScanMs: scansMs,
        completeOpenAndQueryMs: joinMs,
        totalMs: performance.now() - start,
        provenance: "Browser worker wall-clock, including Lean parsing/transport; not isolated compute time",
      },
    };
  } finally {
    for (const handle of handles) {
      try { l4.call("datasetClose", [handle]); } catch { /* keep original result/error */ }
    }
  }
}

self.onmessage = async event => {
  const {id, people} = event.data ?? {};
  try {
    self.postMessage({type: "bgp-phase", id, detail: "Loading the full Lean SPARQL WebAssembly engine…"});
    const result = await execute(people, id);
    self.postMessage({type: "bgp-result", id, result});
  } catch (error) {
    self.postMessage({type: "bgp-error", id, message: error?.message || String(error)});
  }
};
