// Display metadata only: never computes a proof, inference, or type verdict.
export const WIRE_RECIPES = Object.freeze({
  'turtle:merge': ['Dataset → tagged Dataset → merge port', 'The source is graph-tagged by a public API adapter before the checked merge port.'],
  'csvw:merge': ['Dataset → tagged Dataset → merge port', 'The CSVW dataset is graph-tagged by a public API adapter before the checked merge port.'],
  'merge:closure': ['Dataset → default Graph → Graph', 'The graph union is selected by asDefaultGraph before the RDFS component.'],
  'turtle:graphs': ['Dataset provenance', 'Provenance dependency only: the final source quads come through the merge.'],
  'csvw:graphs': ['Dataset provenance', 'Provenance dependency only: the final source quads come through the merge.'],
  'closure:graphs': ['Graph → derived Dataset', 'A public API adapter selects closure minus the exact input union and assigns its graph IRI.'],
  'graphs:query': ['Dataset → Table', 'The registered evaluator receives the named-graph dataset; this app link is not a checked graph composition.'],
  'query:filter': ['Table display → query template + Dataset', 'Display sequencing, not a Table input wire: filtering runs SPARQL against the same dataset, then Lean XQuery projects rows from its XML.'],
  'filter:xml': ['Shared SPARQL Results XML', 'The identical XML string from the filtered query is retained; there is no second filtered SPARQL evaluation.'],
  'xml:xslt': ['String → XSLT result', 'The registered XSLT component consumes this XML string; its component status is tested, not proved.'],
  'xslt:html': ['XSLT result → HTML preview', 'A sandboxed browser frame displays the engine output. Browser rendering has no component proof claim.'],
});

export function nodeAssurance(stage) {
  if (!stage?.evidence) return { badge: 'not run', status: 'not-run', scope: 'Run the flow to obtain actual registry/runtime evidence.' };
  const e = stage.evidence;
  const registered = e.source === 'core.node/run' || e.source === 'core.graph/run';
  return {
    badge: registered ? `${e.status}${e.checked ? ' · checked' : ''}` : 'API / display adapter',
    status: e.status ?? 'unproved-adapter',
    registryStatus: e.registryStatus ?? null,
    checked: e.checked === true, proved: e.proved === true,
    contract: e.contract ?? null, assumptions: e.assumptions ?? [],
    wireIn: e.wireIn ?? null, wireOut: e.wireOut ?? null, ports: e.ports ?? [],
    projection: e.projection ?? null,
    scope: registered ? 'This component/settings contract only; not the full app or adjacent adapters.' : 'Public API/display adapter; no proved adapter contract.',
    graphWideProof: false,
  };
}

export function wireAssurance(from, to, stages) {
  const [wireKind, note] = WIRE_RECIPES[`${from}:${to}`] ?? ['display dependency', 'Manual app recipe link.'];
  const source = stages.get(from), target = stages.get(to);
  return {
    from, to, wireKind, note,
    source: nodeAssurance(source), target: nodeAssurance(target),
    applicationLink: 'manual recipe / display dependency',
    graphWideProof: false, wholeWireProved: false,
    checkedSubcomposition: to === 'merge' && target?.evidence?.graphCheck ? {
      scope: 'Only the tagged Dataset inputs and datasetMerge output inside core.graph/run; graph-tagging adapters remain outside.',
      ...target.evidence.graphCheck,
    } : null,
    limitation: 'Visual adjacency and compatible-looking wire labels do not establish semantic preservation. No assurance ranking is invented.',
  };
}
