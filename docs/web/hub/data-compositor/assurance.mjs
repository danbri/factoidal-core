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
  'xml:diagnostic': ['XML refusal → Diagnostic', 'Only selected when the Lean XML parser refuses the exact serialized result. XML consumers are skipped.'],
  'diagnostic:report': ['Diagnostic → Report', 'The refusal is displayed as text, not interpreted as HTML.'],
  'html:report': ['HTML → Report', 'The final report identifies the HTML branch.'],
  'xslt:html': ['XSLT result → HTML preview', 'A sandboxed browser frame displays the engine output. Browser rendering has no component proof claim.'],
});

export function nodeAssurance(stage) {
  if (!stage?.evidence) return { badge: 'Awaiting evidence', status: 'not-run', contract: null, assumptions: [], scope: 'Run the flow to obtain actual registry/runtime evidence.' };
  const e = stage.evidence;
  const registered = e.source === 'core.node/run' || e.source === 'core.graph/run';
  return {
    badge: e.admission ? (e.admission.accepted ? 'XML parser accepted' : 'XML parser refused') : registered ? (e.status === 'proved' ? (e.checked ? 'Proof contract applied' : 'Proof applicability unknown') : e.status === 'tested' ? 'Tests; no proof contract' : 'Proof not established') : 'Connection / display step',
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

const LINK_OBLIGATIONS = Object.freeze({
  'turtle:merge': 'Prove that assigning urn:studio:turtle preserves the reader’s RDF terms and blank-node identity before the merge scopes the inputs.',
  'csvw:merge': 'Establish the CSVW conversion contract, then prove graph assignment preserves its output before the merge.',
  'merge:closure': 'Prove that selecting the default-graph union supplies exactly the triples to which the RDFS soundness contract applies.',
  'turtle:graphs': 'Establish provenance: the final Turtle graph must come from this exact source run, through the merge and graph partition.',
  'csvw:graphs': 'Establish provenance: the final CSV graph must come from this exact conversion run, through the merge and graph partition.',
  'closure:graphs': 'Prove that closure minus the exact input union selects only additional triples, and retagging preserves their terms and scope.',
  'graphs:query': 'Prove that the evaluator receives this exact named-graph dataset and establish its query/backend domain premises, including any named assumptions.',
  'query:filter': 'This is a display dependency, not table-to-table filtering. Prove the threshold-template binding and relate the second dataset query to the displayed query; do not assume volatile expressions are equal across runs.',
  'filter:xml': 'Prove that table projection and XML output refer to the identical query result, with escaping, datatypes and unbound bindings preserved by the projection.',
  'xml:xslt': 'Establish a contract for this stylesheet over the SPARQL Results XML vocabulary, then prove it consumes the retained XML result and preserves the intended selected values.',
  'xslt:html': 'Relate the emitted HTML to the displayed document under an explicit browser and rendering model. The current sandbox restricts capabilities; it is not a rendering-correctness proof.',
});

export function wireAssurance(from, to, stages) {
  const [wireKind, note] = WIRE_RECIPES[`${from}:${to}`] ?? ['display dependency', 'Manual app recipe link.'];
  const source = stages.get(from), target = stages.get(to);
  return {
    from, to, wireKind, note,
    obligation: LINK_OBLIGATIONS[`${from}:${to}`] ?? 'No preservation obligation has been specified for this display link.',
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

// Explanations are a view of named contracts, not new verdicts or evidence.
export const PROOF_SOURCE = 'https://github.com/danbri/factoidal-core/blob/a9bd50c3b28b3d42c5071cc8c3e74a5ede8706db/';
const CONTRACTS = {
  'L4Factoidal.Dataflow.ReaderContract': ['What does the reader preserve?', 'The reader contract describes RDF set semantics, document-scoped blank nodes, and invariance under changes to blank-node labels. It does not certify that the source statements are true.', 'formal/lean4/L4Factoidal/Dataflow/Reader.lean'],
  'L4Factoidal.RDF.DatasetDen.IsMerge': ['What does merging preserve?', 'The RDF merge contract combines the two datasets with the required blank-node scoping. Assigning the source graph names happens before this checked merge and has no adapter proof here.', 'formal/lean4/L4Factoidal/Dataflow/GraphStages.lean'],
  'L4Factoidal.Dataflow.Regime.Entails': ['What does the inference proof establish?', 'The RDFS soundness contract says the inferred graph follows from the input under the formal RDFS entailment relation. This is not a proof of completeness, source truth, or the surrounding graph-selection steps.', 'formal/lean4/L4Factoidal/Dataflow/Reasoner.lean'],
  'L4Factoidal.Dataflow.EvalContract': ['What does the query proof establish?', 'The evaluator contract relates answers to the reference semantics on its stated domain. Backend patterns outside the proved fragment and selected fast paths rely on named agreement assumptions. A checked flag does not remove those assumptions or prove the whole query-to-display path.', 'formal/lean4/L4Factoidal/Dataflow/Evaluator.lean'],
};
export function explainEvidence(stage) {
  const a = nodeAssurance(stage), e = stage?.evidence;
  const known = CONTRACTS[a.contract];
  return {
    title: known?.[0] ?? (a.status === 'tested' ? 'What do the tests establish?' : e ? 'What does this step do?' : 'Evidence is not available yet'),
    claim: known?.[1] ?? (a.status === 'tested' ? 'The registry lists executable tests for this component. There is no registered semantic proof contract for this operation; this run is an execution result, not a fresh conformance-suite report.' : e?.note ?? a.scope),
    source: e?.admission?.source ?? (known ? PROOF_SOURCE + known[2] : null),
    admission: e?.admission ?? null,
    registry: e?.registry ?? null,
    boundaries: [stage?.note, stage?.adapter?.note, e?.prepAdapter?.note].filter(Boolean),
    scope: a.scope,
  };
}
