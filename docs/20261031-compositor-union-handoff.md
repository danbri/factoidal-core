# The compositor's concrete union handoff

Tracking: https://github.com/danbri/factoidal/issues/1214 (actual compositor
link obligations), under https://github.com/danbri/factoidal/issues/975
(foundation-bound composition). Descriptor design:
https://github.com/danbri/factoidal/issues/1213.

The user asks for proved components and the actual links between them.
The first bounded repair concerns `asDefaultGraph(merged)` in the compositor
pipeline at source commit `ee3fef1aca5cca2d26b89883fb2c38ff0b674398`.
It selects a union for the reasoner; it is not another RDF merge.

## Producer and proof

`Dataflow/GraphProjection.lean` names the existing public hash-set fold as
`unionGraph`, then constructs `unionDefault`. `unionGraph_original` is a
kernel-checked definitional equality with the previous literal fold. The
first occurrence of each structural triple stays in its original order.
No blank-node label or RDF term is rewritten. Graph names, including empty
named graphs, are intentionally dropped by this projection.

`unionGraph_mem` states both directions: a structural output triple occurs
in the input default graph or a named graph, and every such input triple
occurs in the output. `unionDefault_graph` lifts this to RDF `DatasetDen`
membership, which uses `Triple.key` rather than confusing structural equality
with RDF term equality. `unionDefault_certified_graph` proves the same exact
input relation after the actual handle certification step.

The production `Wasm/Ops/Handles.datasetGraphAsDefault` union branch calls
this producer. `datasetGraphAsDefault_union_producer` equates that actual IO
operation with storing the proved result when its parsed selector is union.
Its hypotheses recognize the input selector; they do not assume preservation.
A mutation that returned an empty dataset from the actual branch failed this
theorem with unequal IO producers. The source was restored and rebuilt green.
This checks the production connection, not only a separate model function.

`unionDefault_reasoner_handoff` applies a `SoundReasoner` to the exact
certified union input, pairing its source-membership witness and regime
soundness. It claims no completeness. Existing graph-selection contracts
and `rdfsSelect_sound` in `Dataflow/PhaseD.lean` remain available; their
list-valued selection need not equal this deduplicated public adapter.

## Execution boundary still open

The current public `datasetClosure` calls `datasetForOps` normalization before
`closureGraphOfRegime`, whose RDFS branch uses the existing `SoundReasoner`.
This change does not prove that normalizer preserves the union input on every
admitted source. Therefore the handoff theorem does not certify the complete
current browser merge-to-RDFS execution. That remaining normalization agreement
must be established or supplied as an explicit premise for that wider claim.
No new public node identifier, unchecked override guarantee or UI proof badge
is introduced here. The existing union API is wired to the proved adapter.

Other tracked links remain open: graph assignment, closure delta selection,
query binding, shared-results XML projection, XSLT's stylesheet contract and
browser display. The current XML_ROWS display projection intentionally keeps
lexical strings and drops RDF datatype/term-kind distinctions. Its future
contract must preserve the selected display meaning, not pretend a typed-RDF
round-trip. Browser rendering and host scheduling are outside these proofs.

## Validation

- Named warm `lake build +L4Factoidal.Dataflow.GraphProjectionTests` passes
  (414 jobs), including the production Handles module and seven controls.
  Controls cover first-occurrence order/cross-graph duplicates, blank-node
  identity, empty input, empty named graphs, actual handle output, unchanged
  source graphs and language distinctions.
- The actual-producer empty-output mutation is rejected; restored build passes.
- Three public API groups pass against the installed 0.27 WASM: projection
  order/deduplication, blank-node/language preservation, and actual registered
  merge-to-union-to-RDFS output. These are finite baseline tests of unchanged
  behavior. The new proof wiring requires a fresh CI build; no local full WASM
  build was run.
- Kernel axiom reports contain only `propext`, `Classical.choice`, `Quot.sound`.
  No new axiom, sorry, native_decide, partial definition or audit allow-list.
- The existing assurance workflow explicitly builds the regression module;
  default npm tests discover the new public test file.

Scoped compiled-C tail-recursion and csimp-reach gates pass over the two
changed runtime modules (GraphProjection and Handles), with no allow-list
edits. No proof of GPU/DOM behavior or C/JS interpreter correctness is added.
