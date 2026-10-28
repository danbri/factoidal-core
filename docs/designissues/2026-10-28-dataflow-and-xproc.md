# Factoidal checked pipelines and XProc 3.1

Date: 2026-10-28. Status: proposals approved (owner, 2026-10-28: "Merged
https://github.com/danbri/factoidal-core/pull/185 - do it!"; also "we add a
lot more xml stuff soon"). Epic https://github.com/danbri/factoidal/issues/1129;
stage 1 in progress (section "Stage 1").

Owner, 2026-10-28, verbatim (chat): "How does our dataflow architecture
compare to xml processing pipelinez / xproc"

Factoidal side: `formal/lean4/L4Factoidal/Dataflow/` (`Stage.lean`,
`Wire.lean`, `Pipeline.lean`, `Registry.lean`, `NodeSettings.lean`),
`npm/factoidal/lib/nodes.mjs` and `evidence.mjs`, `docs/dataflow-inventory.md`,
`docs/designissues/2026-10-25-pipeline-settings-and-provenance.md`, hub page
`docs/web/hub/checked-pipelines.md`. Tracking:
https://github.com/danbri/factoidal/issues/975 (component contracts),
https://github.com/danbri/factoidal/issues/1002 (dataflow and explanations).

XProc side: XProc 3.1: An XML Pipeline Language, Community Group Report of 30
May 2025 (XProc Next Community Group; not on the W3C Recommendation track),
https://spec.xproc.org/3.1/xproc/, and its Standard Step Library,
https://spec.xproc.org/3.1/steps/. XProc 1.0 is the W3C Recommendation of
2010 (https://www.w3.org/TR/xproc/).

## The common part

Both describe a computation as steps composed into a pipeline. A step has
inputs, outputs and parameters that are fixed when the step is written
(XProc options; Factoidal node settings). Both check the composition before
anything runs. Both ship a library of steps: XProc's standard step library
(XSLT, XQuery, validation with XML Schema, RELAX NG and Schematron, HTTP,
load and store, JSON); Factoidal's registry of 140 stages (readers,
reasoners, the SPARQL evaluator, SHACL and ShEx, writers, RDFC-1.0, CSVW).

## Differences

| | XProc 3.1 | Factoidal (2026-10-28) |
| --- | --- | --- |
| Shape | a directed acyclic graph of steps; a cycle is static error XS0001 | a list: `pipe(n1, n2, ...)`, `Pipeline.lean` is a list of components |
| Ports | named input and output ports per step; one primary port; a port takes one document or a sequence | one input wire and one output wire per stage; no sequences |
| Control | compound steps: `p:for-each`, `p:viewport`, `p:choose`/`p:when`/`p:otherwise`, `p:if`, `p:try`/`p:catch`/`p:finally`, `p:group` | none; a stage error stops the run |
| What flows | a document: a representation (XML, HTML, JSON, text, other media types) plus properties (`content-type` always, `base-uri`, `serialization`) | a typed value on one of 21 wires (`Wire.lean`: text, document, dataset, graph, table, answer, ...), with the evidence records of the steps so far |
| Type check | content types declared on ports; the static phase finds unconnected ports and cycles; type errors are not raised statically | `wellTyped`: each output wire equals the next input wire or converts to it by one of four fixed conversions; theorem `run_no_wire_error`: a well-typed pipeline never stops with a wire error |
| Meaning of a step | prose in the step library; conformance by the XProc test suite | a Lean contract per stage and a status: 82 proved, 26 tested, 16 assumed, 16 missing (out of 140, `docs/dataflow-inventory.md`) |
| Meaning of a pipeline | the steps run in dependency order | `guarantee_sound`: a successful run satisfies the composed contract when the union of the stages' named assumptions holds; one theorem for every pipeline |
| Parameters | options with XPath expressions, static options, `use-when` | settings with a role per stage (`parameter`, `selects-wire`, `inert`, `narrows`, `unlisted`); a setting outside the proved domain makes the node `unproved` |
| Record of a run | not specified (implementations log) | one evidence record per node: stage, status, contract, settings and their digest, assumptions; network reads give retrieval records (CLAUDE.md, 2026-10-25) |
| RDF | not in the standard library; extension steps in implementations (XML Calabash 3: `cx:rdf-merge`, `cx:rdf-graph`) | the data model: datasets with a denotation; blank-node scoping and RDF merge are proved (`scopedParse_combine_isMerge`) |
| Effects | `p:http-request`, `p:load`, `p:store`, file steps | IO stages are `assumed` (`IOStage.Realised` is their named assumption) |
| How a pipeline is written | an XML document, run by more than one implementation (XML Calabash, MorganaXProc-IIIse) | calls to the JS API (`node`, `pipe`, `run`), checked by the wasm op `pipelineCheck`; no pipeline document format |

In short: XProc has the richer graph and control model and a document
format; Factoidal has typed wires, per-stage contracts with a proof status,
a composition theorem and a run record. XProc says nothing about what a
pipeline computes beyond the prose of its steps; Factoidal does not yet have
branching, sequences, error handling or a pipeline document.

## Proposals (decision needed)

1. **A graph of stages with named ports.** Replace the list in
   `Pipeline.lean` with an acyclic graph whose nodes have named, typed
   ports. `guarantee_sound` generalises: the composed contract is the
   conjunction of the stage contracts over the edges, read through `arrive`
   per edge. First users: a merge of two datasets (`scopedParse_combine_isMerge`
   as a stage with two inputs), SHACL with data and shapes as two ports
   (today `shapes` is a setting), a SPARQL query over several sources.
2. **Sequence ports.** A port that carries a list of values of one wire
   (XProc's `sequence="true"`), with `for-each` as a stage combinator: its
   contract is the stage contract for each element.
3. **Choice and error handling.** `choose` on an `answer` wire (ASK) or a
   validation report, and `try`/`catch`. Contracts: for `choose`, the
   contract of the branch taken, with the test in the evidence record; for
   `try`, the disjunction of the two contracts. Both are combinators over
   components, so one theorem each covers every use.
4. **A pipeline document.** A serialised pipeline that the wasm op checks
   and `run()` executes, so a pipeline can be stored, signed, cited in an
   evidence record by digest, and run by another host. Two forms to weigh:
   an RDF vocabulary (the pipeline is data the engine can query and
   reason about), and a subset of XProc 3.1 XML (existing tools and
   readers). They are not exclusive.
5. **XProc 3.1 as an input language.** The Lean tree has XML, XPath 1.0,
   XSLT and Schematron. A Lean reader for an XProc 3.1 subset (atomic steps
   that map to registry stages: `p:xslt`, `p:validate-with-schematron`,
   `p:identity`, `p:load`, `p:store`, plus `p:choose` and `p:for-each` after
   proposals 2 and 3) would let XProc pipelines run with Factoidal's
   evidence records, and could be measured with the XProc 3.1 test suite.
   XPath 2.0 and later, which many XProc 3 pipelines use, is not in the Lean
   tree (`docs/w3c-survey.md`).

Order, if approved: 1 then 2 and 3 (they change `Pipeline.lean` and its
theorems), then 4, then 5. Each stage of the work gets an issue.

## Sources

* XProc 3.1: An XML Pipeline Language: https://spec.xproc.org/3.1/xproc/
* XProc 3.1: Standard Step Library: https://spec.xproc.org/3.1/steps/
* XProc 1.0 (W3C Recommendation): https://www.w3.org/TR/xproc/
* XML Calabash 3, `cx:rdf-merge`: https://docs.xmlcalabash.com/reference/3.0.31/cx-rdf-merge.html

## Stage 1 (https://github.com/danbri/factoidal/issues/1130)

Stage 1a, Lean (2026-10-28):

* `formal/lean4/L4Factoidal/Dataflow/Graph.lean`: `PortSig` (named input
  ports, one output wire), `PortComponent`, `Src` (graph input `k` or node
  `j`), `Graph` (nodes in a topological order: a node reads only graph inputs
  and nodes before it). `graphIssues`: the static check (`unknownInput`,
  `forwardRef` for a cycle, `portCount`, `wireMismatch`). Theorems
  `Graph.guarantee_sound` (every node's contract holds on its sources, under
  the union of the named assumptions) and `Graph.run_stage_error_only` (a
  checked graph with inputs on the declared wires fails only in a stage).
  `PortComponent.ofComponent`: a one-port component of `Pipeline.lean` with
  port `in`; `StageSig.toPortSig` does the same for registry signatures.
* `Dataflow/GraphStages.lean`: `datasetMergeStage`, the first stage with two
  ports (`left`, `right`); theorem `datasetMerge_isMerge`: its output denotes
  an RDF merge of its inputs (blank nodes of the two inputs kept apart).
* `Dataflow/GraphTests.lean`: two N-Triples documents that both use `_:b`,
  two reader nodes, the merge node, selection, BGP SELECT: two solutions; the
  graph's contract with no premise (`twoDocs_sound`); fan-out; each kind of
  static issue with its node and port; registry signatures as port
  signatures.

Stage 1b, next: the wasm op (a JSON graph of registry stages and port stages,
answering the issues, the output wire, the assumptions and each node's
status), a wasm op for `datasetMerge`, and the npm API that runs a graph
(`graph({inputs, nodes})`, `run(graph, inputs)`). The list API (`pipe`)
stays.
