# One shared component descriptor for useful composition

Date: 2026-10-31. Status: design proposal only; no registry/API migration.
Tracking: https://github.com/danbri/factoidal/issues/1213 (shared descriptors).
Based on release branch commit `542730da637060eac46c77d01eadeefc37b235e3`.

## User direction and purpose

The coordinator records the user's direction: standardize the component registry
used by the dataflow node UI; make the account of composition constructive and
pro-human, without an ideologically reductionist account of human purposes.
This paragraph records the steer, not a verbatim transcript of the user.

Here, constructive means useful witnesses, understandable diagnostics, repair
paths and human agency. It does **not** impose constructivist logic, ban classical
mathematics, or disallow Lean's standard axioms. Proof records must state their
actual logic/trust basis, including `propext`, `Classical.choice` and `Quot.sound`
when used. A formal existential theorem does not by itself provide a serialized,
computable witness; name a witness producer/checker separately when one exists.

A component can help people transform documents, compare sources or maintain
attribution without having a complete correctness proof. Unproved is not invalid;
a failed application precondition is not a judgment of the component's worth.
Likewise, a proved algebraic contract is not a judgment that an application is
useful, fair, safe for every setting, or desirable to the people affected.

Purposes are plural, contextual, attributed human statements. Preserve narrative,
graph-level descriptions and disagreement rather than forcing every purpose into
atomic features or a scalar. Record who proposes a use, for whom, with what
constraints, and where that account is uncertain. Do not infer demographic facts,
consent, authority or usefulness from these descriptions. There is no universal
utility/ethics score, assurance ranking or automatic moral endorsement.

## Existing foundations and the concrete gap

Issue [975](https://github.com/danbri/factoidal/issues/975) requires typed semantic
contracts and actual entrypoint binding, not merely an inventory. Issue
[1002](https://github.com/danbri/factoidal/issues/1002) treats graphs/descriptions
and evidence as meaningful units. Issue
[1130](https://github.com/danbri/factoidal/issues/1130) adds named typed ports;
[800](https://github.com/danbri/factoidal/issues/800) covers capability-aware
planning. This proposal complements those obligations; it does not close them.

`Dataflow/Registry.lean` and `Wasm/Ops/StageList.lean` export single-input registry
entries. `Wasm/Ops/GraphNodes.lean` separately exports multi-port stages.
`Dataflow/NodeSettings.lean` and `pipelineCheckNodes` resolve settings, selected
wires and proof-domain changes. `foundation/entrypoints.toml` distinguishes whole
from partial implementation coverage. npm runners add binding availability and
runtime records. The compositor also has manual recipe links and presentation
adapters, which are not all checked graph edges.

The gap is a shared versioned description of these facts and their limits, not
an absence of all component structure. Several existing notes already discuss
[settings/provenance](2026-10-25-pipeline-settings-and-provenance.md),
[graphs/XProc](2026-10-28-dataflow-and-xproc.md),
[proof boundaries](2026-10-21-semantic-proof-boundaries.md) and
[capability-aware planning](2026-10-12-capability-aware-planner.md).

## Proposed model: Factoidal Component Descriptor 1.0

This is a proposed **project interoperability profile**, not an existing external
standard. Use one canonical `ComponentDescriptor` model, serialized as versioned
JSON by the registry producer. UI, API and CLI consume that same descriptor;
they may render different views but must not maintain substitute component tables.

A component definition has stable identity and a source revision. A settings- and
backend-bound view references that definition and records the resolved facts.
Execution evidence references the same descriptor/binding digests. These are
phases/views of the one model, not three independently authored registries.
Keep old stage identifiers and aliases, including `datasetMerge`; never reuse an
identifier for a different operation. Schema version, component revision and
artifact identity are separate values.

Proposed core sections:

| Section | Meaning and required distinction |
| --- | --- |
| `modelVersion`, `id`, `revision`, `legacyIds` | Version negotiation, stable identity and source provenance; not an authorization credential. |
| `presentation` | Title, description, documentation, domain tags and accessibility text. UI coordinates/colors remain view preferences. |
| `purposes` | Attributed intended uses, people/context, constraints and uncertainties. Author-stated or reviewed, never theorem-derived human value. |
| `ports` | Ordered named input/output ports, existing wire identifiers and representation/media annotations. String compatibility alone does not establish XML/RDF meaning. |
| `parameters` | Shape/defaults, binding time and existing role: parameter, selects-wire, inert, narrows or unlisted. Bound values/digest and derived wires are explicit. |
| `contracts` | Individually identified propositions: statement, foundation/specification edition, domain, pre/postconditions, scope and excluded claims. No universal correctness flag. |
| `effects` | Declared possible reads/writes/callbacks/sinks, declaration completeness, required authority, and actual enforcement boundary. Unknown is not pure. Grants are supplied by the trusted execution context, not by descriptor prose. |
| `assurance` | Evidence per contract: exact producer/theorem/checker, proof system/version/axioms, named assumptions, domain applicability and implementation-refinement coverage. Tests are separate support, not proof. |
| `bindings` | Backend/entrypoint/host/artifact identities, whole/partial coverage and unresolved obligations. A semantic model theorem does not automatically cover its JS/WASM transport. |
| `empiricalEvidence` | Suite/input revision, artifact, environment, result location and separate pass/fail/expected-fail/unsupported/unavailable/not-run counts. Missing results mean not known, not zero failures. |
| `unknowns` | Identified gaps, untested conditions, counterexamples and issue links. Distinguish unknown, inapplicable, unsupported and contradicted claims. |

An illustrative descriptor view (candidate field names, **not** a new runtime
export or fresh test result) makes the separation concrete:

```json
{
  "modelVersion": "1.0-draft",
  "id": "urn:factoidal:component:xslt4Transform",
  "revision": {"source": "542730da637060eac46c77d01eadeefc37b235e3"},
  "legacyIds": ["xslt4Transform"],
  "presentation": {"title": "Transform a document with XSLT"},
  "purposes": [{"text": "Help an editor produce a readable document while retaining the source.", "basis": "author-stated design intent", "attributedTo": "component maintainer"}],
  "ports": [
    {"name": "source", "direction": "input", "wire": "String", "representation": "XML source text"},
    {"name": "result", "direction": "output", "wire": "XSLT result"}
  ],
  "parameters": [{"name": "stylesheet", "bindingTime": "node creation", "shape": "String", "contractRole": null}],
  "contracts": [],
  "effects": {
    "declared": [{"kind": "secondary-result-data", "boundary": "returned value"}],
    "declarationCompleteness": "unknown",
    "authoritySource": "not granted by this descriptor"
  },
  "assurance": {
    "legacyStatus": "tested",
    "proofs": [],
    "scope": "Existing adapter tests; no declared Lean stage contract"
  },
  "bindings": [{"entrypoint": "npm:xslt4Transform", "backend": "lean4-wasm", "coverage": "consult mapped entrypoint record", "artifact": null}],
  "empiricalEvidence": [{"suite": "npm/factoidal/test/qt4-public.test.mjs", "result": null, "state": "not replayed by this design note"}],
  "unknowns": ["No whole-pipeline proof", "No fresh artifact acceptance from this descriptor"]
}
```

This component remains usable. Missing contracts/results and unknown exhaustive
effects do not turn into fabricated proofs, scores, purity or authority. A bound
view would add the actual settings/backend/artifact and applicable obligations.

Use JSON Schema Draft 2020-12 for the future descriptor's **JSON shape**, not as
proof of its semantic claims. The schema document can use that dialect's `$schema`
and a project-owned `$id`; no schema endpoint is implemented by this note.
Validate locally from pinned schemas; descriptor input must not trigger arbitrary
schema/context fetches. Optional RDF/JSON-LD projections must be generated from
this same model, preserving identity and scope. Do not introduce a second source
of truth for RDF versus JSON.

Reuse [DCMI Terms](https://www.dublincore.org/specifications/dublin-core/dcmi-terms/)
for titles, descriptions, identifiers and licenses, and
[PROV-O](https://www.w3.org/TR/prov-o/) for the provenance of descriptors,
activities, evidence entities and attribution. Those vocabularies do not supply
our typed-port or security semantics. Their use does not make the complete
Factoidal descriptor an external standard. Proof/effect/port extensions remain
explicit project terms. [JSON Schema](https://json-schema.org/draft/2020-12/json-schema-core)
likewise validates structure, not human purposes, authority or theorem truth.

Unknown optional presentation metadata may be retained and displayed. Unknown
major versions or extensions marked critical for execution/assurance must stop
those decisions with a diagnostic; never silently discard a restriction. Older
clients may show a read-only unknown descriptor. A missing authority analysis
must not be interpreted as permission. Forward compatibility is not implicit trust.

## Mapping the current registry, without inventing evidence

| Current field/source | Proposed mapping and present gap |
| --- | --- |
| `Entry.nodeName`, `stage`, StageList `name`/`declaration` | Stable `id`/`legacyIds` plus source declaration; a Lean refactor must not silently rename public identities. |
| `area`, `dir`, `kind` | Presentation/domain and implementation/interface references. A source directory is not a statement of human purpose. |
| `wireIn`, `wireOut` | Default `ports`; join with `GraphNodes.lean: portStages` for named multi-port signatures. Preserve port order. |
| `Entry.params`, `NodeSettings.lean: settingTable` | `parameters`, roles/defaults and binding-domain rules. Do not guess a setting's contract role from its name. |
| `settings`, `settingsDigest`, `derived`, resolved wires | Bound view references; settings/backend changes require a new resolution and applicability check. |
| `status`, `registryStatus`, `checked`, `outside` | Preserve legacy fields as compatibility summaries; new views expose individual claims and applicability. `unproved` settings do not erase known tests or other valid claims. |
| `contract`, `theorems`, `ioAssumptions` | Contract/evidence references with named premises. Missing today: systematic statement/scope, producer/refinement links and proof-backend details. A theorem name alone is insufficient. |
| `tests` | Suite references only until a versioned run artifact supplies results. Do not manufacture current counts from a test filename. |
| `note` | Human notes and candidate structured limitations; migration requires review, not heuristic extraction as fact. |
| StageList `runnable`, npm `bound`/runner map | Operational availability and adapter binding; neither is permission, usefulness nor a semantic proof. |
| `entrypoints.toml` `covers=whole/part` | Backend binding coverage. Preserve the uncovered parsing/rendering/host steps rather than promoting a partial mapping to a whole producer. |
| `pipelineCheckNodes`, `graphCheckNodes` | Topology/wire reports and conditional composition-contract references for the actual submitted nodes/edges. A drawn/manual dependency is separately identified. |
| Runtime `evidence`, `artefact`, input/output/settings references | Execution view pointing to exact descriptor/binding revision; caller-supplied metadata is not an authenticated certificate. |
| Draft scoped provider context, https://github.com/danbri/factoidal-core/pull/279 | Candidate effect/authority enforcement evidence for a narrow provider boundary only; not a shipped generic capability system. |
| No current structured equivalent | Attributed purposes; structured effect completeness/enforcement; per-backend refinement; empirical freshness; constructive repair diagnostics. Mark these unknown until supplied. |

The registry producer should join the existing typed sources and validated
entrypoint/runner bindings. It must not hand-copy them into UI configuration.
Lean remains authoritative for the existing Lean contracts, setting roles and
wire judgments. Other proof/checker systems may be described with their actual
trust basis; interoperability does not automatically discharge a bridge into the
foundation or forbid classical arguments.

## Composition should give people witnesses and repair paths

Keep at least four judgments separate: wire arrival, semantic-contract
composition, effect-policy admission, and suitability for an attributed purpose.
The first three can have explicit formal or executable obligations; the fourth
requires contextual human judgment and cannot be inferred from their conjunction.

`Stage.comp_ok_contract`, `Pipeline.guarantee_sound` and
`Graph.guarantee_sound` already express conditional composition over actual typed
components. A useful account identifies the relevant middle values/edge witnesses,
which producers/checkers supply evidence, each adapter's preservation obligations,
and the remaining named assumptions. It must not substitute "all badges green"
for these links. A structural check is useful even when semantic or authority
obligations remain open; show exactly the useful result it establishes.

Diagnostics should name the failing edge/port/setting and offer explicit repair
options with their costs, losses and authority changes. Examples:

* A SPARQL Table does not feed an XSLT String input: offer an identified results-XML
  serializer/projection adapter, state its contract/test coverage, and retain the
  same evaluated result rather than quietly running a nondeterministic query again.
* A String wire arrives but its XML representation is unknown: offer a parse/check
  stage, or explain that the downstream transform can refuse it. Wire compatibility
  is not well-formedness or semantic preservation.
* A setting leaves a theorem's domain: identify that setting and domain; offer a
  supported setting, another backend, more evidence, or an explicitly scoped
  experiment. Do not describe the whole component as useless or invalid.
* A provider is not granted: explain the required authority and the trusted party
  who may grant it. Do not suggest that a UI checkbox or proof badge can supply it.
* An empirical result is stale or unavailable: identify the missing artifact/run
  and how to obtain it; preserve useful existing evidence without claiming freshness.

Adapters are components too: describe lossy projections, blank-node scope changes,
term/value distinctions, encoding and new effects explicitly. Recommendations
remain suggestions, not silently inserted semantics. Useful alternatives can
include a tested component, a different representation or a manual review step.

An explicit override records actor/attribution basis, reason, affected obligations,
settings/backend and run scope. It never inherits the bypassed proved guarantee,
changes a named hypothesis into an established fact, or grants missing authority.
Unaffected local proofs may remain visible with their own scope; an enclosing
composed claim that depends on the overridden obligation is unavailable. Preserve
counterexamples and refusal boundaries. This does not require globally demoting
all evidence or treating the experiment as worthless.

## Bounded implementation sequence and acceptance

This note changes documentation only. Follow-on work should:

1. Define the typed descriptor model/versioned schema and a producer joining
   registry entries, named ports, settings and binding coverage; preserve legacy
   identifiers and derive `stageList` compatibility views.
2. Expose the same serialized descriptor via API and CLI; migrate the node UI to
   consume it. Human labels/coordinates are views, not another semantic registry.
3. Add settings/backend-bound resolution and descriptor references to execution
   evidence. Keep effect declarations, actual grants and observed effects distinct.
4. Add constructive diagnostics/adapters and scoped override records. Adopt actual
   capability enforcement only after its host/identity boundary is ready.

Acceptance tests must exercise single/multi-port identity, settings-derived
wires, partial backend bindings, unknown version/critical restriction handling,
missing/stale empirical results, proof-domain changes, effect denials and
caller-forged evidence. Mutate an override and confirm no composed proved claim
survives the bypass. Confirm no unknown effect is treated as pure, no missing
suite becomes 0/0, no tested component becomes a theorem, and no unproved label
becomes a judgment of human value. Add parity tests showing UI/API/CLI consume
one descriptor revision. These are future tests, not results claimed here.
