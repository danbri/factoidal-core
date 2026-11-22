# Mixed SPARQL integration and local Hub demo

Date: 2026-11-22

The GPU join and mixed SPARQL work from PRs 716, 720 and 721 is integrated
with the current `main`, preserving the EPUB reader and shared Foafnaut
import-root checks. The entry-point inventory follows the current Lean-owned
PVGraph API; entries for the removed JavaScript evaluator are not restored.

## Hub workbench

`docs/web/hub/gpu-sparql/` is a standalone Hub workbench. Its initial loader
uses the same-origin `npm/factoidal/browser.js` and matching local Wasm
assets. It has no dependency on publishing a new npm version. The page
checks all four mixed-query operations and the runnable, bound
`gpuSparqlStage` before it evaluates a query.

The user can load a local RDF file, edit RDF and SPARQL, choose automatic,
CPU or required GPU execution, and compare the complete result with a
separate CPU run. The original sample datasets have 64, 2,048 or 8,192
people and include joins, OPTIONAL, grouping, duplicate solution rows,
CONSTRUCT and ASK examples. The UI displays the query result, returned join
and device-phase traces, query wall time, separate load/parse times, and the
live registry entry. A downloadable run record includes the runtime URLs,
query, options, timing and result preview.

RDF parsing, algebra, placement and graph-isomorphism checks remain in the
shipping engine. The UI reads files and presents API results. SELECT
comparison uses exact ordered binding snapshots, including duplicates;
graph comparison calls the engine's isomorphism operation. Separate query
runs can differ for nondeterministic expressions or fresh blank nodes.
These browser measurements do not establish a physical-GPU speedup.

Build and serve instructions are in `docs/web/hub/README.md`. The Hub index
links the workbench and labels its local runtime explicitly.

## Integration checks and fixes

The full package gate exposed refusals from `Wasm.Ops.PVGraph` whose
`Lean.Json` serialization sorted `error` before `ok`. The shared ABI error
path uses an ordered-envelope fast check, so these refusals lacked a
declared error code. PVGraph and mixed-query refusals now use the existing
`errJson` helper. Four build-time checks exercise the actual PVGraph
dispatch entries, in addition to the package's exhaustive reflected-op
error tests.

The compiled recursion audit found a dataset-length continuation chain in
variable GRAPH evaluation. When the dataset has more than 256 named
graphs, that operation now uses the complete reference CPU evaluator.
`pattern_graphVar_large` states the exact fallback, and `pattern_sound`
continues to prove the complete query answer. Boundary fixtures check
dispatch at 256 named graphs and all 257 result rows at 257. The six new
recursion inventory entries individually describe their production bounds
or dependence on query syntax; they do not waive data-length recursion.

The full-Wasm CI lane had overridden Lean's worker stack to 16 MiB. The
existing `JS.Str.decodeUnits_charUnits` proof fails under that override and
passes with the default stack using the same compiler and source. The lane
now keeps the compiler default. No theorem or kernel check was weakened.

The complete package checks also execute README examples and a child TAP
runner. The mixed-query example now creates its own dataset and handles
required-GPU refusal explicitly. The PVGraph example uses the package's
portable engine loader. The child test process requests TAP explicitly so
its result check works on Node versions whose default reporter differs.

The current `main` passes the Foafnaut builder's shared `CORE` roots into
its Std-import audit. The premerge wrapper now passes those same arguments
to the unchanged audit body and refuses missing or malformed root lists.
Focused tests check allowed imports, rejection of forbidden Std imports in
the second root, and refusal of empty or malformed lists.

Validation includes the source-aware Lean closure, the full rebuilt Wasm,
the complete npm suite, actual WebGPU query/protocol tests, the Hub build
and workbench smoke checks, and `tools/premerge.sh`. The source and runtime
used for each execution are recorded by their test runners. npm publication
is a separate later release action.

## Cold-source CI budget

The [SPARQL contract run on the integrated source](https://github.com/danbri/factoidal-core/actions/runs/45009630358)
was cancelled after 20 minutes during its fresh dependency compilation,
at the configured job limit. Its 456-module source closure had completed
319 modules successfully, with no compiler errors or nonzero compile exits;
`SPARQL/DatasetRestriction.lean` was compiling when it stopped. The theorem
axiom-report gate had not yet run.

The caller now allows 90 minutes, matching the existing full-source Wasm
and cold registry/dataflow lanes. The reusable workflow's source isolation,
per-module time, memory and stack limits, 22 requested modules and 67
required theorem reports are unchanged. YAML validation confirms that only
the caller's job budget changes; this repair does not change production
code or claim a completed replacement CI run.

The [replacement contract run](https://github.com/danbri/factoidal-core/actions/runs/45011928104)
completed all 456 fresh source compilations successfully in about 26
minutes. Its hygiene audit passed, but the individual-report check found
one missing report: `L4Factoidal.SPARQL.GpuQuery.Plan.run_eq`. The theorem
was already compiled; its module now explicitly prints its axioms alongside
the existing reports. The same 67-report requirement remains in place.

A single-module rebuild with the CI's strict warning, memory and stack
settings prints that `Plan.run_eq` depends on no axioms. Generated C and
`.olean` are byte-identical before and after this reporting-only edit:

- C SHA-256: `f50f7d11753d8cbc0c6acfbf55b1fa68c943265a0e5ac0963f55292f2ede780c`
- `.olean` SHA-256: `95602254c86acb07e39d9daf466d5c4cfd6502cda498c38bd948475a961e598c`
