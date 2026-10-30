# QT4 engines through npm, the CLI and dataflow

Release follow-up: https://github.com/danbri/factoidal/issues/1210
(careful XML release and public integration). No release or workflow is
dispatched by this change.

The existing `xpath4Eval`, `xqueryEval` and `xslt4Transform` npm APIs already
called the Lean QT4 engines. Their dataflow runners and CLI commands were
missing. The public dynamic context also left `fn:transform` disconnected,
so the recent assertion/serialization adapter fixes could not be exercised
through those public evaluation APIs.

This change adds three tested registry entries with the operation names,
preserving the existing descriptive registry identifiers. XML context text
is the input wire. New `Serialized XDM result` and `XSLT result` wires describe
the public serialized envelopes, rather than claiming a live XDM sequence
or an XML document for XSLT text/JSON output. No implicit conversion is added.
`NodeSettings` checks each required string and rejects unknown settings.
The host calls the existing API functions, checks only transport shapes,
and retains the Lean settings digest and evidence. The entries have no stage
contract and retain status `tested`. The existing node policy permits tested
nodes to run, with `checked: false` evidence and `proved: false`; the optional
`unchecked: true` setting also records the opt-in and reason.
Component theorems do not establish evaluator or adapter correctness.

The CLI `xpath4`, `xquery` and `xslt4` commands read explicit files and pass
strings to the existing dispatch operations. Query/module texts can be
positional or supplied by an option/file; ambiguous sources fail. The CLI
prints engine JSON by default, with explicit engine-serialization display
modes. QT errors keep their namespace/code/message, exit 1, and are printed
as JSON on stderr. Usage errors exit 2. No query/XML parsing, output-method
selection, secondary-result file writes, or stylesheet fetching is in JS.

The public XPath/XQuery environment now installs the same pure
`XSLT4.Qt.transformHost` used by the QT4 harness, with the existing public
evaluator fuel. Inline stylesheet transforms therefore reach the existing
assertion option: default false and explicit true/false. The connection adds
no external resource provider or new evaluator. Direct XSLT assertions stay
enabled. The common `source-node: .` invocation preserves the supplied XML
context. The callback environment is not reentrant: a `post-process` callback
that itself calls `fn:transform` currently fails with `FOXT0004`, matching the
existing QT4 harness adapter. Full callback reentrancy is not added here.
Input XML/schema-provider contexts are not extended. In particular,
the new schema-driven element-to-map PSVI/inheritance fixes remain dependent
on a validating host; public tests cover untyped/explicit-plan conversion and
its errors. They do not claim that every native schema test is reachable.

XProc is partially connected in Lean: `XProc31/Bridge.lean` lowers atomic
steps to the typed dataflow graph. The bridge does not prove the XML reader,
and no public npm/WASM XProc entry exists. A full XProc WASM binding is outside
this increment.

Validation uses named Lean targets and the native driver of the identical
dispatch ABI where disk space prevents a full local WASM rebuild. The npm
public integration tests default to the actual shipped WASM; a missing/stale
engine fails. The explicit `FACTOIDAL_QT4_NATIVE` test-only mode creates the
same public API over a real native dispatch process. It is not a WASM result.
The actual CLI helper is exercised through that same engine; help/usage also
run as real CLI processes. Exact-head build CI must run the default tests
against the rebuilt WASM before release.
The default WASM path additionally runs real `bin/factoidal.mjs` subprocesses
for success JSON and a nonzero QT4 error. The explicit native-driver mode
does not report that WASM subprocess test as run or passed.

## Local validation, 2026-10-30

- `tools/ensure-test-env.sh --check`: all suite fixtures present; optional
  F* native build products absent, so no F* binary suite score is claimed.
- Named `Wasm.Ops.Qt4` and `Dataflow.Qt4NodeTests` targets pass, including
  assertion/default/disabled-test/resource/e2m error guards and the new node
  settings/wire/status guards. Named `l4wasm-cli` builds successfully.
- Nine npm public integration test groups pass against that fresh native
  dispatch driver, with zero failures/skips. The earlier Oct-27 driver fails
  the new test because it has no QT4 dispatch operations; stale capability
  metadata is not accepted as a successful integration run.
- The tests check the actual public API and node runners, serialized atomic/
  map/element results, text and secondary XSLT results/messages, assertion
  default/true/false and unevaluated test/body behavior, direct-XSLT default,
  explicit element-to-map cast failure, no resource fetch, QT error QName,
  CLI-helper display/error handling, actual CLI help/usage processes, and a
  backend without QT4 operations refusing rather than falling back. The native
  test handle mirrors the actual raw `Error.envelope` transport; a dedicated
  refusal test prevents loss of the QT4 error QName in the direct CLI helper.
- `tests/dataflow/run.sh` passes: ten negative registry entries, fresh
  generated inventory, foundation, entry-point, runner and assumption gates,
  plus their 60 fixture tests. The existing unpinned `packSetStage` note is
  unchanged. Inventory has 147 entries: 82 proved, 33 tested, 16 assumed,
  16 missing. The three added entries are all tested, with no contract.
- Compiled-C tail and csimp gates pass on the scoped IR for `Wasm/Ops/Qt4`,
  `Wasm/Dispatch`, `Dataflow/Wire`, `Dataflow/Registry`, and
  `Dataflow/NodeSettings`. No allowlist or gate rule changed. This is a
  scoped result, not a new full-library compiled audit.
- JS syntax checks and `git diff --check` pass. No conformance fixture,
  exclusion, evaluator fuel, WebDAV implementation or release workflow changed.

No local full WASM rebuild was attempted under the disk budget. The default
CI path has ten test groups, including the additional actual operational
WASM CLI subprocess case. Those WASM results remain pending exact-head CI;
the nine native groups are not reported as a WASM measurement.

Root additionally checked the actual new CLI router with a valid cached
0.26 WASM artifact: `xpath4 1+1` exits 0 with JSON `xml: "2"`; malformed
`xquery '1 +'` exits 1 with JSON `xml.failed` and the full `XPST0003` QName.
This verifies the CLI transport against real WASM, not the new transform
host or dataflow metadata, which still require the rebuilt exact-head artifact.
