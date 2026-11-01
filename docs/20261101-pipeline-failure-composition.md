# Pipeline success and failure composition

Added three theorems over the actual `Dataflow.Pipeline.run` implementation:

- `run_append`: concatenation is executable Except composition.
- `run_append_ok_iff`: output exists exactly when the prefix succeeds and the suffix succeeds on that same intermediate value.
- `run_append_error_iff`: an error comes from the prefix, or from the suffix after a successful prefix.

These hold for arbitrary wire systems and components, without a component
soundness assumption. They preserve exact errors, including wire failures.
They do not prove successful execution of any particular compositor recipe,
nor certify host IO, publication, or browser behavior.

Validation on 2026-11-01: `lake build L4Factoidal.Dataflow.Pipeline` passed
(78 jobs). `run_append` has no axioms; the two equivalences use only
`propext` and `Quot.sound`. A temporary mutation replacing component-error
propagation with `.ok x` was rejected at `run_append` (and existing proofs).
The mutation was not applied to repository source.

Also reran `node --test tests/hub/compositor_document_test.mjs
tests/hub/compositor_pod_storage_test.mjs` with Node 22: 13 passed, zero
failures/skips, including a real temporary loopback LWS server. This does not
establish browser interoperability with Dan's actual laptop pod. That and
publication remain pending. Credentials are excluded as schema fields;
arbitrary user-entered source text can still contain secrets.

## Compositor worker failures

The actual app now rejects pending pod requests on worker error and refuses
further requests to the failed worker. A synchronous postMessage failure clears
its pending entry so a corrected request can be retried. Previously both paths
could leave the pod controls blocked indefinitely. Two lightweight tests execute
the component methods in a DOM-free VM; both pass. They are included in the
existing package compositor test wrapper (expected discovery now 30). A full
package-wrapper run remains pending; this is not browser/pod acceptance.

## Exact failure witness

`Pipeline.run_error_iff` now characterizes every error by a list split, a
successful prefix run, its intermediate value and the failing component's
actual packed run. The reverse implication proves that the witness forces
that same error regardless of the suffix. Duplicate component names do not
weaken the witness: it identifies a list position by its prefix. This theorem
uses only `propext`; the normal 78-job Pipeline build passed.

The expanded package compositor wrapper discovered all 33 tests but 28
engine-dependent tests failed because this source checkout lacks its local
`l4factoidal.mjs` build artifact; the five new UI regression tests passed.
That wrapper is not yet validated against rebuilt current-source artifacts.
The docs shell dependency was restored with the locked docs npm install; the
real Eleventy page test now passes for both compositor and SVG hub shells.

A separate run of the same six leaf suites against the installed published
0.27.0 engine passed all 33 tests (zero skips). This validates the UI fixes and
existing recipe behavior with that artifact, not the absent rebuilt local
package. Routing tests inject admission reports to exercise host branching;
they do not substitute for testing the newly compiled admission producer.
