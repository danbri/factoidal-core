# GDSL public API and independent Hub application

Date: 2026-11-22

Tracking: [GDSL application integration](https://github.com/danbri/factoidal-core/issues/741).
Architecture: [public API and execution boundary](designissues/2026-11-22-gdsl-app-api.md).

## Change

`docs/web/hub/gdsl-app/` demonstrates the public GDSL interface with a
generic two-input signal mixer: multiply A, add B, and calculate inclusive
prefix sums. The same DOM-free recipe builds the PVGraph used by the UI,
copied JavaScript module, downloadable standalone HTML and automated
runner. Operator construction, admission, evaluation and planning remain
in Lean/Wasm.

The page loads the repository's same-origin `gdsl.mjs`, `browser.js` and
matching installed Wasm on demand. An independent app can vendor the
package at `vendor/factoidal/`. No npm publication is part of this change.
CPU, automatic and required-GPU modes expose execution status, complete
outputs, comparison results and phase timings.

The public runner now handles the shipping loader's thrown Lean refusal
envelope. Automatic execution of a reduction-containing PVGraph selects
the reference evaluator; malformed input and unrelated failures remain
errors, and required GPU never falls back. Selection is for a whole
PVGraph. Mixed SPARQL planning separately chooses individual query joins.

## Checks

The targeted host suite passed 45 tests; documentation passed 42 checks
(39 executed examples and three browser syntax checks); host-purity lint
passed 72 checks. Each reported zero failures and zero skips. Two of the
six new refusal regression tests failed before the host repair and passed
after it.

`tools/gdsl-app-smoke.mjs` passed 16 Node cases and 20 actual WebGPU cases
on SwiftShader. The same installed release from core commit
`e0666850902b16471c3299bde30944aa389604ec` was used, with Wasm SHA-256
`4688ddc7cf486b50982e783ad892336a1ff7bf8b4b7021e6fc5a9778f59b8ae8`.
Reports record the modified host-source hashes separately. Default,
empty, high-u32, 65-word and 4,097-word mixer cases matched the complete
reference outputs, and the shared GPU session released every tracked
buffer. Physical-GPU performance was not measured.

The initial local browser harness encountered socket `EPERM`, and the
initial full npm run lacked seven external fixture sets. The later CI and
deployment checks below complete those stages. The
[design record](designissues/2026-11-22-gdsl-app-api.md) links the relevant
source, deployment instructions, transport bounds and assurance limits.

## Completed CI and deployment

[PR 746](https://github.com/danbri/factoidal-core/pull/746) merged as
`b9f6c92bd022d7659752e0962aa34f7b4b53ccd1`. All 15 checks on its final
head passed, including the
[fresh full-Wasm run](https://github.com/danbri/factoidal-core/actions/runs/45032301445),
[browser smoke run](https://github.com/danbri/factoidal-core/actions/runs/45032301477)
and [npm/dataflow run](https://github.com/danbri/factoidal-core/actions/runs/45032301347).
The npm suite reported 2,165 passes with no failures or skips. The browser
run passed 23 GDSL app cases and 28 Paralliverse cases using Chrome 157
with SwiftShader, including all standalone export modes and refusal/recovery.

The [Pages deployment](https://github.com/danbri/factoidal/actions/runs/45019684127/attempts/2)
completed at 17:35 UTC. The
[live application](https://danbri.github.io/factoidal/web/hub/gdsl-app/)
and [source stamp](https://danbri.github.io/factoidal/source-commit.txt)
were checked afterwards. Its four application/public-runner modules match
their Git blobs at the merged commit. The normal release fetch verified
all 21 runtime files. Live runtime metadata records official
`build-ef1710ff226d-web`, from
`ef1710ff226d84f41f92156e1d271f907235579b`; the complete 33,229,668-byte
Wasm download matched SHA-256
`a0bfdcce867302d353101f65fff2faa9c1f0c38e9daa29219ec9a8fd6702e754`.
The deployed host is newer than this ancestor runtime. Subsequent XML/font
source changes mean this is not an exact runtime-producer match for merged
main.

A direct live browser run completed in automatic mode. That browser had
no WebGPU adapter, so the documented CPU fallback produced mixed values
`[7,13,16,26,42,41,57,62]` and cumulative values
`[7,20,36,62,104,145,202,264]`, with zero GPU dispatches. The page reported
31.9 ms for construction/execution; this single browser measurement is
not a physical-GPU performance result. The
[completion comment](https://github.com/danbri/factoidal-core/pull/746#issuecomment-7083016520)
records the final release evidence.
