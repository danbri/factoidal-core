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

The local browser harness is blocked by socket `EPERM`; Linux CI and
published-page checks remain pending in the tracking issue. The full npm
suite was not rerun locally after the fixture check reported seven
missing external sets. The [design record](designissues/2026-11-22-gdsl-app-api.md)
links the relevant source, deployment instructions, transport bounds and
assurance limits.
