# Numeric refinement of the paired dash normalizer

`NativeSVGDash.normalizeLengths_numeric` establishes the whole result
identity for the actual producer:

```lean
(normalizeLengths pattern).map (List.map Length.value) =
  normalize (pattern.map Length.value)
```

It covers successful numeric lists and the exact error strings. The proof uses
an auxiliary result-shape lemma over the existing numeric normalizer, then
checks error, zero-result, odd-list and even-list branches. It does not replace
the production normalizer with a new definition.

This is stronger than the existing provenance and even-cardinality statements:
returning an empty list for every admitted input satisfies those statements but
loses actual numeric dash data. Whole-result equality closes that gap. It is a
refinement to the existing bounded Float normalizer, not a claim that the latter
implements all real-number SVG semantics or guarantees GPU pixel agreement.

`Length.calibrated_percentage` additionally proves that the actual calibration
function preserves a percentage record's magnitude for every supplied scale.
Both new theorem axiom reports contain only propext, Classical.choice and
Quot.sound. No new axiom, sorry or native_decide is used.

## Mutation and executable checks

A temporary compiled mutation retained numeric validation/errors but returned
`[]` for every successful input. The original provenance and evenness proofs
still checked with clean axiom reports. The new refinement theorem failed on
both nonempty odd and even result branches; Lean exited 1 with unsolved false
goals. This demonstrates sensitivity to the specific vacuous-output defect,
not a missing import or compilation failure in the mutant producer.
Files are under `/private/tmp/svg-unit-empty-mutation`.

The unchanged producer and complete proof file check successfully. Nine direct
unit controls pass, including new checks requiring `[2,3]` for a valid nonzero
even input and the exact negative-length error message. Existing build wiring
already checks this proof and test module. No renderer, sampling, normalized
value behavior, fixture, WASM or deployment was changed; no heavy build ran.

Commands ran from `labs/demos/foafnaut`:

```sh
LEAN_PATH=/private/tmp/svg-paired-check lean +leanprover/lean4:v4.33.1 SVGDashUnitProofs.lean
LEAN_PATH=/private/tmp/svg-paired-check lean +leanprover/lean4:v4.33.1 SVGDashUnitTests.lean
LEAN_PATH=/private/tmp/svg-unit-empty-mutation lean +leanprover/lean4:v4.33.1 SVGDashUnitProofs.lean
```

The final command is expected to fail; the first two must succeed.
