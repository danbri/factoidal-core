# Exact compiled overlap-sum loop

The compiled-recursion gate in
https://github.com/danbri/factoidal-core/actions/runs/41535751642 rejected
`UI.LayoutPolicy.overlapSum`: its mapped-list sum retained a non-tail
`List.foldr` call proportional to the number of supplied footprints.

The declarative `overlapSum` remains unchanged. `overlapSumTR` fuses the map
into a `List.foldl` Nat accumulator. The kernel-checked compiler replacement
`overlapSum_eq_overlapSumTR` proves equality of the complete functions for
every box and list, using associativity of Nat addition. Repeated overlapping
regions still count repeatedly. There is no union-area interpretation and no
change to the application policy or budget. Its axiom footprint is
`[propext, Quot.sound]`; no assumptions, partial definitions, trust escapes,
raised limits or allow-list entries were introduced.

Validation used Lean 4.33.1 and actual Lake package compilation:

```sh
# Working directory: formal/lean4
lake build L4Factoidal.UI.LayoutPolicyTests \
  L4Factoidal.UI.PresentationTests L4Factoidal.UI.PolicyProtocolTests
# Working directory: repository root
python3 tools/lean-tail-recursion-audit.py --gate \
  --json /tmp/factoidal-graphics-ci-lake-tail.json
python3 tools/lean-csimp-reach.py --gate --cross-check \
  --json /tmp/factoidal-graphics-ci-csimp.json
```

The build completed 12 jobs and evaluated all 106 existing guards in the
three UI test modules (35 layout-policy, 24 presentation, 47 protocol).
Both compiled audits returned zero. The replacement audit resolved all seven
replacement theorems in these 11 compiled modules, found 11 calls of their
replacements, and agreed with Lean's own compiler-replacement table on all
seven. The emitted `checkFootprints` caller invokes `overlapSumTR`; its
specialized fold advances through `goto _start` rather than a self-call.
The original right-fold specification remains emitted but is not reached by
compiled callers.

This is targeted UI validation. Another 234 replacement-bearing modules were
explicitly unbuilt locally; these results do not claim the full repository CI
has run. The separate stale dataflow inventory failure in
https://github.com/danbri/factoidal-core/actions/runs/41535751593 still requires
fresh registry generation; it is not repaired by this proof change.

The dataflow workflow now runs that generator against its freshly built
registry and preserves both outputs, their SHA-256 values, the source commit,
generator hash and Lean version as a seven-day CI artifact. It then runs the
existing negative/positive gates and requires the generated files to match
the committed tree. A stale document therefore still fails CI. The upload
runs after later failures only if fresh generation itself succeeded; checkout
files are never relabeled generated output after a failed build/generation.
This permits retrieval of actual generator output for review when the local
disk cannot accommodate the 456-module registry closure.
