# Independent SSZ container proof repair — 24 November 2026

Tracking #875, #872 and #725. Base #873 at `5decf5cfe421acd5f2fff0f8b6b749e7a624799e`. New isolated branch; no main changes.

## Observed failure (prior exact CI run)

[Run 45330906097, job 138231613722](https://github.com/danbri/factoidal-core/actions/runs/45330906097/job/138231613722): BasicTypes and its dependencies completed in 5.501 seconds; ContainerRoots hit its 120 s build cap and direct 45 s cap. The prefix through line 147 completed in 0.914 s; through 154 returned exit 1 in 0.964 s, an unsolved goal containing `throw ContainerError.versionWidth` followed by the rest of the do block. The first failing prefix is not evidence that this is the sole cause of the timeout. All subsequent native tests were skipped due to failure. Raw diagnostics artifact 14891792288.

## Repair

Use explicit Except case analysis in the real version admission, header construction and header/attestation Merkle-root paths, keeping the prior check ordering and propagation. Restrict simp to the relevant defining equations and premises instead of asking it to reduce unrelated cryptographic operations. Keep all 10 container and 5 attestation theorem statements byte-identical (checked by extracting the statement text before and after), and all 7 signing-domain statements unchanged. No theorem removed. Keep the SHA2 code and all reference oracle code unchanged. The active attestation audit pins the two newly edited source blobs; the earlier versions remain in their historical commits. No new package or compiler.

## Verification status

No local Lean toolchain or shared Mac checkout is accessible from this session. The current branch is a candidate repair, not a checked proof result. The existing specialised workflow must run the full native comparisons and exact-checkout axiom audits, with the prior regressions and falsification controls intact. Compiler, runtime, caller-provided state context, and unproved full SHA-256 refinement remain explicit trust boundaries. No BLS or state transition acceptance is implied.
