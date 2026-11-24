# Checked header to executable BLOBBASEFEE, 24 November 2026

Pre-code obligations: [#858](https://github.com/danbri/factoidal-core/issues/858). Base `07fc8d35dbd2f61a016b1dd4fdb84550a5edc9ef` ([#857](https://github.com/danbri/factoidal-core/pull/857)).

The new B operation uses the existing canonical checked parent/child path, computes the selected Cancun/Prague integer blob price from child excess, projects prices into Core.State and executes the real 0x4a dispatcher. No runtime oracle. H and P remain unchanged. This is a narrow frame-context connection, not a full block or transaction execution path.

Normative sources: EIP-4844 gas accounting and integer exponential, EIP-7691 first Prague block parameters, EIP-7516 opcode. Before Cancun and at/after Osaka this operation is indeterminate. Excess above 64 times the denominator or nontermination within 512 terms is an implementation refusal; not a consensus-invalid verdict. This cap is not a proof of completeness. Parent authentication, transaction-derived blob counts, full settlement, KZG, Osaka/BPO, proof of normative recurrence refinement and full client operation remain open. Compiler/runtime and experimental Keccak opt-in remain explicit.

Run the existing header RLP Linux workflow (native executable build, actual axiom output, source pins, independent test-only Node oracle, retained and added adversarial controls). Local container has no pinned Lean installation or direct GitHub network; no local Lean compilation, timing comparison or axiom evidence is claimed. Hosted CI is pending at submission; results must be recorded from the actual run. No merge or release.

First hosted attempt [45302404923](https://github.com/danbri/factoidal-core/actions/runs/45302404923) at `dec4a717389543d5d8e5f268e059e7483997e93d` failed to compile two multiline structure updates (and the dependent dispatcher theorem). No native rows executed; transient elaborator recovery terms are not evidence. Fix record-update layout; retain all proof statements and gates.
