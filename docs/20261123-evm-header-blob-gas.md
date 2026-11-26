# Independent blob-gas header checks — 23 November 2026

Issue #856; strict goal #725 / #652. Base e15d8083d8ba27d604a8043e24259019557f1c94, draft #855. This change is an unverified source candidate until fresh CI has passed.

The canonical pair checker now checks the declared blob fields after successful legacy linkage and fee checks. It uses the target at the child timestamp, the maximum at each header's own timestamp, and saturating natural subtraction. Pre-Cancun missing fields supply zero. RLP/hash admission is unchanged. Osaka remains indeterminate. No external implementation, Lake dependency, compiler change or runtime oracle. The native executable still requires the experimental Keccak opt-in.

The five additional statements cover saturation, exact subtraction, pre-Cancun bypass, declared blob-check soundness and error propagation. The revised pair-connected theorem includes the new checker; earlier admission/hash theorems remain. Actual axiom sets and source pins must be collected from the existing CI gate, not inferred.

Reproduce via the existing header RLP workflow: fresh native build, direct Lean axiom print, independent test-only RLP/Keccak comparison and integer recurrence grid, mutations. The former width-only hash vectors remain; pair vectors now set correct blob fields. No local Lean executable or shared Mac access is available in this session. The GitHub branch is isolated, with no main merge or release.

Normative inputs: EIP-4844 and EIP-7691 as retrieved 23 November 2026. The declared-use checks do not compute blob count from actual transactions; neither authenticated parent history nor blob base fee, KZG, receipt/state commitments, Osaka/BPO or full EL/CL validity is established. Compiler/runtime, existing Keccak and host I/O assumptions remain. No new performance measurements or independent client comparison yet.
