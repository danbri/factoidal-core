# GSSL term-ID width profiles for Shardborough

21 November 2026. Work: PR #692, release gate #691. No assured Hub lab is published by this work.

## Decision: u64 storage IDs, two portable execution profiles

Keep the logical identifier in the GSSL/Sh​ardborough adapter as an actual
SBM11 `TermId` wrapping Lean `UInt64`. Do **not** narrow a database ID by
casting to `UInt32`. Expose two different and explicitly named execution
representations:

1. **direct64-lanes:** represent each global `TermId.bits` in WGSL as
   two 32-bit words (`lo`, `hi`). The exact pair is reconstructable. Join
   equality tests *both* lanes. A source triple is 6 words/24 bytes; a
   projected 2-term result is 4 words/16 bytes.
2. **dense32-snapshot:** assign reversible query/snapshot-local `u32`
   codes to the actual 64-bit IDs within the selected graph fragment,
   reserving code 0 for unbound values. GPU triples use 3 words/12 bytes;
   2-term results use 2 words/8 bytes. Every returned code must decode
   against the *same* dictionary before a result is considered usable.

These layouts are alternatives for the **backend**, not competing RDF term
identities or a change to SPARQL semantics.

## Why SBM11 u64 matters

SBM11 `Storage.Sbm11.TermId.lean` uses the top nibble for term type:
1 blank nodes; 2 IRIs; 3 dictionary literals; 4 inline integer;
5 inline boolean; 9 RDF 1.2 triple terms. The remaining bits encode a
dictionary rank or inline value/subtype. The inline integer form is
valid only for a canonical lexical form, so lexically distinct literals
are not improperly folded. `TermIdTheorems.toId?_eq_iff` proves
dictionary-scoped term-ID equality is exactly RDF term equality.

A distinct `GraphId` uses 0 for the default graph; `TermId` never
uses 0. Never conflate graph identifiers and term identifiers merely
because both wrap `UInt64`.

SBM11 dictionary ranks are generation-dependent; equal integer bits
from different generations do **not** authorize a cross-generation
semantic join. Snapshot/generation equality is a production precondition.

## The WebGPU constraint

WGSL's October 2026 spec supports concrete `u32` and `i32`
integers, but not a concrete `u64` integer scalar.
A `vec2<u32>` or two adjacent storage words is a portable exact
representation for equality and copying. The experimental fused BGP
kernel uses six adjacent `u32` words per source triple; it never
converts IDs to `f32` or JavaScript `Number` before splitting.
The JavaScript host accepts `BigInt` or exact decimal/hex strings,
then extracts exact low/high words.

WGSL source reference: https://www.w3.org/TR/2026/CRD-WGSL-20261021/

## Assurance argument now in source

* `Storage.DeltaLog.joinU64LowHigh32_correct` exports a proven
  bitvector reconstruction lemma already used to round-trip durable
  DLE1/CEP1 64-bit values.
* `Sbm11U64Lanes.join_split` and `split_eq_iff` connect this to the
  two-word GPU representation without inventing an axiom.
* `Sbm11U64Lanes.fromTermId_eq_iff_eqb` composes that result with
  SBM11 term-ID and canonical RDF equality theorems.
* `joinRows_split_eq` and `bgpLaneModel_eq_bgpSpec` specialize
  reusable GSSL bag-join semantics to lossless 64-bit keys; exact
  ordering and multiplicity are preserved in the pure interpretation.
* `readRecord_recordWords` establishes a six-word triple round trip.

Actual software WebGPU device testing in the PR executes the fixed
BGP count/scan/emit kernels and compares returned rows against an
independent BigInt CPU oracle. A second execution uses the existing
`u32` kernel with a reversible dense dictionary and checks the same
original full-width answers. These are independent tests, not Lean
proofs about the generated WGSL source.

## Trade-offs (per triple, excluding metadata and buffers)

| Layout | Source triple | 2-ID result | Requirement |
|:--|--:|--:|:--|
| direct64-lanes | 24 bytes | 16 bytes | Keep both lanes; same SBM11 generation |
| dense32-snapshot | 12 bytes | 8 bytes | Injective dictionary and exact snapshot |

Performance direction cannot be inferred from widths alone. Direct64
avoids dictionary construction and suits repeated zero-copy reuse of
already coded SBM11 rows, but consumes more GPU bandwidth and generally
needs twice as many 32-bit equality comparisons. Dense32 reduces
transfer and device working set, but pays for remapping and decoding;
it may win on repeated queries or large joins after the conversion is
amortized. Actual device benchmarks must include **encoding, upload,
dispatch, readback and decoding**, and must distinguish hardware GPU
from Mesa software Vulkan.

An experimental test-run's observed times are **not** a general
performance claim; no stable speed threshold or automatic policy
has yet been chosen.

## Still required before the assured Hub lab (#691)

- End-to-end mapping from the *actual SBM11 generation and graph
  snapshot* to these GPU buffers, with checked membership and scope.
- Reviewable proofs that the particular WGSL kernels refine the pure
  lane-count/scan/emit model, including bounds, independent write
  intervals, overflows, and device-loss behavior.
- Snapshot/request identity tied to async GPU output and safe CPU fallback.
- Selection of the GSSL path through the actual shipping SPARQL API,
  rather than only a standalone experimental device harness.
- Differential W3C SPARQL tests, adversarial graph fixtures and
  robust end-to-end GPU performance measurements.

Do not interpret device-test passes as a proof of GPU compiler,
driver or hardware correctness. GSSL does not use an `admit` or
`sorry` to convert an actual device output into a certified result.
