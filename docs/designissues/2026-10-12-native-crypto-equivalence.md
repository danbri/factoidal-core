# Native crypto externs and the Lean specifications: options for an equivalence statement

Tracking: https://github.com/danbri/factoidal/issues/777.
Owner request, 2026-10-12, verbatim: "web research subagent #777".
Status: research record and recommendation. No code changed with this note.
All web sources were read on 2026-10-12.

## The problem

1. The Lean tree calls five HACL\* C functions through `@[extern]` over `opaque`:
   `sha256Hacl`, `sha256BlocksHacl` (`L4Factoidal/Crypto/SHA2Native.lean`) and
   `secretToPublic`, `sign`, `verify` (`L4Factoidal/Crypto/Ed25519.lean`).
2. An `opaque` constant has a type and no usable value in the kernel, so no Lean
   theorem can relate `sha256Hacl` to the pure `Crypto.sha256`.
3. Agreement is measured only: `lake exe l4vc-probe` and
   `lake exe l4native-crypto-smoke` (FIPS 180-4 and RFC 8032 vectors, block and
   padding boundaries, a 1 MiB buffer).
4. There is no Lean Ed25519 specification, so for Ed25519 there is not even a
   statement to measure against except the RFC 8032 vectors.
5. The expected-failure case NX-1 in `tests/known-defects/run.sh` stays XFAIL
   until a declaration named `sha256Hacl_eq_sha256` exists. Ed25519 has no
   corresponding case.

## What no option changes

Every option below still trusts these, because no available tool checks
compiled C from Lean:

- the HACL\* proofs (F\*, Z3, Low\*) and the KaRaMeL extraction, vendored
  unmodified from `cryspen/hacl-packages` `05c3d8fb`
  (`third_party/hacl/PROVENANCE.md`). HACL\* states its code is "verified for
  memory safety, functional correctness, and secret independence"
  (https://github.com/hacl-star/hacl-star). Functional correctness is relative
  to its own F\* specifications: `specs/Spec.SHA2.fst`, `Spec.Hash.Definitions.fst`,
  `Spec.Ed25519.fst`, `Spec.Ed25519.PointOps.fst`, `Spec.Curve25519.fst`
  (https://github.com/hacl-star/hacl-star/tree/main/specs);
- the C compiler (native) and the C-to-wasm toolchain;
- the shims in `formal/lean4/ffi/` (length checks and `lean_sarray` plumbing);
- the Lean C FFI convention. The Lean reference says of the interface: "The
  current interface was designed for internal use in Lean and should be
  considered unstable"
  (https://lean-lang.org/doc/reference/latest/Run-Time-Code/Foreign-Function-Interface/).

The options differ in two things: where the remaining assumption is written,
and whether the two specifications (HACL\*'s F\* one and ours in Lean) are
related by proof or by review.

## Lean mechanisms that matter

- `@[extern "sym"]` "causes compiled code to use the C declaration `sym` as the
  implementation" (Lean reference, section 12.4.1, URL above). It can be put on
  a `def` that HAS a body. The kernel then uses the body; compiled code calls
  the C symbol. Lean core does this for its own primitives (for example
  `Nat.add` with `lean_nat_add`).
- The reference, section "Validating a Lean Proof"
  (https://lean-lang.org/doc/reference/latest/ValidatingProofs/), says
  native evaluation "depends on the correctness of the Lean compiler and all
  definitions with an `@[implemented_by]` attribute", and that "for every
  `implemented_by`/`extern` attribute in libraries it becomes part of the
  trusted code base". An `@[extern]` attribute is therefore trusted code, and
  `#print axioms` does NOT report it. (The same page says "The
  `Lean.trustCompiler` machinery was removed from Lean in version 4.35.0"; this
  tree pins `leanprover/lean4:v4.33.1`. Neither version reports extern
  attributes in `#print axioms`.)
- `#print axioms` "prints the set of axioms used by the theorem and the
  theorems it depends on" (same page). A user `axiom` IS reported. The tree's
  policy (`skills/factoidal-lean-basics/SKILL.md`, Proof policy) is "No `sorry`.
  No user `axiom`. No `native_decide`".
- "it is not possible to interpret an `extern` declaration in the same file"
  (FFI reference, section 12.4.3). This is why the FIPS vectors on
  `Crypto.sha256` are `#guard`s and the HACL\* comparison is a run-time probe.

## Related work found

| Project | What it proves | Tool chain | Relevance here |
|---|---|---|---|
| sha2-fv 0.1.0 (2026-10-09), fork of RustCrypto `sha2` (https://docs.rs/sha2-fv, repository https://github.com/remix7531/hashes-fv) | "The Aeneas-extracted entry point returns the FIPS 180-4 digest for any input under 2^61 bytes" (`sha256_spec`). Pinned axioms: `{propext, Classical.choice, Quot.sound, Aeneas.Std.core.fmt.Formatter}` | Rust, Charon, Aeneas, Lean 4; spec "fips-180-4-lean" (https://remix7531.com/fips-180-4-lean) | A second, independent Lean FIPS 180-4 specification. A proof that it equals `Crypto.sha256` would cross-check our spec. Its code is Rust, not HACL\* C. |
| curve25519-dalek-lean-verify (https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify; stats page https://beneficial-ai-foundation.github.io/curve25519-dalek-lean-verify/stats: 191 verified, 191 specified, 194 total functions) | Function-level specifications of the Rust `curve25519-dalek` crate; folders `Math/Edwards`, `Math/Montgomery`, `Math/Ristretto` | Aeneas, Lean 4; requires `aeneas` (which requires Mathlib) and `PrimeCert` | The only Lean 4 Edwards-curve material found. It covers curve and field operations, not Ed25519 signing as specified in RFC 8032. Not checked in detail. |
| SymCrypt Rust ML-KEM and SHA-3 (Ho et al., "Scaling Verification of Cryptographic Software with Aeneas, Rust, and Lean", https://arxiv.org/abs/2609.15648, 2026-09-14; Microsoft Research blog, 2026-07-13, https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/) | Functional correctness of Rust code against Lean specifications; the blog says "the Lean specification is designed to stay close to the standard" and "we can run the formal model against official test vectors to catch transcription errors" | Aeneas, Lean 4 | The method: a Lean spec written from the standard, checked against official vectors, then a refinement proof. No SHA-2 or Ed25519. |
| hax (https://github.com/cryspen/hax; Lean manual https://hax.cryspen.com/manual/lean/) | Translates Rust to F\* ("Stable"), Rocq, SSProve, ProVerif, EasyCrypt ("Experimental"), and to Lean "via Aeneas" ("Recommended for Lean") | Rust only | Does not read F\* or C, so it cannot carry HACL\*'s F\* specs to Lean. |
| hacspec (RWC 2023 slides https://iacr.org/submit/files/slides/2023/rwc/rwc2023/124/slides.pdf) | Executable specs in a Rust subset, compiled to F\*, Coq, EasyCrypt | hacspec, now continued in hax | No Lean target found. No published translation of `Spec.SHA2` or `Spec.Ed25519` to Lean found. |
| libcrux (https://docs.rs/libcrux-ed25519) | Rust "compiled from verified C originating in the HACL\* project" (libcrux-ecdh docs) | HACL\* C to safe Rust | A Rust form of the same HACL\* code. In principle Aeneas could take it to Lean; nobody has published that. |
| Fiat-Crypto, Edwards group law | Coq-generated field arithmetic (BoringSSL `third_party/fiat`); Edwards group law in Isabelle/HOL (Hales and Raya, https://isa-afp.org/entries/Edwards_Elliptic_Curves_Group.html) | Coq, Isabelle | No Lean 4 port found. Mathlib has the Weierstrass group law (Angdinata and Xu, https://arxiv.org/abs/2302.10640), not the Edwards form. |

Search method and its reach (anti-pattern 28): web searches and direct reads of
the pages listed; GitHub API access to third-party repositories was refused in
this session, so repository contents were read through rendered pages only.
"Not found" above means not found by this method.

## Options

### Option A: one axiom per extern, citing the HACL\* theorem

Statement, for example:
`axiom sha256Hacl_eq_sha256 (m : ByteArray) (h : m.size < 2^32) : sha256Hacl m = Crypto.sha256 m`.
The hypothesis is required: the shim refuses longer input with the empty array,
so an axiom without it is false about the compiled program (it stays
consistent in the kernel, because the `opaque` has no unfoldable value).

- Proves: nothing new. It records the assumption in a form `#print axioms`
  reports on every theorem that uses it.
- Trusted base: as above, plus the claim that HACL\*'s `Spec.SHA2` and
  `Crypto.sha256` denote the same function (by review and vectors).
- Effort: hours for SHA-256 (two axioms). For Ed25519 it needs a Lean
  specification first (option D).
- Prerequisite: an owner decision, because the tree's policy is "No user
  `axiom`".
- NX-1: turns XPASS (the probe matches `axiom`). Retire NX-1 and update issue
  777 in the same commit.

### Option B: `def` with `@[extern]` whose body is the specification

Replace `opaque sha256Hacl` by a `def` with the same `@[extern
"l4_hacl_sha256"]` attribute and the body
`if m.size < 2^32 then Crypto.sha256 m else ByteArray.empty`. Do the same for
`sha256BlocksHacl` with a body over `Crypto.processBlocks256At`, its refusal
conditions and the big-endian state encoding the header already describes.
Then `theorem sha256Hacl_eq_sha256 (m) (h : m.size < 2^32) : sha256Hacl m =
Crypto.sha256 m` is proved by unfolding.

- Proves: in the kernel, the extern's meaning IS the specification; every
  theorem about consumers (`BlockMerkle`'s `Hasher`) can be stated once over
  `sha256Hacl` and holds by the specification.
- Trusted base: as above. The assumption moves into the `@[extern]` attribute
  ("becomes part of the trusted code base", Lean reference), where
  `#print axioms` does not show it. It must therefore be written in the module
  header and in the theorem registry's trust-surface table.
- Effort: about one day for the two SHA-256 externs, most of it on the
  `sha256BlocksHacl` body and its proof. Probes stay as they are.
- Prerequisite: none for SHA-256. For Ed25519, option D first.
- NX-1: turns XPASS by a theorem. The probe also reports ERROR "probe drifted"
  once `opaque sha256Hacl` is gone, so the same commit retires NX-1, updates
  issue 777 and edits the registry.

### Option C: spec-to-spec proof against HACL\*'s F\* specification

Transcribe `Spec.SHA2` / `Spec.Hash.Definitions` (and later `Spec.Ed25519`)
into Lean, as close to the F\* text as possible, and prove the transcription
equal to `Crypto.sha256`.

- Proves: that our Lean specification and a Lean copy of HACL\*'s
  specification are the same function. That closes the gap between "HACL\*
  meets `Spec.SHA2`" and "our theorems are about `Crypto.sha256`", except for
  the faithfulness of the transcription, which stays a review item. No tool
  that translates F\* specifications to Lean was found.
- Trusted base: as above, minus the informal "both match FIPS 180-4" step.
- Effort: one to two weeks for SHA-2; several weeks for Ed25519 (field, point
  operations, encoding, SHA-512 use).
- Prerequisite: for Ed25519, a Lean Ed25519 specification (option D).
- NX-1: no direct effect. It strengthens the meaning of an option A axiom or
  an option B attribute.
- Variant: prove `Crypto.sha256` equal to the fips-180-4-lean specification
  used by sha2-fv. That is a cross-check against an independent Lean
  transcription of the standard, with a smaller effort if its licence and
  Lean version allow import. It does not involve HACL\*.

### Option D: a Lean Ed25519 specification

An executable, `Nat`-arithmetic specification of RFC 8032 section 5.1 (key
generation, signing, verification), over the existing pure `Crypto.sha512`,
with the RFC 8032 section 7.1 vectors as build-time `#guard`s. It is never on
the compiled path when used with option B.

- Proves: gives Ed25519 a meaning in the kernel, so `VC/Theorems.lean` can
  state signature correctness about a function instead of taking it as a
  hypothesis, and options A to C become possible for the three Ed25519 externs.
- Trusted base: the transcription of RFC 8032 (review plus vectors).
- Effort: about a week for the executable specification and vectors. A proof
  of the group law is a separate and larger task; Mathlib does not have the
  Edwards form, and this tree has no Mathlib dependency.
- Prerequisite: 🧭 an owner ruling. `skills/crypto-policy/SKILL.md` item 2
  says for signatures: "HACL\* via Lean FFI ONLY ... Never a hand-written Lean
  implementation." A specification that the compiled program never runs is a
  different artifact, but the policy text does not say so.
- NX-1: none. Add an expected-failure case NX-2 for "Ed25519 externs have no
  Lean specification" (the stated-shortfall rule requires one; today only the
  module header records it).

### Option E: stronger differential measurement

Add to `l4vc-probe` or `l4native-crypto-smoke`:

- Wycheproof `testvectors_v1/ed25519_test.json` (151 `EddsaVerify` cases,
  read 2026-10-12 from https://github.com/C2SP/wycheproof). The project states
  it is "a community managed repository of test vectors that can be used by
  cryptography library developers to test against known attacks". The
  submodule `third_party/testing/wycheproof` is registered in `.gitmodules` but
  is not checked out in a fresh worktree (`tools/ensure-test-env.sh`).
- The `ed25519-speccheck` vectors (https://github.com/jedisct1/ed25519-speccheck)
  from Chalkias, Garillot and Nikolaenko, "Taming the many EdDSAs"
  (https://eprint.iacr.org/2020/1244): small-order points, non-canonical
  encodings, `S` at or above the group order, cofactored and cofactorless
  verification. Record HACL\*'s answer for each case as the expected value.
- Wycheproof has no plain SHA-256 file; `hmac_sha256_test.json` (174 cases)
  exercises SHA-256 through HMAC, and the tree has HMAC both in pure Lean
  (`Crypto/Hmac.lean`) and through HACL\* (`Crypto/Hkdf.lean`).
- NIST SHAVS byte-oriented vectors: "The Short Messages Test", "The Selected
  Long Messages Test" and "The Pseudorandomly Generated Messages (Monte Carlo)
  Test" (SHAVS, https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/SHAVS.pdf).
- A seeded random differential (lengths 0 to a few block sizes, and random
  chunkings for `sha256BlocksHacl`).

- Proves: nothing; it widens the measured input set.
- Trusted base: unchanged.
- Effort: two to three days.
- Prerequisite: none.
- NX-1: stays XFAIL.

### Option F: replace HACL\* C with Rust verified in Lean (Aeneas or hax)

Use sha2-fv for SHA-256 and, later, a verified Ed25519 over
curve25519-dalek-lean-verify.

- Proves: a kernel-checked theorem from the Aeneas model of the Rust code to a
  Lean FIPS 180-4 specification.
- Trusted base: Charon, Aeneas and rustc instead of KaRaMeL and F\*; the model
  is still not the compiled binary.
- Effort: weeks, plus a Rust toolchain in the native and wasm builds and a
  Mathlib dependency (Aeneas's Lean library requires `mathlib`, per its
  `backends/lean/lakefile.lean`).
- Prerequisite: an owner decision to change the crypto policy ("adopt HACL\*")
  and the dependency rules.
- NX-1: XPASS only if a bridging theorem to `Crypto.sha256` is also proved.

## Summary

| Option | Kernel statement added | Trust that remains outside `#print axioms` | Effort | Owner decision |
|---|---|---|---|---|
| A axiom per extern | assumed equality | HACL\* chain, shim, FFI | hours | yes (no-axiom policy) |
| B `def` + `@[extern]` | proved equality to the spec | HACL\* chain, shim, FFI, the extern attribute | about 1 day (SHA-256) | no |
| C spec-to-spec | Lean copy of `Spec.SHA2` = `Crypto.sha256` | transcription review | 1-2 weeks (SHA-2) | no |
| D Lean Ed25519 spec | Ed25519 gets a meaning | RFC transcription review | about 1 week | yes (crypto policy item 2) |
| E more vectors | none | unchanged | 2-3 days | no |
| F Rust via Aeneas | refinement of a Rust model | Charon, Aeneas, rustc | weeks | yes (policy, Mathlib) |

## Recommendation

1. Option B for `sha256Hacl` and `sha256BlocksHacl`. First step: change
   `opaque sha256Hacl` in `SHA2Native.lean` to
   `@[extern "l4_hacl_sha256"] def sha256Hacl (m : @& ByteArray) : ByteArray :=
   if m.size < 2^32 then Crypto.sha256 m else ByteArray.empty`, prove
   `sha256Hacl_eq_sha256`, rewrite the module's trust statement (the extern
   attribute is now the trusted item), retire NX-1, edit the registry's
   trust-surface row, and keep both probes. One commit.
2. Option E in parallel: Wycheproof Ed25519 and HMAC-SHA-256, the speccheck
   cases, SHAVS, and a seeded random differential. This is the only
   strengthening available today for the Ed25519 externs.
3. 🧭 Ask the owner one question: may the Lean tree hold an Ed25519
   SPECIFICATION (never compiled into the executable path) under crypto-policy
   item 2? If yes, option D, then option B for the three Ed25519 externs, and
   add NX-2 now so the shortfall is a failing test.
4. Option C later, and first in its cheaper variant (cross-check
   `Crypto.sha256` against the fips-180-4-lean specification), when a second
   specification of SHA-2 is useful to the registry.
5. Option A only if the owner prefers `#print axioms` visibility to the
   no-axiom rule. Option F is not recommended while the policy is "adopt
   HACL\*"; watch sha2-fv and curve25519-dalek-lean-verify for reusable Lean
   specifications.

## Theorem registry

`docs/theorem-registry.md`, section "Trust surface added by this section",
row "SHA-256, Ed25519 (FIPS 180-4, RFC 8032) | HACL\*, Project Everest |
`lake exe l4vc-probe` (119 pass, 0 fail)", and the "Not proved" row "that
HACL\* computes what its specification says". Under option B, split the row:
SHA-256 gets a proved entry (`sha256Hacl_eq_sha256`) and a trust entry for the
`@[extern]` attribute; Ed25519 keeps the measured entry until option D. Under
option A, add the axiom to the trust surface by name. Option E changes only
the measured counts.
