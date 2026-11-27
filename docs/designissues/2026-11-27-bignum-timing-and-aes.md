# Lean big integers, timing, and the relation to the AES rule

Date: 2026-11-27. Written after the owner asked to expand the statement "Lean's big integers
(GMP-backed) don't run in constant time, so signing could leak key material through timing" and
asked whether it is related to the AES refusal on CPUs with no AES instructions.

Kind: explanation. It adds no rule. The rules are in
[`skills/crypto-policy`](../../skills/crypto-policy/SKILL.md) and
[`skills/aes-hardware-only`](../../skills/aes-hardware-only/SKILL.md).

## 1. The statement is correct

Lean's `Nat` and `Int` have two forms. A value below 2^63 is a scalar in the pointer word. A larger
value is a heap object; on native builds its arithmetic calls GMP's `mpz_*` functions; the wasm
builds are GMP-free and use Lean's own big-number code. Both forms leak the values through time:

1. **Size follows the value.** `mpz` strips high zero limbs. An intermediate with leading zero bits
   is shorter, and every later operation on it is faster.
2. **The algorithms branch on the data.** `mpz_powm` uses a sliding window over the exponent bits;
   division and reduction take a different number of correction steps for different inputs. GMP's
   constant-time functions (`mpz_powm_sec`, `mpn_sec_*`) exist, but Lean's `Nat` does not call them.
3. **The runtime branches on the data.** Each operation checks the scalar or heap form, allocates a
   new object of a size that depends on the result, and changes reference counts. The allocator's
   time depends on that size.
4. **The compiler promises nothing.** Lean's compiler, and the C compiler after it, can turn a
   branch-free expression into a branch. A proof of functional correctness says nothing about time.
   `Crypto/RsaOaep.lean` states this limit in its module comment.

## 2. Why signing, and not verification

A timing leak is a risk only when the input is secret. In signing, the private key is secret (RSA
`d`, `p`, `q`; the ECDSA and BLS scalar), and in ECDSA the per-signature nonce `k` is secret too.

- RSA: a variable-time modular exponentiation with `d` gives the exponent bits. Kocher (1996) showed
  the method; Brumley and Boneh (2003) did it over a network against OpenSSL.
- ECDSA: a leak of a few bits of `k` per signature is sufficient. Over many signatures a lattice
  computation (the hidden number problem) gives the key. Published cases: Minerva and TPM-Fail
  (2019), LadderLeak (2020).

Verification uses only the public key, the message and the signature. All are public by the
protocol, so a variable-time pure Lean verifier leaks nothing secret. This is the test of
`skills/crypto-policy`: "is the input non-secret by the definition of the protocol, in every
deployment?" The pure Lean Ethereum BLS and G2 modules
(`docs/20261124-ethereum-g2-admission.md`, `docs/20261125-ethereum-bls-hash-field.md`) are in that
case: public verification only, no signer, and each record says "no constant-time claim".

## 3. Relation to the AES rule

Same class of defect (a secret-dependent time or memory address seen by another program), different
cause, different fix.

| | AES | Big-integer signing |
|---|---|---|
| Where the leak is | the usual software algorithm: S-box or T-table lookups at an index that depends on key bytes; the cache line is visible through timing | the arithmetic library and the runtime: value-dependent lengths, branches, allocation |
| Does a CPU instruction remove it | yes: AES-NI (x86-64), the ARMv8 crypto extensions | no: no CPU instruction makes `mpz` or Lean's `Nat` constant time |
| Portable fix | bit-sliced AES (no tables, slower) | fixed-width limb arithmetic with no secret-dependent branch or address: Montgomery multiplication, a fixed-window or ladder exponentiation, constant-time selection; for curves, complete formulas and a ladder |
| Our choice | HACL\* Vale assembly when the CPU reports AES-NI; refusal elsewhere | HACL\* (verified secret independence) for every operation on a private key: `Crypto/RsaOaep.lean` (RSA private operation), `Crypto/P256Native.lean`, Ed25519 in `ffi/hacl_ed25519.c` |

What the two cases share:

- A Lean proof of correctness does not show constant time, in either case.
- Pure Lean is worse than C for this, because the runtime adds allocation and representation
  changes that C code does not have.
- The fix in both cases is code whose secret independence is proved at the code level (HACL\*'s
  Low\* discipline: no branch and no memory address depends on a secret), or a refusal.

The emulator concern of https://github.com/danbri/factoidal/issues/1305 (AES on an emulated CPU) is
specific to AES: CPUID reports AES-NI, but the emulator can run the instruction in software, maybe
with tables. The big-integer case has no such trap, because it never relied on a CPU instruction.
Both cases share the general limit that a wasm engine or an emulator gives no constant-time
guarantee for the code it runs.

## 4. What this means for new work

- A new signer, key agreement or decryption in this repository uses a HACL\* operation, or it is a
  flagged risk under [`skills/lean-risk-flags`](../../skills/lean-risk-flags/SKILL.md) and refused by
  default.
- A pure Lean implementation of the same operation is acceptable as the specification and as a
  differential oracle, never as the run-time path for secret data.
- A pure Lean Ethereum signer (secp256k1 ECDSA or BLS) would fall under this rule. No such signer
  exists today.
