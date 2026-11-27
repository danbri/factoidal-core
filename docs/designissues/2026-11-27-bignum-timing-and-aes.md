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

## 5. HACL\* for big-integer work (owner question, 2026-11-27)

Owner, verbatim: "can we use HACL* for bigint work then?"

- It is already vendored and used: `third_party/hacl/src/Hacl_Bignum64.c` (and `Hacl_Bignum.c`).
  `formal/lean4/ffi/hacl_rsa.c` calls `Hacl_Bignum64_mod_exp_consttime` for the RSA private
  operation and `Hacl_Bignum64_mod_exp_vartime` for the public operation.
- What it gives: fixed-length numbers (the length in 64-bit limbs is public), add, subtract,
  multiply, reduction, Montgomery contexts, modular exponentiation (constant-time and variable-time
  forms) and inversion modulo a prime. Constant time is with respect to the values, not the length.
- What it does not give: a general replacement for Lean `Nat`. It has no arbitrary-length values and
  no general division. For public data, Lean `Nat` stays the right tool.
- Curves: HACL\* has secp256k1 ECDSA (`Hacl_K256_ECDSA`, vendored 2026-11-27, section 7). HACL\*
  has no BLS12-381.
- Ethereum: the owner approved HACL\* for Ethereum the same day (section 7).

## 6. Checking constant time from Lean (owner question, 2026-11-27)

Owner, verbatim: "can we find a way to police these issues with proofs in Lean?"

The standard definition (Barthe et al., Almeida et al., ct-verif, USENIX Security 2016): a program is
constant time when two runs with the same public inputs and any secret inputs produce the same
leakage trace (branch conditions and memory addresses). This is observational noninterference. The
tree already proves noninterference theorems of this form (`PageCanvas/Theorems.lean`,
`Net/Socks5Theorems.lean`). Four layers, from cheap to costly:

1. **Secret types (source level).** A `Secret` wrapper over `UInt64` and `UInt8` (the model is
   HACL\*'s `Lib.IntTypes` with `SEC`). It has no `Decidable` equality, no `toNat`, and comparisons
   that return a mask, not a `Bool`. So the type checker refuses an `if`, a `match` or an array index
   on a secret. Plus a gate that refuses `Nat` and `Int` in modules that take secret inputs.
2. **A leakage model with theorems (Lean semantics).** Write constant-time code in a small monad that
   records each branch condition and address in a trace. For each routine prove: equal public
   inputs give equal traces. This proves the property of the Lean definition.
3. **A check of the compiled code (tests, not proofs).** No Lean theorem covers the machine code,
   because Lean has no verified compiler. On Linux CI: Valgrind memcheck with the secret marked
   undefined (each branch or address that depends on it is reported, Lean runtime included), and a
   statistical timing test (dudect). These run on the HACL\* paths too.
4. **The HACL\* paths.** Their constant-time proof is in F\*/Low\*. The Lean side passes bytes only.
   The equivalence between the externs and the Lean specifications is
   https://github.com/danbri/factoidal/issues/777.

HACL\* has the same limit as layer 2: it trusts the C compiler.

## 7. What landed (2026-11-27)

Owner, verbatim: "Yes, start both" (layers 1 and 3), then "HACL* is both approved and PREFERED over
our own (crazy yolo roll your own etc.) Lean hackery." and, on the secp256k1 signer, "Do it."

Consequence for layer 1: we write no constant-time arithmetic in Lean. A secret is an opaque type
that only HACL\* calls use.

- **secp256k1 over HACL\*.** `third_party/hacl` gains `Hacl_K256_ECDSA.c`, `Hacl_EC_K256.c`,
  `Hacl_HMAC_DRBG.c` and their headers, unchanged, from the pinned commit. `ffi/hacl_k256.c` signs a
  hash with the RFC 6979 nonce (HACL\* HMAC-DRBG, RFC 6979 section 3.3), normalises to low S, and
  takes the recovery id from y(R), with R from HACL\*'s constant-time point multiplication.
  `L4Factoidal/Crypto/K256Native.lean` gives `SecretKey`, `signHash`, `verifyLowS` and the Ethereum
  `v` values.
- **Layer 1.** `SecretKey` has a private constructor and field. `#check_failure` lines fail the
  build if it gets equality, `BEq`, `ToString`, `Repr`, `Hashable` or `Ord`.
  `tools/secret-type-gate.py` checks the same rules from source, with a self-test of five mutants.
- **Layer 3.** `tests/ct/ct_valgrind.c` marks the key undefined and counts memcheck errors in each
  case. Two controls must leak: HACL\* `mod_exp_vartime`, and a textbook square-and-multiply. CI runs
  it with gcc and clang (`.github/workflows/check-k256-ct.yml`).

Measured on macOS arm64 before the push (no Valgrind on that host): `tests/ct/run.sh`, 8 pass, 0
fail; the probe, linked by hand outside Lake, `k256: 13 pass, 0 fail (out of 13)`. Both include the
EIP-155 example (r, s and v = 37 as published). Valgrind results: section 8.

Not done: Ethereum transaction signing in `evm-cleanroom` does not call this yet (that package
imports no FFI); a Valgrind run of Lean-compiled code (the Lean runtime on `Nat`, as a third
control); the wasm build is wired but not built here.

## 8. First Valgrind run: clang x86-64 breaks HACL\* `mod_exp_consttime`

CI run https://github.com/danbri/factoidal-core/actions/runs/45930142123 (Ubuntu x86-64), memcheck
errors with the secret marked undefined:

| Case | gcc -O2 | clang -O2 |
|---|---|---|
| secp256k1 sign, EIP-155 key secret | 0 | 0 |
| secp256k1 `secret_to_public` | 0 | 0 |
| HACL\* `Hacl_Bignum64_mod_exp_consttime` | 0 | **316** |
| control: HACL\* `mod_exp_vartime` (must leak) | 2,176 | 192 |
| control: textbook square-and-multiply (must leak) | 106 | 129 |

All 316 errors are at `Hacl_Bignum.c:1322`, the mask select `(m & tmp[i]) | (~m & res[i])` at the end
of `Hacl_Bignum_AlmostMontgomery_bn_almost_mont_reduction_u64`. clang's x86-64 output has
`testq %r8, %r8; je` in that loop, `%r8` being the reduction carry: a jump on whether the extra
reduction happens. The RSA private operation (`Crypto/RsaOaep.lean`) calls this function. Apple
clang 17 for arm64 compiles the same function with `cmeq` and `csel` and no branch (assembly read
for this one function only). Issue, exposure and options:
https://github.com/danbri/factoidal-core/issues/1200 (clang x86-64 branch in HACL\*
`mod_exp_consttime`). The harness records it as an expected failure that turns the run red if the
leak disappears.

This is the case of section 1 item 4 (the compiler can turn branch-free code into a branch),
measured. It is why layer 3 runs on compiled code, with each compiler that builds HACL\*.

**Error in our method, 2026-11-27.** The first workflow piped each Valgrind step into `tee` with no
`pipefail`, so the job was green although the clang step printed `FAIL ct_valgrind: 1 failures`.
Found by reading the log, not from the status. Repair: the job's shell has `-euo pipefail`. Rule:
a CI step that pipes into `tee` sets `pipefail` (`shell: bash` does; the default shell does not).
