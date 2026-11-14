---
name: aes-hardware-only
description: AES in this repository is only ever HACL*'s verified assembly that uses the CPU's AES instructions, refused where the CPU has none. Never a table-based or other hand-written AES, in any language. The theorems and the build gate that hold this in place, and what they cannot show. Use before touching AES, AES-GCM, AES-CBC, AES-CTR, AES-KW, WebCrypto's AES algorithms, XML Encryption or JWE content encryption, or when a test asks for AES on a platform that refuses it.
---

# AES: the CPU's instructions only, never a table implementation

Part of the crypto policy ([`crypto-policy`](../crypto-policy/SKILL.md): HACL\*, never hand-rolled).
This skill exists because AES is the primitive most often written "quickly, just to pass the test",
and the quick version is the dangerous one.

## 1. Why a do-it-yourself AES is not acceptable

- **The ordinary portable AES leaks the key.** The textbook and reference implementations look up an
  S-box or T-tables at an index that depends on key bytes. Which cache line the lookup touches is
  visible to other code on the machine through timing, and the key has been recovered that way in
  practice. A page script in the same browser is such an observer.
- **That is why HACL\* has no such AES.** HACL\* proves that no branch and no memory address depends on
  a secret. A table AES cannot pass that proof, so the verified library does not contain one.
- **Fast, safe AES uses the CPU.** AES-NI and PCLMULQDQ on x86-64 (the ARMv8 crypto extensions on
  arm64) do the rounds in constant time in hardware. HACL\*'s answer is Vale: verified assembly that
  uses those instructions, for x86-64, chosen at run time by EverCrypt only when the CPU reports them.
- **Lean makes it worse, not better.** Pure Lean on `Nat`, `UInt8` and arrays leaks through
  allocation and the timing of the runtime as well. A correct-looking Lean AES with all its FIPS 197
  vectors passing is still not constant time, and a proof of its functional correctness says nothing
  about that.
- **A portable constant-time AES exists in principle** (bit-slicing: no tables, no CPU instructions,
  slower). Taking one, even a verified one from a later HACL\*, is a change of policy for the owner to
  decide. Writing one here is hand-rolled crypto.

So: where there is no verified hardware AES, AES is **refused** (`NotSupportedError` to a page, a
message that names issue 677 on the command line). Refusing is the safe default and is not a bug to
fix by writing AES. A failing WPT AES subtest on such a platform is the correct outcome.

## 2. What exists

| Where | AES | Notes |
|---|---|---|
| Native x86-64, Linux and macOS | AES-128-GCM and AES-256-GCM: `Crypto/AesGcmNative.lean` over `ffi/hacl_aesgcm.c`, EverCrypt's AEAD, and `third_party/hacl/vale/src/aesgcm-x86_64-*.S` | only when the CPU reports AES-NI, PCLMULQDQ, AVX, SSE and MOVBE |
| Native arm64, the Wasm builds, x86-64 without those instructions | none: refused | the Wasm modules never contain AES code |
| JavaScript hosts (Node, Deno, browsers), for XML Encryption and JWE | the host's own WebCrypto, called through the request-and-resume step | not our code; decided in `crypto-policy`, checked by differential tests |
| Foafnaut's `crypto.subtle` for page scripts | none: every AES algorithm is refused | AES key objects without an AES operation are an open owner decision |

AES-CBC, AES-CTR, AES-KW, AES-OCB and AES-192 have no implementation at all.

## 3. How it is held in place

Three layers. Each covers what the others cannot.

1. **Theorems, in `Crypto/AesGcmNative.lean`** (kernel-checked; axioms `propext` and `Quot.sound` only).
   `available` is the C shim's answer that this build has the Vale assembly and the CPU has the five
   features.
   - `aesGcmEncrypt?_available`, `aesGcmDecrypt?_available`: an AES result exists only when
     `available = true`.
   - `aesGcmEncrypt?_refused`, `aesGcmDecrypt?_refused`: when `available = false` every call is refused.
   - `nativeOps_available`, `nativeOps_encrypt_ok`, `nativeOps_decrypt_ok`: the same for the instance
     that XML Encryption and JWE call.
   These prove that our Lean never produces AES output on a CPU without the instructions. They do not
   prove that the shim's answer is right or what the linked code does: Lean cannot see either.
2. **HACL\*'s own proofs** (trusted, pinned): the Vale assembly is verified against a model of the
   AES-NI instructions, and EverCrypt tests the CPU before calling it. The files are pinned by
   `third_party/hacl/SHA256SUMS` and `PROVENANCE.md`.
3. **The gate `tools/aes-gate.py`** (run on every push by `.github/workflows/check-aes.yml`). It fails when:
   - any tracked file holds the AES S-box, the inverse S-box or a T-table, as numbers in source (hex or
     decimal), as a hex string, or as raw bytes. A table implementation cannot exist without one;
   - a code file names two or more of the round functions of FIPS 197 (SubBytes, ShiftRows,
     MixColumns, AddRoundKey, KeyExpansion). This catches an AES that computes its S-box at run time;
   - an `@[extern]` in Lean that mentions AES is not one of the three in `Crypto/AesGcmNative.lean`, or
     a code file named for AES is not in the gate's list of entry points.
   `python3 tools/aes-gate.py --binary FILE...` runs the table check on built libraries and Wasm
   modules. On 2026-11-14 the engine library and Wasm module of main fbde2abf1 were clean, and
   OpenSSL's library, as a control, was reported.

## 4. What this does not show

- A determined author could hide an AES from the gate. The gate stops the naive and the copied; review
  and the crypto policy cover the rest.
- Nothing here inspects the instructions the linked code runs. That rests on HACL\*.
- The host's WebCrypto on JavaScript hosts is not ours: its vendor chooses hardware or constant-time
  software AES, and we measure it by differential tests only.
- Open: the binary check is not yet a step of the engine and Wasm builds; run it on release candidates
  until it is.

## 5. If you need AES somewhere it is refused

1. Check whether the pinned HACL\* (or a newer release) has a verified implementation for that CPU.
   If it does, propose the pin change and the new extern: both go through the owner (the extern
   baseline is a ratchet).
2. Otherwise leave the refusal, record the subtests it costs, and list it as open.
3. Never: write AES or GCM in Lean, C, JavaScript or assembly; port or transcribe a reference
   implementation; add an AES entry point or an exception in `tools/aes-gate-allow.txt` without the
   owner's decision. Adding to the gate's entry-point list is a change of crypto policy.
