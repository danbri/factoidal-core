# Ethereum wallet: signing, what is checked at run time, and timing leaks

2026-11-27. Record for `formal/lean4/ethereum-wallet` (modules `Sign*`, `Tx*`),
part of the independent Ethereum implementation
([issue 725](https://github.com/danbri/factoidal-core/issues/725)).
The package builds and signs transactions. It has no network code and sends
nothing anywhere.

## What the code does

- **Transactions** (`Tx.lean`): one `Unsigned` record for kinds 0 (legacy, with
  or without EIP-155), 1 (EIP-2930), 2 (EIP-1559), 3 (EIP-4844, without sidecar)
  and 4 (EIP-7702); the wallet's own RLP encoder; the exact signing payload and
  its Keccak-256; the signed envelope; the EIP-7702 authorization hash.
- **Signing** (`Sign.lean`, `SignRfc6979.lean`, `SignSecp.lean`): ECDSA on
  secp256k1 with RFC 6979 nonces (HMAC-SHA-256 from `L4Factoidal.Crypto`), EIP-2
  low `s`, and the one-bit recovery id.
- **Point arithmetic** is the shared `EVMCleanroom/Precompiles/Secp256k1.lean`
  (with `Curve`, `Field`, `Basic`), owned by the precompile work. The wallet
  adds no second implementation of point addition: only a table-driven way of
  walking the same `Curve.add` for a secret scalar.

## Decision: check every output before returning it

Two results are checked at run time, and the theorems rest on those checks:

1. **Every signature is recovered before it is returned.** `signHash` runs
   `Secp256k1.recover` on its own output and returns it only if the result is
   the signer's public key and `r`, `s`, `yParity` are in range with `s ≤ n/2`.
2. **Every raw transaction is decoded before it is returned.** `signTransaction`
   decodes its own output with the independent decoder and returns it only if the
   fields, the signature and the signing bytes all come back unchanged.

Why: a proof that the Jacobian formulas implement the group law, or that the
RLP encoder and the admission decoder are inverse for all inputs, is a large
piece of work that does not exist yet. The checks give statements that are
true for all inputs today, at a known price (one recovery, about three
quarters of the signing time; the decode is under 0.1 ms). The recovery check
is also the standard guard against a fault during signing: a wrong signature
made with a correct nonce can reveal the key, and here it is never returned.

What the checks do not give is completeness. That a valid transaction is
never refused is tested (below), not proved.

## Proved, tested, open

Proved (Lean theorems; axioms `propext`, `Quot.sound`, `Classical.choice`):

| Theorem | Says |
|---|---|
| `Sign.signHash_sound` | a returned signature has `r ∈ [1, n-1]`, `s ∈ [1, n/2]`, `yParity ∈ {0, 1}`, and the shared recovery gives the public key held in the key pair (that this key is `[secret]G` is tested, not proved) |
| `Sign.signHash_recovers_address` | the recovered address is the signer's address |
| `Sign.signHash_nonce_range`, `Rfc6979.search_range`, `Rfc6979.nonce_range` | the signature was produced by the ECDSA attempt on some `k ∈ [1, n-1]`; a nonce returned by `nonce` is in `[1, n-1]`. That `k` is the RFC 6979 value is tested against vectors, not carried by the theorem |
| `Sign.normalizeS_low` | EIP-2 normalisation maps `[1, n-1]` into `[1, n/2]` |
| `Sign.signHash_zero_hash`, `signHash_hash_length`, `signHash_invalid_key`, `ofSecret_invalid` | the defined refusals |
| `Sign.ofSecret_valid`, `Secp.mulBaseSecret_onCurve` | a public key made here is on the curve, its scalar in range |
| `TxSign.roundTrip_legacy`, `roundTrip_eip2930`, `roundTrip_eip1559`, `roundTrip_eip4844` | `SignedTransaction.decode` (the existing decoder of the EVM work) accepts the returned bytes and gives back the transaction, the signature and the signing payload |
| `TxSign.roundTrip_eip7702` | the same for kind 4 with the wallet's set-code reader (see below) |
| `TxSign.signTransaction_sound`, `signTransaction_sender`, `signTransaction_invalid`, `signAuthorization_sound` | the above combined for the two entry points |

Tested, not proved:

- that signing and encoding succeed on valid input, and produce the right
  bytes: the EIP-155 specification example; the 12,885 distinct signed
  transactions of the execution-specs `tests@v21.0.3` Prague state tests
  (fields and published test key in, `txbytes` out: 12,869 reproduced byte for
  byte, the other 16 are transactions the fixtures mark invalid and the wallet
  refuses to build), 500 of them committed; EthereumJS as an oracle on random
  transactions with fresh keys in CI;
- RFC 6979 nonces and signatures: the bitcoinjs-lib fixture (7 signatures,
  30 nonce candidates including the 2nd and 16th of the sequence) and
  RFC 6979 appendix A.2.5 (2 nonces for the P-256 order);
- verification edge cases: Wycheproof `ecdsa_secp256k1_sha256_p1363` (252 tests);
- the comb multiplication against the shared double-and-add;
- agreement of the shared recovery with the affine `SecpRecovery` used by
  transaction admission (a sample in each vector run);
- negative controls throughout: a changed hash, `s`, key, field or byte must
  change or invalidate the result.

Open:

- No group law, no primality, no ECDSA correctness proof. The theorems are
  about the functions in this repository, not about the mathematical curve.
- Keccak-256 and SHA-256 are tested against vectors, not proved.
- Kind 4 has no independently written decoder in the repository yet.
  `TxDecode.decodeSetCode` uses the canonical RLP reader and field helpers of
  the admission decoder, but its field layout was written with the encoder, so
  the kind 4 round trip is weaker evidence than kinds 0 to 3. It should be
  replaced by the admission decoder's kind 4 case when that exists.
- Completeness of encoding (a valid transaction is never refused) is not proved.
- Limits: the admission decoder's local caps apply to what the wallet will
  emit (16 MiB raw, its access list caps), and 8,192 authorizations.
  Chain ids are below 2^64, nonces below 2^64 − 1 (EIP-2681).
- `validate` does not yet refuse a chain id of zero or more blob hashes than a
  fork allows, and an authorization with chain id 0 (valid on every chain) is
  signed without a separate opt-in. The JSON tool refuses a missing chain id
  (only an explicit `null` on a legacy transaction gives the replayable
  pre-EIP-155 form), conflicting field aliases and fee fields of another kind.
- The encoders (`signingPayload`, `signedRaw`, `authorizationPayload`) are
  meant for validated input; called directly with out-of-range values they
  wrap (kind byte, fixed-width fields). `signTransaction` and
  `signAuthorization` check first.

## Timing: what is and is not constant-time

**Signing here is not constant-time and must not be treated as side-channel
resistant.** Field elements and scalars are Lean `Nat`, which is GMP's
arbitrary-precision integer above 63 bits and an unboxed machine word below.

What was done to reduce the leak:

- **No secret-dependent schedule in the scalar multiplication.** `[k]G` is 64
  additions of entries of a precomputed table (4-bit comb) to a fixed public
  starting point, whatever `k` is. There is no doubling chain, no branch on a
  bit of `k`, and no dependence on the bit length of `k` in the wallet's code.
  The digits are recoded (the scalar is shifted by a public constant) so that
  no selected entry is the point at infinity. The starting point `[2^255]G`
  is there because of a review finding: without it the running sum equalled
  the next entry for about one scalar in 240 (low byte of the recoded scalar
  `0x0F`, and similar patterns), the shared `add` then took its doubling
  branch, and timing would have shown those low bits. With it the two can
  coincide only when the digits consumed so far equal one exact number of
  about 250 bits. The textbook double-and-add of the shared module, which
  is right for public data, would leak the bit pattern and length of the nonce
  directly; a few leaked nonce bits per signature are enough to recover a key
  with lattice methods, which is why this was the first thing to remove.
- **Inverses by a fixed public exponent** (Fermat) for `k⁻¹ mod n` and for the
  conversion to affine coordinates, not Euclid's algorithm, whose number of
  steps depends on the secret operand.
- **RFC 6979 nonces**: no dependence on a random source at signing time.
- **The self-check** stops a faulted signature from leaving.
- A key pair has no `Repr` instance and the tool never prints a key.

What still leaks:

| Leak | Where | Note |
|---|---|---|
| Operand-dependent time of multiplication and reduction | every `a * b % p` on `Nat` (GMP) | division time depends on the values; a value with leading zero limbs is shorter and faster |
| Small-value representation | Lean runtime | a `Nat` below 2^63 is a tagged word, not a GMP number: other code path, no allocation |
| Allocation pattern | every `Nat` result | sizes and counts of allocations follow the values |
| Secret-indexed table lookup | `mulBaseComb` | cache timing reveals digits of the recoded nonce to an attacker sharing the cache |
| Special-case branches | shared `Curve.add` (equal points, inverse points, infinity) | with the public starting point, reached only for exact values of the scalar (probability about 2⁻²⁴⁸), but the code is not branch-free |
| Low-`s` branch | `normalizeS` | whether `s` was replaced by `n − s` (one bit about the nonce's sign) is taken as a branch; the output does not show it |
| Rare-case branches | `attempt` (`R.x ≥ n`, `r = 0`, `s = 0`), `Rfc6979.search` (range test) | negligible probability each |
| Digit extraction | `(k >>> 4i) % 16` on a GMP number | value- and length-dependent like the other `Nat` operations |
| The key on the command line | `eth-wallet-sign --test-key-hex` | visible in the process list and shell history: test keys only |
| Reduction of the key and hash | `(z + r·d) % n`, `natToBE` of the key for HMAC | value-dependent |
| HMAC-SHA-256 | `L4Factoidal.Crypto` | `UInt32` arithmetic with no secret-dependent branch in the source; not examined at the level of generated code |
| Memory | everywhere | secrets are not wiped; Lean values are immutable and freed by reference counting |

So: against an attacker who can time many signatures precisely, or who shares
a processor cache with the signer, this code should be assumed to leak. It is
suitable for test keys and for development of the rest of the wallet. A key
that holds funds must not be used with it. The risk is carried in the types:
`signHash`, `signTransaction` and `signAuthorization` take a
`Risk.Accepted .variableTimeSigning`, which only `Risk.dangerouslyAccept` makes
(skills/lean-risk-flags), and the `eth-wallet-sign` tool calls it only under
`--dangerously-enable-variable-time-signing`, with a warning.

Acceptances of the risk in this change (each needs the owner's confirmation
before it is relied on beyond tests): `EthereumWallet/SignTests.lean`
(published test keys) and `SignMain.lean` (the command-line flag).

The route to a constant-time signer, in order of value: fixed-width limb
arithmetic on `UInt64` with complete addition formulas and constant-time
table selection (no `Nat` on the secret path), proved equal to the `Nat`
specification used today, which then stays as the readable reference; or
signing in a separate verified component reached through the host. That choice
is the owner's.

## Performance

Measured on the shared Mac under load, 100 runs each (the CI run records the
Linux numbers in `bench-sign.json`):

| | p50 | p95 | max |
|---|---|---|---|
| Before: signature using the affine scalar multiplication of `SecpRecovery` (what the tree had) | 46.5 ms | 48.7 ms | 49.3 ms |
| Before: signature using the shared Jacobian double-and-add | 2.8 ms | 2.9 ms | 3.0 ms |
| After: `signTransaction`, kind 2, everything included | 4.2 ms | 4.3 ms | 4.4 ms |

Parts of the 4.2 ms: recovery self-check about 3.1 ms, comb multiplication
0.62 ms, inverse 0.15 ms, RFC 6979 0.13 ms, encode and decode back 0.06 ms.
The self-check is a shared double-and-add over public data; it gets faster
when the shared field arithmetic does. The table (1,024 points and the
starting point) takes about 7 ms to build, once, by whoever signs; a program
that never signs does not build it.
