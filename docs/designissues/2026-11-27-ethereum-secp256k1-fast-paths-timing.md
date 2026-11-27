# secp256k1 fast paths: what depends on the data in time, and why they are for public data only

Date: 2026-11-27. Record for `formal/lean4/evm-cleanroom/EVMCleanroom/Precompiles/`
`Secp256k1Fast.lean`, `Secp256k1FieldFast.lean` and `ScalarMul.lean`, part of the independent
Ethereum implementation ([issue 725](https://github.com/danbri/factoidal-core/issues/725)).

Kind: explanation and a warning. It adds no rule. The rules are in
[`skills/crypto-policy`](../../skills/crypto-policy/SKILL.md) and in `CLAUDE.md`
("HACL\* is preferred"); the background is
[Lean big integers, timing, and the relation to the AES rule](2026-11-27-bignum-timing-and-aes.md).
It uses the terms of the wallet's signing record,
`docs/designissues/2026-11-27-ethereum-wallet-signing.md` (on the wallet branch,
`wip/eth-wallet-sign-20261127`, at the time of writing).

## The statement

**`Secp256k1.recoverFast`, `mulAddFast` and `mulBaseFast` are for public data only. They must
never be given a secret scalar** (a private key, an ECDSA nonce, a key-derivation tweak that is
secret). Their running time, the table entries they read and the branches they take all depend on
the scalars, directly and by design. A few leaked bits of an ECDSA nonce per signature are enough
to recover the key by lattice methods (see the bignum record, section 2), and these functions leak
far more than a few bits.

They are used where every input is public by the definition of the protocol: ECRECOVER
(precompile 0x01) takes a hash and a signature from call data. A signature self-check that
recovers the public key from a finished signature is also public data. Fixed-base multiplication
for a public scalar is public data. Deriving a public key from a private key is not.

This is not a path to a signer. By `CLAUDE.md`, every operation on a secret key goes through
HACL\* (`L4Factoidal/Crypto/K256Native.lean`), and pure Lean curve code is a specification or a
differential oracle. The limb field here looks like the fixed-width arithmetic that a
constant-time signer would be built from, so this note exists so that nobody takes it for one.

## What depends on the data in time

| Part | Where | How it depends on the data |
|---|---|---|
| Scalar inverse `r⁻¹ mod n` | `Ff.xgcd` (binary extended GCD), used by `scalarInvFast` | every step branches on the low bits of the two numbers being reduced and on their comparison; the number of steps (about 380 for random input, at most 600) depends on the operand |
| GLV decomposition | `glvCandidate`, `glvSplit` | `Nat`/`Int` arithmetic (GMP on native builds): value-dependent lengths, allocation and division time; the signs of the two halves are branches |
| Signed-window recoding | `ScalarMul.wnaf` | a branch per bit on parity and on the window residue; the number of digits is the bit length of the half (up to 130) |
| Length of the doubling chain | `Fast.plan`, `Fast.mainLoop` | the chain runs as many times as the longest recoding: the bit length of the half-scalars shows in the time |
| Which steps have an addition | `Fast.addG`, `Fast.addQ` | an addition happens only for a non-zero digit (about one step in 9 for the `G` halves, one in 6 for the `Q` halves), so the pattern of additions is the pattern of non-zero digits |
| Table lookups | `gTable`, `lgTable` (64 affine points each), the per-call tables of `Q` | the index is the absolute value of a digit of the scalar: cache timing shows digits to an attacker who shares the cache |
| Conditional negation by the digit's sign | `Ff.cneg` in `madd`, `padd` | written as a mask select, no branch in the source |
| Special cases of the addition | `Fast.madd`, `Fast.padd` | explicit branches for infinity, equal points (doubling) and opposite points |
| Fall-backs | `glvPick`, `scalarInvPick`, `Fast.go`, `mulAddChecked` | a failed run-time check sends the call to the old path, which is about twenty times slower; none was seen in any test, but the branch exists |
| Range and parity tests | `recoverFast`, `Fast.pickRoot` | branches on `r`, `s`, the parity bit and on whether `x³ + 7` is a square |
| Conversion between `Nat` and limbs | `U256.ofNat`, `U256.toNat` | `Nat` shifts and multiplications, value-dependent as all `Nat` arithmetic |
| The on-curve check of the result | `Fast.keepOnCurve` (`Secp256k1.onCurve`) | `Nat` arithmetic and a branch |

The older limb field `Secp256k1.Fe` (`Secp256k1Field.lean`, `Limb.lean`), which the fast path does
not use in its point formulas, has in addition:

| Part | Where | How |
|---|---|---|
| Final conditional subtraction | `U256.condSub`, at the end of `Fe.mul`, `Fe.sqr`, `Fe.add` | a branch on whether the value reached the modulus |
| Borrow in subtraction, zero test in negation | `U256.subMod`, `U256.negMod` | branches |
| Carries | `Limb.mac`, `Limb.adc`, `Limb.sbb` | written as `if a < b then 1 else 0`; whether the machine code has a branch there is the C compiler's choice |
| Scalar field inverse | `Mont256.inv` | Euclid on `Nat`: the number of steps depends on the operand |

## What has a fixed schedule

- **The addition chains.** `Ff.inv` (`a^(p−2)`) and `Ff.sqrtCandidate` (`a^((p+1)/4)`) run the same
  255 squarings and 15 or 13 multiplications for every input. So do `Fe.inv` and `Fe.sqrt?`, but
  there each field operation still ends in the `condSub` branch.
- **The field operations of `Secp256k1FieldFast`.** `Ff.mul`, `Ff.sqr`, `Ff.add`, `Ff.sub`,
  `Ff.neg`, `Ff.cneg`, `Ff.mulSmall` are straight-line in the source: carries are comparisons
  converted to a word, and the final subtraction of `p` is a select under a mask. They were written
  that way for speed (a branch at the end of an operation forces its result into a heap object),
  not for secrecy.
- **The doubling.** `Fast.dbl` has no branch.

None of this is a constant-time claim. The property is one of the Lean source. Lean's compiler and
the C compiler after it may turn a select into a branch (the bignum record, section 1, point 4), a
32-bit by 32-bit multiplication is not constant-time on every processor, and nothing here measures
or checks the machine code. The repository's check for code that handles secrets is Valgrind on the
compiled code with leaking controls (`tests/ct/run.sh valgrind`), and it is applied to the HACL\*
operations, not to this module.

## What a signing path would need from a limb field

For the record, since the question will come up. A pure Lean signer is not planned: this is what
would have to be true before the limb code could be considered for secret data at all, and each
item would need evidence at the level of the machine code, not of the source.

1. A conditional subtraction and a conditional select with no branch, for every field operation
   on the secret path (`Ff.condSub` and `Ff.select` are written this way; `U256.condSub` is not).
2. A multiplication primitive whose time does not depend on its operands on the target processor.
3. A scalar multiplication with a fixed schedule: a fixed-window ladder or comb with the same
   number of doublings and additions for every scalar, digits recoded so that none is zero, and a
   table selection that reads every entry and keeps one under a mask. Signed sliding windows, GLV
   with `Nat` rounding and a doubling chain cut to the scalar's length are all excluded.
4. Complete addition formulas (no branch for equal points, opposite points or infinity), or a
   schedule in which those cases cannot occur for any scalar, with a proof.
5. Inverses by a fixed exponent (the addition chains above), never a GCD.
6. No `Nat` or `Int` on the secret path, including conversions and range checks.
7. Scalar arithmetic modulo `n` on limbs with the same properties (the Montgomery field
   `Secp256k1.scalarField` has the `condSub` branch today).
8. A test on the compiled code, with leaking controls, as for the HACL\* operations.

The wallet's own comb (`EthereumWallet.Sign`, fixed schedule over the shared `Nat` curve code) and
its list of remaining leaks are described in its record; the faster public-data functions here
change the time of its recovery self-check and nothing else about it.

## Evidence that the fast paths agree with the old ones

Tested, not proved (no group law is proved in this package): build-time guards on edge cases in
`Secp256k1Fast.lean`; the run-time differential check `evm-secpperf` in the workflow
`evm-fieldperf.yml` (2,000 valid signatures with known keys, 2,000 arbitrary inputs, 2,000 double
multiplications of which a quarter sum to infinity, 2,028 fixed-base scalars, each against the old
path; non-zero exit on any difference or any use of a fall-back); and the published ECRECOVER
vectors through the precompile router. Every point returned has passed the curve equation in the
`Nat` field (`recoverFast_onCurve` and its siblings), so a fault in the fast path cannot return a
pair that is not a point of the curve.
