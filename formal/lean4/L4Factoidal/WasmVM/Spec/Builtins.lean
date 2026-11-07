/-!
# WebAssembly integer built-ins on `BitVec`

The WebAssembly 3.0 SpecTec sources declare many numeric operators with `hint(builtin)`:
SpecTec gives their type and leaves their meaning to the prose specification. The
generated spec layer (`Spec/Wasm30.lean`) can only make them `opaque`. This module
defines the INTEGER ones, by hand, from the prose of the pinned specification
(WebAssembly/spec `f3268fa9`, `third_party/wasm-spec/document/core/exec/numerics.rst`,
chapter 4.3 "Numerics"). Owner decision, 2026-11-07, issue
https://github.com/danbri/factoidal/issues/1244.

Each definition cites its section and the `numerics.rst` anchor, and quotes the
defining sentence or formula. Review this module as spec text: it is the only
hand-written meaning in the spec layer.

Representation. An `iN` value is a `BitVec N`; the spec's bit sequence `ibits_N(i)` is
its bits, most significant first. Shift and rotate counts are natural numbers, taken
modulo `N` as the spec says. Results of predicates are `Bool`; the spec's `bool(C)`
(1 or 0) is applied in the `OnNat` bridge.

`OnNat` (at the end) is the bridge to the generated layer, where every `iN` is a
`Nat`: it reads a `Nat` as `BitVec.ofNat N`, so an argument outside `iN(N)` is first
reduced modulo `2^N`. The spec never applies these operators to such arguments.
`tools/wasmvm/port_builtins.py` replaces each matching `opaque` of the generated
layer by a call into `OnNat`.

Not here: floating-point operators and conversions (they need an IEEE 754 model;
plan in docs/designissues/2026-11-07-wasmvm-spec-layer.md), the vector lifting
functions, and the relaxed-SIMD operators, whose results are sets.

Imports Lean core only, so it builds quickly. The definitions are computable (no
recursion of their own) so `decide` and tests can run them.
-/

namespace L4Factoidal.WasmVM.Spec.Builtins

/-! ## 4.3 conventions: signed interpretation and saturation -/

/-- Spec 4.3.2, "Sign Interpretation" (`aux-signed`):
`signed_N(i) = i (0 ≤ i < 2^(N-1))`, `signed_N(i) = i - 2^N (2^(N-1) ≤ i < 2^N)`. -/
def signed_ (N : Nat) (i : Nat) : Int :=
  if i < 2 ^ (N - 1) then (i : Int) else (i : Int) - 2 ^ N

/-- Spec 4.3.2, "Sign Interpretation": the inverse of `signed_N`, as in SpecTec
`$inv_signed_(N, i) = i (0 ≤ i < 2^(N-1))`, `= i + 2^N (-2^(N-1) ≤ i < 0)`. -/
def inv_signed_ (N : Nat) (i : Int) : Nat :=
  if 0 ≤ i then i.toNat else (i + 2 ^ N).toNat

/-- Spec 4.3, conventions (`aux-sat`): "`sat_u_N(i)` clamps `i` to between `0` and
`2^N-1`". -/
def sat_u_ (N : Nat) (i : Int) : Nat :=
  if i < 0 then 0 else if i > 2 ^ N - 1 then 2 ^ N - 1 else i.toNat

/-- Spec 4.3, conventions (`aux-sat`): "`sat_s_N(i)` clamps `i` to between
`-2^(N-1)` and `2^(N-1)-1`". -/
def sat_s_ (N : Nat) (i : Int) : Int :=
  if i < -2 ^ (N - 1) then -2 ^ (N - 1)
  else if i > 2 ^ (N - 1) - 1 then 2 ^ (N - 1) - 1 else i

/-! ## 4.3.1 Representations -/

/-- Spec 4.3.1, "Integers" (`aux-ibits`): integers are "base two unsigned numbers",
`ibits_N(i) = d_(N-1) ... d_0` with `i = 2^(N-1)·d_(N-1) + ... + 2^0·d_0`.
Most significant bit first. -/
def ibits_ {n : Nat} (i : BitVec n) : List Bool :=
  (List.range n).map fun k => i.getMsbD k

/-- Spec 4.3.1, "Representations": `ibits_N` "is a bijection, hence ... invertible".
The inverse reads the bits most significant first:
`i = 2^(N-1)·d_(N-1) + ... + 2^0·d_0`. -/
def inv_ibits_ (n : Nat) (ds : List Bool) : BitVec n :=
  BitVec.ofNat n (ds.foldl (fun acc d => 2 * acc + (if d then 1 else 0)) 0)

/-- Spec 4.3.1, "Storage" (`aux-bytes`): a stored number becomes bytes "in little
endian byte order": `bytes_t(i) = littleendian(bits_t(i))`, with
`littleendian(d^8 d'*) = littleendian(d'*) ibits_8^-1(d^8)`. Byte `k` holds bits
`8k .. 8k+7`; the least significant byte comes first. `N` is a multiple of 8 wherever
the spec uses it. -/
def ibytes_ {n : Nat} (i : BitVec n) : List (BitVec 8) :=
  (List.range (n / 8)).map fun k => i.extractLsb' (8 * k) 8

/-- Spec 4.3.1, "Storage": "these functions are invertible bijections". The inverse of
`ibytes_N`: the first byte is the least significant, `i = Σ_k 256^k · b_k`. -/
def inv_ibytes_ (n : Nat) (bs : List (BitVec 8)) : BitVec n :=
  BitVec.ofNat n (bs.foldr (fun b acc => b.toNat + 256 * acc) 0)

/-! ## 4.3.2 Integer operations: bitwise -/

/-- Spec 4.3.2 (`op-inot`): "Return the bitwise negation of `i`."
`inot_N(i) = ibits_N^-1(ibits_N(i) ⊻ ibits_N(2^N-1))`. -/
def inot_ {n : Nat} (i : BitVec n) : BitVec n := ~~~i

/-- Spec 4.3.2 (`op-iand`): "Return the bitwise conjunction of `i_1` and `i_2`." -/
def iand_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := i₁ &&& i₂

/-- Spec 4.3.2 (`op-iandnot`): "Return the bitwise conjunction of `i_1` and the bitwise
negation of `i_2`." `iandnot_N(i_1, i_2) = iand_N(i_1, inot_N(i_2))`. -/
def iandnot_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := iand_ i₁ (inot_ i₂)

/-- Spec 4.3.2 (`op-ior`): "Return the bitwise disjunction of `i_1` and `i_2`." -/
def ior_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := i₁ ||| i₂

/-- Spec 4.3.2 (`op-ixor`): "Return the bitwise exclusive disjunction of `i_1` and
`i_2`." -/
def ixor_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n := i₁ ^^^ i₂

/-- Spec 4.3.2 (`op-irev`): "Return the bitwise reversal of `i`." -/
def irev_ {n : Nat} (i : BitVec n) : BitVec n := i.reverse

/-- Spec 4.3.2 (`op-ibitselect`):
`ibitselect_N(i_1, i_2, i_3) = ior_N(iand_N(i_1, i_3), iand_N(i_2, inot_N(i_3)))`. -/
def ibitselect_ {n : Nat} (i₁ i₂ i₃ : BitVec n) : BitVec n :=
  ior_ (iand_ i₁ i₃) (iand_ i₂ (inot_ i₃))

/-! ## 4.3.2 Integer operations: shifts and rotates (count modulo `N`) -/

/-- Spec 4.3.2 (`op-ishl`): "Let `k` be `i_2` modulo `N`. Return the result of shifting
`i_1` left by `k` bits, modulo `2^N`." -/
def ishl_ {n : Nat} (i₁ : BitVec n) (i₂ : Nat) : BitVec n := i₁ <<< (i₂ % n)

/-- Spec 4.3.2 (`op-ishr`). Unsigned: "Let `k` be `i_2` modulo `N`. Return the result of
shifting `i_1` right by `k` bits, extended with `0` bits." Signed: "... extended with
the most significant bit of the original value." `signed = true` is `ishr_s`. -/
def ishr_ {n : Nat} (signed : Bool) (i₁ : BitVec n) (i₂ : Nat) : BitVec n :=
  if signed then i₁.sshiftRight (i₂ % n) else i₁ >>> (i₂ % n)

/-- Spec 4.3.2 (`op-irotl`): "Let `k` be `i_2` modulo `N`. Return the result of rotating
`i_1` left by `k` bits." -/
def irotl_ {n : Nat} (i₁ : BitVec n) (i₂ : Nat) : BitVec n := i₁.rotateLeft (i₂ % n)

/-- Spec 4.3.2 (`op-irotr`): "Let `k` be `i_2` modulo `N`. Return the result of rotating
`i_1` right by `k` bits." -/
def irotr_ {n : Nat} (i₁ : BitVec n) (i₂ : Nat) : BitVec n := i₁.rotateRight (i₂ % n)

/-! ## 4.3.2 Integer operations: bit counts -/

/-- Spec 4.3.2 (`op-iclz`): "Return the count of leading zero bits in `i`; all bits are
considered leading zeros if `i` is `0`." `iclz_N(i) = k (if ibits_N(i) = 0^k (1 d*)?)`.
Core's `BitVec.clz` counts from the most significant bit; it is `N` on `0`. -/
def iclz_ {n : Nat} (i : BitVec n) : BitVec n := i.clz

/-- Spec 4.3.2 (`op-ictz`): "Return the count of trailing zero bits in `i`; all bits are
considered trailing zeros if `i` is `0`." -/
def ictz_ {n : Nat} (i : BitVec n) : BitVec n := i.ctz

/-- Spec 4.3.2 (`op-ipopcnt`): "Return the count of non-zero bits in `i`." -/
def ipopcnt_ {n : Nat} (i : BitVec n) : BitVec n := i.cpop

/-! ## 4.3.2 Integer operations: tests and comparisons -/

/-- Spec 4.3.2 (`op-ieqz`): "Return `1` if `i` is zero, `0` otherwise." -/
def ieqz_ {n : Nat} (i : BitVec n) : Bool := i == 0#n

/-- Spec 4.3.2 (`op-ilt`): `ilt_u_N(i_1, i_2) = bool(i_1 < i_2)`,
`ilt_s_N(i_1, i_2) = bool(signed_N(i_1) < signed_N(i_2))`. `signed = true` is `ilt_s`;
`BitVec.slt` compares the two's complement values (`ilt_s_eq_signed`). -/
def ilt_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : Bool :=
  if signed then i₁.slt i₂ else i₁.ult i₂

/-- Spec 4.3.2 (`op-igt`): `igt_N(i_1, i_2) = bool(i_1 > i_2)`, signed as for `ilt_`. -/
def igt_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : Bool := ilt_ signed i₂ i₁

/-- Spec 4.3.2 (`op-ile`): `ile_N(i_1, i_2) = bool(i_1 ≤ i_2)`, signed as for `ilt_`. -/
def ile_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : Bool :=
  if signed then i₁.sle i₂ else i₁.ule i₂

/-- Spec 4.3.2 (`op-ige`): `ige_N(i_1, i_2) = bool(i_1 ≥ i_2)`, signed as for `ilt_`. -/
def ige_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : Bool := ile_ signed i₂ i₁

/-! ## 4.3.2 Integer operations with clauses in SpecTec

The SpecTec sources define these; the generated layer made them opaque. They are
transcribed from the clauses, using `signed_`, `inv_signed_` and the saturations. -/

/-- Spec 4.3.2 (`op-iabs`): `iabs_N(i) = i (if signed_N(i) ≥ 0)`, else
`-signed_N(i) mod 2^N`. -/
def iabs_ {n : Nat} (i : BitVec n) : BitVec n :=
  if 0 ≤ signed_ n i.toNat then i else -i

/-- Spec 4.3.2 (`op-imin`): "Return `i_1` if `ilt_N(i_1, i_2)` is `1`, return `i_2`
otherwise", for `u` and `s`. -/
def imin_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : BitVec n :=
  if ilt_ signed i₁ i₂ then i₁ else i₂

/-- Spec 4.3.2 (`op-imax`): "Return `i_1` if `igt_N(i_1, i_2)` is `1`, return `i_2`
otherwise", for `u` and `s`. -/
def imax_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : BitVec n :=
  if igt_ signed i₁ i₂ then i₁ else i₂

/-- Spec 4.3.2 (`op-iadd_sat`): `iadd_sat_u_N(i_1, i_2) = sat_u_N(i_1 + i_2)`;
`iadd_sat_s_N(i_1, i_2) = signed_N^-1(sat_s_N(signed_N(i_1) + signed_N(i_2)))`. -/
def iadd_sat_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : BitVec n :=
  if signed then
    BitVec.ofNat n (inv_signed_ n (sat_s_ n (signed_ n i₁.toNat + signed_ n i₂.toNat)))
  else BitVec.ofNat n (sat_u_ n ((i₁.toNat : Int) + i₂.toNat))

/-- Spec 4.3.2 (`op-isub_sat`): `isub_sat_u_N(i_1, i_2) = sat_u_N(i_1 - i_2)`;
`isub_sat_s_N(i_1, i_2) = signed_N^-1(sat_s_N(signed_N(i_1) - signed_N(i_2)))`. -/
def isub_sat_ {n : Nat} (signed : Bool) (i₁ i₂ : BitVec n) : BitVec n :=
  if signed then
    BitVec.ofNat n (inv_signed_ n (sat_s_ n (signed_ n i₁.toNat - signed_ n i₂.toNat)))
  else BitVec.ofNat n (sat_u_ n ((i₁.toNat : Int) - i₂.toNat))

/-- Spec 4.3.2 (`op-iavgr`): `iavgr_u_N(i_1, i_2) = truncz((i_1 + i_2 + 1) / 2)`.
The spec defines the unsigned form only. -/
def iavgr_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n :=
  BitVec.ofNat n ((i₁.toNat + i₂.toNat + 1) / 2)

/-- Spec 4.3.2 (`op-iq15mulrsat`):
`iq15mulr_sat_s_N(i_1, i_2) = signed_N^-1(sat_s_N(ishr_s_N(i_1 · i_2 + 2^14, 15)))`,
where the product is of the signed interpretations and the shift is arithmetic
(floor division by `2^15`). The spec defines the signed form only. -/
def iq15mulr_sat_ {n : Nat} (i₁ i₂ : BitVec n) : BitVec n :=
  BitVec.ofNat n (inv_signed_ n
    (sat_s_ n ((signed_ n i₁.toNat * signed_ n i₂.toNat + 2 ^ 14) >>> 15)))

/-! ## 4.3.4 Conversions -/

/-- Spec 4.3.4 (`op-wrap`): "Return `i` modulo `2^N`." `wrap_(M,N)(i) = i mod 2^N`. -/
def wrap_ {m : Nat} (n : Nat) (i : BitVec m) : BitVec n := i.setWidth n

/-- Spec 4.3.4 (`op-extend`). Unsigned: `extend_u_(M,N)(i) = i`. Signed: "Let `j` be the
signed interpretation of `i` of size `M`. Return the two's complement of `j` relative to
size `N`": `extend_s_(M,N)(i) = signed_N^-1(signed_M(i))`. `signed = true` is
`extend_s`; `BitVec.signExtend` is that two's complement (`extend_s_eq_spec`). -/
def extend_ {m : Nat} (n : Nat) (signed : Bool) (i : BitVec m) : BitVec n :=
  if signed then i.signExtend n else i.setWidth n

/-- Spec 4.3.2 (`op-iextendn`) as SpecTec writes it:
`$iextend_(N, K, U, i) = i mod 2^K`, `$iextend_(N, K, S, i) = inv_signed_N(signed_K(i mod 2^K))`:
extend the low `K` bits of `i` back to `N` bits (`i32.extend8_s` and friends). -/
def iextend_ {n : Nat} (k : Nat) (signed : Bool) (i : BitVec n) : BitVec n :=
  extend_ n signed (wrap_ k i)

/-- Spec 4.3.4 (`op-narrow`): `narrow_s_(M,N)(i) = signed_N^-1(sat_s_N(signed_M(i)))`;
`narrow_u_(M,N)(i) = sat_u_N(signed_M(i))`. -/
def narrow_ {m : Nat} (n : Nat) (signed : Bool) (i : BitVec m) : BitVec n :=
  if signed then BitVec.ofNat n (inv_signed_ n (sat_s_ n (signed_ m i.toNat)))
  else BitVec.ofNat n (sat_u_ n (signed_ m i.toNat))

/-! ## Bridge to the generated layer, where `iN` is a `Nat`

Each function reads its `Nat` arguments as `BitVec.ofNat N` and returns `toNat` of the
result. `tools/wasmvm/port_builtins.py` calls these from `Spec/Wasm30.lean`. -/

namespace OnNat

/-- SpecTec `$bool(b)`: `1` for true, `0` for false. -/
def bool (b : Bool) : Nat := if b then 1 else 0

def inot_ (N i : Nat) : Nat := (Builtins.inot_ (BitVec.ofNat N i)).toNat
def iand_ (N i₁ i₂ : Nat) : Nat := (Builtins.iand_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def iandnot_ (N i₁ i₂ : Nat) : Nat :=
  (Builtins.iandnot_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def ior_ (N i₁ i₂ : Nat) : Nat := (Builtins.ior_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def ixor_ (N i₁ i₂ : Nat) : Nat := (Builtins.ixor_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def irev_ (N i : Nat) : Nat := (Builtins.irev_ (BitVec.ofNat N i)).toNat
def ibitselect_ (N i₁ i₂ i₃ : Nat) : Nat :=
  (Builtins.ibitselect_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂) (BitVec.ofNat N i₃)).toNat
def ishl_ (N i₁ i₂ : Nat) : Nat := (Builtins.ishl_ (BitVec.ofNat N i₁) i₂).toNat
def ishr_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  (Builtins.ishr_ signed (BitVec.ofNat N i₁) i₂).toNat
def irotl_ (N i₁ i₂ : Nat) : Nat := (Builtins.irotl_ (BitVec.ofNat N i₁) i₂).toNat
def irotr_ (N i₁ i₂ : Nat) : Nat := (Builtins.irotr_ (BitVec.ofNat N i₁) i₂).toNat
def iclz_ (N i : Nat) : Nat := (Builtins.iclz_ (BitVec.ofNat N i)).toNat
def ictz_ (N i : Nat) : Nat := (Builtins.ictz_ (BitVec.ofNat N i)).toNat
def ipopcnt_ (N i : Nat) : Nat := (Builtins.ipopcnt_ (BitVec.ofNat N i)).toNat
def ilt_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  bool (Builtins.ilt_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂))
def igt_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  bool (Builtins.igt_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂))
def ile_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  bool (Builtins.ile_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂))
def ige_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  bool (Builtins.ige_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂))
def iabs_ (N i : Nat) : Nat := (Builtins.iabs_ (BitVec.ofNat N i)).toNat
def imin_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  (Builtins.imin_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def imax_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  (Builtins.imax_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def iadd_sat_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  (Builtins.iadd_sat_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def isub_sat_ (N : Nat) (signed : Bool) (i₁ i₂ : Nat) : Nat :=
  (Builtins.isub_sat_ signed (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def iavgr_ (N i₁ i₂ : Nat) : Nat := (Builtins.iavgr_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def iq15mulr_sat_ (N i₁ i₂ : Nat) : Nat :=
  (Builtins.iq15mulr_sat_ (BitVec.ofNat N i₁) (BitVec.ofNat N i₂)).toNat
def wrap_ (M N i : Nat) : Nat := (Builtins.wrap_ N (BitVec.ofNat M i)).toNat
def extend_ (M N : Nat) (signed : Bool) (i : Nat) : Nat :=
  (Builtins.extend_ N signed (BitVec.ofNat M i)).toNat
def narrow_ (M N : Nat) (signed : Bool) (i : Nat) : Nat :=
  (Builtins.narrow_ N signed (BitVec.ofNat M i)).toNat
/-- Bits as `0`/`1`, most significant first (the generated `bit` holds a `Nat`). -/
def ibits_ (N i : Nat) : List Nat := (Builtins.ibits_ (BitVec.ofNat N i)).map bool
def inv_ibits_ (N : Nat) (ds : List Nat) : Nat :=
  (Builtins.inv_ibits_ N (ds.map fun d => d != 0)).toNat
def ibytes_ (N i : Nat) : List Nat := (Builtins.ibytes_ (BitVec.ofNat N i)).map BitVec.toNat
def inv_ibytes_ (N : Nat) (bs : List Nat) : Nat :=
  (Builtins.inv_ibytes_ N (bs.map (BitVec.ofNat 8))).toNat

end OnNat

end L4Factoidal.WasmVM.Spec.Builtins
