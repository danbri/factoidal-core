import EVMCleanroom.Precompiles.Basic

/-!
# BLAKE2b compression function F (precompile 0x09, EIP-152)

Written from RFC 7693 section 3.2 and EIP-152. The input is exactly 213
bytes: a big-endian 32-bit round count, the state `h` (8 little-endian
64-bit words), the message block `m` (16 words), the offset counters `t`
(2 words) and the final-block flag (one byte, 0 or 1). Gas is one per round.

The round count is attacker-chosen (below 2^32) and is paid for one gas per
round, so the forwarded gas bounds the work. As a second, local bound the
implementation refuses more than `maxRounds` rounds after the gas check.

Checked against the EIP-152 vectors. No cryptographic property is proved.
-/

namespace EVMCleanroom.Precompiles.Blake2f

private def iv : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

@[inline] private def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

structure Quad where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64

@[inline] private def g (q : Quad) (x y : UInt64) : Quad :=
  let a := q.a + q.b + x
  let d := rotr (q.d ^^^ a) 32
  let c := q.c + d
  let b := rotr (q.b ^^^ c) 24
  let a := a + b + y
  let d := rotr (d ^^^ a) 16
  let c := c + d
  let b := rotr (b ^^^ c) 63
  ⟨a, b, c, d⟩

/-- The sixteen working words. All fields are unboxed machine words. -/
structure Work where
  v0 : UInt64
  v1 : UInt64
  v2 : UInt64
  v3 : UInt64
  v4 : UInt64
  v5 : UInt64
  v6 : UInt64
  v7 : UInt64
  v8 : UInt64
  v9 : UInt64
  v10 : UInt64
  v11 : UInt64
  v12 : UInt64
  v13 : UInt64
  v14 : UInt64
  v15 : UInt64

/-- The sixteen message words. -/
structure Message where
  m0 : UInt64
  m1 : UInt64
  m2 : UInt64
  m3 : UInt64
  m4 : UInt64
  m5 : UInt64
  m6 : UInt64
  m7 : UInt64
  m8 : UInt64
  m9 : UInt64
  m10 : UInt64
  m11 : UInt64
  m12 : UInt64
  m13 : UInt64
  m14 : UInt64
  m15 : UInt64

/-- One round on message words already permuted: four column steps, four diagonal steps. -/
private def mix (w : Work) (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt64) : Work :=
  let q0 := g ⟨w.v0, w.v4, w.v8, w.v12⟩ x0 x1
  let q1 := g ⟨w.v1, w.v5, w.v9, w.v13⟩ x2 x3
  let q2 := g ⟨w.v2, w.v6, w.v10, w.v14⟩ x4 x5
  let q3 := g ⟨w.v3, w.v7, w.v11, w.v15⟩ x6 x7
  let d0 := g ⟨q0.a, q1.b, q2.c, q3.d⟩ x8 x9
  let d1 := g ⟨q1.a, q2.b, q3.c, q0.d⟩ x10 x11
  let d2 := g ⟨q2.a, q3.b, q0.c, q1.d⟩ x12 x13
  let d3 := g ⟨q3.a, q0.b, q1.c, q2.d⟩ x14 x15
  { v0 := d0.a, v1 := d1.a, v2 := d2.a, v3 := d3.a
    v4 := d3.b, v5 := d0.b, v6 := d1.b, v7 := d2.b
    v8 := d2.c, v9 := d3.c, v10 := d0.c, v11 := d1.c
    v12 := d1.d, v13 := d2.d, v14 := d3.d, v15 := d0.d }

/-- One round with the message schedule of SIGMA row `row` (RFC 7693, section 2.7),
    written out so every word is a direct field read. -/
private def round (m : Message) (row : Nat) (w : Work) : Work :=
  match row with
  | 0 => mix w m.m0 m.m1 m.m2 m.m3 m.m4 m.m5 m.m6 m.m7 m.m8 m.m9 m.m10 m.m11 m.m12 m.m13 m.m14 m.m15
  | 1 => mix w m.m14 m.m10 m.m4 m.m8 m.m9 m.m15 m.m13 m.m6 m.m1 m.m12 m.m0 m.m2 m.m11 m.m7 m.m5 m.m3
  | 2 => mix w m.m11 m.m8 m.m12 m.m0 m.m5 m.m2 m.m15 m.m13 m.m10 m.m14 m.m3 m.m6 m.m7 m.m1 m.m9 m.m4
  | 3 => mix w m.m7 m.m9 m.m3 m.m1 m.m13 m.m12 m.m11 m.m14 m.m2 m.m6 m.m5 m.m10 m.m4 m.m0 m.m15 m.m8
  | 4 => mix w m.m9 m.m0 m.m5 m.m7 m.m2 m.m4 m.m10 m.m15 m.m14 m.m1 m.m11 m.m12 m.m6 m.m8 m.m3 m.m13
  | 5 => mix w m.m2 m.m12 m.m6 m.m10 m.m0 m.m11 m.m8 m.m3 m.m4 m.m13 m.m7 m.m5 m.m15 m.m14 m.m1 m.m9
  | 6 => mix w m.m12 m.m5 m.m1 m.m15 m.m14 m.m13 m.m4 m.m10 m.m0 m.m7 m.m6 m.m3 m.m9 m.m2 m.m8 m.m11
  | 7 => mix w m.m13 m.m11 m.m7 m.m14 m.m12 m.m1 m.m3 m.m9 m.m5 m.m0 m.m15 m.m4 m.m8 m.m6 m.m2 m.m10
  | 8 => mix w m.m6 m.m15 m.m14 m.m9 m.m11 m.m3 m.m0 m.m8 m.m12 m.m2 m.m13 m.m7 m.m1 m.m4 m.m10 m.m5
  | _ => mix w m.m10 m.m2 m.m8 m.m4 m.m7 m.m6 m.m1 m.m5 m.m15 m.m11 m.m9 m.m14 m.m3 m.m12 m.m13 m.m0

/-- `remaining` rounds are still to run out of `total`; round `i` uses SIGMA row `i mod 10`. -/
private def rounds (m : Message) (total : Nat) : Nat → Work → Work
  | 0, w => w
  | remaining+1, w => rounds m total remaining (round m ((total - (remaining + 1)) % 10) w)

@[inline] private def word (b : ByteArray) (off : Nat) : UInt64 := UInt64.ofNat (leNat b off 8)

private def putWord (acc : ByteArray) (w : UInt64) : ByteArray := acc ++ natToLE 8 w.toNat

/-- The function F on decoded arguments; returns the eight new state words. -/
def compress (roundCount : Nat) (h : Array UInt64) (m : Message) (t0 t1 : UInt64) (final : Bool) :
    Array UInt64 :=
  let start : Work :=
    { v0 := h[0]!, v1 := h[1]!, v2 := h[2]!, v3 := h[3]!
      v4 := h[4]!, v5 := h[5]!, v6 := h[6]!, v7 := h[7]!
      v8 := iv[0]!, v9 := iv[1]!, v10 := iv[2]!, v11 := iv[3]!
      v12 := iv[4]! ^^^ t0, v13 := iv[5]! ^^^ t1
      v14 := if final then ~~~iv[6]! else iv[6]!, v15 := iv[7]! }
  let w := rounds m roundCount roundCount start
  #[h[0]! ^^^ w.v0 ^^^ w.v8, h[1]! ^^^ w.v1 ^^^ w.v9, h[2]! ^^^ w.v2 ^^^ w.v10, h[3]! ^^^ w.v3 ^^^ w.v11,
    h[4]! ^^^ w.v4 ^^^ w.v12, h[5]! ^^^ w.v5 ^^^ w.v13, h[6]! ^^^ w.v6 ^^^ w.v14, h[7]! ^^^ w.v7 ^^^ w.v15]

/-- Local work bound, above any block gas limit in use. Not an Ethereum rule. -/
def maxRounds : Nat := 1 <<< 30

/-- The round count field: the first four bytes, big-endian. -/
def roundField (input : ByteArray) : Nat := beNat input 0 4

/-- The price is known only for well-formed input; malformed input fails at any gas. -/
def gasCost (input : ByteArray) : Nat := roundField input

private def encode (out : Array UInt64) : ByteArray :=
  out.foldl putWord ByteArray.empty

def body (input : ByteArray) : Body :=
  if roundField input > maxRounds then .refuse
  else
    let h := (Array.range 8).map fun i => word input (4 + 8 * i)
    let x (i : Nat) : UInt64 := word input (68 + 8 * i)
    let m : Message := ⟨x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, x 14, x 15⟩
    .output (encode (compress (roundField input) h m (word input 196) (word input 204)
      (byteAt input 212 == 1)))

/-- Precompile 0x09. Length and flag are validated before gas, as in EIP-152. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  if input.size ≠ 213 then .failure
  else if byteAt input 212 > 1 then .failure
  else charge gas (gasCost input) fun _ => body input

/-- Kind: input-length contract.
    Says: any input that is not exactly 213 bytes fails, whatever the gas.
    Does not say: anything about well-formed input. -/
theorem run_wrong_length (gas : Nat) (input : ByteArray) (h : input.size ≠ 213) :
    run gas input = .failure := by
  simp [run, h]

/-- Kind: input contract.
    Says: a final-block flag other than 0 or 1 fails, whatever the gas.
    Does not say: anything about well-formed input. -/
theorem run_bad_flag (gas : Nat) (input : ByteArray) (h : byteAt input 212 > 1) :
    run gas input = .failure := by
  unfold run
  split <;> simp_all

/-- Kind: gas admission.
    Says: well-formed input with fewer gas units than rounds fails before any round runs.
    Does not say: anything about funded calls. -/
theorem run_underfunded (gas : Nat) (input : ByteArray) (h : gas < roundField input) :
    run gas input = .failure := by
  unfold run
  split
  · rfl
  · split
    · rfl
    · exact charge_underfunded _ _ _ h

private theorem beLoop_bound (b : ByteArray) (n off acc : Nat) :
    beLoop b n off acc < (acc + 1) * 256 ^ n := by
  induction n generalizing off acc with
  | zero => simp [beLoop]
  | succ n ih =>
    simp only [beLoop]
    have hb : (byteAt b off).toNat < 256 := UInt8.toNat_lt _
    have := ih (off + 1) (acc * 256 + (byteAt b off).toNat)
    calc beLoop b n (off + 1) (acc * 256 + (byteAt b off).toNat)
        < (acc * 256 + (byteAt b off).toNat + 1) * 256 ^ n := this
      _ ≤ ((acc + 1) * 256) * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
      _ = (acc + 1) * 256 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 256]

/-- Kind: work bound.
    Says: the round count read from any input is below 2^32.
    Does not say: that many rounds are ever run (gas and `maxRounds` bound that). -/
theorem roundField_bound (input : ByteArray) : roundField input < 2 ^ 32 := by
  have := beLoop_bound input 4 0 0
  simpa [roundField, beNat] using this

/-- Kind: work bound and accounting.
    Says: a successful call ran at most `maxRounds` rounds, at most one per forwarded gas
    unit, returned the exact unspent gas, and had a well-formed 213-byte input.
    Does not say: the output is the BLAKE2b F function (tested, not proved). -/
theorem run_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run gas input = .success out left) :
    input.size = 213 ∧ roundField input ≤ maxRounds ∧ left + roundField input = gas := by
  unfold run at h
  split at h
  · cases h
  · rename_i hSize
    split at h
    · cases h
    · have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
      refine ⟨by omega, ?_, hGas⟩
      unfold body at hBody
      split at hBody
      · cases hBody
      · omega

/-- Kind: local bound.
    Says: a funded, well-formed request for more than `maxRounds` rounds is refused,
    not answered.
    Does not say: Ethereum has this limit. -/
theorem run_refuses_over_bound (gas : Nat) (input : ByteArray) (hSize : input.size = 213)
    (hFlag : ¬ byteAt input 212 > 1) (hGas : roundField input ≤ gas)
    (hRounds : maxRounds < roundField input) : run gas input = .refusal := by
  have hNot : ¬ gas < gasCost input := by simp only [gasCost]; omega
  simp [run, hSize, hFlag, charge, hNot, body, hRounds]

private def vector (rounds : String) (final : String) : ByteArray :=
  hex (rounds ++
    "48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b" ++
    "6162630000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
    "000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000" ++
    "0300000000000000" ++ "0000000000000000" ++ final)

private def outHex (gas : Nat) (input : ByteArray) : String :=
  match run gas input with
  | .success out left => toHex out ++ ":" ++ toString left
  | .failure => "failure"
  | .refusal => "refusal"

-- EIP-152 test vectors 4, 5, 6 and 7 (12 rounds final, 0 rounds, non-final, 1 round).
#guard (vector "0000000c" "01").size == 213
#guard outHex 12 (vector "0000000c" "01") ==
  "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d17d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923:0"
#guard outHex 100 (vector "00000000" "01") ==
  "08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b:100"
#guard outHex 12 (vector "0000000c" "00") ==
  "75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d2875298743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735:0"
#guard outHex 1 (vector "00000001" "01") ==
  "b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fba551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421:0"
-- EIP-152 vectors 0 to 3: empty input, short and long input, malformed flag; and too little gas.
#guard outHex 100 ByteArray.empty == "failure"
#guard outHex 100 ((vector "0000000c" "01").extract 1 213) == "failure"
#guard outHex 100 (hex "00" ++ vector "0000000c" "01") == "failure"
#guard outHex 100 (vector "0000000c" "02") == "failure"
#guard outHex 11 (vector "0000000c" "01") == "failure"
#guard outHex (1 <<< 32) (vector "ffffffff" "01") == "refusal"

#print axioms run_wrong_length
#print axioms run_bad_flag
#print axioms run_underfunded
#print axioms roundField_bound
#print axioms run_success
#print axioms run_refuses_over_bound
#print axioms beLoop_bound

end EVMCleanroom.Precompiles.Blake2f
