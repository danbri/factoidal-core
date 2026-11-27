import EVMCleanroom.BLSSig.Reference
import EVMCleanroom.BLSSig.Rfc9380Vectors

/-!
# `evm-blssig`: checks, vectors and timing of BLS signature verification

Modes:

* `--check [SCALE]` (the default): the RFC 9380 vectors on the limb path and on the `Nat`
  path, a differential run of `Precompiles.BLSSignature` against `BLSSig.Reference`
  (generated keys, messages and signatures with negative cases; decoders; hash to `G2`;
  aggregates), then timings. Non-zero exit on any disagreement.
* `--vectors FILE`: published cases, one per line, `SUITE NAME EXPECTED ARGS…`
  (written by `scripts/blssig/run-vectors.py` from the vendored JSON). Non-zero exit on
  any mismatch.
* `--verify PKHEX MSGHEX SIGHEX`: prints `true`, `false`, or `invalid` (the key or the
  signature does not decode). `-` stands for empty bytes; a `0x` prefix is accepted.
* `--verify-file FILE`: one `PKHEX MSGHEX SIGHEX` per line, one answer per line.

Test tool only. The signatures of generated cases come from public test scalars through
`Reference.testOnlyScalarMulG2`; nothing here signs with a secret.
-/

namespace EVMCleanroom.BLSSig

open EVMCleanroom.Precompiles
open BLS12381 (p r field field2)

abbrev M := BLS12381.Fast.M

/-! ### Deterministic pseudo-random values -/

def walk (x : Nat) : Nat :=
  (x * x + 0x6a09e667f3bcc908bb67ae8584caa73b3c6ef372fe94f82ba54ff53a5f1d36f1510e527fade682d1) % (2 ^ 521 - 1)

def randoms (seed count : Nat) : Array Nat := Id.run do
  let mut x := seed * 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95 + 777
  let mut out : Array Nat := #[]
  for _ in [0:count] do
    x := walk x
    out := out.push x
  return out

/-- `len` pseudo-random bytes. -/
def messageOf (seed len : Nat) : ByteArray := Id.run do
  let mut x := seed + 1
  let mut out := ByteArray.empty
  for _ in [0:len / 64 + 1] do
    x := walk x
    out := out ++ natToBE 64 x
  return out.extract 0 len

def messageLengths : Array Nat := #[32, 0, 1, 31, 33, 55, 56, 64, 100, 200, 7, 32]

/-! ### Generated cases -/

structure Signed where
  scalar : Nat
  key : Nat × Nat
  pk : ByteArray
  msg : ByteArray
  hashed : JPoint Fp2
  sigPoint : Option (Fp2 × Fp2)
  sig : ByteArray

instance : Inhabited Signed :=
  ⟨{ scalar := 0, key := (0, 0), pk := ByteArray.empty, msg := ByteArray.empty,
     hashed := ⟨Fp2.zero, Fp2.zero, Fp2.zero⟩, sigPoint := none, sig := ByteArray.empty }⟩

def makeSigned (k : Nat) (msg dst : ByteArray) : Signed :=
  let key := (Reference.testOnlyKeyPoint k).getD (0, 0)
  let hashed := (Reference.hashToG2 dst msg).getD (Curve.infinity field2)
  let sigPoint := Reference.affine2 (Reference.testOnlyScalarMulG2 k hashed)
  { scalar := k, key, pk := Reference.compress1 (some key), msg, hashed, sigPoint,
    sig := Reference.compress2 sigPoint }

def flipFlag (bytes : ByteArray) (mask : UInt8) : ByteArray :=
  if bytes.size == 0 then bytes else bytes.set! 0 (byteAt bytes 0 ^^^ mask)

def flipByte (bytes : ByteArray) (index : Nat) (mask : UInt8) : ByteArray :=
  if index < bytes.size then bytes.set! index (byteAt bytes index ^^^ mask) else bytes

/-- A curve point with an `x` near `start`: almost surely outside the order-`r` subgroup. -/
def liftG1 (start : Nat) : Option (Nat × Nat) := Id.run do
  for t in [0:60] do
    let x := (start + t) % p
    match Fp.sqrt? p ((x * x % p * x + 4) % p) with
    | some y => return some (x, y)
    | none => pure ()
  return none

def fastDecode1 (bytes : ByteArray) : Option (Option (Nat × Nat)) :=
  (BLSSignature.decompressG1 bytes).map fun point => point.map fun a => (M.toNat a.1, M.toNat a.2)

def fastDecode2 (bytes : ByteArray) : Option (Option (Fp2 × Fp2)) :=
  (BLSSignature.decompressG2 bytes).map fun point =>
    point.map fun a => (BLS12381.Fast.ofLimbs2 a.1, BLS12381.Fast.ofLimbs2 a.2)

def boolText (b : Bool) : String := if b then "true" else "false"
def showExpected : Option Bool → String
  | some b => boolText b
  | none => "unknown"

structure Tally where
  cases : Nat := 0
  bad : Nat := 0
  accepted : Nat := 0

def Tally.report (t : Tally) (name : String) : IO Unit :=
  IO.println s!"RESULT blssig {name}: {t.cases} cases ({t.accepted} accepted), {if t.bad == 0 then "no differences" else s!"{t.bad} FAILURES"}"

def Tally.add (t : Tally) (label : String) (fast reference : Bool) (expected : Option Bool) (detail : String) :
    IO Tally := do
  let wrong := fast != reference || (match expected with | some e => fast != e | none => false)
  if wrong && t.bad < 8 then
    IO.println s!"DIFF {label}: fast {boolText fast}, reference {boolText reference}, expected {showExpected expected}: {detail}"
  return { cases := t.cases + 1, bad := t.bad + (if wrong then 1 else 0), accepted := t.accepted + (if fast then 1 else 0) }

/-! ### RFC 9380 vectors at run time -/

def rfcChecks : IO Nat := do
  let mut bad := 0
  for v in Rfc9380.xmdVectors do
    if !Rfc9380.xmdAgrees v then
      bad := bad + 1
      IO.println s!"DIFF expand_message_xmd len {v.len} msg {v.msg.length} chars"
  IO.println s!"RESULT blssig RFC 9380 K.1 expand_message_xmd (SHA-256): {Rfc9380.xmdVectors.size} vectors, {if bad == 0 then "all agree" else s!"{bad} FAILURES"}"
  let mut badPoints := 0
  for v in Rfc9380.g2Vectors do
    let dst := Rfc9380.g2Dst.toUTF8
    let msg := v.msg.toUTF8
    let limbs := Rfc9380.fieldsAgree v && Rfc9380.pointsAgree v
    let nat :=
      Reference.affine2 (Reference.mapToCurve v.u0) == some v.q0 &&
      Reference.affine2 (Reference.mapToCurve v.u1) == some v.q1 &&
      (Reference.hashToG2 dst msg).bind Reference.affine2 == some v.point
    if !limbs || !nat then
      badPoints := badPoints + 1
      IO.println s!"DIFF hash_to_curve G2 msg {v.msg.length} chars: limb path {boolText limbs}, Nat path {boolText nat}"
  IO.println s!"RESULT blssig RFC 9380 J.10.1 BLS12381G2_XMD:SHA-256_SSWU_RO_ (u, Q0, Q1, P; limb path and Nat path): {Rfc9380.g2Vectors.size} messages, {if badPoints == 0 then "all agree" else s!"{badPoints} FAILURES"}"
  return bad + badPoints

/-! ### Differential run -/

def differential (scale : Nat) : IO (Nat × Array Signed) := do
  let dst := BLSSignature.consensusDst
  let count := 6 * scale
  let rs := randoms 1 (4 * count + 16)
  let mut signed : Array Signed := #[]
  for i in [0:count] do
    let k := 1 + rs.getD (4 * i) 1 % (r - 1)
    let msg := messageOf (rs.getD (4 * i + 1) 0) (messageLengths.getD (i % messageLengths.size) 32)
    signed := signed.push (makeSigned k msg dst)
  let infinityPk := Reference.compress1 none
  let infinitySig := Reference.compress2 none
  -- Hash to G2: limb path against the Nat path.
  let mut hash : Tally := {}
  for s in signed do
    let fast := (HashToCurve.hashToG2 dst s.msg).bind Rfc9380.affineNat
    let reference := Reference.affine2 s.hashed
    let same := fast == reference && fast.isSome
    hash ← hash.add "hash to G2" same true (some true) s!"msg {toHex s.msg}"
  hash.report "hash to G2, limb path against the Nat definition"
  -- Single verification.
  let mut single : Tally := {}
  let mut dec1 : Tally := {}
  let mut dec2 : Tally := {}
  for i in [0:count] do
    let some s := signed[i]? | continue
    let other := signed.getD ((i + 1) % count) s
    let v := rs.getD (4 * i + 2) 0
    let outside1 := Reference.compress1 (liftG1 (v % p))
    let outside2 := Reference.compress2 (Reference.affine2 (Reference.mapToCurve ⟨v % p, (v / 3) % p⟩))
    let otherScalar := Reference.compress2 (Reference.affine2 (Reference.testOnlyScalarMulG2 (s.scalar + 1) s.hashed))
    let tampered := flipByte s.sig (1 + v % 95) (UInt8.ofNat (1 + v / 97 % 255))
    let bigC0 := s.sig.extract 0 48 ++ natToBE 48 (p + v % 1000)
    let variants : Array (String × ByteArray × ByteArray × ByteArray × Option Bool) := #[
      ("valid", s.pk, s.msg, s.sig, some true),
      ("message with one more byte", s.pk, s.msg.push 1, s.sig, some false),
      ("key of another case", other.pk, s.msg, s.sig, if other.scalar == s.scalar then none else some false),
      ("negated signature", s.pk, s.msg, flipFlag s.sig 0x20, some false),
      ("signature of the next scalar", s.pk, s.msg, otherScalar, some false),
      ("tampered signature byte", s.pk, s.msg, tampered, none),
      ("signature outside the subgroup", s.pk, s.msg, outside2, none),
      ("infinity signature", s.pk, s.msg, infinitySig, some false),
      ("infinity key", infinityPk, s.msg, s.sig, some false),
      ("infinity key and signature", infinityPk, s.msg, infinitySig, some false),
      ("key outside the subgroup", outside1, s.msg, s.sig, none),
      ("negated key", flipFlag s.pk 0x20, s.msg, s.sig, some false),
      ("key of 47 bytes", s.pk.extract 0 47, s.msg, s.sig, some false),
      ("key of 49 bytes", s.pk.push 0, s.msg, s.sig, some false),
      ("signature of 95 bytes", s.pk, s.msg, s.sig.extract 0 95, some false),
      ("signature of 97 bytes", s.pk, s.msg, s.sig.push 0, some false),
      ("key without the compression flag", flipFlag s.pk 0x80, s.msg, s.sig, some false),
      ("signature without the compression flag", s.pk, s.msg, flipFlag s.sig 0x80, some false),
      ("signature with the infinity flag", s.pk, s.msg, flipFlag s.sig 0x40, some false),
      ("signature with x.c0 not below p", s.pk, s.msg, bigC0, some false)]
    for (label, pk, msg, sig, expected) in variants do
      let fast := BLSSignature.verify pk msg sig dst
      let reference := Reference.verify pk msg sig dst
      single ← single.add s!"verify, {label}" fast reference expected s!"pk {toHex pk} msg {toHex msg} sig {toHex sig}"
      let d1 := fastDecode1 pk
      let r1 := Reference.decodeG1 pk
      dec1 ← dec1.add s!"decode G1, {label}" (d1 == r1) true (some true) s!"{toHex pk}"
      let d2 := fastDecode2 sig
      let r2 := Reference.decodeG2 sig
      dec2 ← dec2.add s!"decode G2, {label}" (d2 == r2) true (some true) s!"{toHex sig}"
    -- The decoded points are the generated ones.
    dec1 ← dec1.add "decode G1, coordinates" (fastDecode1 s.pk == some (some s.key)) true (some true) (toHex s.pk)
    dec2 ← dec2.add "decode G2, coordinates" (fastDecode2 s.sig == some s.sigPoint) true (some true) (toHex s.sig)
  single.report "verify against the Nat reference (valid, wrong message, wrong key, negated, tampered, infinity, outside the subgroup, wrong length, flags)"
  -- More encodings for the decoders: pseudo-random strings with the compression flag.
  let more := randoms 2 (40 * scale)
  let mut onCurve1 := 0
  for v in more do
    let bytes := natToBE 48 (v % 2 ^ 382 + 2 ^ 383)
    let r1 := Reference.decodeG1 bytes
    dec1 ← dec1.add "decode G1, pseudo-random" (fastDecode1 bytes == r1) true (some true) (toHex bytes)
    let lifted := Reference.compress1 (liftG1 (v % p))
    if (liftG1 (v % p)).isSome then onCurve1 := onCurve1 + 1
    dec1 ← dec1.add "decode G1, curve point" (fastDecode1 lifted == Reference.decodeG1 lifted) true (some true) (toHex lifted)
  for v in more.extract 0 (8 * scale) do
    let bytes := natToBE 48 (v % 2 ^ 382 + 2 ^ 383) ++ natToBE 48 (walk v % 2 ^ 381)
    dec2 ← dec2.add "decode G2, pseudo-random" (fastDecode2 bytes == Reference.decodeG2 bytes) true (some true) (toHex bytes)
  dec1.report s!"G1 decompression with subgroup check against KZG.decompressG1 ({onCurve1} lifted curve points)"
  dec2.report "G2 decompression with subgroup check against the Nat definition"
  -- Aggregates.
  let mut agg : Tally := {}
  let mut keys : Tally := {}
  let sizes : Array Nat := #[1, 2, 3, 5, 8]
  for round in [0:scale] do
    for n in sizes do
      let start := (round * 7 + n) % count
      let group : Array Signed := (Array.range n).map fun j => signed.getD ((start + j) % count) default
      let pks := group.map (·.pk)
      let msgs := group.map (·.msg)
      let common := messageOf (round * 100 + n) 32
      let hashed := (Reference.hashToG2 dst common).getD (Curve.infinity field2)
      let total := group.foldl (fun acc s => (acc + s.scalar) % r) 0
      let commonSig := Reference.compress2 (Reference.affine2 (Reference.testOnlyScalarMulG2 total hashed))
      let sumSig := Reference.compress2 (Reference.affine2
        (group.foldl (fun acc s =>
          match s.sigPoint with
          | some point => Curve.add field2 acc (Curve.ofAffine field2 point.1 point.2)
          | none => acc) (Curve.infinity field2)))
      let fastCases : Array (String × Array ByteArray × ByteArray × ByteArray × Option Bool) := #[
        ("valid", pks, common, commonSig, some true),
        ("wrong message", pks, common.push 7, commonSig, some false),
        ("one key missing", pks.extract 0 (n - 1), common, commonSig, some false),
        ("one key twice", pks.push (pks.getD 0 infinityPk), common, commonSig, some false),
        ("with the infinity key", pks.push infinityPk, common, commonSig, some false),
        ("with a key of 47 bytes", pks.push ((pks.getD 0 infinityPk).extract 0 47), common, commonSig, some false),
        ("infinity signature", pks, common, infinitySig, some false),
        ("key and its negation", #[pks.getD 0 infinityPk, flipFlag (pks.getD 0 infinityPk) 0x20], common, infinitySig, some false),
        ("no keys, infinity signature", #[], common, infinitySig, some false),
        ("no keys, other signature", #[], common, commonSig, some false)]
      for (label, ks, msg, sig, expected) in fastCases do
        agg ← agg.add s!"fastAggregateVerify {n} keys, {label}" (BLSSignature.fastAggregateVerify ks msg sig dst)
          (Reference.fastAggregateVerify ks msg sig dst) expected s!"sig {toHex sig}"
        let ethExpected := if label == "no keys, infinity signature" then some true else expected
        agg ← agg.add s!"ethFastAggregateVerify {n} keys, {label}" (BLSSignature.ethFastAggregateVerify ks msg sig dst)
          (Reference.ethFastAggregateVerify ks msg sig dst) ethExpected s!"sig {toHex sig}"
        let fastKeys := (BLSSignature.aggregatePublicKeys ks).map toHex
        let referenceKeys := (Reference.aggregatePublicKeys ks).map toHex
        keys ← keys.add s!"aggregatePublicKeys {n} keys, {label}" (fastKeys == referenceKeys) true (some true)
          s!"fast {fastKeys.getD "none"} reference {referenceKeys.getD "none"}"
      let rotated := (Array.range n).map fun j => msgs.getD ((j + 1) % n) ByteArray.empty
      let distinct := (Array.range n).any fun j => (msgs.getD j ByteArray.empty).data != (rotated.getD j ByteArray.empty).data
      let aggCases : Array (String × Array ByteArray × Array ByteArray × ByteArray × Option Bool) := #[
        ("valid", pks, msgs, sumSig, some true),
        ("messages rotated", pks, rotated, sumSig, if distinct then some false else none),
        ("one message missing", pks, msgs.extract 0 (n - 1), sumSig, some false),
        ("one pair missing", pks.extract 0 (n - 1), msgs.extract 0 (n - 1), sumSig, some false),
        ("with the infinity key", pks.push infinityPk, msgs.push common, sumSig, some false),
        ("signature of the common message", pks, msgs, commonSig, none),
        ("infinity signature", pks, msgs, infinitySig, some false),
        ("signature of 95 bytes", pks, msgs, sumSig.extract 0 95, some false),
        ("no keys", #[], #[], infinitySig, some false)]
      for (label, ks, ms, sig, expected) in aggCases do
        agg ← agg.add s!"aggregateVerify {n} keys, {label}" (BLSSignature.aggregateVerify ks ms sig dst)
          (Reference.aggregateVerify ks ms sig dst) expected s!"sig {toHex sig}"
  agg.report "fastAggregateVerify, ethFastAggregateVerify and aggregateVerify against the Nat reference"
  keys.report "aggregatePublicKeys against the Nat reference"
  let enough : Bool :=
    decide (single.accepted ≥ count) && decide (agg.accepted ≥ 3 * sizes.size * scale) && decide (dec1.cases > 50 * scale)
  if !enough then IO.println "RESULT blssig differential: too few accepted cases, FAILURES"
  return (hash.bad + single.bad + dec1.bad + dec2.bad + agg.bad + keys.bad + (if enough then 0 else 1), signed)

/-! ### Timing -/

@[noinline] def force (run : Unit → Nat) : IO Nat := pure (run ())

def micros (ns : Nat) : String :=
  let tenths := ns / 100
  s!"{tenths / 10}.{tenths % 10}"

/-- Time `run` on every input `reps` times; every sample is kept. -/
def timeEach {α : Type} (label : String) (reps : Nat) (inputs : Array α) (run : α → Nat) : IO Nat := do
  let mut samples : Array Nat := #[]
  let mut digest := 0
  for input in inputs do
    for _ in [0:reps] do
      let t0 ← IO.monoNanosNow
      let value ← force fun _ => run input
      let t1 ← IO.monoNanosNow
      samples := samples.push (t1 - t0)
      digest := digest + value
  let sorted := samples.qsort (· < ·)
  let nth (percent : Nat) : Nat := sorted.getD ((sorted.size - 1) * percent / 100) 0
  IO.println s!"TIMING blssig {label}: p50 {micros (nth 50)} us, p95 {micros (nth 95)} us, p99 {micros (nth 99)} us, max {micros (nth 100)} us (n={sorted.size}, check {digest % 1000003})"
  return nth 50

def bit (b : Bool) : Nat := if b then 1 else 0

structure Prepared where
  pk : ByteArray
  msg : ByteArray
  sig : ByteArray
  key : BLSSignature.PublicKey
  signature : BLSSignature.Signature
  hashed : JPoint (Q2 U384)

def prepare (s : Signed) (dst : ByteArray) : Option Prepared :=
  match BLSSignature.decodePublicKey s.pk, BLSSignature.decodeSignature s.sig, HashToCurve.hashToG2 dst s.msg with
  | some key, some signature, some hashed => some { pk := s.pk, msg := s.msg, sig := s.sig, key, signature, hashed }
  | _, _, _ => none

def timings (signed : Array Signed) (scale : Nat) : IO Unit := do
  let dst := BLSSignature.consensusDst
  let inputs := signed.filterMap fun s => prepare s dst
  let reps := 5
  IO.println s!"TIMING blssig: {inputs.size} generated signatures, {reps} runs each; all samples kept; times in microseconds"
  let pkTime ← timeEach "decodePublicKey (48 bytes: square root, subgroup check)" reps inputs fun c =>
    match BLSSignature.decodePublicKey c.pk with
    | some key => key.y.l0.toNat % 7 + 1
    | none => 0
  let sigTime ← timeEach "decodeSignature (96 bytes: Fp2 square root, subgroup check)" reps inputs fun c =>
    match BLSSignature.decodeSignature c.sig with
    | some ⟨some point⟩ => point.2.c1.l0.toNat % 7 + 1
    | _ => 0
  let hashTime ← timeEach "hashToG2 (expand, 2 maps, isogenies, add, clear cofactor)" reps inputs fun c =>
    match HashToCurve.hashToG2 dst c.msg with
    | some point => point.z.c0.l0.toNat % 7 + 1
    | none => 0
  let _ ← timeEach "expandMessageXmd 256 bytes + reduction to 2 Fp2 elements" reps inputs fun c =>
    match HashToCurve.hashToFieldFp2 dst c.msg with
    | some u => u.2.c1 % 7 + 1
    | none => 0
  let pairTime ← timeEach "verifyPoints (affine conversion, 2 Miller loops shared, final exponentiation)" reps inputs fun c =>
    bit (BLSSignature.verifyPoints c.key c.hashed c.signature)
  let decodedTime ← timeEach "verifyDecoded (hash + pairing; for callers with cached keys)" reps inputs fun c =>
    bit (BLSSignature.verifyDecoded c.key c.msg c.signature dst)
  let fullTime ← timeEach "verify (all of it, from bytes)" reps inputs fun c =>
    bit (BLSSignature.verify c.pk c.msg c.sig dst)
  let few := inputs.extract 0 (min inputs.size (2 + scale))
  let oldTime ← timeEach "OLD Nat reference verify (definitional subgroup checks, Nat map, Nat pairing)" 1 few fun c =>
    bit (Reference.verify c.pk c.msg c.sig dst)
  let oldHash ← timeEach "OLD Nat hash to G2" 1 few fun c =>
    match Reference.hashToG2 dst c.msg with
    | some point => point.z.c0 % 7 + 1
    | none => 0
  IO.println s!"TIMING blssig split at p50 (us): decode key {micros pkTime} + decode signature {micros sigTime} + hash to G2 {micros hashTime} + pairing {micros pairTime} = {micros (pkTime + sigTime + hashTime + pairTime)}; verify measured {micros fullTime}; verifyDecoded {micros decodedTime}; old Nat verify {micros oldTime}, old Nat hash {micros oldHash}; old/new {oldTime / (fullTime + 1)}x"
  -- Aggregates: many keys for one message.
  let common := messageOf 4242 32
  let hashed := (Reference.hashToG2 dst common).getD (Curve.infinity field2)
  for n in #[64, 512] do
    let scalars := (randoms (1000 + n) n).map fun v => 1 + v % (r - 1)
    let pks := scalars.map fun k => Reference.compress1 (Reference.testOnlyKeyPoint k)
    let total := scalars.foldl (fun acc k => (acc + k) % r) 0
    let sig := Reference.compress2 (Reference.affine2 (Reference.testOnlyScalarMulG2 total hashed))
    let valid := BLSSignature.fastAggregateVerify pks common sig dst
    IO.println s!"RESULT blssig fastAggregateVerify with {n} generated keys: {if valid then "accepted" else "REJECTED, FAILURES"}"
    let _ ← timeEach s!"fastAggregateVerify, {n} keys from bytes (each key decoded and checked)" 3 #[pks] fun ks =>
      bit (BLSSignature.fastAggregateVerify ks common sig dst)
    match BLSSignature.decodePublicKeys pks, BLSSignature.decodeSignature sig with
    | some keys, some signature =>
      let _ ← timeEach s!"fastAggregateVerifyDecoded, {n} decoded keys" 5 #[keys] fun ks =>
        bit (BLSSignature.fastAggregateVerifyDecoded ks common signature dst)
      let _ ← timeEach s!"aggregateDecoded (sum of {n} decoded keys, one inversion)" 5 #[keys] fun ks =>
        match BLSSignature.aggregateDecoded ks with
        | some key => key.x.l0.toNat % 7 + 1
        | none => 0
      pure ()
    | _, _ => IO.println "RESULT blssig aggregate timing: keys did not decode, FAILURES"
  let eight := inputs.extract 0 8
  let _ ← timeEach "aggregateVerifyDecoded, 8 keys and 8 messages (verdict false: unrelated signature)" 3 #[eight] fun cs =>
    bit (BLSSignature.aggregateVerifyDecoded (cs.map (·.key)) (cs.map (·.msg))
      ((cs[0]?.map (·.signature)).getD ⟨none⟩) dst)
  pure ()

/-! ### Published vectors and the command line -/

def stripPrefix (s : String) : String :=
  match s.toList with
  | '0' :: 'x' :: rest => String.ofList rest
  | _ => s

def hexArg (s : String) : Option ByteArray :=
  if s == "-" then some ByteArray.empty else ofHex? (stripPrefix s)

def listArg (s : String) : Option (Array ByteArray) :=
  if s == "-" then some #[] else ((s.splitOn ",").mapM hexArg).map List.toArray

def need (s : String) : Except String ByteArray :=
  match hexArg s with
  | some bytes => .ok bytes
  | none => .error s!"not hexadecimal: {s}"

def needList (s : String) : Except String (Array ByteArray) :=
  match listArg s with
  | some list => .ok list
  | none => .error s!"not a list of hexadecimal strings: {s}"

/-- The answer of this implementation for one vector line, as the text the line expects. -/
def answer (suite : String) (args : List String) : Except String String := do
  let dst := BLSSignature.consensusDst
  match suite, args with
  | "verify", [pk, msg, sig] =>
    return boolText (BLSSignature.verify (← need pk) (← need msg) (← need sig) dst)
  | "aggregate_verify", [pks, msgs, sig] =>
    return boolText (BLSSignature.aggregateVerify (← needList pks) (← needList msgs) (← need sig) dst)
  | "fast_aggregate_verify", [pks, msg, sig] =>
    return boolText (BLSSignature.fastAggregateVerify (← needList pks) (← need msg) (← need sig) dst)
  | "eth_fast_aggregate_verify", [pks, msg, sig] =>
    return boolText (BLSSignature.ethFastAggregateVerify (← needList pks) (← need msg) (← need sig) dst)
  | "eth_aggregate_pubkeys", [pks] =>
    return ((BLSSignature.aggregatePublicKeys (← needList pks)).map toHex).getD "null"
  | "deserialization_G1", [bytes] =>
    return boolText (BLSSignature.decompressG1 (← need bytes)).isSome
  | "deserialization_G2", [bytes] =>
    return boolText (BLSSignature.decompressG2 (← need bytes)).isSome
  | "hash_to_G2", [tag, msg] =>
    match (HashToCurve.hashToG2 (← need tag) (← need msg)).bind Rfc9380.affineNat with
    | some (x, y) =>
      return s!"{toHex (natToBE 48 x.c0)},{toHex (natToBE 48 x.c1)},{toHex (natToBE 48 y.c0)},{toHex (natToBE 48 y.c1)}"
    | none => return "none"
  | _, _ => throw s!"unknown suite or wrong number of arguments: {suite}"

def runVectors (path : String) : IO UInt32 := do
  let lines ← IO.FS.lines path
  let mut total := 0
  let mut bad := 0
  let mut suites : List (String × Nat) := []
  for line in lines do
    match (line.splitOn " ").filter (· ≠ "") with
    | [] => pure ()
    | suite :: name :: expected :: args =>
      total := total + 1
      suites := match suites.find? (·.1 == suite) with
        | some _ => suites.map fun entry => if entry.1 == suite then (entry.1, entry.2 + 1) else entry
        | none => suites ++ [(suite, 1)]
      match answer suite args with
      | .ok got =>
        if got != expected then
          bad := bad + 1
          IO.println s!"MISMATCH {suite} {name}: expected {expected}, got {got}"
      | .error message =>
        bad := bad + 1
        IO.println s!"MISMATCH {suite} {name}: {message}"
    | _ =>
      bad := bad + 1
      IO.println s!"MISMATCH malformed line: {line}"
  let bySuite := ", ".intercalate (suites.map fun entry => s!"{entry.1} {entry.2}")
  IO.println s!"RESULT blssig vectors: {total} cases, {bad} mismatches ({bySuite})"
  return if bad == 0 && decide (total > 0) then 0 else 1

/-- `true`, `false`, `invalid` (the key or the signature does not decode) or `badhex`. -/
def verdict (pk msg sig : String) : String :=
  match hexArg pk, hexArg msg, hexArg sig with
  | some pk, some msg, some sig =>
    match BLSSignature.decodePublicKey pk, BLSSignature.decodeSignature sig with
    | some key, some signature => boolText (BLSSignature.verifyDecoded key msg signature)
    | _, _ => "invalid"
  | _, _, _ => "badhex"

def runCheck (scale : Nat) : IO UInt32 := do
  let rfcBad ← rfcChecks
  let (bad, signed) ← differential scale
  timings signed scale
  if rfcBad + bad == 0 then
    IO.println "RESULT blssig: RFC 9380 vectors and all differential checks agree"
    return 0
  else
    IO.println s!"RESULT blssig: {rfcBad + bad} FAILURES"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--verify", pk, msg, sig] =>
    IO.println (verdict pk msg sig)
    return 0
  | ["--verify-file", path] =>
    let lines ← IO.FS.lines path
    for line in lines do
      match (line.splitOn " ").filter (· ≠ "") with
      | [pk, msg, sig] => IO.println (verdict pk msg sig)
      | [] => pure ()
      | _ => IO.println "badline"
    return 0
  | ["--vectors", path] => runVectors path
  | [] => runCheck 2
  | ["--check"] => runCheck 2
  | ["--check", scale] =>
    match scale.toNat? with
    | some n => runCheck (max n 1)
    | none => IO.eprintln "SCALE is not a number"; return 2
  | _ =>
    IO.eprintln "usage: evm-blssig [--check [SCALE] | --vectors FILE | --verify PKHEX MSGHEX SIGHEX | --verify-file FILE]"
    return 2

end EVMCleanroom.BLSSig

def main (args : List String) : IO UInt32 := EVMCleanroom.BLSSig.main args
