/-
L4Factoidal.XPath4.Fn4 — F&O 4.0 functions added after Stage 2:
`fn:hash` (§5.3.18), `fn:random-number-generator` (§5.13.2).

Spec: F&O 4.0 editor's draft (read 2026-10-28).
-/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.Crypto.MD5
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.Blake3
import L4Factoidal.Codec.Crc32

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-! ## `fn:hash` (§5.3.18) -/

def hexBinaryOf (b : ByteArray) : Atomic := ⟨.b .hexBinary, .x (.bin true (b.toList.map (·.toNat)))⟩

def be32 (x : UInt32) : ByteArray :=
  ByteArray.mk #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The algorithms of §5.3.18, by their effective name
    (`upper-case(normalize-space($algorithm))`). -/
def hashBytes (alg : String) (b : ByteArray) : Option ByteArray :=
  match alg with
  | "MD5" => some (Crypto.md5 b)
  | "SHA-1" => some (Crypto.sha1 b)
  | "SHA-256" => some (Crypto.sha256 b)
  | "BLAKE3" => some (Crypto.Blake3.hash b)
  | "CRC-32" => some (be32 (Codec.crc32 b))
  | _ => none

def hashFn : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    let bytes := match bytesOfAtomic v with
      | some b => b
      | none => v.str.toUTF8
    let alg := if (argN a 1).isEmpty then "MD5" else (normSpace (strOf (argN a 1))).toUpper
    match hashBytes alg bytes with
    | some h => pure [.atom (hexBinaryOf h)]
    | none => err "FOHA0001" ("unsupported hash algorithm " ++ alg)

/-! ## `fn:random-number-generator` (§5.13.2)

The generator is SplitMix64 (Steele, Lea, Flood, "Fast splittable
pseudorandom number generators", OOPSLA 2014) over a 64-bit state. The
state of a seeded generator is the FNV-1a 64-bit hash of the seed's type
name and string value; with no seed it is a fixed constant, so that two
calls in one evaluation give the same sequence (the spec allows it: the
seed is then implementation-dependent, and fixed within an execution
scope). `number` is the top 53 bits of the output over 2^53; `next`
advances the state; `permute` is Fisher-Yates driven by successive
numbers; `take(n)` is the first n numbers. The three functions are
inline function items (so they have the record's function types) over
the internal entries `rng-record#`, `rng-permute#`, `rng-take#` of the
catalog. -/

def golden : UInt64 := 0x9E3779B97F4A7C15

def splitmix (s : UInt64) : UInt64 :=
  let z := s + golden
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001B3) 0xCBF29CE484222325

def rngNumber (s : UInt64) : Float := (splitmix s >>> 11).toFloat / 9007199254740992.0

def rngNext (s : UInt64) : UInt64 := s + golden

def rngQ (l : String) : QN := { uri := nsFN, loc := l }

def rngRecord (s : UInt64) : Item :=
  let st : Expr := .lit (Atomic.ofInt s.toNat)
  let vIn : QN := { uri := "", loc := "input" }
  let vN : QN := { uri := "", loc := "count" }
  .map [
    (Atomic.ofStr "number", [.atom (Atomic.ofDbl (rngNumber s))]),
    (Atomic.ofStr "next", [.fn (.inline [] (parseTy "map(xs:string, item())")
      (.call (rngQ "rng-record#") [some (.lit (Atomic.ofInt (rngNext s).toNat))] []) false [])]),
    (Atomic.ofStr "permute", [.fn (.inline [(vIn, parseTy "item()*")] (parseTy "item()*")
      (.call (rngQ "rng-permute#") [some st, some (.var vIn)] []) false [])]),
    (Atomic.ofStr "take", [.fn (.inline [(vN, parseTy "xs:nonNegativeInteger")] (parseTy "xs:double*")
      (.call (rngQ "rng-take#") [some st, some (.var vN)] []) false [])])]

def rngFn : LibFn := fun _ _ a =>
  match optAtom (argN a 0) with
  | none => pure [rngRecord 0x2545F4914F6CDD1D]
  | some v => pure [rngRecord (fnv1a (v.ty.name ++ ":" ++ v.str))]

def stateOf (s : Seq) : UInt64 := (intOf s).toNat.toUInt64

def rngRecordFn : LibFn := fun _ _ a => pure [rngRecord (stateOf (argN a 0))]

def rngPermuteFn : LibFn := fun _ _ a => do
  let xs := (argN a 1).toArray
  let mut arr := xs
  let mut s := stateOf (argN a 0)
  let n := arr.size
  for k in [0:n] do
    let i := n - 1 - k
    if i == 0 then break
    let j := ((splitmix s >>> 11).toNat * (i + 1)) / 9007199254740992
    s := rngNext s
    let xi := arr[i]!
    arr := (arr.set! i arr[j]!).set! j xi
  pure arr.toList

def rngTakeFn : LibFn := fun _ _ a => do
  let n := (intOf (argN a 1)).toNat
  let mut s := stateOf (argN a 0)
  let mut out : Array Item := #[]
  for _ in [0:n] do
    out := out.push (.atom (Atomic.ofDbl (rngNumber s)))
    s := rngNext s
  pure out.toList

def fn4Table : List (String × LibFn) :=
  [("hash", hashFn), ("random-number-generator", rngFn), ("rng-record#", rngRecordFn),
   ("rng-permute#", rngPermuteFn), ("rng-take#", rngTakeFn)]

end L4Factoidal.XPath4
