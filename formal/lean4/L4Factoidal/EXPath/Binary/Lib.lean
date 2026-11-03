/-
L4Factoidal.EXPath.Binary.Lib — the `bin:` functions of the EXPath
Binary Module 4.0 as an XPath 4.0 function library
(`XPath4.LibFn`), with the error codes of the specification.

Every implementation receives its arguments already coerced to the
signature of `EXPath.Catalog` (applied by `XPath4.Eval`), so a binary
argument is an `xs:hexBinary` or `xs:base64Binary` value, an
`xs:integer` argument is an integer, and the `$order` argument has
already passed the `enum(...)` test (a wrong value is `XPTY0004`, as
the 4.0 specification says; § Octet order).

Errors are raised with the expanded QName `Q{http://expath.org/ns/binary}local`
as the error code.
-/
import L4Factoidal.XPath4.Lib
import L4Factoidal.EXPath.Binary.Octets
import L4Factoidal.EXPath.Binary.Text
import L4Factoidal.JOSE.Base64Url

namespace L4Factoidal.EXPath.Binary

open L4Factoidal.XPath4
open L4Factoidal.XSD

def nsBIN : String := "http://expath.org/ns/binary"

/-- A dynamic error with a code in the binary namespace. -/
def binErr {α} (local_ : String) (msg : String := "") : M α :=
  err ("Q{" ++ nsBIN ++ "}" ++ local_) msg

/-! ## Values -/

/-- The octets of a binary argument (`none`: the empty sequence). -/
def binArg (s : Seq) : Option (List Nat) :=
  match s with
  | [.atom ⟨_, .x (.bin _ bs)⟩] => some bs
  | _ => none

/-- A result of type `xs:base64Binary`. -/
def b64 (bs : List Nat) : Seq := [.atom ⟨.b .base64Binary, .x (.bin false bs)⟩]

def optB64 (r : Option (List Nat)) : Seq := match r with | some bs => b64 bs | none => []

/-- An optional integer argument. -/
def optInt (s : Seq) : Option Int := (optAtom s).map (fun _ => intOf s)

def littleArg (s : Seq) : Bool := match optAtom s with | some a => isLittle a.str | none => false

/-! ## Checks shared by several functions -/

def checkOffset (len : Nat) (off : Int) : M Nat :=
  if off < 0 || off > len then binErr "index-out-of-range" s!"offset {off} is outside 0..{len}"
  else pure off.toNat

def checkSize (sz : Int) : M Nat :=
  if sz < 0 then binErr "negative-size" s!"size {sz} is negative" else pure sz.toNat

/-- `bin:part($value, $offset, $size)` with its checks. -/
def partChecked (bs : List Nat) (off : Int) (size : Option Int) : M (List Nat) := do
  let o ← checkOffset bs.length off
  match size with
  | none => pure (bs.drop o)
  | some sz =>
    let n ← checkSize sz
    if o + n > bs.length then binErr "index-out-of-range" s!"offset {o} + size {n} exceeds {bs.length}"
    else pure (part bs o n)

/-! ## The functions -/

def fToOctets : LibFn := fun _ _ a =>
  pure (((binArg (argN a 0)).getD []).map (fun (b : Nat) => Item.atom ⟨.b .unsignedByte, .int (Int.ofNat b)⟩))

def fFromOctets : LibFn := fun _ _ a =>
  pure (b64 ((argN a 0).map (fun i => match i with | .atom ⟨_, .int v⟩ => v.toNat | _ => 0)))

def fToBase64url : LibFn := fun _ _ a =>
  match binArg (argN a 0) with
  | none => pure []
  | some bs => pure (sStr (String.ofList (JOSE.Base64Url.encodeChars (bs.map UInt8.ofNat))))

/-- bin:from-base64url on a string: strip whitespace and trailing `=`,
then decode with the RFC 4648 §5 alphabet. -/
def fromBase64url? (s : String) : Option (List Nat) :=
  let cs := s.toList.filter (fun c => !(c == ' ' || c == '\t' || c == '\n' || c == '\r'))
  let cs := (cs.reverse.dropWhile (· == '=')).reverse
  (JOSE.Base64Url.decodeChars cs).map (·.map UInt8.toNat)

def fFromBase64url : LibFn := fun _ _ a =>
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    match fromBase64url? v.str with
    | some bs => pure (b64 bs)
    | none => binErr "conversion-error" "not a base64url string"

def numCtor (f : String → Option (List Nat)) (what : String) : LibFn := fun _ _ a =>
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    match f v.str with
    | some bs => pure (b64 bs)
    | none => binErr "non-numeric-character" ("not a " ++ what ++ " string: " ++ v.str)

def fPart : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs => pure (b64 (← partChecked bs (intOf (argN a 1)) (optInt (argN a 2))))

def fInsertBefore : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs =>
    let o ← checkOffset bs.length (intOf (argN a 1))
    match binArg (argN a 2) with
    | none => pure (b64 bs)
    | some ex => pure (b64 (insertBefore bs o ex))

def fLength : LibFn := fun _ _ a =>
  pure (sInt ((binArg (argN a 0)).getD []).length)

def fJoin : LibFn := fun _ _ a =>
  pure (b64 ((argN a 0).flatMap (fun i => (binArg [i]).getD [])))

def fPad (left : Bool) : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs =>
    let n ← checkSize (intOf (argN a 1))
    let o := match optAtom (argN a 2) with | some _ => (intOf (argN a 2)).toNat | none => 0
    let pad := List.replicate n o
    pure (b64 (if left then pad ++ bs else bs ++ pad))

def fFind : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs =>
    let o ← checkOffset bs.length (intOf (argN a 1))
    let pat := (binArg (argN a 2)).getD []
    match findFrom bs pat o with
    | some p => pure (sInt p)
    | none => pure []

def encodingRecord (name : String) (off : Nat) : Seq :=
  [.map [(Atomic.ofStr "encoding", sStr name), (Atomic.ofStr "offset", sInt off)]]

def fInferEncoding : LibFn := fun _ _ a => do
  let bs := (binArg (argN a 0)).getD []
  let enc := (optAtom (argN a 1)).map Atomic.str
  match inferEncoding bs enc with
  | some (n, o) => pure (encodingRecord n o)
  | none => binErr "unknown-encoding" ("encoding not supported: " ++ enc.getD "")

/-- Decode octets with the rules of bin:decode-string (after the
optional part): infer the encoding, skip a byte order mark, decode;
a character that is not an XML character is a conversion error. -/
def decodeOctets (bs : List Nat) (enc : Option String) : M String := do
  match inferEncoding bs enc with
  | none => binErr "unknown-encoding" ("encoding not supported: " ++ enc.getD "")
  | some (n, o) =>
    match encOfName? n with
    | none => binErr "unknown-encoding" ("encoding not supported: " ++ n)
    | some e =>
      match decodeWith e (bs.drop o) with
      | none => binErr "conversion-error" ("the octets are not valid " ++ n)
      | some s =>
        if s.toList.all (fun c => XML.isXmlChar c) then pure s
        else binErr "conversion-error" "the decoded text contains a character that is not allowed in XML"

def fDecodeString : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs =>
    let off := optInt (argN a 2)
    let sz := optInt (argN a 3)
    let eff ← if off.isSome || sz.isSome then partChecked bs (off.getD 0) sz else pure bs
    pure (sStr (← decodeOctets eff ((optAtom (argN a 1)).map Atomic.str)))

def fEncodeString : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    let name := match optAtom (argN a 1) with | some e => e.str | none => "UTF-8"
    match encOfName? name with
    | none => binErr "unknown-encoding" ("encoding not supported: " ++ name)
    | some e =>
      match encodeWith e v.str with
      | some bs => pure (b64 bs)
      | none => binErr "conversion-error" ("a character cannot be written in " ++ name)

def fPackInteger : LibFn := fun _ _ a => do
  let v := intOf (argN a 0)
  let n ← checkSize (intOf (argN a 1))
  pure (b64 (orderBytes (littleArg (argN a 2)) (packBEAcc n (twosComplement n v) [])))

/-- The largest integer unpacked, in octets (implementation-defined,
Binary 4.0 § Integer representation): xs:integer here is unbounded,
so the limit only bounds the work. -/
def maxIntOctets : Nat := 1 <<< 20

def unpackInt (signed : Bool) : LibFn := fun _ _ a => do
  let bs := (binArg (argN a 0)).getD []
  let sz ← checkSize (intOf (argN a 2))
  let p ← partChecked bs (intOf (argN a 1)) (some sz)
  if sz > maxIntOctets then binErr "integer-too-large" s!"{sz} octets" else
  let u := beValue (orderBytes (littleArg (argN a 3)) p)
  pure (sInt (if signed then signedOf sz u else u))

def fUnpackDouble : LibFn := fun _ _ a => do
  let bs := (binArg (argN a 0)).getD []
  let p ← partChecked bs (intOf (argN a 1)) (some 8)
  let bits := beValue (orderBytes (littleArg (argN a 2)) p)
  pure (single (Atomic.ofDbl (Float.ofBits (UInt64.ofNat bits))))

def fUnpackFloat : LibFn := fun _ _ a => do
  let bs := (binArg (argN a 0)).getD []
  let p ← partChecked bs (intOf (argN a 1)) (some 4)
  let bits := beValue (orderBytes (littleArg (argN a 2)) p)
  pure (single (Atomic.ofFlt (Float32.ofBits (UInt32.ofNat bits)).toFloat))

/-- The bits of a double; NaN is the quiet NaN `0x7FF8000000000000`
(Binary 4.0 § Representation of floating point numbers). -/
def doubleBits (f : Float) : Nat :=
  if f.isNaN then 0x7FF8000000000000 else f.toBits.toNat

def floatBits (f : Float) : Nat :=
  if f.isNaN then 0x7FC00000 else f.toFloat32.toBits.toNat

def numOf (s : Seq) : Float :=
  match optAtom s with
  | some ⟨_, .dbl f⟩ => f
  | _ => numFloat s

def fPackDouble : LibFn := fun _ _ a =>
  pure (b64 (orderBytes (littleArg (argN a 1)) (packBEAcc 8 (doubleBits (numOf (argN a 0))) [])))

def fPackFloat : LibFn := fun _ _ a =>
  pure (b64 (orderBytes (littleArg (argN a 1)) (packBEAcc 4 (floatBits (numOf (argN a 0))) [])))

def bitwise (f : Nat → Nat → Nat) : LibFn := fun _ _ a => do
  match binArg (argN a 0), binArg (argN a 1) with
  | some x, some y =>
    if x.length != y.length then binErr "differing-length-arguments" s!"lengths {x.length} and {y.length}"
    else pure (b64 (List.zipWith f x y))
  | _, _ => pure []

def fNot : LibFn := fun _ _ a =>
  pure (optB64 ((binArg (argN a 0)).map (·.map octetNot)))

def fShift : LibFn := fun _ _ a =>
  pure (optB64 ((binArg (argN a 0)).map (fun bs => shiftBits bs (intOf (argN a 1)))))

def fRotate : LibFn := fun _ _ a =>
  pure (optB64 ((binArg (argN a 0)).map (fun bs => rotateBits bs (intOf (argN a 1)))))

def checkBit (bs : List Nat) (i : Int) : M Nat :=
  if i < 0 || i ≥ 8 * bs.length then binErr "index-out-of-range" s!"bit index {i} is outside 0..{8 * bs.length - 1}"
  else pure i.toNat

def fIsBitSet : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs => pure (sBool (bitSet bs (← checkBit bs (intOf (argN a 1)))))

def fSetBits : LibFn := fun _ _ a => do
  match binArg (argN a 0) with
  | none => pure []
  | some bs =>
    let b := boolOf (argN a 2)
    let mut r := bs
    for i in argN a 1 do
      let k ← checkBit bs (intOf [i])
      r := setBit r k b
    pure (b64 r)

def fCountBitsSet : LibFn := fun _ _ a =>
  pure (match binArg (argN a 0) with | some bs => sInt (countBits bs) | none => [])

/-- The `bin:` functions, by local name. -/
def binTable : List (String × LibFn) := [
  ("to-octets", fToOctets), ("from-octets", fFromOctets),
  ("to-base64url", fToBase64url), ("from-base64url", fFromBase64url),
  ("hex", numCtor ofHex "hexadecimal"), ("bin", numCtor ofBin "binary"),
  ("octal", numCtor ofOctal "octal"),
  ("part", fPart), ("insert-before", fInsertBefore), ("length", fLength),
  ("join", fJoin), ("pad-left", fPad true), ("pad-right", fPad false), ("find", fFind),
  ("infer-encoding", fInferEncoding), ("decode-string", fDecodeString),
  ("encode-string", fEncodeString),
  ("pack-integer", fPackInteger), ("unpack-integer", unpackInt true),
  ("unpack-unsigned-integer", unpackInt false),
  ("unpack-double", fUnpackDouble), ("unpack-float", fUnpackFloat),
  ("pack-double", fPackDouble), ("pack-float", fPackFloat),
  ("or", bitwise octetOr), ("xor", bitwise octetXor), ("and", bitwise octetAnd),
  ("not", fNot), ("shift", fShift), ("rotate", fRotate),
  ("is-bit-set", fIsBitSet), ("set-bits", fSetBits), ("count-bits-set", fCountBitsSet)
]

end L4Factoidal.EXPath.Binary
