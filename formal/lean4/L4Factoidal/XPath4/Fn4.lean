/-
L4Factoidal.XPath4.Fn4 — F&O 4.0 functions added after Stage 2:
`fn:hash` (§5.3.18).

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

def fn4Table : List (String × LibFn) := [("hash", hashFn)]

end L4Factoidal.XPath4
