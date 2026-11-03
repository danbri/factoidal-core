/-
L4Factoidal.WHATWG.URL.PercentEncode — percent-encoded bytes of the WHATWG URL
Standard (section 1.3 "Percent-encoded bytes"), over the Encoding Standard
encoders of `L4Factoidal.WHATWG.Encoding.Core`.

Specification: **URL Standard**, WHATWG Living Standard (section names as in
https://url.spec.whatwg.org/ on 2026-10-29). This module has the percent-encode
sets and "percent-encode after encoding", the step that the URL parser's query
state and the application/x-www-form-urlencoded serializer use with a legacy
encoding. The URL parser itself is milestone 3 of
https://github.com/danbri/factoidal/issues/1167.

No `partial`, no `sorry`.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.WHATWG.URL

open L4Factoidal.WHATWG.Encoding

/-- The percent-encode sets of section 1.3. Each set includes the ones it is
defined from. -/
inductive PercentEncodeSet where
  | c0control | fragment | query | specialQuery | path | userinfo | component
  | formUrlencoded
  deriving DecidableEq, Repr, Inhabited

def inC0control (c : Nat) : Bool := c ≤ 0x1F || c > 0x7E
def inFragment (c : Nat) : Bool :=
  inC0control c || c == 0x20 || c == 0x22 || c == 0x3C || c == 0x3E || c == 0x60
def inQuery (c : Nat) : Bool :=
  inC0control c || c == 0x20 || c == 0x22 || c == 0x23 || c == 0x3C || c == 0x3E
def inSpecialQuery (c : Nat) : Bool := inQuery c || c == 0x27
def inPath (c : Nat) : Bool :=
  inQuery c || c == 0x3F || c == 0x5E || c == 0x60 || c == 0x7B || c == 0x7D
def inUserinfo (c : Nat) : Bool :=
  inPath c || c == 0x2F || c == 0x3A || c == 0x3B || c == 0x3D || c == 0x40
    || (0x5B ≤ c && c ≤ 0x5E) || c == 0x7C
def inComponent (c : Nat) : Bool :=
  inUserinfo c || (0x24 ≤ c && c ≤ 0x26) || c == 0x2B || c == 0x2C
def inFormUrlencoded (c : Nat) : Bool :=
  inComponent c || c == 0x21 || (0x27 ≤ c && c ≤ 0x29) || c == 0x7E

/-- Membership of a code point in a percent-encode set (section 1.3). -/
def PercentEncodeSet.contains : PercentEncodeSet → Nat → Bool
  | .c0control => inC0control
  | .fragment => inFragment
  | .query => inQuery
  | .specialQuery => inSpecialQuery
  | .path => inPath
  | .userinfo => inUserinfo
  | .component => inComponent
  | .formUrlencoded => inFormUrlencoded

def PercentEncodeSet.ofName? : String → Option PercentEncodeSet
  | "c0control" => some .c0control
  | "fragment" => some .fragment
  | "query" => some .query
  | "special-query" => some .specialQuery
  | "path" => some .path
  | "userinfo" => some .userinfo
  | "component" => some .component
  | "application/x-www-form-urlencoded" => some .formUrlencoded
  | _ => none

def hexUpper (n : Nat) : Char := if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x41 + n - 10)

/-- percent-encode a byte (section 1.3): `%` and two upper-case hex digits. -/
def percentEncodeByte (b : UInt8) : String :=
  String.ofList ['%', hexUpper (b.toNat / 16), hexUpper (b.toNat % 16)]

/-- The output step of "percent-encode after encoding" for one run of bytes. -/
def appendEncodedBytes (set : PercentEncodeSet) (spaceAsPlus : Bool) (acc : String)
    (bs : ByteArray) : String :=
  bs.foldl (fun s b =>
    if spaceAsPlus && b == 0x20 then s.push '+'
    else if set.contains b.toNat then s ++ percentEncodeByte b
    else s.push (Char.ofNat b.toNat)) acc

/-- percent-encode after encoding (section 1.3), given an encoding,
scalar values, a percent-encode set and spaceAsPlus. The encoding is used as
given; callers pass the result of get an output encoding. An encoding with no
encoder (replacement, UTF-16BE/LE) is replaced by UTF-8 here, which is what
get an output encoding gives for it. -/
def percentEncodeAfterEncoding (enc : Encoding) (input : Array UInt32)
    (set : PercentEncodeSet) (spaceAsPlus := false) : String :=
  let encoder := (getEncoder enc).getD .utf8
  -- Each round consumes at least one code point or ends, so the input length
  -- plus one rounds suffice.
  let rec go (fuel : Nat) (e : Encoder) (q : CpQueue) (out : String) : String :=
    match fuel with
    | 0 => out
    | fuel + 1 =>
      let (e', q', bytes, err) := encodeOrFail q e
      let out := appendEncodedBytes set spaceAsPlus out bytes
      match err with
      | none => out
      | some cp => go fuel e' q' (out ++ "%26%23" ++ toString cp.toNat ++ "%3B")
  go (input.size + 1) encoder { data := input } ""

/-- The value of an ASCII hex digit byte, or `none`. -/
def hexValue? (b : UInt8) : Option Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else none

/-- percent-decode a byte sequence (section 1.3): `%` followed by two ASCII
hex digits is the byte they name; every other byte is itself. -/
def percentDecode (input : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut i := 0
  for _ in [0:input.size] do
    if h : i < input.size then
      let b := input[i]
      match (if b == 0x25 then (input[i + 1]?.bind hexValue?, input[i + 2]?.bind hexValue?)
             else (none, none)) with
      | (some hi, some lo) =>
        out := out.push (hi * 16 + lo).toUInt8
        i := i + 3
      | _ =>
        out := out.push b
        i := i + 1
  return out

end L4Factoidal.WHATWG.URL
