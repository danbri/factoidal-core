/-
L4Factoidal.WHATWG.Base64 — forgiving-base64 (Infra Standard §4.6, "Forgiving
base64") and the `atob` / `btoa` methods of HTML §8.3 ("Base64 utility
methods").

Specifications:
  * Infra Standard, WHATWG Living Standard, section "Forgiving base64":
    forgiving-base64 encode and forgiving-base64 decode.
  * HTML Standard, section 8.3: `btoa(data)` throws "InvalidCharacterError"
    when `data` has a code unit above U+00FF, else answers the forgiving-base64
    encode of `data` isomorphic-encoded; `atob(data)` answers the
    isomorphic decode of the forgiving-base64 decode of `data`, or throws
    "InvalidCharacterError" when that is failure.

The page API (`WasmVM.Hosts.WebApi`, ops 20 and 21) passes JavaScript strings as
UTF-8; a lone surrogate never reaches the Lean side as a code point below U+0100,
so `btoa` refuses it as the standard does.

Round trip: `#guard` checks below (every byte value, every tail length).

No `partial`, no `sorry`.
-/
namespace L4Factoidal.WHATWG.Base64

/-- The 64 characters of the standard alphabet (RFC 4648 Table 1). -/
def alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- The value of an alphabet character. -/
def value? (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62
  else if c == '/' then some 63
  else none

/-- ASCII whitespace (Infra): TAB, LF, FF, CR, SPACE. -/
def isAsciiWhitespace (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

/-- The six-bit group `i` (0 to 3) of a 24-bit word. -/
def sextet (w i : Nat) : Char := alphabet[(w >>> (18 - 6 * i)) % 64]!

/-- forgiving-base64 encode: RFC 4648 section 4 base64 with padding. Each group of three
bytes is four characters; a last group of two bytes is three and `=`, of one byte two and
`==`. A loop over the groups (no recursion on the input's length). -/
def encodeBytes (b : Array UInt8) : String := Id.run do
  let mut out := ""
  let n := b.size
  for g in [0:(n + 2) / 3] do
    let i := 3 * g
    let at_ := fun (k : Nat) => if i + k < n then b[i + k]!.toNat else 0
    let w := at_ 0 * 65536 + at_ 1 * 256 + at_ 2
    out := (out.push (sextet w 0)).push (sextet w 1)
    out := out.push (if i + 1 < n then sextet w 2 else '=')
    out := out.push (if i + 2 < n then sextet w 3 else '=')
  return out

def encode (bs : ByteArray) : String := encodeBytes bs.data

/-- The bytes of a run of sextets (Infra step 7): every four sextets are three bytes; a
tail of three sextets (18 bits) is two bytes and a tail of two (12 bits) is one byte, the
remaining bits discarded. -/
def bytesOf (xs : Array Nat) : Array UInt8 := Id.run do
  let mut out : Array UInt8 := Array.emptyWithCapacity (xs.size * 3 / 4 + 2)
  let n := xs.size
  for g in [0:(n + 3) / 4] do
    let i := 4 * g
    let x := fun (k : Nat) => if i + k < n then xs[i + k]! else 0
    let w := ((x 0 * 64 + x 1) * 64 + x 2) * 64 + x 3
    let left := n - i
    if left ≥ 2 then out := out.push (w / 65536).toUInt8
    if left ≥ 3 then out := out.push (w / 256 % 256).toUInt8
    if left ≥ 4 then out := out.push (w % 256).toUInt8
  return out

/-- forgiving-base64 decode (Infra): `none` is failure. -/
def decodeChars (input : Array Char) : Option (Array UInt8) := Id.run do
  -- 1. Remove all ASCII whitespace.
  let cs := input.filter (!isAsciiWhitespace ·)
  -- 2. If the length divides by 4, remove one or two trailing `=`.
  let cs :=
    if cs.size % 4 == 0 then
      if cs.size ≥ 2 && cs[cs.size - 1]! == '=' && cs[cs.size - 2]! == '=' then cs.extract 0 (cs.size - 2)
      else if cs.size ≥ 1 && cs[cs.size - 1]! == '=' then cs.extract 0 (cs.size - 1)
      else cs
    else cs
  -- 3. A length of 1 modulo 4 is failure.
  if cs.size % 4 == 1 then return none
  -- 4. A character outside the alphabet is failure; 5 to 8: the bytes.
  let mut vs : Array Nat := Array.emptyWithCapacity cs.size
  for c in cs do
    match value? c with
    | some v => vs := vs.push v
    | none => return none
  return some (bytesOf vs)

def decode (s : String) : Option ByteArray := (decodeChars s.toList.toArray).map ByteArray.mk

/-! ## The HTML methods -/

/-- `btoa(data)`: `none` is an "InvalidCharacterError" (a code point above U+00FF). -/
def btoa (data : String) : Option String :=
  if data.toList.all (·.toNat ≤ 0xFF) then
    some (encodeBytes (data.toList.toArray.map (·.toNat.toUInt8)))
  else none

/-- `atob(data)`: the isomorphic decode of the bytes; `none` is an
"InvalidCharacterError". -/
def atob (data : String) : Option String :=
  (decodeChars data.toList.toArray).map fun bs => bs.foldl (fun s b => s.push (Char.ofNat b.toNat)) ""

/-! ## Checks (Infra examples and the WPT `html/webappapis/atob/base64.html` cases) -/

#guard encode "".toUTF8 == ""
#guard encode "f".toUTF8 == "Zg=="
#guard encode "fo".toUTF8 == "Zm8="
#guard encode "foobar".toUTF8 == "Zm9vYmFy"
#guard decode "Zm9vYmFy" == some "foobar".toUTF8
#guard decode " Zm 9v\nYg== " == some "foob".toUTF8
#guard decode "Zg" == some "f".toUTF8
#guard decode "Zg=" == none
#guard decode "Zg===" == none
#guard decode "Z" == none
#guard decode "ab=c" == none
#guard atob "YQ" == some "a"
#guard btoa "\u00ff" == some "/w=="
#guard btoa "\u0100" == none
-- Round trip on every byte value and every tail length.
#guard (List.range 256).all fun b => decode (encode (ByteArray.mk #[b.toUInt8])) == some (ByteArray.mk #[b.toUInt8])
#guard (List.range 40).all fun n =>
  let bs := ByteArray.mk ((List.range n).map (fun i => (i * 37 + 11).toUInt8)).toArray
  decode (encode bs) == some bs

end L4Factoidal.WHATWG.Base64
