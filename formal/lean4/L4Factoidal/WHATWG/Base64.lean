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

/-- The characters of one group of up to three bytes: four characters with `=` for
each missing byte. -/
def encodeGroup : List UInt8 → List Char
  | [a, b, c] =>
    let w := a.toNat * 65536 + b.toNat * 256 + c.toNat
    [sextet w 0, sextet w 1, sextet w 2, sextet w 3]
  | [a, b] =>
    let w := a.toNat * 65536 + b.toNat * 256
    [sextet w 0, sextet w 1, sextet w 2, '=']
  | [a] =>
    let w := a.toNat * 65536
    [sextet w 0, sextet w 1, '=', '=']
  | _ => []

/-- The groups of three bytes, the last one shorter. -/
def groups : List UInt8 → List (List UInt8)
  | a :: b :: c :: rest => [a, b, c] :: groups rest
  | [] => []
  | xs => [xs]

/-- forgiving-base64 encode: RFC 4648 section 4 base64 with padding. -/
def encodeList (bs : List UInt8) : List Char := (groups bs).flatMap encodeGroup

def encode (bs : ByteArray) : String := String.ofList (encodeList bs.data.toList)

/-- The bytes of a run of sextets (Infra step 7): every four sextets are three
bytes; a tail of three sextets (18 bits) is two bytes and a tail of two (12 bits)
is one byte, the remaining bits discarded. -/
def bytesOf : List Nat → List UInt8
  | a :: b :: c :: d :: rest =>
    let w := ((a * 64 + b) * 64 + c) * 64 + d
    (w / 65536).toUInt8 :: (w / 256 % 256).toUInt8 :: (w % 256).toUInt8 :: bytesOf rest
  | [a, b, c] =>
    let w := (a * 64 + b) * 64 + c
    [(w / 1024).toUInt8, (w / 4 % 256).toUInt8]
  | [a, b] => [((a * 64 + b) / 16).toUInt8]
  | _ => []

/-- forgiving-base64 decode (Infra): `none` is failure. -/
def decodeList (input : List Char) : Option (List UInt8) :=
  -- 1. Remove all ASCII whitespace.
  let cs := input.filter (!isAsciiWhitespace ·)
  -- 2. If the length divides by 4, remove one or two trailing `=`.
  let cs :=
    if cs.length % 4 == 0 then
      match cs.reverse with
      | '=' :: '=' :: rest => rest.reverse
      | '=' :: rest => rest.reverse
      | _ => cs
    else cs
  -- 3. A length of 1 modulo 4 is failure.
  if cs.length % 4 == 1 then none
  -- 4. A character outside the alphabet is failure; 5 to 8: the bytes.
  else (cs.mapM value?).map bytesOf

def decode (s : String) : Option ByteArray := (decodeList s.toList).map (·.toByteArray)

/-! ## The HTML methods -/

/-- `btoa(data)`: `none` is an "InvalidCharacterError" (a code point above U+00FF). -/
def btoa (data : String) : Option String :=
  if data.toList.all (·.toNat ≤ 0xFF) then
    some (String.ofList (encodeList (data.toList.map (·.toNat.toUInt8))))
  else none

/-- `atob(data)`: the isomorphic decode of the bytes; `none` is an
"InvalidCharacterError". -/
def atob (data : String) : Option String :=
  (decodeList data.toList).map fun bs => String.ofList (bs.map fun b => Char.ofNat b.toNat)

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
