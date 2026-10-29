/-
L4Factoidal.WHATWG.URL.Host — hosts of the WHATWG URL Standard, section 3:
the host representation, the IPv4 and IPv6 parsers and serializers, the
opaque-host parser, the domain parser, and the host parser.

Specification: URL Standard, WHATWG Living Standard, Last Updated 19 October
2026 (commit snapshot whatwg/url `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`);
section names are the names of that text. The tests are web-platform-tests
`url/` (third_party/testing/wpt-url). The domain parser uses UTS #46 18.0.0
through `L4Factoidal.WHATWG.URL.Idna`.

https://github.com/danbri/factoidal/issues/1167, milestone 3. No `partial`, no
`sorry`.
-/
import L4Factoidal.WHATWG.URL.Idna
import L4Factoidal.WHATWG.URL.PercentEncode

namespace L4Factoidal.WHATWG.URL

open L4Factoidal.WHATWG.Encoding

/-- A host (section 3.1). An IPv4 address is a 32-bit number, an IPv6 address
eight 16-bit pieces. -/
inductive Host where
  | domain (s : String)
  | ipv4 (n : Nat)
  | ipv6 (pieces : Array Nat)
  | opaque (s : String)
  | empty
  deriving DecidableEq, Repr, Inhabited

/-- A forbidden host code point (section 3.2). -/
def isForbiddenHost (c : Char) : Bool :=
  c == '\x00' || c == '\t' || c == '\n' || c == '\r' || c == ' ' || c == '#' || c == '/'
    || c == ':' || c == '<' || c == '>' || c == '?' || c == '@' || c == '[' || c == '\\'
    || c == ']' || c == '^' || c == '|'

/-- A forbidden domain code point (section 3.2). -/
def isForbiddenDomain (c : Char) : Bool :=
  isForbiddenHost c || c.toNat ≤ 0x1F || c == '%' || c.toNat == 0x7F

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isAsciiHexDigit (c : Char) : Bool :=
  isAsciiDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
def isAsciiAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def asciiLower (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
def asciiLowerStr (s : String) : String := s.map asciiLower

def hexDigitVal (c : Char) : Nat :=
  if isAsciiDigit c then c.toNat - 48
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87 else c.toNat - 55

/-! ## Percent-encoding of one code point (section 1.3) -/

/-- UTF-8 percent-encode a code point using a percent-encode set. A byte of
0x80 or more is in every set, because the C0 control set contains it. -/
def utf8PercentEncodeChar (set : PercentEncodeSet) (c : Char) : String :=
  if c.toNat < 0x80 && !set.contains c.toNat then String.singleton c
  else (String.utf8EncodeChar c).foldl (fun s b => s ++ percentEncodeByte b) ""

def utf8PercentEncodeString (set : PercentEncodeSet) (s : String) : String :=
  s.foldl (fun acc c => acc ++ utf8PercentEncodeChar set c) ""

/-! ## IPv4 (section 3.5) -/

/-- The IPv4 number parser: the value and whether a validation error was
seen, or `none` for failure. -/
def parseIPv4Number (input : String) : Option Nat :=
  if input.isEmpty then none
  else
    let cs := input.toList
    let (radix, digits) :=
      match cs with
      | '0' :: x :: rest => if x == 'x' || x == 'X' then (16, rest) else (8, x :: rest)
      | _ => (10, cs)
    if digits.isEmpty then some 0
    else if radix == 16 then
      if digits.all isAsciiHexDigit then some (digits.foldl (fun n c => n * 16 + hexDigitVal c) 0)
      else none
    else if radix == 8 then
      if digits.all (fun c => '0' ≤ c && c ≤ '7') then
        some (digits.foldl (fun n c => n * 8 + (c.toNat - 48)) 0)
      else none
    else if digits.all isAsciiDigit then some (digits.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)
    else none

/-- The ends-in-a-number checker. -/
def endsInANumber (input : String) : Bool :=
  let parts := input.splitOn "."
  let parts :=
    if parts.getLast! == "" then (if parts.length == 1 then [] else parts.dropLast) else parts
  match parts.getLast? with
  | none => false
  | some last =>
    (!last.isEmpty && last.toList.all isAsciiDigit) || (parseIPv4Number last).isSome

/-- The IPv4 parser. -/
def parseIPv4 (input : String) : Option Nat := do
  let parts := input.splitOn "."
  let parts := if parts.getLast! == "" && parts.length > 1 then parts.dropLast else parts
  if parts.length > 4 then none
  let numbers ← parts.mapM parseIPv4Number
  let n := numbers.length
  let init := numbers.dropLast
  if init.any (· > 255) then none
  let last := numbers.getLast!
  if last ≥ 256 ^ (5 - n) then none
  let (ipv4, _) := init.foldl (fun (acc, counter) x => (acc + x * 256 ^ (3 - counter), counter + 1))
    (last, 0)
  return ipv4

/-- The IPv4 serializer. -/
def serializeIPv4 (n : Nat) : String :=
  s!"{n / 16777216 % 256}.{n / 65536 % 256}.{n / 256 % 256}.{n % 256}"

/-! ## IPv6 (section 3.5) -/

/-- The IPv6 parser, transcribed from the standard: `pointer` indexes the
input; each round of the main loop reads at least one code point. -/
def parseIPv6 (input : String) : Option (Array Nat) := Id.run do
  let cs := input.toList.toArray
  let n := cs.size
  let at? := fun (i : Nat) => cs[i]?
  let mut address : Array Nat := Array.replicate 8 0
  let mut pieceIndex := 0
  let mut compress : Option Nat := none
  let mut p := 0
  if at? 0 == some ':' then
    if at? 1 != some ':' then return none
    p := 2
    pieceIndex := pieceIndex + 1
    compress := some pieceIndex
  for _ in [0:n + 1] do
    if p < n then
      if pieceIndex == 8 then return none
      if at? p == some ':' then
        if compress.isSome then return none
        p := p + 1
        pieceIndex := pieceIndex + 1
        compress := some pieceIndex
      else
        let mut value := 0
        let mut length := 0
        for _ in [0:4] do
          match at? p with
          | some c =>
            if isAsciiHexDigit c then
              value := value * 16 + hexDigitVal c
              p := p + 1
              length := length + 1
          | none => pure ()
        -- The loop above stops at the first non-hex code point because p does
        -- not move past it; length counts the digits read.
        if at? p == some '.' then
          if length == 0 then return none
          p := p - length
          if pieceIndex > 6 then return none
          let mut numbersSeen := 0
          for _ in [0:n + 1] do
            if p < n then
              let mut ipv4Piece : Option Nat := none
              if numbersSeen > 0 then
                if at? p == some '.' && numbersSeen < 4 then p := p + 1
                else return none
              match at? p with
              | some c => if !isAsciiDigit c then return none
              | none => return none
              for _ in [0:n + 1] do
                match at? p with
                | some c =>
                  if isAsciiDigit c then
                    let number := c.toNat - 48
                    match ipv4Piece with
                    | none => ipv4Piece := some number
                    | some 0 => return none
                    | some v => ipv4Piece := some (v * 10 + number)
                    if ipv4Piece.getD 0 > 255 then return none
                    p := p + 1
                | none => pure ()
              address := address.set! pieceIndex (address[pieceIndex]! * 0x100 + ipv4Piece.getD 0)
              numbersSeen := numbersSeen + 1
              if numbersSeen == 2 || numbersSeen == 4 then pieceIndex := pieceIndex + 1
          if numbersSeen != 4 then return none
          p := n
          -- break: the address is complete; skip the compress check below by
          -- falling through to it with p at the end.
        else
          if at? p == some ':' then
            p := p + 1
            if p ≥ n then return none
          else if p < n then return none
          address := address.set! pieceIndex value
          pieceIndex := pieceIndex + 1
  match compress with
  | some c =>
    let mut swaps := pieceIndex - c
    let mut pi := 7
    for _ in [0:8] do
      if pi != 0 && swaps > 0 then
        let a := address[pi]!
        let b := address[c + swaps - 1]!
        address := (address.set! pi b).set! (c + swaps - 1) a
        pi := pi - 1
        swaps := swaps - 1
    return some address
  | none =>
    if pieceIndex != 8 then return none
    return some address

def hexLower (n : Nat) : String :=
  if n == 0 then "0"
  else String.ofList (Nat.toDigits 16 n)

/-- The IPv6 serializer, with the compression of the first longest run of
two or more zero pieces. -/
def serializeIPv6 (a : Array Nat) : String := Id.run do
  -- Find the first longest run of zero pieces of length > 1.
  let mut best : Option Nat := none
  let mut bestLen := 1
  let mut i := 0
  for _ in [0:8] do
    if i < 8 then
      if a[i]! == 0 then
        let mut j := i
        for _ in [0:8] do
          if j < 8 && a[j]! == 0 then j := j + 1
        if j - i > bestLen then
          best := some i
          bestLen := j - i
        i := j
      else i := i + 1
  let mut out := ""
  let mut ignore0 := false
  for k in [0:8] do
    if ignore0 && a[k]! == 0 then continue
    else if ignore0 then ignore0 := false
    if best == some k then
      out := out ++ (if k == 0 then "::" else ":")
      ignore0 := true
      continue
    out := out ++ hexLower a[k]!
    if k != 7 then out := out.push ':'
  return out

/-! ## Opaque hosts, the domain parser (section 3.3), the host parser (section 3.5) -/

/-- The opaque-host parser. -/
def parseOpaqueHost (input : String) : Option Host :=
  if input.toList.any isForbiddenHost then none
  else
    -- Hosts are strings in the standard, so an opaque host of no code points
    -- is the empty host.
    let s := utf8PercentEncodeString .c0control input
    some (if s.isEmpty then .empty else .opaque s)

/-- The domain parser ToASCII: UTS #46 ToASCII with the flags of section 3.3. -/
def domainParserToASCII (domain : String) (beStrict : Bool) : Option String :=
  Idna.toASCII { checkHyphens := beStrict, useSTD3ASCIIRules := beStrict,
                 verifyDnsLength := beStrict } domain

/-- The domain parser (section 3.3), given domain and beStrict. With beStrict
false an ASCII domain is lowercased and not checked by UTS #46; the standard
gives web compatibility as the reason. -/
def domainParser (domain : String) (beStrict := false) : Option String := do
  let result ←
    if beStrict then domainParserToASCII domain true
    else if domain.toList.all (fun c => c.toNat < 0x80) then some (asciiLowerStr domain)
    else domainParserToASCII domain false
  if result.isEmpty then none
  if result.toList.any isForbiddenDomain then none
  return result

/-- The host parser, given input and isOpaque. -/
def parseHost (input : String) (isOpaque : Bool) : Option Host :=
  if input.startsWith "[" then
    if !input.endsWith "]" then none
    else
      let inner := String.ofList ((input.toList.drop 1).dropLast)
      (parseIPv6 inner).map .ipv6
  else if isOpaque then parseOpaqueHost input
  else
    let domain := utf8DecodeWithoutBOM (percentDecode input.toUTF8)
    match domainParser domain with
    | none => none
    | some ascii =>
      if endsInANumber ascii then (parseIPv4 ascii).map .ipv4
      else some (.domain ascii)

/-- The host serializer. -/
def Host.serialize : Host → String
  | .ipv4 n => serializeIPv4 n
  | .ipv6 a => "[" ++ serializeIPv6 a ++ "]"
  | .domain s => s
  | .opaque s => s
  | .empty => ""

#guard parseIPv4 "0x7f.1" == some 0x7F000001
#guard parseIPv4 "256" == some 256
#guard parseIPv4 "1.2.3.256" == none
#guard (parseIPv6 "::1").map serializeIPv6 == some "::1"
#guard (parseIPv6 "1:0:0:2::3:0").map serializeIPv6 == some "1::2:0:0:3:0"
#guard (parseIPv6 "::ffff:192.168.0.1").map serializeIPv6 == some "::ffff:c0a8:1"
#guard parseIPv6 "1:2:3:4:5:6:7:8:9" == none
#guard (parseHost "EXAMPLE.com" false) == some (.domain "example.com")
#guard (parseHost "0x7f.0.0.1" false) == some (.ipv4 0x7F000001)

end L4Factoidal.WHATWG.URL
