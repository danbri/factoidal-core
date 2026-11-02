/-
L4Factoidal.XML.X509 — the parts of an X.509 certificate (RFC 5280 §4.1)
that XML Signature 1.1 §4.5.4 (`ds:X509Data`) needs to find a key: the
issuer and subject names, the serial number, the SubjectPublicKeyInfo and
the subject key identifier extension (RFC 5280 §4.2.1.2); and the
distinguished name strings of RFC 4514 that `X509IssuerName` and
`X509SubjectName` carry (https://github.com/danbri/factoidal/issues/1226,
track B item 4 of https://github.com/danbri/factoidal/issues/1165).

This module reads DER. It does not check a certificate's signature, its
validity period, its extensions or a certification path. Those are the
caller's decision (XML Signature 1.1 §4.5.4: "the validation of
certificates ... is outside the scope of this specification").

Name matching (`nameMatches`): the RDN sequence of the string, in reverse
order (RFC 4514 §2.1), must have the same length as the certificate's;
each RDN must hold the same number of attribute type and value pairs, and
each pair of the string must match one of the certificate's: the same
attribute type OID, and either the same DER octets (a `#hex` value, RFC
4514 §2.4) or a string value equal after ASCII case folding and the
folding of white space runs to one space, with leading and trailing white
space removed. That is a subset of the caseIgnoreMatch preparation of
RFC 4518 (no Unicode case folding, no normalisation). Every X.500
attribute type of RFC 4514 §3 uses caseIgnoreMatch or a stricter rule
for which these strings agree.

Decoders are loops over the input with fuel bounded by its length (one
DER item is at least two octets), not one stack frame per item.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.X509

/-- A DER TLV at `i` with a definite length (short form, or long form with
one to three length octets): tag, content start, content end. -/
def derTlv? (b : ByteArray) (i : Nat) : Option (UInt8 × Nat × Nat) :=
  if i + 2 > b.size then none else
  let tag := b.get! i
  let l0 := (b.get! (i + 1)).toNat
  if l0 < 128 then
    if i + 2 + l0 ≤ b.size then some (tag, i + 2, i + 2 + l0) else none
  else
    let k := l0 - 128
    if k == 0 || k > 3 || i + 2 + k > b.size then none else
    let l := (List.range k).foldl (fun acc j => acc * 256 + (b.get! (i + 2 + j)).toNat) 0
    let s := i + 2 + k
    if s + l ≤ b.size then some (tag, s, s + l) else none

/-- The TLVs from `s` to exactly `e`, in order, each as tag, start of the
TLV, content start, content end; `none` when they do not fill the range. -/
def tlvsIn (b : ByteArray) (s e : Nat) : Option (List (UInt8 × Nat × Nat × Nat)) := Id.run do
  let mut i := s
  let mut acc : Array (UInt8 × Nat × Nat × Nat) := #[]
  for _ in [0:e - s + 1] do
    if i == e then return some acc.toList
    match derTlv? b i with
    | some (t, cs, ce) =>
        if ce > e then return none
        acc := acc.push (t, i, cs, ce)
        i := ce
    | none => return none
  return none

/-- One attribute type and value of a name (RFC 5280 §4.1.2.4). -/
structure Atv where
  /-- The content octets of the attribute type OID. -/
  oid : List UInt8
  /-- The value, the whole DER TLV. -/
  raw : ByteArray
  /-- The value as a string, for the directory string types. -/
  str : Option String

/-- A name: its RDNs in DER order, each a set of attribute type and value
pairs; and its DER octets. -/
structure Name where
  rdns : List (List Atv)
  der : ByteArray

/-- The certificate fields `ds:X509Data` identifies a certificate by. -/
structure Cert where
  der : ByteArray
  serial : Int
  issuer : Name
  subject : Name
  /-- The SubjectPublicKeyInfo, the whole DER TLV. -/
  spki : ByteArray
  /-- The subject key identifier extension (RFC 5280 §4.2.1.2). -/
  ski : Option ByteArray

def slice (b : ByteArray) (s e : Nat) : List UInt8 := (b.extract s e).data.toList

/-- A DER INTEGER's content octets as an integer (two's complement). -/
def intOf (l : List UInt8) : Int :=
  let n : Nat := l.foldl (fun acc x => acc * 256 + x.toNat) 0
  match l with
  | x :: _ => if x.toNat ≥ 128 then (n : Int) - ((256 ^ l.length : Nat) : Int) else (n : Int)
  | [] => 0

/-- Code points as a string; `none` when one is not a Unicode scalar value. -/
def ofCodes (cs : List Nat) : Option String :=
  if cs.all fun c => c < 0xD800 || (0xE000 ≤ c && c < 0x110000) then
    some (String.ofList (cs.map Char.ofNat))
  else none

/-- The directory string types of RFC 5280 §4.1.2.4 (and IA5String,
VisibleString), decoded to a string. T61String is read as ISO 8859-1. -/
def dirString? (tag : UInt8) (c : List UInt8) : Option String :=
  match tag with
  | 0x0C => String.fromUTF8? ⟨c.toArray⟩
  | 0x13 | 0x16 | 0x1A => if c.all (·.toNat < 128) then ofCodes (c.map (·.toNat)) else none
  | 0x14 => ofCodes (c.map (·.toNat))
  | 0x1E =>
      if c.length % 2 != 0 then none else
      ofCodes ((List.range (c.length / 2)).map fun i => c[2*i]!.toNat * 256 + c[2*i+1]!.toNat)
  | 0x1C =>
      if c.length % 4 != 0 then none else
      ofCodes ((List.range (c.length / 4)).map fun i =>
        ((c[4*i]!.toNat * 256 + c[4*i+1]!.toNat) * 256 + c[4*i+2]!.toNat) * 256 + c[4*i+3]!.toNat)
  | _ => none

/-- A Name (RDNSequence) TLV at `i`. -/
def name? (b : ByteArray) (i : Nat) : Option Name := do
  let (t, s, e) ← derTlv? b i
  if t != 0x30 then none
  let rdnTlvs ← tlvsIn b s e
  let rdns ← rdnTlvs.mapM fun (rt, _, rs, re) => do
    if rt != 0x31 then none
    let atvs ← tlvsIn b rs re
    atvs.mapM fun (aty, _, as, ae) => do
      if aty != 0x30 then none
      match ← tlvsIn b as ae with
      | [(0x06, _, os, oe), (vt, v0, vs, ve)] =>
          some { oid := slice b os oe, raw := b.extract v0 ve, str := dirString? vt (slice b vs ve) }
      | _ => none
  some { rdns, der := b.extract i e }

/-- The OID of the subject key identifier extension, 2.5.29.14. -/
def oidSki : List UInt8 := [0x55, 0x1d, 0x0e]

/-- The subject key identifier among the extensions `[3]` at `s`..`e`. -/
def skiIn (b : ByteArray) (s e : Nat) : Option ByteArray := do
  let (t, xs, xe) ← derTlv? b s
  if !(t == 0x30 && xe == e) then none
  let exts ← tlvsIn b xs xe
  let found := exts.findSome? fun (et, _, es, ee) =>
    if et != 0x30 then none else
    match tlvsIn b es ee with
    | some ((0x06, _, os, oe) :: rest) =>
        if slice b os oe != oidSki then none else
        match rest.getLast? with
        | some (0x04, _, vs, ve) =>
            match derTlv? b vs with
            | some (0x04, ks, ke) => if ke == ve then some (b.extract ks ke) else none
            | _ => none
        | _ => none
    | _ => none
  found

/-- A DER certificate (RFC 5280 §4.1). Nothing after it is allowed. -/
def parseCert? (b : ByteArray) : Option Cert := do
  let (t0, s0, e0) ← derTlv? b 0
  if !(t0 == 0x30 && e0 == b.size) then none
  let (t1, s1, e1) ← derTlv? b s0
  if t1 != 0x30 then none
  let items ← tlvsIn b s1 e1
  -- the optional explicit version [0]
  let items := match items with
    | (0xA0, _, _, _) :: rest => rest
    | l => l
  match items with
  | (0x02, _, ss, se) :: (0x30, _, _, _) :: (0x30, i0, _, _) :: (0x30, _, _, _) :: (0x30, u0, _, _) ::
      (0x30, p0, _, pe) :: rest =>
      let issuer ← name? b i0
      let subject ← name? b u0
      let ski := rest.findSome? fun (xt, _, xs, xe) => if xt == 0xA3 then skiIn b xs xe else none
      some { der := b, serial := intOf (slice b ss se), issuer, subject,
             spki := b.extract p0 pe, ski }
  | _ => none

/-! ## Distinguished name strings (RFC 4514) -/

/-- The DER content octets of a dotted OID (X.690 §8.19). -/
def oidOfDotted? (s : String) : Option (List UInt8) := do
  let arcs ← (s.splitOn ".").mapM String.toNat?
  match arcs with
  | a :: b :: rest =>
      if a > 2 || (a < 2 && b ≥ 40) then none
      let base128 (n : Nat) : List UInt8 := Id.run do
        let mut out : List UInt8 := [UInt8.ofNat (n % 128)]
        let mut m := n / 128
        for _ in [0:10] do
          if m == 0 then break
          out := UInt8.ofNat (m % 128 + 128) :: out
          m := m / 128
        return out
      some ((40 * a + b) :: rest |>.flatMap base128)
  | _ => none

/-- The attribute type names of RFC 4514 §3, and those common in
certificates (RFC 4519). -/
def shortNames : List (String × String) :=
  [("CN", "2.5.4.3"), ("SURNAME", "2.5.4.4"), ("SERIALNUMBER", "2.5.4.5"), ("C", "2.5.4.6"),
   ("L", "2.5.4.7"), ("ST", "2.5.4.8"), ("S", "2.5.4.8"), ("STREET", "2.5.4.9"), ("O", "2.5.4.10"),
   ("OU", "2.5.4.11"), ("T", "2.5.4.12"), ("TITLE", "2.5.4.12"), ("GIVENNAME", "2.5.4.42"),
   ("INITIALS", "2.5.4.43"), ("GENERATIONQUALIFIER", "2.5.4.44"), ("DNQUALIFIER", "2.5.4.46"),
   ("PSEUDONYM", "2.5.4.65"), ("DC", "0.9.2342.19200300.100.1.25"), ("UID", "0.9.2342.19200300.100.1.1"),
   ("E", "1.2.840.113549.1.9.1"), ("EMAILADDRESS", "1.2.840.113549.1.9.1")]

def typeOid? (t : String) : Option (List UInt8) :=
  let u := t.toUpper
  let u := if u.startsWith "OID." then (u.drop 4).toString else u
  match shortNames.find? (·.1 == u) with
  | some (_, d) => oidOfDotted? d
  | none => oidOfDotted? u

/-- A value of a DN string: a string, or the DER octets of `#hex`. -/
inductive DnValue where
  | str (s : String)
  | ber (b : ByteArray)

def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def utf8Of (c : Char) : List UInt8 := (String.singleton c).toUTF8.data.toList

/-- An RFC 4514 string as a list of RDNs, each a list of attribute type
OIDs and values, in the order written. Escapes: `\` and a special
character, or `\` and two hex digits (one octet of UTF-8). Unescaped `,`
and `;` separate RDNs, `+` separates the pairs of one RDN. Leading and
trailing unescaped spaces of a type or value are removed. -/
def parseDn? (s : String) : Option (List (List (List UInt8 × DnValue))) := Id.run do
  -- leading and trailing white space removed, but not an escaped space
  let t := s.trimAsciiStart.toString
  let core := t.trimAsciiEnd.toString
  let bs := (core.toList.reverse.takeWhile (· == '\\')).length
  let core := if bs % 2 == 1 && core.length < t.length then core ++ " " else core
  let cs := core.toList.toArray
  let mut rdns : Array (List (List UInt8 × DnValue)) := #[]
  let mut cur : Array (List UInt8 × DnValue) := #[]
  let mut i := 0
  if cs.isEmpty then return some []
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    -- attribute type, up to '='
    let mut ty : Array Char := #[]
    for _ in [0:cs.size] do
      if i ≥ cs.size || cs[i]! == '=' then break
      ty := ty.push cs[i]!
      i := i + 1
    if i ≥ cs.size then return none
    i := i + 1
    let some oid := typeOid? (String.ofList ty.toList).trimAscii.toString | return none
    -- skip leading spaces of the value
    for _ in [0:cs.size] do
      if i < cs.size && cs[i]! == ' ' then i := i + 1 else break
    let mut val : DnValue := .str ""
    let mut sep : Char := ' '
    if i < cs.size && cs[i]! == '#' then
      i := i + 1
      let mut hx : Array Char := #[]
      for _ in [0:cs.size] do
        if i ≥ cs.size || cs[i]! == ',' || cs[i]! == ';' || cs[i]! == '+' then break
        hx := hx.push cs[i]!
        i := i + 1
      let h := (String.ofList hx.toList).trimAscii.toString.toList.toArray
      if h.size % 2 != 0 || h.size == 0 then return none
      let mut out : ByteArray := .empty
      for k in [0:h.size / 2] do
        match hexVal? h[2*k]!, hexVal? h[2*k+1]! with
        | some a, some b => out := out.push (UInt8.ofNat (a * 16 + b))
        | _, _ => return none
      val := .ber out
    else
      let mut bytes : Array UInt8 := #[]
      -- the length of `bytes` up to the last escaped or non-space octet
      let mut keep := 0
      for _ in [0:cs.size] do
        if i ≥ cs.size then break
        let c := cs[i]!
        if c == ',' || c == ';' || c == '+' then break
        if c == '\\' then
          if i + 1 ≥ cs.size then return none
          let d := cs[i+1]!
          match hexVal? d, (if i + 2 < cs.size then hexVal? cs[i+2]! else none) with
          | some a, some b =>
              bytes := bytes.push (UInt8.ofNat (a * 16 + b)); i := i + 3
          | _, _ =>
              if " \"#+,;<=>\\".toList.contains d then
                bytes := bytes ++ (utf8Of d).toArray; i := i + 2
              else return none
          keep := bytes.size
        else
          bytes := bytes ++ (utf8Of c).toArray
          if c != ' ' then keep := bytes.size
          i := i + 1
      let some v := String.fromUTF8? ⟨bytes.extract 0 keep⟩ | return none
      val := .str v
    if i < cs.size then sep := cs[i]!; i := i + 1
    cur := cur.push (oid, val)
    if sep != '+' then
      rdns := rdns.push cur.toList
      cur := #[]
    -- skip spaces after a separator
    for _ in [0:cs.size] do
      if i < cs.size && cs[i]! == ' ' then i := i + 1 else break
    if sep != ' ' && i ≥ cs.size then return none
  if !cur.isEmpty then rdns := rdns.push cur.toList
  return some rdns.toList

/-- ASCII case folding, white space runs folded to one space, leading and
trailing white space removed. -/
def prep (s : String) : String :=
  let words := (s.toList.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c.toLower)
    |> String.ofList |>.splitOn " " |>.filter (· != "")
  " ".intercalate words

def atvMatches (p : List UInt8 × DnValue) (a : Atv) : Bool :=
  p.1 == a.oid && match p.2 with
    | .ber b => b == a.raw
    | .str s => match a.str with
      | some t => prep s == prep t
      | none => false

/-- An RFC 4514 string names the certificate name `n`. -/
def nameMatches (s : String) (n : Name) : Bool :=
  match parseDn? s with
  | none => false
  | some dn =>
      let r := dn.reverse
      r.length == n.rdns.length &&
        (r.zip n.rdns).all fun (pr, cr) =>
          pr.length == cr.length && pr.all fun p => cr.any (atvMatches p)

/-- Two names are equal: the same DER octets (RFC 5280 §7.1 allows a
looser comparison; issuer chaining here only orders certificates that
the caller gives, so exact octets are enough). -/
def Name.same (a b : Name) : Bool := a.der == b.der

/-! ## Checks -/

#guard ((parseDn? "\n  CN=Badb,OU=X/Secure,O=Baltimore Technologies Ltd.,ST=Dublin,C=IE\n ").map (·.length)) == some 5
#guard (parseDn? "CN=a\\,b + UID=x;C=IE").map (fun l => l.map (·.length)) == some [2, 1]
#guard (match parseDn? "CN=a\\2Cb" with | some [[(_, .str v)]] => v == "a,b" | _ => false)
#guard (match parseDn? "CN= x  " with | some [[(_, .str v)]] => v == "x" | _ => false)
#guard (match parseDn? "CN=x\\ " with | some [[(_, .str v)]] => v == "x " | _ => false)
#guard (match parseDn? "1.3.6.1.4.1.1466.0=#04024869" with
  | some [[(o, .ber b)]] => o == [0x2b, 6, 1, 4, 1, 0x8b, 0x3a, 0] && b.data.toList == [4, 2, 0x48, 0x69]
  | _ => false)
#guard (parseDn? "CN").isNone
#guard (parseDn? "CN=a,").isNone
#guard (parseDn? "CN=a\\").isNone
#guard oidOfDotted? "2.5.4.3" == some [0x55, 4, 3]
#guard oidOfDotted? "1.2.840.113549.1.9.1" == some [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 1, 9, 1]
#guard prep "  Baltimore   Technologies\tLTD. " == "baltimore technologies ltd."
#guard intOf [0x00, 0xEC] == 236
#guard intOf [0xFF] == -1
#guard derTlv? ⟨#[0x30, 0x82, 0x00, 0x01, 0x05]⟩ 0 == some (0x30, 4, 5)
#guard derTlv? ⟨#[0x30, 0x80]⟩ 0 == none

end L4Factoidal.X509
