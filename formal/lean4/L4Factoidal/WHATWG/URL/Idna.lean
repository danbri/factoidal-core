/-
L4Factoidal.WHATWG.URL.Idna — UTS #46 Unicode IDNA Compatibility Processing
(version 18.0.0) and Punycode (RFC 3492), as the URL Standard's domain parser
uses them.

Specifications:
- UTS #46, Unicode IDNA Compatibility Processing, version 18.0.0: section 4
  (Processing), section 4.1 (Validity Criteria), section 4.2 (ToASCII), with the
  data of `IdnaData` (IdnaMappingTable.txt 18.0.0).
- RFC 3492 (Punycode), sections 6.1 to 6.3.
- RFC 5892 Appendix A.1 and A.2 (CONTEXTJ rules), for CheckJoiners.
- RFC 5893 section 2 (the Bidi Rule), for CheckBidi.

The flags are those that the URL Standard's "domain parser ToASCII" passes when
beStrict is false: CheckHyphens false, CheckBidi true, CheckJoiners true,
UseSTD3ASCIIRules false, Transitional_Processing false, VerifyDnsLength false,
IgnoreInvalidPunycode false. They are fields of `Options`, so a strict caller
can set them.

Normalization to NFC reuses `L4Factoidal.XPath4.Unicode.normalize`, whose
tables are Unicode 16.0.0; the IDNA tables here are 18.0.0. A character new in
17.0 or 18.0 with a canonical decomposition is therefore not decomposed.

https://github.com/danbri/factoidal/issues/1167, milestone 3. No `partial`, no
`sorry`.
-/
import L4Factoidal.WHATWG.URL.IdnaData
import L4Factoidal.XPath4.Unicode

namespace L4Factoidal.WHATWG.URL.Idna

/-! ## The tables -/

def hexVal (s : String) : Nat :=
  s.foldl (fun n c =>
    n * 16 + (if c.isDigit then c.toNat - 48
              else if 'a' ≤ c then c.toNat - 87 else c.toNat - 55)) 0

/-- One row of a range table. -/
structure Row (α : Type) where
  lo : Nat
  hi : Nat
  val : α
  deriving Inhabited

def parseRange (s : String) : Nat × Nat :=
  match s.splitOn "-" with
  | [a, b] => (hexVal a, hexVal b)
  | _ => (hexVal s, hexVal s)

/-- The rows of a generated table text: `RANGE[:FIELDS];...`. -/
def rowsOf {α : Type} (t : String) (f : List String → α) : Array (Row α) :=
  (t.splitOn ";").foldl (fun acc e =>
    if e.isEmpty then acc
    else match e.splitOn ":" with
      | r :: rest => let (lo, hi) := parseRange r; acc.push ⟨lo, hi, f rest⟩
      | [] => acc) #[]

/-- Binary search for the row that contains `c`. The rows are sorted and do not
overlap. -/
def lookup {α : Type} (t : Array (Row α)) (c : Nat) : Option α := Id.run do
  let mut lo := 0
  let mut hi := t.size
  -- 64 halvings cover any array that fits in memory.
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < t.size then
        let r := t[mid]
        if c < r.lo then hi := mid
        else if r.hi < c then lo := mid + 1
        else return some r.val
      else return none
  return none

/-- The status of a code point in the IDNA Mapping Table (UTS #46 section 5). -/
inductive Status where
  | valid
  | deviation
  | mapped (m : Array Nat)
  | ignored
  | disallowed
  deriving Inhabited, BEq, Repr

def statusOf (fields : List String) : Status :=
  match fields with
  | "v" :: _ => .valid
  | "d" :: _ => .deviation
  | "i" :: _ => .ignored
  | "m" :: m :: _ => .mapped (((m.splitOn " ").filter (· != "")).map hexVal).toArray
  | "m" :: [] => .mapped #[]
  | _ => .disallowed

def idnaTable : Array (Row Status) := rowsOf IdnaData.idnaText statusOf

/-- The status of a code point; a code point not in the table is disallowed. -/
def status (c : Nat) : Status := (lookup idnaTable c).getD .disallowed

def bidiTable : Array (Row String) :=
  rowsOf IdnaData.bidiText (fun fs => fs.headD "L")

/-- The Bidi_Class short name of a code point (UCD 18.0.0). -/
def bidiClass (c : Nat) : String := (lookup bidiTable c).getD "L"

def joinTable : Array (Row String) :=
  rowsOf IdnaData.joinText (fun fs => fs.headD "U")

/-- The Joining_Type of a code point (UCD 18.0.0). -/
def joiningType (c : Nat) : String := (lookup joinTable c).getD "U"

def markTable : Array (Row Unit) := rowsOf IdnaData.markText (fun _ => ())

/-- General_Category is Mn, Mc or Me. -/
def isMark (c : Nat) : Bool := (lookup markTable c).isSome

def viramaTable : Array (Row Unit) := rowsOf IdnaData.viramaText (fun _ => ())

/-- Canonical_Combining_Class is 9 (Virama). -/
def isVirama (c : Nat) : Bool := (lookup viramaTable c).isSome

/-! ## Punycode (RFC 3492) -/

namespace Punycode

def base : Nat := 36
def tmin : Nat := 1
def tmax : Nat := 26
def skew : Nat := 38
def damp : Nat := 700
def initialBias : Nat := 72
def initialN : Nat := 128

/-- RFC 3492 section 6.1, bias adaptation. -/
def adapt (delta0 numPoints : Nat) (first : Bool) : Nat := Id.run do
  let mut delta := if first then delta0 / damp else delta0 / 2
  delta := delta + delta / numPoints
  let mut k := 0
  -- Each round divides delta by 35; 64 rounds cover any delta below 35^64.
  for _ in [0:64] do
    if delta > ((base - tmin) * tmax) / 2 then
      delta := delta / (base - tmin)
      k := k + base
  return k + ((base - tmin + 1) * delta) / (delta + skew)

/-- The value of a basic code point used as a digit, or `none`. -/
def digitOf (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48 + 26)
  else if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 65)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 97)
  else none

/-- The lower-case basic code point of a digit value (0 to 35). -/
def digitChar (d : Nat) : Char :=
  if d < 26 then Char.ofNat (97 + d) else Char.ofNat (48 + d - 26)

/-- The threshold `t` of RFC 3492 section 6.2 for position `k`. -/
def threshold (k bias : Nat) : Nat :=
  if k ≤ bias then tmin else if k ≥ bias + tmax then tmax else k - bias

/-- A bound above every code point; a value that passes it is an overflow. -/
def limit : Nat := 0x110000 * 0x10000

/-- RFC 3492 section 6.2, decoding. `none` is failure: a non-basic code point
before the last delimiter, a bad digit, an input that ends inside a number, a
result that is not a Unicode scalar value, or a basic code point in the
extended part. -/
def decode (input : List Char) : Option (Array Nat) := Id.run do
  let arr := input.toArray
  -- b: the position of the last delimiter, if any.
  let lastDelim := (List.range arr.size).foldl (fun acc i => if arr[i]! == '-' then some i else acc) none
  let mut out : Array Nat := #[]
  let mut pos := 0
  match lastDelim with
  | some b =>
    for i in [0:b] do
      let c := arr[i]!
      if c.toNat ≥ 0x80 then return none
      out := out.push c.toNat
    pos := b + 1
  | none => pos := 0
  let mut n := initialN
  let mut i := 0
  let mut bias := initialBias
  -- Each outer round reads at least one input digit.
  for _ in [0:arr.size + 1] do
    if pos ≥ arr.size then return some out
    let oldi := i
    let mut w := 1
    let mut k := base
    let mut done := false
    for _ in [0:arr.size + 1] do
      if !done then
        if pos ≥ arr.size then return none
        let some digit := digitOf arr[pos]! | return none
        pos := pos + 1
        i := i + digit * w
        if i ≥ limit then return none
        let t := threshold k bias
        if digit < t then done := true
        else
          w := w * (base - t)
          if w ≥ limit then return none
          k := k + base
    if !done then return none
    let len := out.size + 1
    bias := adapt (i - oldi) len (oldi == 0)
    n := n + i / len
    i := i % len
    if n < 0x80 || n > 0x10FFFF || (0xD800 ≤ n && n ≤ 0xDFFF) then return none
    out := (out.insertIdxIfInBounds i n)
    i := i + 1
  return some out

/-- RFC 3492 section 6.3, encoding. -/
def encode (input : Array Nat) : String := Id.run do
  let mut out : String := ""
  for c in input do
    if c < 0x80 then out := out.push (Char.ofNat c)
  let b := out.length
  let mut h := b
  if b > 0 then out := out.push '-'
  let mut n := initialN
  let mut delta := 0
  let mut bias := initialBias
  -- Each outer round handles at least one non-basic code point.
  for _ in [0:input.size + 1] do
    if h < input.size then
      let m := input.foldl (fun acc c => if c ≥ n && c < acc then c else acc) (0x110000 + 1)
      delta := delta + (m - n) * (h + 1)
      n := m
      for c in input do
        if c < n then delta := delta + 1
        if c == n then
          let mut q := delta
          let mut k := base
          -- q falls by a factor of at least 10 each round while it can.
          for _ in [0:64] do
            let t := threshold k bias
            if q ≥ t then
              out := out.push (digitChar (t + (q - t) % (base - t)))
              q := (q - t) / (base - t)
              k := k + base
          out := out.push (digitChar q)
          bias := adapt delta (h + 1) (h == b)
          delta := 0
          h := h + 1
      delta := delta + 1
      n := n + 1
  return out

#guard encode #[0x62, 0xFC, 0x63, 0x68, 0x65, 0x72] == "bcher-kva"
#guard decode "bcher-kva".toList == some #[0x62, 0xFC, 0x63, 0x68, 0x65, 0x72]
-- RFC 3492 section 7.1 (A) Arabic (Egyptian).
#guard encode #[0x0644, 0x064A, 0x0647, 0x0645, 0x0627, 0x0628, 0x062A, 0x0643, 0x0644,
  0x0645, 0x0648, 0x0634, 0x0639, 0x0631, 0x0628, 0x064A, 0x061F] == "egbpdaj6bu4bxfgehfvwxn"
#guard decode "egbpdaj6bu4bxfgehfvwxn".toList == some #[0x0644, 0x064A, 0x0647, 0x0645,
  0x0627, 0x0628, 0x062A, 0x0643, 0x0644, 0x0645, 0x0648, 0x0634, 0x0639, 0x0631, 0x0628,
  0x064A, 0x061F]

end Punycode

/-! ## Processing (UTS #46 section 4) -/

/-- The UTS #46 flags. The defaults are those of the URL Standard's "domain to
ASCII" with beStrict false. -/
structure Options where
  checkHyphens : Bool := false
  checkBidi : Bool := true
  checkJoiners : Bool := true
  useSTD3ASCIIRules : Bool := false
  transitional : Bool := false
  verifyDnsLength : Bool := false
  ignoreInvalidPunycode : Bool := false

def toStr (xs : Array Nat) : String := String.ofList (xs.toList.map Char.ofNat)
def ofStr (s : String) : Array Nat := (s.toList.map Char.toNat).toArray

/-- Step 1, Map. A disallowed code point stays; step 4 records the error. -/
def mapCps (opts : Options) (input : Array Nat) : Array Nat :=
  input.foldl (fun acc c =>
    match status c with
    | .valid => acc.push c
    | .deviation =>
      if opts.transitional then
        match c with
        | 0x00DF => acc ++ #[0x73, 0x73]
        | 0x03C2 => acc.push 0x03C3
        | 0x200C | 0x200D => acc
        | _ => acc.push c
      else acc.push c
    | .mapped m => acc ++ m
    | .ignored => acc
    | .disallowed => acc.push c) #[]

/-- Step 2, Normalize to NFC. -/
def nfc (s : String) : String := (L4Factoidal.XPath4.Unicode.normalize "NFC" s).getD s

/-- Split at U+002E FULL STOP (step 3). -/
def splitLabels (s : String) : List String := s.splitOn "."

def isAsciiLabel (s : String) : Bool := s.toList.all (fun c => c.toNat < 0x80)

/-- RFC 5892 Appendix A.1 and A.2: every ZERO WIDTH NON-JOINER and ZERO WIDTH
JOINER of the label is in a permitted context. -/
def contextJ (label : Array Nat) : Bool := Id.run do
  for i in [0:label.size] do
    let c := label[i]!
    if c == 0x200C || c == 0x200D then
      let afterVirama := i > 0 && isVirama label[i - 1]!
      if !afterVirama then
        if c == 0x200D then return false
        -- (Joining_Type:{L,D})(Joining_Type:T)* before, (Joining_Type:T)*(Joining_Type:{R,D}) after.
        let mut leftOk := false
        let mut stop := false
        for j' in [0:i] do
          let j := i - 1 - j'
          if !stop then
            let t := joiningType label[j]!
            if t == "T" then pure ()
            else
              leftOk := t == "L" || t == "D"
              stop := true
        let mut rightOk := false
        stop := false
        for j in [i + 1:label.size] do
          if !stop then
            let t := joiningType label[j]!
            if t == "T" then pure ()
            else
              rightOk := t == "R" || t == "D"
              stop := true
        if !(leftOk && rightOk) then return false
  return true

/-- The Bidi Rule of RFC 5893 section 2, for a non-empty label. -/
def bidiRule (label : Array Nat) : Bool :=
  match label[0]? with
  | none => true
  | some c0 =>
    let first := bidiClass c0
    let classes := label.map bidiClass
    -- The last class that is not NSM.
    let trimmed := (classes.toList.reverse.dropWhile (· == "NSM"))
    let lastCls := trimmed.headD ""
    if first == "R" || first == "AL" then
      -- Rules 2, 3, 4.
      classes.all (fun k => ["R", "AL", "AN", "EN", "ES", "CS", "ET", "ON", "BN", "NSM"].contains k)
        && ["R", "AL", "EN", "AN"].contains lastCls
        && !(classes.contains "EN" && classes.contains "AN")
    else if first == "L" then
      -- Rules 5, 6.
      classes.all (fun k => ["L", "EN", "ES", "CS", "ET", "ON", "BN", "NSM"].contains k)
        && ["L", "EN"].contains lastCls
    else false

/-- RFC 5893 section 1.4: a label that contains a code point of class R, AL
or AN. -/
def isRtlLabel (label : Array Nat) : Bool :=
  label.any (fun c => let k := bidiClass c; k == "R" || k == "AL" || k == "AN")

/-- UTS #46 section 4.1, Validity Criteria, except the Bidi criterion, which
needs the whole domain name (`process` applies it). -/
def validLabel (opts : Options) (label : String) : Bool :=
  let cps := ofStr label
  let chars := label.toList
  nfc label == label
    && (!opts.checkHyphens ||
        (!(chars.length ≥ 4 && chars[2]! == '-' && chars[3]! == '-')
          && !label.startsWith "-" && !label.endsWith "-"))
    && (opts.checkHyphens || !label.startsWith "xn--")
    && !chars.contains '.'
    && (match cps[0]? with | some c => !isMark c | none => true)
    && cps.all (fun c =>
        match status c with
        | .valid => !opts.useSTD3ASCIIRules || c ≥ 0x80 ||
            (0x61 ≤ c && c ≤ 0x7A) || (0x30 ≤ c && c ≤ 0x39) || c == 0x2D
        | .deviation => !opts.transitional
        | _ => false)
    && (!opts.checkJoiners || contextJ cps)

/-- UTS #46 section 4, Processing: the processed labels and whether an error
was recorded. -/
def process (opts : Options) (domain : String) : List String × Bool :=
  let mapped := nfc (toStr (mapCps opts (ofStr domain)))
  let step := fun (label : String) =>
    if label.startsWith "xn--" then
      if !isAsciiLabel label then (label, false)
      else match Punycode.decode (label.toList.drop 4) with
        | none => (label, false)
        | some cps =>
          let dec := toStr cps
          if dec.isEmpty || isAsciiLabel dec then (dec, false)
          else (dec, validLabel opts dec)
    else (label, validLabel opts label)
  let results := (splitLabels mapped).map step
  let labels := results.map (·.1)
  let ok := results.all (·.2)
  let bidiDomain := labels.any (fun l => isRtlLabel (ofStr l))
  let bidiOk := !opts.checkBidi || !bidiDomain ||
    labels.all (fun l => l.isEmpty || bidiRule (ofStr l))
  (labels, ok && bidiOk)

/-- UTS #46 section 4.2, ToASCII. `none` when an error was recorded. -/
def toASCII (opts : Options) (domain : String) : Option String :=
  let (labels, ok) := process opts domain
  if !ok then none
  else
    let out := labels.map (fun l => if isAsciiLabel l then l else "xn--" ++ Punycode.encode (ofStr l))
    let joined := ".".intercalate out
    if opts.verifyDnsLength then
      let ls := joined.splitOn "."
      let ls' := if ls.length > 1 && ls.getLast! == "" then ls.dropLast else ls
      if joined.length == 0 || joined.length > 253 || ls'.any (fun l => l.length == 0 || l.length > 63)
      then none else some joined
    else some joined

#guard toASCII {} "faß.de" == some "xn--fa-hia.de"
#guard toASCII {} "Fass.DE" == some "fass.de"
#guard toASCII {} "xn--fa-hia.de" == some "xn--fa-hia.de"
#guard toASCII {} "a‌b" == none
#guard toASCII {} "xn--a" == none

end L4Factoidal.WHATWG.URL.Idna
