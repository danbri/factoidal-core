/-
L4Factoidal.XPath4.Collation — collations of F&O 4.0 §5.2 and the
substring matching of §5.4.

The collations:

* the Unicode codepoint collation (§5.2.3);
* the HTML ASCII case-insensitive collation (§5.2.6) and the Unicode
  case-insensitive collation (§5.2.5): the strings are folded (ASCII
  letters; `fn:lower-case`) and compared by codepoint; every character is
  one collation unit;
* the Unicode Collation Algorithm family `http://www.w3.org/2013/collation/UCA`
  (§5.2.4, UTS #10): NFD (S1), the longest contiguous match in the DUCET
  of UCA 16.0.0 (`XPath4.UcaData`) with the discontiguous match of
  S2.1.1-S2.1.3, implicit weights (§10.1.3), variable weighting (§4), and
  the sort key of S3 (levels separated by a zero weight). A collation unit
  of §5.4 is one collation element; a unit covers the characters of the
  input from which its collation element came, and a match must begin and
  end at a boundary between units of different characters.

Implementation-defined choices (F&O 4.0 §5.2.4):

* Parameters supported: `fallback`, `strength` (1 to 5 and the names),
  `alternate` (`non-ignorable`, `shifted`, `blanked`), `maxVariable` (also
  spelled `max-variable`), `backwards` (reversed secondary level),
  `caseFirst` (`upper`, `lower`; `upper` orders the tertiary weights of
  upper-case forms before those of the other forms), `caseLevel` (a case
  level after the primary level, or after the secondary level when the
  strength is 2 or more), `numeric` (a maximal run of characters whose
  collation element has a digit primary weight sorts by its numeric
  value: leading zeros are ignored, one collation element gives the count
  of significant digits, then one per digit; a count above 9 is written
  as 9, so two runs of 9 or more significant digits compare digit by
  digit), `normalization` (the input is always converted to NFD,
  both values are accepted), `version` (`16`, `16.0`, `16.0.0`).
* Tailorings: none. `lang` selects the DUCET root order for every
  language. With `fallback=no`, a `lang` other than `en`, `en-*`, `und`
  or `root` is refused (FOCH0002), as are `reorder`, a `version` other
  than 16.0.0, an unknown keyword and an unknown value. With
  `fallback=yes` (the default) these are ignored.
* Defaults: tertiary strength, `alternate=non-ignorable`,
  `maxVariable=punct`, `caseFirst=lower`.
* A relative collation URI is resolved against the static base URI; with
  no base URI it is refused (FOCH0002).
-/
import L4Factoidal.XPath4.Core
import L4Factoidal.XPath4.Unicode
import L4Factoidal.XPath4.UcaData
import L4Factoidal.Fn.String
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.XPath4

open Std

namespace Uca

/-- A collation element: primary, secondary and tertiary weight. -/
structure CE where
  p : Nat
  s : Nat
  t : Nat
deriving Inhabited, BEq

def parseCE (str : String) : CE :=
  let body := if str.startsWith "*" then (str.drop 1).toString else str
  match body.splitOn "." with
  | [p] => ⟨Unicode.hexVal p, 0x20, 2⟩
  | [p, s] => ⟨Unicode.hexVal p, Unicode.hexVal s, 2⟩
  | [p, s, t] => ⟨Unicode.hexVal p, Unicode.hexVal s, Unicode.hexVal t⟩
  | _ => ⟨0, 0, 0⟩

structure Table where
  single : HashMap Nat (Array CE) := {}
  multi : HashMap (List Nat) (Array CE) := {}
  /-- Every proper prefix of a contraction. -/
  prefixes : HashSet (List Nat) := {}
deriving Inhabited

def buildTable (_ : Unit) : Table := Id.run do
  let mut tb : Table := {}
  for r in UcaData.ducetText.splitOn ";" do
    match r.splitOn ":" with
    | [k, v] =>
      let ces := ((v.splitOn "|").map parseCE).toArray
      if k.contains ' ' then
        let cps := (k.splitOn " ").map Unicode.hexVal
        let mut pre := tb.prefixes
        for i in [1:cps.length] do pre := pre.insert (cps.take i)
        tb := { tb with multi := tb.multi.insert cps ces, prefixes := pre }
      else
        match k.splitOn "+" with
        | [c] => tb := { tb with single := tb.single.insert (Unicode.hexVal c) ces }
        | [c, n] =>
          let c0 := Unicode.hexVal c
          let ce := ces.getD 0 default
          let mut m := tb.single
          for i in [0:Unicode.hexVal n + 1] do m := m.insert (c0 + i) #[{ ce with p := ce.p + i }]
          tb := { tb with single := m }
        | _ => pure ()
    | _ => pure ()
  pure tb

/-- The DUCET, parsed on first use. -/
def table : Thunk Table := Thunk.mk buildTable

/-- Implicit weights (UTS #10 §10.1.3). -/
def implicitCEs (c : Nat) : Array CE :=
  match UcaData.implicitRanges.find? (fun (a, b, _) => a ≤ c && c ≤ b) with
  | some (a, _, base) => #[⟨base, 0x20, 2⟩, ⟨(c - a) ||| 0x8000, 0, 0⟩]
  | none =>
    let base :=
      if UcaData.unifiedIdeographs.any (fun (a, b) => a ≤ c && c ≤ b) then
        (if (0x4E00 ≤ c && c ≤ 0x9FFF) || (0xF900 ≤ c && c ≤ 0xFAFF) then 0xFB40 else 0xFB80)
      else 0xFBC0
    #[⟨base + (c >>> 15), 0x20, 2⟩, ⟨(c &&& 0x7FFF) ||| 0x8000, 0, 0⟩]

inductive Alt where
  | nonIgnorable
  | shifted
  | blanked
deriving Inhabited, BEq, Repr

structure Opts where
  strength : Nat := 3
  alt : Alt := .nonIgnorable
  /-- The last primary weight that is variable (`maxVariable`). -/
  maxVar : Nat := UcaData.topPunct
  backwards : Bool := false
  upperFirst : Bool := false
  caseLevel : Bool := false
  numeric : Bool := false
deriving Inhabited, BEq, Repr

/-- The NFD form of `s` (UTS #10 S1.1), each code point with the index of
    the character of `s` it came from. -/
def nfdTagged (s : String) : Array (Nat × Nat) := Id.run do
  let mut a : Array (Nat × Nat) := #[]
  let mut i := 0
  for c in s.toList do
    for d in Unicode.decompChar false c.toNat do a := a.push (d, i)
    i := i + 1
  for j in [1:a.size] do
    let mut k := j
    for _ in [0:j] do
      if k == 0 then break
      let x := a.getD k (0, 0)
      let y := a.getD (k - 1) (0, 0)
      let cx := Unicode.ccc x.1
      if cx != 0 && Unicode.ccc y.1 > cx then
        a := (a.set! k y).set! (k - 1) x
        k := k - 1
      else break
  pure a

/-- The decimal digit value of a code point whose one collation element
    has a digit primary weight. -/
def digitOf (tb : Table) (c : Nat) : Option (Nat × CE) :=
  let p0 := ((tb.single.getD 0x30 #[]).getD 0 default).p
  match tb.single.get? c with
  | some #[ce] => if p0 ≤ ce.p && ce.p ≤ p0 + 9 then some (ce.p - p0, ce) else none
  | _ => none

/-- The collation elements of `s` (UTS #10 S2), each with the range of
    characters of `s` it came from. -/
def collElems (o : Opts) (s : String) : Array (CE × Nat × Nat) := Id.run do
  let tb := table.get
  let p0 := ((tb.single.getD 0x30 #[]).getD 0 default).p
  let mut a := nfdTagged s
  let mut out : Array (CE × Nat × Nat) := #[]
  let mut i := 0
  for _ in [0:a.size + 1] do
    if i ≥ a.size then break
    let (c, oi) := a.getD i (0, 0)
    -- numeric: a maximal run of digits
    if o.numeric && (digitOf tb c).isSome then
      let mut j := i
      let mut ds : Array (Nat × CE) := #[]
      for _ in [0:a.size] do
        match a[j]? with
        | some (cj, _) =>
          match digitOf tb cj with
          | some d => ds := ds.push d; j := j + 1
          | none => break
        | none => break
      let lastO := (a.getD (j - 1) (0, 0)).2
      let sig := (ds.toList.dropWhile (fun d => d.1 == 0)).toArray
      let sig := if sig.isEmpty then #[(0, (ds.getD 0 default).2)] else sig
      out := out.push (⟨p0 + min sig.size 9, 0x20, 2⟩, oi, lastO + 1)
      for (v, ce) in sig do out := out.push (⟨p0 + v, ce.s, ce.t⟩, oi, lastO + 1)
      i := j
      continue
    -- S2.1: the longest initial substring that has a match
    let mut len := 1
    let mut ces := tb.single.get? c
    if tb.prefixes.contains [c] then
      for k in [0:UcaData.maxContraction - 1] do
        let l := UcaData.maxContraction - k
        if i + l ≤ a.size then
          let key := (List.range l).map (fun q => (a.getD (i + q) (0, 0)).1)
          match tb.multi.get? key with
          | some x => len := l; ces := some x; break
          | none => pure ()
    let mut key := (List.range len).map (fun q => (a.getD (i + q) (0, 0)).1)
    let mut st := oi
    let mut en := oi + 1
    for q in [0:len] do
      let o2 := (a.getD (i + q) (0, 0)).2
      st := min st o2
      en := max en (o2 + 1)
    -- S2.1.1-S2.1.3: unblocked non-starters that extend the match
    if tb.prefixes.contains key then
      let mut j := i + len
      let mut lastSkipped := 0
      for _ in [0:a.size] do
        match a[j]? with
        | none => break
        | some (cj, oj) =>
          let cc := Unicode.ccc cj
          if cc == 0 then break
          let unblocked := lastSkipped == 0 || lastSkipped < cc
          match (if unblocked then tb.multi.get? (key ++ [cj]) else none) with
          | some x =>
            key := key ++ [cj]
            ces := some x
            st := min st oj
            en := max en (oj + 1)
            a := a.eraseIdxIfInBounds j
          | none =>
            lastSkipped := cc
            j := j + 1
    let found := match ces with
      | some x => x
      | none => implicitCEs c
    for ce in found do out := out.push (ce, st, en)
    i := i + len
  pure out

def isUpperT (t : Nat) : Bool :=
  t == 0x8 || t == 0x9 || t == 0xA || t == 0xB || t == 0xC || t == 0x1D

/-- A weighted collation element: the three levels, the quaternary
    level of the variable weighting (UTS #10 §4), and the case weight. -/
structure W where
  p : Nat
  s : Nat
  t : Nat
  q : Nat
  cs : Nat
  st : Nat
  en : Nat
deriving Inhabited

/-- Variable weighting (UTS #10 §4, Table 11) and the case options. -/
def weigh (o : Opts) (ces : Array (CE × Nat × Nat)) : Array W := Id.run do
  let mut out : Array W := #[]
  let mut afterVar := false
  for (ce, st, en) in ces do
    let isVar := ce.p != 0 && ce.p ≤ o.maxVar
    let t := if ce.t == 0 then 0 else if o.upperFirst then (if isUpperT ce.t then ce.t else ce.t + 0x20) else ce.t
    let cs := if ce.p == 0 then 0 else if isUpperT ce.t then (if o.upperFirst then 1 else 2) else (if o.upperFirst then 2 else 1)
    match o.alt with
    | .nonIgnorable => out := out.push ⟨ce.p, ce.s, t, 0, cs, st, en⟩
    | .shifted | .blanked =>
      let q4 := o.alt == .shifted
      if isVar then
        out := out.push ⟨0, 0, 0, if q4 then ce.p else 0, 0, st, en⟩
        afterVar := true
      else if ce.p == 0 && ce.s == 0 && ce.t == 0 then
        out := out.push ⟨0, 0, 0, 0, 0, st, en⟩
      else if ce.p == 0 && afterVar then
        out := out.push ⟨0, 0, 0, 0, 0, st, en⟩
      else
        out := out.push ⟨ce.p, ce.s, t, if q4 then 0xFFFF else 0, cs, st, en⟩
        afterVar := false
  pure out

def Opts.caseLevelAfterPrimary (o : Opts) : Bool := o.caseLevel && o.strength == 1
def Opts.caseLevelAfterSecondary (o : Opts) : Bool := o.caseLevel && o.strength ≥ 2
def Opts.hasQuaternary (o : Opts) : Bool := o.strength ≥ 4 && o.alt == .shifted

/-- The sort key of UTS #10 S3: 16-bit weights, levels separated by a
    zero weight, then (strength 5) the NFD code points as 24-bit units. -/
def sortKey (o : Opts) (s : String) : List Nat := Id.run do
  let ws := weigh o (collElems o s)
  let mut out : Array Nat := #[]
  let push16 (a : Array Nat) (w : Nat) : Array Nat := (a.push (w >>> 8)).push (w &&& 0xFF)
  for w in ws do if w.p != 0 then out := push16 out w.p
  if o.caseLevelAfterPrimary then
    out := push16 out 0
    for w in ws do if w.p != 0 then out := push16 out w.cs
  if o.strength ≥ 2 then
    out := push16 out 0
    let l2 := ws.filterMap (fun w => if w.s != 0 then some w.s else none)
    for w in (if o.backwards then l2.reverse else l2) do out := push16 out w
  if o.caseLevelAfterSecondary then
    out := push16 out 0
    for w in ws do if w.p != 0 then out := push16 out w.cs
  if o.strength ≥ 3 then
    out := push16 out 0
    for w in ws do if w.t != 0 then out := push16 out w.t
  if o.hasQuaternary then
    out := push16 out 0
    for w in ws do if w.q != 0 then out := push16 out w.q
  if o.strength ≥ 5 then
    out := push16 out 0
    for c in Unicode.decompose false s do
      out := ((out.push (c >>> 16)).push ((c >>> 8) &&& 0xFF)).push (c &&& 0xFF)
  pure out.toList

/-- The collation units of `s` for substring matching: the weights of
    each collation element at the levels of `o` (an ignorable one is
    left out), with its character range. -/
def units (o : Opts) (s : String) : Array (List Nat × Nat × Nat) :=
  (weigh o (collElems o s)).filterMap (fun w =>
    let k := [w.p,
      if o.strength ≥ 2 then w.s else 0,
      if o.strength ≥ 3 then w.t else 0,
      if o.hasQuaternary then w.q else 0,
      if o.caseLevel then w.cs else 0]
    if k.all (· == 0) then none else some (k, w.st, w.en))

end Uca

/-! ## Collation values -/

inductive Coll where
  | codepoint
  | htmlAscii
  | unicodeCI
  | uca (o : Uca.Opts)
deriving Inhabited, BEq, Repr

def codepointCollation : String := "http://www.w3.org/2005/xpath-functions/collation/codepoint"
def htmlAsciiCollation : String := "http://www.w3.org/2005/xpath-functions/collation/html-ascii-case-insensitive"
def unicodeCICollation : String := "http://www.w3.org/2005/xpath-functions/collation/unicode-case-insensitive"
def ucaCollation : String := "http://www.w3.org/2013/collation/UCA"

def asciiLower (s : String) : String :=
  String.ofList (s.toList.map (fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c))

def collHasScheme (u : String) : Bool :=
  match u.splitOn ":" with
  | sch :: _ :: _ => sch != "" && sch.all (fun c => c.isAlphanum || c == '+' || c == '-' || c == '.')
      && (sch.toList.headD ' ').isAlpha
  | _ => false

/-- A relative collation URI resolved against the static base URI
    (F&O 4.0 §5.2.7). -/
def resolveCollationUri (base u : String) : M String :=
  if collHasScheme u then pure u
  else if base == "" then err "FOCH0002" ("relative collation URI " ++ u ++ " and no base URI")
  else if u.startsWith "/" then
    match base.splitOn "//" with
    | sch :: rest :: _ => pure (sch ++ "//" ++ ((rest.splitOn "/").headD "") ++ u)
    | _ => pure u
  else
    let dir := match (base.splitOn "/").dropLast with | [] => "" | ps => String.intercalate "/" ps ++ "/"
    pure (dir ++ u)

/-- The parameters of a UCA collation URI (F&O 4.0 §5.2.4). -/
def parseUca (query : String) : M Coll := do
  let params := (query.splitOn ";").filter (· != "") |>.map (fun p =>
    match p.splitOn "=" with
    | k :: rest => (k, String.intercalate "=" rest)
    | [] => ("", ""))
  -- the last occurrence of a keyword wins
  let mut kv : List (String × String) := []
  for (k, v) in params do kv := (kv.filter (·.1 != k)) ++ [(k, v)]
  let fallback ← match kv.lookup "fallback" with
    | none | some "yes" => pure true
    | some "no" => pure false
    | some v => err "FOCH0002" ("invalid fallback value " ++ v)
  let mut o : Uca.Opts := {}
  let bad (what : String) : M Unit :=
    if fallback then pure () else err "FOCH0002" ("unsupported UCA collation parameter " ++ what)
  let yesNo (v : String) : Option Bool := if v == "yes" then some true else if v == "no" then some false else none
  for (k, v) in kv do
    match k with
    | "fallback" => pure ()
    | "strength" =>
      match v with
      | "primary" | "1" => o := { o with strength := 1 }
      | "secondary" | "2" => o := { o with strength := 2 }
      | "tertiary" | "3" => o := { o with strength := 3 }
      | "quaternary" | "4" => o := { o with strength := 4 }
      | "identical" | "5" => o := { o with strength := 5 }
      | _ => bad (k ++ "=" ++ v)
    | "alternate" =>
      match v with
      | "non-ignorable" => o := { o with alt := .nonIgnorable }
      | "shifted" => o := { o with alt := .shifted }
      | "blanked" => o := { o with alt := .blanked }
      | _ => bad (k ++ "=" ++ v)
    | "maxVariable" | "max-variable" =>
      match v with
      | "space" => o := { o with maxVar := UcaData.topSpace }
      | "punct" => o := { o with maxVar := UcaData.topPunct }
      | "symbol" => o := { o with maxVar := UcaData.topSymbol }
      | "currency" => o := { o with maxVar := UcaData.topCurrency }
      | _ => bad (k ++ "=" ++ v)
    | "backwards" =>
      match yesNo v with
      | some b => o := { o with backwards := b }
      | none => bad (k ++ "=" ++ v)
    | "normalization" =>
      match yesNo v with
      | some _ => pure ()
      | none => bad (k ++ "=" ++ v)
    | "caseLevel" =>
      match yesNo v with
      | some b => o := { o with caseLevel := b }
      | none => bad (k ++ "=" ++ v)
    | "numeric" =>
      match yesNo v with
      | some b => o := { o with numeric := b }
      | none => bad (k ++ "=" ++ v)
    | "caseFirst" =>
      match v with
      | "upper" => o := { o with upperFirst := true }
      | "lower" | "off" => o := { o with upperFirst := false }
      | _ => bad (k ++ "=" ++ v)
    | "lang" =>
      let l := v.toLower
      if !(l == "" || l == "en" || l.startsWith "en-" || l == "und" || l == "root") then bad (k ++ "=" ++ v)
    | "version" =>
      if !(v == "16" || v == "16.0" || v == "16.0.0") then bad (k ++ "=" ++ v)
    | "reorder" => if v != "" then bad (k ++ "=" ++ v)
    | _ => bad k
  pure (.uca o)

/-- The collation a collation URI names (F&O 4.0 §5.2.7): FOCH0002 for
    one this processor does not provide. -/
def collationOf (base uri : String) : M Coll := do
  let u ← resolveCollationUri base uri
  if u == codepointCollation then pure .codepoint
  else if u == htmlAsciiCollation then pure .htmlAscii
  else if u == unicodeCICollation then pure .unicodeCI
  else if u == ucaCollation then pure (.uca {})
  else if u.startsWith (ucaCollation ++ "?") then parseUca (u.drop (ucaCollation.length + 1)).toString
  else err "FOCH0002" ("unsupported collation " ++ uri)

/-- The collation of a `$collation` argument: the default collation when
    it is absent or the empty sequence. -/
def Env.collation (e : Env) (c : Seq) : M Coll :=
  let u := match c with
    | [.atom a] => a.str
    | _ => e.defaultCollation
  if u == codepointCollation then pure .codepoint else collationOf e.baseUri u

def Coll.isCodepoint : Coll → Bool
  | .codepoint => true
  | _ => false

/-- The default collation of the static context, as a collation (the
    codepoint collation if its URI is not known). -/
def Env.defaultColl (e : Env) : Coll :=
  if e.defaultCollation == codepointCollation then .codepoint
  else (collationOf e.baseUri e.defaultCollation).toOption.getD .codepoint

def codepointKey (s : String) : List Nat :=
  s.toList.foldr (fun c acc => let n := c.toNat; (n >>> 16) :: ((n >>> 8) &&& 0xFF) :: (n &&& 0xFF) :: acc) []

/-- The collation key (F&O 4.0 §5.2.11): octets whose order is the order
    of the strings under the collation. -/
def Coll.key (c : Coll) (s : String) : List Nat :=
  match c with
  | .codepoint => codepointKey s
  | .htmlAscii => codepointKey (asciiLower s)
  | .unicodeCI => codepointKey (Fn.String.lowerCase s)
  | .uca o => Uca.sortKey o s

def Coll.compare (c : Coll) (a b : String) : Ordering :=
  match c with
  | .codepoint => if a < b then .lt else if a == b then .eq else .gt
  | .htmlAscii => let x := asciiLower a; let y := asciiLower b; if x < y then .lt else if x == y then .eq else .gt
  | .unicodeCI =>
    let x := Fn.String.lowerCase a; let y := Fn.String.lowerCase b
    if x < y then .lt else if x == y then .eq else .gt
  | .uca o => Ord.compare (Uca.sortKey o a) (Uca.sortKey o b)

def Coll.eq (c : Coll) (a b : String) : Bool := c.compare a b == .eq

/-! ## Substring matching (F&O 4.0 §5.4) -/

/-- The collation units of `s`: a key for each unit, and the range of
    characters it covers. Ignorable units are left out. -/
def Coll.units (c : Coll) (s : String) : Array (List Nat × Nat × Nat) :=
  match c with
  | .uca o => Uca.units o s
  | _ => Id.run do
    let mut out : Array (List Nat × Nat × Nat) := #[]
    let mut i := 0
    for ch in s.toList do
      let k := match c with
        | .htmlAscii => (asciiLower (String.ofList [ch])).toList.map Char.toNat
        | .unicodeCI => (Fn.String.lowerCase (String.ofList [ch])).toList.map Char.toNat
        | _ => [ch.toNat]
      out := out.push (k, i, i + 1)
      i := i + 1
    pure out

/-- The matches of `p` in `q`: (index of the first unit, number of
    units), where the match begins and ends at a boundary between
    characters (§5.4, boundary condition B). -/
def matchesAt (qs ps : Array (List Nat × Nat × Nat)) : List Nat := Id.run do
  let m := ps.size
  let mut out : Array Nat := #[]
  if m > qs.size then return []
  for a in [0:qs.size - m + 1] do
    let mut ok := true
    for k in [0:m] do
      if (qs.getD (a + k) default).1 != (ps.getD k default).1 then ok := false; break
    if !ok then continue
    let startOk := a == 0 || (qs.getD (a - 1) default).2.1 != (qs.getD a default).2.1
      || (qs.getD (a - 1) default).2.2 != (qs.getD a default).2.2
    let lastU := qs.getD (a + m - 1) default
    let endOk := a + m == qs.size || (qs.getD (a + m) default).2.1 != lastU.2.1
      || (qs.getD (a + m) default).2.2 != lastU.2.2
    if startOk && endOk then out := out.push a
  pure out.toList

/-- Where `p` occurs in `q` under the collation, as character ranges
    (start of the match, end of the match); `none` when it does not
    occur. `first` selects the first match, otherwise the last. An empty
    or wholly ignorable `p` matches at the start (first) or the end. -/
def Coll.find (c : Coll) (q p : String) (first : Bool) : Option (Nat × Nat) :=
  let qs := c.units q
  let ps := c.units p
  if ps.isEmpty then
    let n := q.length
    some (if first then (0, 0) else (n, n))
  else
    let ms := matchesAt qs ps
    let pick := if first then ms.head? else ms.getLast?
    pick.map (fun a => ((qs.getD a default).2.1, (qs.getD (a + ps.size - 1) default).2.2))

def Coll.contains (c : Coll) (q p : String) : Bool := (c.find q p true).isSome

def Coll.startsWith (c : Coll) (q p : String) : Bool :=
  let ps := c.units p
  if ps.isEmpty then true else (matchesAt (c.units q) ps).head? == some 0

def Coll.endsWith (c : Coll) (q p : String) : Bool :=
  let ps := c.units p
  let qs := c.units q
  if ps.isEmpty then true
  else qs.size ≥ ps.size && (matchesAt qs ps).getLast? == some (qs.size - ps.size)

def charsTake (s : String) (n : Nat) : String := String.ofList (s.toList.take n)
def charsDrop (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

#guard (Uca.sortKey {} "a") < Uca.sortKey {} "b"
#guard Coll.compare (.uca { strength := 1 }) "abc" "ABC" == .eq
#guard Coll.compare (.uca {}) "abc" "ABC" == .lt
#guard Coll.compare (.uca { strength := 2 }) "pêche" "péché" == .gt
#guard Coll.compare (.uca { strength := 2, backwards := true }) "pêche" "péché" == .lt
#guard Coll.compare (.uca { strength := 3, alt := .shifted }) "a-bc" "abc" == .eq
#guard Coll.compare (.uca { strength := 4, alt := .shifted }) "a-bc" "abc" == .lt
#guard Coll.compare (.uca { numeric := true }) "ab1a" "ab12a" == .lt
#guard Coll.compare (.uca {}) "ab1a" "ab12a" == .gt
#guard Coll.compare (.uca { upperFirst := true }) "ab" "Ab" == .gt
#guard Coll.compare (.uca { strength := 1, caseLevel := true }) "Epee" "épee" == .gt
#guard Coll.contains (.uca { strength := 1 }) "dâtÅbase" "âtabÃse"
#guard !Coll.contains (.uca { strength := 2 }) "database" "dâta"
#guard Coll.contains (.uca { alt := .blanked }) "abc-def" "abcdef"

end L4Factoidal.XPath4
