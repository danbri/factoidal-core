/-
L4Factoidal.XPath4.Lib — the F&O 4.0 function library (the Stage 1
core): `fn:` strings, numerics, booleans, sequences, aggregates,
higher-order functions, node accessors and QNames; `map:`, `array:`
and `math:`. Collations: `XPath4.Collation`; a string comparison under
a collation other than the codepoint collation goes through the
collation key of the string (`collProxy`).

Every implementation receives its arguments ALREADY COERCED to the
parameter types of the F&O 4.0 signature (`XPath4.Catalog`, applied by
`XPath4.Eval`), so an implementation reads `xs:string?` as "zero or one
atomic value". A higher-order function calls back into the evaluator
through `Hooks.call`.

Not implemented (they raise `XPST0017` with "not implemented"): the
date/time formatting and arithmetic functions beyond the component
accessors, `fn:format-*`, `fn:analyze-string`, `fn:tokenize` with a
non-trivial pattern, JSON/CSV/XML/HTML parsing and serialization,
`fn:transform`, `fn:load-xquery-module`, `fn:normalize-unicode` beyond NFC on
input that is already NFC, and `fn:doc`/`fn:collection` beyond the
documents the caller registers.
-/
import L4Factoidal.XPath4.Core
import L4Factoidal.Fn.String
import L4Factoidal.Regex.XPath
import Std.Data.HashSet
import L4Factoidal.XPath4.Grapheme
import L4Factoidal.XPath4.Collation

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

structure Hooks where
  call : Item → List Seq → M Seq

abbrev LibFn := Hooks → Env → List Seq → M Seq

/-! ## Argument access -/

def argN (a : List Seq) (i : Nat) : Seq := a.getD i []

def optAtom (s : Seq) : Option Atomic :=
  match s with
  | [.atom x] => some x
  | _ => none

def strOf (s : Seq) : String := match optAtom s with | some x => x.str | none => ""
def intOf (s : Seq) : Int := match optAtom s with
  | some ⟨_, .int i⟩ => i
  | some a => match a.num? with
      | some (.d d) => Int.tdiv d.mantissa ((10 : Int) ^ d.scale)
      | some (.f f) | some (.g f) => Float.truncI f
      | _ => 0
  | none => 0
def boolOf (s : Seq) : Bool := match optAtom s with | some ⟨_, .bool b⟩ => b | _ => false

/-- Call a function item, dropping trailing arguments the function
    does not accept (XPath 4.0 §3.4.4 function coercion by arity). -/
def Hooks.callN (h : Hooks) (f : Item) (args : List Seq) : M Seq :=
  match f.fnArity with
  | some k => if k < args.length then h.call f (args.take k) else h.call f args
  | none => h.call f args

def Hooks.pred (h : Hooks) (f : Item) (args : List Seq) : M Bool := do
  let r ← h.callN f args
  match r with
  | [.atom ⟨_, .bool b⟩] => pure b
  | [] => pure false
  | _ => err "XPTY0004" "predicate must return xs:boolean"

def collationOk (c : Seq) : M Unit :=
  match optAtom c with
  | none => pure ()
  | some a =>
    let u := a.str
    if u == "http://www.w3.org/2005/xpath-functions/collation/codepoint" then pure ()
    else err "FOCH0002" ("unsupported collation " ++ u)

def isStrish (a : Atomic) : Bool := a.is .string || a.is .anyURI || a.ty == .untyped

/-- The value that stands for a string-like `a` under the collation `c`:
    a string whose codepoint order and equality are the order and
    equality of `a` under `c` (its collation key, one character per
    octet). Other values, and every value under the codepoint
    collation, stand for themselves. -/
def collProxy (c : Coll) (a : Atomic) : Atomic :=
  if !c.isCodepoint && isStrish a then
    ⟨a.ty, .str (String.ofList ((c.key a.str).map (fun b => Char.ofNat (b + 0x100))))⟩
  else a

/-! ## Strings -/

def cps (s : String) : List Char := s.toList

def substr (s : String) (start : Float) (len : Option Float) : String :=
  -- F&O 4.0 §5.4.3: characters at positions p with round(start) ≤ p < round(start)+round(len)
  let cs := cps s
  let rnd (f : Float) : Float := (f + 0.5).floor
  let st := rnd start
  let en : Float := match len with | some l => st + rnd l | none => (1.0 / 0.0)
  if st.isNaN || en.isNaN then ""
  else
    let sel := (List.range cs.length).filter (fun i =>
      let p := (i + 1).toFloat
      p ≥ st && p < en)
    String.ofList (sel.map (fun i => cs.getD i ' '))

def numFloat (s : Seq) : Float := match optAtom s with
  | some a => (a.num?.map Num.toFloat).getD (0.0 / 0.0)
  | none => 0.0 / 0.0

def normSpace (s : String) : String :=
  String.intercalate " " ((String.ofList (s.toList.map (fun c => if isWs c then ' ' else c))).splitOn " " |>.filter (· != ""))

def translateStr (s m t : String) : String :=
  let mc := cps m
  let tc := cps t
  String.ofList (cps s |>.filterMap (fun c =>
    match mc.findIdx? (· == c) with
    | some i => tc[i]?
    | none => some c))

/-- XML 1.1 `Char` (what XPath 4.0 strings may hold). -/
def isXmlCp (n : Nat) : Bool :=
  (0x1 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0x10FFFF)

def regexErr {α} : Regex.RegexError → M α
  | .invalidFlags f => err "FORX0001" ("invalid regex flags " ++ f)
  | .invalidPattern p => err "FORX0002" ("invalid or unsupported regex " ++ p)
  | .matchesEmptyString _ => err "FORX0003" "pattern matches the empty string"
  | .invalidReplacement r => err "FORX0004" ("invalid replacement " ++ r)

/-- The largest number in a `{m,n}` quantifier of a pattern. -/
def maxQuant (p : String) : Nat := Id.run do
  let mut best := 0
  let mut cur : Option Nat := none
  for c in p.toList do
    if c == '{' then cur := some 0
    else if c.isDigit then
      cur := cur.map (fun v => if v > 1000000 then v else v * 10 + (c.toNat - 48))
    else
      if let some v := cur then best := max best v
      cur := if c == ',' then (if cur.isSome then some 0 else none) else none
  pure best

def compileRe (p f : String) : M Regex.Compiled :=
  if maxQuant p > 1000 then err "FOER0000" "implementation limit: regex quantifier above 1000" else
  match Regex.compile p f with
  | .ok r => pure r
  | .error e => regexErr e

/-- `fn:tokenize` for a pattern with no metacharacters (literal
    separator), and the one-argument form. -/
def tokenizeLiteral (s sep : String) : List String :=
  if s == "" then [] else s.splitOn sep

def isRegexMeta (c : Char) : Bool := "\\^$.|?*+()[]{}".toList.contains c

/-! ## Numerics -/

def roundDec (d : Dec) (prec : Int) (halfEven : Bool) : Dec :=
  -- scale by 10^prec, round to integer, scale back
  let d := Dec.norm d
  let intDigits : Int := (natDigits d.mantissa.natAbs : Int) - (d.scale : Int)
  if prec ≥ 0 && d.scale ≤ prec.toNat then d
  else if prec < 0 && -prec > intDigits + 1 then Dec.zero
  else
    let num : Int := if prec ≥ 0 then d.mantissa * (10 : Int) ^ prec.toNat else d.mantissa
    let den : Int := if prec ≥ 0 then (10 : Int) ^ d.scale else (10 : Int) ^ d.scale * (10 : Int) ^ (-prec).toNat
    let q := Int.fdiv num den
    let r := num - q * den
    let rounded :=
      if 2 * r > den then q + 1
      else if 2 * r < den then q
      else if halfEven then (if q % 2 == 0 then q else q + 1)
      else q + 1
    if prec ≥ 0 then Dec.norm ⟨rounded, prec.toNat⟩ else Dec.ofInt (rounded * (10 : Int) ^ (-prec).toNat)

def roundNum (a : Atomic) (prec : Int) (halfEven : Bool) : Atomic :=
  match a.num? with
  | some (.i i) =>
      if prec ≥ 0 then Atomic.ofInt i else
      match (roundDec (Dec.ofInt i) prec halfEven).toInt? with
      | some v => Atomic.ofInt v | none => Atomic.ofInt i
  | some (.d d) => Atomic.ofDec (roundDec d prec halfEven)
  | some (.f f) | some (.g f) =>
      let mk := fun (x : Float) => if a.is .float then Atomic.ofFlt x else Atomic.ofDbl x
      if f.isNaN || f.isInf || f == 0 then a
      else
        let r := floatOfDec (roundDec (decOfFloat f) prec halfEven)
        mk (if r == 0 && f < 0 then -0.0 else r)
  | none => a

def numUnary (a : Atomic) (fi : Int → Int) (fd : Dec → Dec) (ff : Float → Float) : Atomic :=
  match a.num? with
  | some (.i i) => Atomic.ofInt (fi i)
  | some (.d d) => Atomic.ofDec (fd d)
  | some (.f f) => Atomic.ofFlt (ff f)
  | some (.g f) => Atomic.ofDbl (ff f)
  | none => a

def decFloor (d : Dec) : Dec := Dec.ofInt (Int.fdiv d.mantissa ((10 : Int) ^ d.scale))
def decCeil (d : Dec) : Dec := Dec.ofInt (-(Int.fdiv (-d.mantissa) ((10 : Int) ^ d.scale)))

def fFloor (f : Float) : Float := let r := f.floor; if r == 0 && f < 0 then -0.0 else r
def fCeil (f : Float) : Float := let r := f.ceil; if r == 0 && f < 0 then -0.0 else r

/-! ## Aggregates -/

def untypedToDouble (a : Atomic) : M Atomic :=
  if a.ty == .untyped then castAtomic a (.b .double) else pure a

def addAtoms (a b : Atomic) : M Atomic := do
  match a.num?, b.num? with
  | some x, some y => pure (← numArith .add x y).atomic
  | _, _ =>
    match a.v, b.v with
    | .x (.dur x), .x (.dur y) =>
        if (a.is .yearMonthDuration && b.is .yearMonthDuration) then
          pure ⟨.b .yearMonthDuration, .x (.dur { months := x.months + y.months, seconds := Dec.zero })⟩
        else if a.is .dayTimeDuration && b.is .dayTimeDuration then
          pure ⟨.b .dayTimeDuration, .x (.dur { months := 0, seconds := Dec.norm (Dec.add x.seconds y.seconds) })⟩
        else err "FORG0006" "cannot add these durations"
    | _, _ => err "FORG0006" "invalid argument to fn:sum/fn:avg"

def sumAtoms (as : List Atomic) (zero : Seq) : M Seq := do
  match as with
  | [] => pure zero
  | a :: rest =>
    let a ← untypedToDouble a
    if !(a.isNumeric || a.is .yearMonthDuration || a.is .dayTimeDuration) then
      err "FORG0006" ("cannot sum xs:" ++ a.ty.name)
    let mut acc := a
    for b in rest do
      let b ← untypedToDouble b
      acc ← addAtoms acc b
    pure (single acc)

def minMax (isMax : Bool) (as : List Atomic) : M Seq := do
  match as with
  | [] => pure []
  | _ =>
    let as ← as.mapM (fun a => if a.ty == .untyped then castAtomic a (.b .double) else pure a)
    -- promote numerics to a common type
    let numeric := as.all Atomic.isNumeric
    let as := if numeric then
        let r := as.foldl (fun m a => max m ((a.num?.map Num.rank).getD 0)) 0
        as.map (fun a => match a.num? with | some n => (n.promote r).atomic | none => a)
      else if as.all (fun a => a.is .string || a.is .anyURI) && as.any (fun a => a.is .anyURI) && as.any (fun a => a.is .string) then
        as.map (fun a => Atomic.ofStr a.str)
      else as
    if as.any (fun a => !(a.ty.ordered)) then err "FORG0006" "values are not ordered"
    -- NaN wins
    match as.find? (fun a => match a.num? with | some n => n.rank ≥ 2 && n.toFloat.isNaN | none => false) with
    | some nan => pure (single nan)
    | none =>
      let mut best := as.head!
      for b in as.tail do
        match ← atomicCmp b best with
        | some .gt => if isMax then best := b
        | some .lt => if !isMax then best := b
        | _ => pure ()
      pure (single best)

/-- `fn:min`/`fn:max` under a collation (F&O 4.0 §14.4.3): strings
    compare under `c`; other values as without one. -/
def minMaxC (c : Coll) (isMax : Bool) (as : List Atomic) : M Seq := do
  if c.isCodepoint then minMax isMax as else
  let as' ← as.mapM (fun a => if a.ty == .untyped then castAtomic a (.b .double) else pure a)
  match as' with
  | x :: rest =>
    if as'.all (fun a => a.is .string || a.is .anyURI) then
      let mut best := x
      for b in rest do
        match c.compare b.str best.str with
        | .gt => if isMax then best := b
        | .lt => if !isMax then best := b
        | .eq => pure ()
      let mixed := as'.any (fun a => a.is .anyURI) && as'.any (fun a => a.is .string)
      pure (single (if mixed then Atomic.ofStr best.str else best))
    else minMax isMax as
  | [] => pure []

/-! ## Sorting -/

/-- Stable merge sort with a comparator that may fail. -/
def msortM {α} (lt : α → α → M Bool) : Nat → List α → M (List α)
  | 0, xs => pure xs
  | f + 1, xs =>
    if xs.length ≤ 1 then pure xs
    else do
      let n := xs.length / 2
      let a ← msortM lt f (xs.take n)
      let b ← msortM lt f (xs.drop n)
      -- merge
      let mut out : Array α := #[]
      let mut l := a
      let mut r := b
      for _ in [0:a.length + b.length] do
        match l, r with
        | x :: xs', y :: ys' =>
            if ← lt y x then out := out.push y; r := ys'
            else out := out.push x; l := xs'
        | x :: xs', [] => out := out.push x; l := xs'
        | [], y :: ys' => out := out.push y; r := ys'
        | [], [] => pure ()
      pure out.toList

/-- Compare two atomic values for sorting (F&O 4.0 §15.2.4): NaN is
    least, values compare by `lt`; incomparable is XPTY0004. -/
def sortCmpAtom (a b : Atomic) : M Ordering := do
  let a := if a.ty == .untyped then Atomic.ofStr a.str else a
  let b := if b.ty == .untyped then Atomic.ofStr b.str else b
  let nanA := (a.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false
  let nanB := (b.num?.map (fun n => n.rank ≥ 2 && n.toFloat.isNaN)).getD false
  if nanA && nanB then pure .eq
  else if nanA then pure .lt
  else if nanB then pure .gt
  else match ← atomicCmp a b with
    | some o => pure o
    | none => pure .eq

def sortCmpKeys : List Atomic → List Atomic → M Ordering
  | [], [] => pure .eq
  | [], _ => pure .lt
  | _, [] => pure .gt
  | a :: as, b :: bs => do
    match ← sortCmpAtom a b with
    | .eq => sortCmpKeys as bs
    | o => pure o

/-! ## Maps and arrays -/

def mapGet (kvs : List (Atomic × Seq)) (k : Atomic) : Option Seq :=
  (kvs.find? (fun (k2, _) => atomicEqual k k2)).map (·.2)

def mapPut (kvs : List (Atomic × Seq)) (k : Atomic) (v : Seq) : List (Atomic × Seq) :=
  if kvs.any (fun (k2, _) => atomicEqual k k2) then
    kvs.map (fun (k2, v2) => if atomicEqual k k2 then (k, v) else (k2, v2))
  else kvs ++ [(k, v)]

def mapRemove (kvs : List (Atomic × Seq)) (k : Atomic) : List (Atomic × Seq) :=
  kvs.filter (fun (k2, _) => !atomicEqual k k2)

def asMap (s : Seq) : M (List (Atomic × Seq)) :=
  match s with
  | [.map kvs] => pure kvs
  | _ => err "XPTY0004" "expected a map"

def asArr (s : Seq) : M (List Seq) :=
  match s with
  | [.arr ms] => pure ms
  | _ => err "XPTY0004" "expected an array"

def arrIdx (ms : List Seq) (i : Int) : M Seq :=
  if i ≥ 1 && i.toNat ≤ ms.length then pure (ms.getD (i.toNat - 1) [])
  else err "FOAY0001" ("array index " ++ toString i ++ " out of bounds")

def mapItem (kvs : List (Atomic × Seq)) : Seq := [.map kvs]
def arrItem (ms : List Seq) : Seq := [.arr ms]

/-- `map:merge` duplicates option. -/
def mergeMaps (maps : List (List (Atomic × Seq))) (dup : String) : M (List (Atomic × Seq)) := do
  let mut acc : MB := {}
  for m in maps do
    for (k, v) in m do
      match acc.get? k with
      | none => acc := acc.set k v
      | some old =>
        match dup with
        | "use-first" => pure ()
        | "use-last" => acc := acc.set k v
        | "use-any" => pure ()
        | "combine" => acc := acc.set k (old ++ v)
        | "reject" => err "FOJS0003" "duplicate key in map:merge"
        | _ => err "FOJS0005" ("invalid duplicates option " ++ dup)
  pure acc.toList

def optionStr (opts : Seq) (key : String) (dflt : String) : String :=
  match opts with
  | [.map kvs] => match mapGet kvs (Atomic.ofStr key) with
      | some s => strOf s
      | none => dflt
  | _ => dflt

/-! ## The table -/

def qnOfAtom (a : Atomic) : Option QN := match a.v with | .qn q => some q | _ => none

def mathFn (f : Float → Float) : LibFn := fun _ _ a =>
  match optAtom (argN a 0) with
  | none => pure []
  | some x => pure (single (Atomic.ofDbl (f ((x.num?.map Num.toFloat).getD 0))))

def nodeArg (e : Env) (s : Seq) : M (Option NodeRef) :=
  match s with
  | [] => pure none
  | [.node n] => pure (some n)
  | _ => err "XPTY0004" "expected a node"

/-- The ancestors of a GNode (any order). -/
def Env.gAncestors (e : Env) (i : Item) : List Item :=
  match i with
  | .node n => (e.ancestors n).map Item.node
  | j@(.jnode ..) => jancestors j
  | _ => []

/-- One step of `fn:path` for a JNode (F&O 4.0 §14.1.10, "For a JNode"). -/
def jpathStep (k : Atomic) : String :=
  if k.isStringLike then
    let cs := k.str.toList.toArray
    if (match ncnameAt cs 0 with | some (_, j) => j == cs.size | none => false) then k.str
    else "\"" ++ String.intercalate "\"\"" (k.str.splitOn "\"") ++ "\""
  else if k.isNumeric then k.str
  else match k.v with
    | .qn q => "#" ++ q.eqn
    | .bool b => if b then "true()" else "false()"
    | _ => "child::{xs:" ++ k.ty.name ++ "(\"" ++ k.str ++ "\")}"

/-- `fn:path` of a JNode, relative to `origin` (a root by default). -/
def jpathOf (j : Item) (origin : Option Item) : M String := do
  let anc := (j :: jancestors j)
  match origin with
  | none =>
    let ks := ((j :: jancestors j).filterMap jkeyOf).reverse
    pure ("/" ++ String.intercalate "/" (ks.map jpathStep))
  | some o =>
    match anc.findIdx? (jsame o) with
    | some i =>
      let ks := ((anc.take i).filterMap jkeyOf).reverse
      pure (String.intercalate "/" (ks.map jpathStep))
    | none => err "FOPA0001" "the origin is not an ancestor of the node"

def Env.rootOf (e : Env) (n : NodeRef) : NodeRef :=
  match (e.ancestors n).getLast? with
  | some r => r
  | none => n

def Env.nodeName (e : Env) (n : NodeRef) : Option QN :=
  let r := e.nrec n
  match r.kind with
  | .element | .attribute | .pi => some r.name
  | .namespace => if r.name.loc == "" then none else some { uri := "", loc := r.name.loc }
  | _ => none

def distinctAtomsSlow (as : List Atomic) : List Atomic :=
  as.foldl (fun acc a =>
    let a' := if a.ty == .untyped then Atomic.ofStr a.str else a
    if acc.any (fun b => atomicEqual (if b.ty == .untyped then Atomic.ofStr b.str else b) a') then acc else acc ++ [a]) []

def distinctAtoms (as : List Atomic) : List Atomic :=
  if as.all (fun a => (sameKey a).isSome) then Id.run do
    let mut seen : Std.HashSet String := {}
    let mut out : Array Atomic := #[]
    for a in as do
      let k := (sameKey a).getD ""
      if !seen.contains k then
        seen := seen.insert k
        out := out.push a
    pure out.toList
  else distinctAtomsSlow as

/-- `fn:distinct-values` under a collation: the first item of each class
    of values equal under `c`. -/
def distinctAtomsC (c : Coll) (as : List Atomic) : List Atomic :=
  let ps := as.map (collProxy c)
  if ps.all (fun a => (sameKey a).isSome) then Id.run do
    let mut seen : Std.HashSet String := {}
    let mut out : Array Atomic := #[]
    for (a, p) in as.zip ps do
      let k := (sameKey p).getD ""
      if !seen.contains k then
        seen := seen.insert k
        out := out.push a
    pure out.toList
  else
    let norm (b : Atomic) : Atomic := if b.ty == .untyped then Atomic.ofStr b.str else b
    ((as.zip ps).foldl (fun acc (a, p) =>
      if acc.any (fun (_, q) => atomicEqual (norm q) (norm p)) then acc else acc ++ [(a, p)]) []).map (·.1)

/-- The values that occur more than once, first occurrence order of the
    second occurrence. -/
def duplicateAtoms (as : List Atomic) (eqf : Atomic → Atomic → Bool) : List Atomic :=
  if as.all (fun a => (sameKey a).isSome) then Id.run do
    let mut seen : Std.HashSet String := {}
    let mut reported : Std.HashSet String := {}
    let mut out : Array Atomic := #[]
    for a in as do
      let k := (sameKey a).getD ""
      if seen.contains k then
        if !reported.contains k then
          reported := reported.insert k
          out := out.push a
      else seen := seen.insert k
    pure out.toList
  else
    let rec go (xs : List Atomic) (seen : List Atomic) (out : List Atomic) : List Atomic :=
      match xs with
      | [] => out
      | x :: r =>
        if seen.any (fun s => eqf s x) && !out.any (fun s => eqf s x) then go r seen (out ++ [x])
        else go r (seen ++ [x]) out
    go as [] []

def eqForIndexOf (a b : Atomic) : Bool :=
  let a := if a.ty == .untyped then Atomic.ofStr a.str else a
  let b := if b.ty == .untyped then Atomic.ofStr b.str else b
  match atomicCmp a b with
  | .ok (some .eq) => true
  | _ => false

/-- F&O 4.0 `fn:slice` positions (0-based) for a sequence of `len` items. -/
def sliceIdx (len : Nat) (a1 a2 a3 : Seq) : List Nat :=
  let n : Int := len
  let norm (v : Seq) (d : Int) : Int :=
    match v with
    | [] => d
    | _ => let x := intOf v; if x == 0 then d else if x < 0 then n + x + 1 else x
  let st : Int := norm a1 1
  let en : Int := norm a2 n
  let step0 : Int := match a3 with | [] => 0 | v => intOf v
  let step : Int := if step0 == 0 then (if st ≤ en then 1 else -1) else step0
  if step > 0 then
    (List.range len).filter (fun (i : Nat) =>
      let p : Int := (i : Int) + 1
      decide (st ≤ p) && decide (p ≤ en) && (p - st) % step == 0)
  else
    ((List.range len).reverse).filter (fun (i : Nat) =>
      let p : Int := (i : Int) + 1
      decide (p ≤ st) && decide (en ≤ p) && (st - p) % (-step) == 0)

def ent (n : String) (f : LibFn) : String × LibFn := (n, f)

/-- The ·jvalue· of a single JNode, repeatedly; any other value as is. -/
def unwrapJValue : Nat → Seq → Seq
  | 0, s => s
  | f + 1, s => match s with
    | [.jnode _ _ v _] => unwrapJValue f v
    | _ => s

def fnTable : List (String × LibFn) := [
  -- accessors
  -- a JNode: `string(jvalue($value))` (F&O 4.0 §2.1.3)
  ent "string" (fun _ e a => match unwrapJValue 64 (argN a 0) with
    | [] => pure (sStr "")
    | [.atom x] => pure (sStr x.str)
    | [.node n] => pure (sStr (e.nodeString n))
    | [.fn _] | [.map _] => err "FOTY0014" "fn:string of a function item"
    | [.arr _] => err "FOTY0014" "fn:string of an array"
    | _ => err "XPTY0004" "fn:string of a sequence"),
  ent "data" (fun _ e a => do pure (seqOfAtoms (← e.atomize (argN a 0)))),
  ent "boolean" (fun _ _ a => do pure (sBool (← ebv (argN a 0)))),
  ent "not" (fun _ _ a => do pure (sBool !(← ebv (argN a 0)))),
  ent "true" (fun _ _ _ => pure (sBool true)),
  ent "false" (fun _ _ _ => pure (sBool false)),
  -- strings
  ent "string-length" (fun _ _ a => pure (sInt (cps (strOf (argN a 0))).length)),
  ent "normalize-space" (fun _ _ a => pure (sStr (normSpace (strOf (argN a 0))))),
  ent "upper-case" (fun _ _ a => pure (sStr (Fn.String.upperCase (strOf (argN a 0))))),
  ent "lower-case" (fun _ _ a => pure (sStr (Fn.String.lowerCase (strOf (argN a 0))))),
  ent "concat" (fun _ e a => do
    let mut out := ""
    for s in a do
      for x in ← e.atomize s do out := out ++ x.str
    pure (sStr out)),
  ent "string-join" (fun _ _ a => pure (sStr (String.intercalate (strOf (argN a 1)) ((argN a 0).map (fun i => match i with | .atom x => x.str | _ => ""))))),
  ent "substring" (fun _ _ a =>
    let len := match argN a 2 with | [] => none | s => some (numFloat s)
    pure (sStr (substr (strOf (argN a 0)) (numFloat (argN a 1)) len))),
  ent "substring-before" (fun _ e a => do
    let c ← e.collation (argN a 2)
    let q := strOf (argN a 0); let p := strOf (argN a 1)
    if c.isCodepoint || p == "" then pure (sStr (Fn.String.substringBefore q p))
    else pure (sStr (match c.find q p true with | some (st, _) => charsTake q st | none => ""))),
  ent "substring-after" (fun _ e a => do
    let c ← e.collation (argN a 2)
    let q := strOf (argN a 0); let p := strOf (argN a 1)
    if c.isCodepoint || p == "" then pure (sStr (Fn.String.substringAfter q p))
    else pure (sStr (match c.find q p true with | some (_, en) => charsDrop q en | none => ""))),
  ent "contains" (fun _ e a => do
    let c ← e.collation (argN a 2)
    if c.isCodepoint then pure (sBool (Fn.String.contains (strOf (argN a 0)) (strOf (argN a 1))))
    else pure (sBool (c.contains (strOf (argN a 0)) (strOf (argN a 1))))),
  ent "starts-with" (fun _ e a => do
    let c ← e.collation (argN a 2)
    if c.isCodepoint then pure (sBool ((strOf (argN a 0)).startsWith (strOf (argN a 1))))
    else pure (sBool (c.startsWith (strOf (argN a 0)) (strOf (argN a 1))))),
  ent "ends-with" (fun _ e a => do
    let c ← e.collation (argN a 2)
    if c.isCodepoint then pure (sBool ((strOf (argN a 0)).endsWith (strOf (argN a 1))))
    else pure (sBool (c.endsWith (strOf (argN a 0)) (strOf (argN a 1))))),
  ent "translate" (fun _ _ a => pure (sStr (translateStr (strOf (argN a 0)) (strOf (argN a 1)) (strOf (argN a 2))))),
  ent "codepoints-to-string" (fun _ _ a => do
    let mut out : Array Char := #[]
    for i in argN a 0 do
      let n := intOf [i]
      if n < 0 || !isXmlCp n.toNat then err "FOCH0001" ("invalid codepoint " ++ toString n)
      out := out.push (Char.ofNat n.toNat)
    pure (sStr (String.ofList out.toList))),
  ent "string-to-codepoints" (fun _ _ a => pure ((cps (strOf (argN a 0))).map (fun c => .atom (Atomic.ofInt c.toNat)))),
  ent "compare" (fun _ e a => do
    let c ← e.collation (argN a 2)
    match optAtom (argN a 0), optAtom (argN a 1) with
    | some x, some y => pure (sInt (match c.compare x.str y.str with | .lt => -1 | .eq => 0 | .gt => 1))
    | _, _ => pure []),
  ent "codepoint-equal" (fun _ _ a =>
    match optAtom (argN a 0), optAtom (argN a 1) with
    | some x, some y => pure (sBool (x.str == y.str))
    | _, _ => pure []),
  ent "characters" (fun _ _ a => pure ((cps (strOf (argN a 0))).map (fun c => .atom (Atomic.ofStr (String.ofList [c]))))),
  ent "normalize-unicode" (fun _ _ a => do
    let f := (trimWs (strOf (argN a 1))).toUpper
    let s := strOf (argN a 0)
    if (argN a 1).isEmpty || f == "NFC" || f == "" then
      if s.toList.all (fun c => c.toNat < 0x300) then pure (sStr s)
      else err "XPST0017" "fn:normalize-unicode is not implemented for non-ASCII input"
    else if f == "NFD" || f == "NFKC" || f == "NFKD" || f == "FULLY-NORMALIZED" then
      if s.toList.all (fun c => c.toNat < 0xA0) then pure (sStr s)
      else err "XPST0017" "fn:normalize-unicode is not implemented for non-ASCII input"
    else err "FOCH0003" ("unsupported normalization form " ++ f)),
  ent "encode-for-uri" (fun _ _ a => pure (sStr (Fn.String.encodeForUri (strOf (argN a 0))))),
  ent "iri-to-uri" (fun _ _ a => pure (sStr (Fn.String.iriToUri (strOf (argN a 0))))),
  ent "escape-html-uri" (fun _ _ a => pure (sStr (Fn.String.escapeHtmlUri (strOf (argN a 0))))),
  ent "matches" (fun _ _ a => do
    let r ← compileRe (strOf (argN a 1)) (strOf (argN a 2))
    pure (sBool (Regex.isMatch r (strOf (argN a 0))))),
  ent "replace" (fun _ _ a => do
    match argN a 2 with
    | [.fn _] | [.map _] | [.arr _] => err "XPST0017" "fn:replace with an action function is not implemented"
    | _ => pure ()
    let r ← compileRe (strOf (argN a 1)) (strOf (argN a 3))
    match Regex.replace r (strOf (argN a 0)) (strOf (argN a 2)) with
    | .ok out => pure (sStr out)
    | .error e => regexErr e),
  ent "tokenize" (fun _ _ a => do
    let s := strOf (argN a 0)
    if (argN a 1).isEmpty then
      pure ((normSpace s).splitOn " " |>.filter (· != "") |>.map (fun t => .atom (Atomic.ofStr t)))
    else
      let p := strOf (argN a 1)
      let f := strOf (argN a 2)
      let _ ← compileRe p f
      if s == "" then pure [] else
      -- every match becomes a separator character absent from the input
      -- (fn:replace with a literal replacement), then the string is split
      let sep : Char := (([0xE000, 0xE001, 0xE002, 0xF8FF, 0x10FFFD].map Char.ofNat).find? (fun c => !s.toList.contains c)).getD (Char.ofNat 0x10FFFC)
      let r ← compileRe p f
      match Regex.replace r s (String.ofList [sep]) with
      | .ok out => pure ((out.splitOn (String.ofList [sep])).map (fun t => .atom (Atomic.ofStr t)))
      | .error e => regexErr e),
  -- numerics
  ent "abs" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some x => single (numUnary x (fun i => (i.natAbs : Int)) (fun d => if d.mantissa < 0 then Dec.neg d else d) Float.abs)
    | none => [])),
  ent "ceiling" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some x => single (numUnary x id decCeil fCeil) | none => [])),
  ent "floor" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some x => single (numUnary x id decFloor fFloor) | none => [])),
  ent "round" (fun _ _ a => do
    let mode := strOf (argN a 2)
    if !(argN a 2).isEmpty && mode != "half-to-ceiling" then
      err "XPST0017" ("fn:round mode " ++ mode ++ " is not implemented")
    pure (match optAtom (argN a 0) with
      | some x => single (roundNum x (if (argN a 1).isEmpty then 0 else intOf (argN a 1)) false) | none => [])),
  ent "round-half-to-even" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some x => single (roundNum x (if (argN a 1).isEmpty then 0 else intOf (argN a 1)) true) | none => [])),
  ent "number" (fun _ e a => do
    match ← e.atomize (argN a 0) with
    | [x] => match castAtomic x (.b .double) with
        | .ok d => pure (single d)
        | .error _ => pure (single (Atomic.ofDbl (0.0 / 0.0)))
    | _ => pure (single (Atomic.ofDbl (0.0 / 0.0)))),
  ent "is-NaN" (fun _ _ a => pure (sBool (match optAtom (argN a 0) with
    | some x => match x.num? with | some n => n.rank ≥ 2 && n.toFloat.isNaN | none => false
    | none => false))),
  -- sequences
  ent "empty" (fun _ _ a => pure (sBool (argN a 0).isEmpty)),
  ent "exists" (fun _ _ a => pure (sBool !(argN a 0).isEmpty)),
  ent "count" (fun _ _ a => pure (sInt (argN a 0).length)),
  ent "head" (fun _ _ a => pure ((argN a 0).take 1)),
  ent "tail" (fun _ _ a => pure ((argN a 0).drop 1)),
  ent "foot" (fun _ _ a => pure (match (argN a 0).getLast? with | some x => [x] | none => [])),
  ent "trunk" (fun _ _ a => pure ((argN a 0).dropLast)),
  ent "reverse" (fun _ _ a => pure (argN a 0).reverse),
  ent "unordered" (fun _ _ a => pure (argN a 0)),
  ent "identity" (fun _ _ a => pure (argN a 0)),
  ent "void" (fun _ _ _ => pure []),
  ent "insert-before" (fun _ _ a =>
    let s := argN a 0
    let p := intOf (argN a 1)
    let k := if p < 1 then 0 else (p - 1).toNat
    pure (s.take k ++ argN a 2 ++ s.drop k)),
  ent "remove" (fun _ _ a =>
    let s := argN a 0
    let ps := (argN a 1).map (fun i => intOf [i])
    pure ((List.range s.length).filterMap (fun (i : Nat) => if ps.contains ((i : Int) + 1) then none else s[i]?))),
  ent "subsequence" (fun _ _ a =>
    let s := argN a 0
    let len := match argN a 2 with | [] => none | l => some (numFloat l)
    let rnd (f : Float) : Float := (f + 0.5).floor
    let st := rnd (numFloat (argN a 1))
    let en : Float := match len with | some l => st + rnd l | none => (1.0 / 0.0)
    pure ((List.range s.length).filterMap (fun (i : Nat) =>
      let p := (i + 1).toFloat
      if p ≥ st && p < en then s[i]? else none))),
  ent "items-at" (fun _ _ a => do
    let s := argN a 0
    let sa := s.toArray
    let mut out : Array Item := #[]
    for i in argN a 1 do
      let k := intOf [i]
      if k ≥ 1 && k.toNat ≤ sa.size then out := out.push (sa.getD (k.toNat - 1) default)
    pure out.toList),
  ent "slice" (fun _ _ a => do
    let s := argN a 0
    pure ((sliceIdx s.length (argN a 1) (argN a 2) (argN a 3)).filterMap (fun i => s[i]?))),
  ent "replicate" (fun _ _ a => do
    let k := intOf (argN a 1)
    if k < 0 then err "XPTY0004" "negative count"
    pure ((List.replicate k.toNat (argN a 0)).flatten)),
  ent "distinct-values" (fun _ e a => do
    let c ← e.collation (argN a 1)
    let as := (argN a 0).filterMap (fun i => match i with | .atom x => some x | _ => none)
    if c.isCodepoint then pure (seqOfAtoms (distinctAtoms as))
    else pure (seqOfAtoms (distinctAtomsC c as))),
  ent "duplicate-values" (fun _ e a => do
    let c ← e.collation (argN a 1)
    let as := (argN a 0).filterMap (fun i => match i with | .atom x => some x | _ => none)
    if c.isCodepoint then pure (seqOfAtoms (duplicateAtoms as eqForIndexOf))
    else
      let ps := as.map (collProxy c)
      let ds := duplicateAtoms ps eqForIndexOf
      -- the first item of each duplicated class
      pure (seqOfAtoms (ds.filterMap (fun d => ((as.zip ps).find? (fun (_, p) => eqForIndexOf p d)).map (·.1))))),
  ent "index-of" (fun _ e a => do
    let c ← e.collation (argN a 2)
    match optAtom (argN a 1) with
    | some t =>
      let xs := argN a 0
      let t := collProxy c t
      pure ((List.range xs.length).filterMap (fun (i : Nat) => match xs[i]? with
        | some (.atom x) => if eqForIndexOf (collProxy c x) t then some (.atom (Atomic.ofInt (i + 1))) else none
        | _ => none))
    | none => pure []),
  ent "deep-equal" (fun _ e a => do
    match argN a 2 with
    | [] => pure ()
    | [.map []] => pure ()
    | [.atom c] => collationOk [.atom c]
    | _ => err "XPST0017" "fn:deep-equal options are not implemented"
    pure (sBool (e.deepEq (argN a 0) (argN a 1)))),
  ent "zero-or-one" (fun _ _ a => if (argN a 0).length ≤ 1 then pure (argN a 0) else err "FORG0003" "more than one item"),
  ent "one-or-more" (fun _ _ a => if (argN a 0).length ≥ 1 then pure (argN a 0) else err "FORG0004" "empty sequence"),
  ent "exactly-one" (fun _ _ a => if (argN a 0).length == 1 then pure (argN a 0) else err "FORG0005" "not exactly one item"),
  ent "sum" (fun _ _ a => do
    let as := (argN a 0).filterMap (fun i => match i with | .atom x => some x | _ => none)
    sumAtoms as (if (argN a 1).isEmpty && a.length < 2 then sInt 0 else argN a 1)),
  ent "avg" (fun _ _ a => do
    let as := (argN a 0).filterMap (fun i => match i with | .atom x => some x | _ => none)
    match as with
    | [] => pure []
    | _ =>
      let s ← sumAtoms as []
      match s with
      | [.atom t] =>
        match t.num? with
        | some n => pure (single (← numArith .div n (.i as.length)).atomic)
        | none => match t.v with
          | .x (.dur d) =>
            if t.is .yearMonthDuration then
              let m := Fn.Numeric.decDiv? 18 (Dec.ofInt d.months) (Dec.ofInt as.length)
              pure (single ⟨t.ty, .x (.dur { months := (m.map Fn.Numeric.decRound).getD 0, seconds := Dec.zero })⟩)
            else
              let sd := (Fn.Numeric.decDiv? 18 d.seconds (Dec.ofInt as.length)).getD Dec.zero
              pure (single ⟨t.ty, .x (.dur { months := 0, seconds := sd })⟩)
          | _ => err "FORG0006" "fn:avg"
      | _ => pure []),
  ent "max" (fun _ e a => do
    let c ← e.collation (argN a 1)
    minMaxC c true ((argN a 0).filterMap (fun i => match i with | .atom x => some x | _ => none))),
  ent "min" (fun _ e a => do
    let c ← e.collation (argN a 1)
    minMaxC c false ((argN a 0).filterMap (fun i => match i with | .atom x => some x | _ => none))),
  ent "all-equal" (fun _ e a => do
    let c ← e.collation (argN a 1)
    let as := (argN a 0).filterMap (fun i => match i with | .atom x => some (collProxy c x) | _ => none)
    pure (sBool (match as with | [] => true | x :: r => r.all (fun y => eqForIndexOf x y || atomicEqual x y)))),
  ent "all-different" (fun _ e a => do
    let c ← e.collation (argN a 1)
    let as := (argN a 0).filterMap (fun i => match i with | .atom x => some (collProxy c x) | _ => none)
    pure (sBool ((distinctAtoms as).length == as.length))),
  ent "position" (fun _ e _ => if e.ctx.isNone then err "XPDY0002" "context is absent" else pure (sInt e.pos)),
  ent "last" (fun _ e _ => if e.ctx.isNone then err "XPDY0002" "context is absent" else pure (sInt e.size)),
  -- higher-order
  ent "for-each" (fun h _ a => do
    let f := (argN a 1).headD default
    let xs := argN a 0
    let mut out : Array Item := #[]
    for (x, i) in xs.zip (List.range xs.length) do
      for r in ← h.callN f [[x], sInt (i + 1)] do out := out.push r
    pure out.toList),
  ent "filter" (fun h _ a => do
    let f := (argN a 1).headD default
    let xs := argN a 0
    let mut out : Array Item := #[]
    for (x, i) in xs.zip (List.range xs.length) do
      if ← h.pred f [[x], sInt (i + 1)] then out := out.push x
    pure out.toList),
  ent "fold-left" (fun h _ a => do
    let f := (argN a 2).headD default
    let xs := argN a 0
    let mut acc := argN a 1
    for (x, i) in xs.zip (List.range xs.length) do
      acc ← h.callN f [acc, [x], sInt (i + 1)]
    pure acc),
  ent "fold-right" (fun h _ a => do
    let f := (argN a 2).headD default
    let xs := argN a 0
    let mut acc := argN a 1
    for (x, i) in (xs.zip (List.range xs.length)).reverse do
      acc ← h.callN f [[x], acc, sInt (i + 1)]
    pure acc),
  ent "for-each-pair" (fun h _ a => do
    let f := (argN a 2).headD default
    let xs := argN a 0
    let ys := argN a 1
    let mut out : Array Item := #[]
    for ((x, y), i) in (xs.zip ys).zip (List.range (min xs.length ys.length)) do
      for r in ← h.callN f [[x], [y], sInt (i + 1)] do out := out.push r
    pure out.toList),
  ent "index-where" (fun h _ a => do
    let f := (argN a 1).headD default
    let xs := argN a 0
    let mut out : Array Item := #[]
    for (x, i) in xs.zip (List.range xs.length) do
      if ← h.pred f [[x], sInt (i + 1)] then out := out.push (.atom (Atomic.ofInt (i + 1)))
    pure out.toList),
  ent "take-while" (fun h _ a => do
    let f := (argN a 1).headD default
    let xs := argN a 0
    let mut out : Array Item := #[]
    for (x, i) in xs.zip (List.range xs.length) do
      if ← h.pred f [[x], sInt (i + 1)] then out := out.push x else break
    pure out.toList),
  ent "some" (fun h _ a => do
    let xs := argN a 0
    match argN a 1 with
    | [] => pure (sBool (← xs.anyM (fun x => ebv [x])))
    | f :: _ =>
      let mut r := false
      for (x, i) in xs.zip (List.range xs.length) do
        if ← h.pred f [[x], sInt (i + 1)] then r := true; break
      pure (sBool r)),
  ent "every" (fun h _ a => do
    let xs := argN a 0
    match argN a 1 with
    | [] => pure (sBool (← xs.allM (fun x => ebv [x])))
    | f :: _ =>
      let mut r := true
      for (x, i) in xs.zip (List.range xs.length) do
        if !(← h.pred f [[x], sInt (i + 1)]) then r := false; break
      pure (sBool r)),
  ent "highest" (fun h e a => do
    let c ← e.collation (argN a 1)
    let xs := argN a 0
    let keyOf (x : Item) : M (List Atomic) := do
      match argN a 2 with
      | [] => pure ((← e.atomize [x]).map (collProxy c))
      | f :: _ => pure ((← e.atomize (← h.callN f [[x]])).map (collProxy c))
    let ks ← xs.mapM keyOf
    let mut best : List (Item × List Atomic) := []
    for (x, k) in xs.zip ks do
      match best with
      | [] => best := [(x, k)]
      | (_, bk) :: _ =>
        match ← sortCmpKeys k bk with
        | .gt => best := [(x, k)]
        | .eq => best := best ++ [(x, k)]
        | .lt => pure ()
    pure (best.map (·.1))),
  ent "lowest" (fun h e a => do
    let c ← e.collation (argN a 1)
    let xs := argN a 0
    let keyOf (x : Item) : M (List Atomic) := do
      match argN a 2 with
      | [] => pure ((← e.atomize [x]).map (collProxy c))
      | f :: _ => pure ((← e.atomize (← h.callN f [[x]])).map (collProxy c))
    let ks ← xs.mapM keyOf
    let mut best : List (Item × List Atomic) := []
    for (x, k) in xs.zip ks do
      match best with
      | [] => best := [(x, k)]
      | (_, bk) :: _ =>
        match ← sortCmpKeys k bk with
        | .lt => best := [(x, k)]
        | .eq => best := best ++ [(x, k)]
        | .gt => pure ()
    pure (best.map (·.1))),
  ent "sort" (fun h e a => do
    let c ← e.collation (argN a 1)
    let xs := argN a 0
    let keyed ← xs.mapM (fun x => do
      match argN a 2 with
      | [] => pure (x, (← e.atomize [x]).map (collProxy c))
      | f :: _ => pure (x, (← e.atomize (← h.callN f [[x]])).map (collProxy c)))
    let sorted ← msortM (fun p q => do pure ((← sortCmpKeys p.2 q.2) == .lt)) 64 keyed
    pure (sorted.map (·.1))),
  ent "sort-with" (fun h _ a => do
    let xs := argN a 0
    let fs := argN a 1
    let cmpBy (x y : Item) : M Ordering := do
      let mut res := Ordering.eq
      for f in fs do
        let r ← h.callN f [[x], [y]]
        let v := intOf r
        if v < 0 then res := .lt; break
        if v > 0 then res := .gt; break
      pure res
    let sorted ← msortM (fun p q => do pure ((← cmpBy p q) == .lt)) 64 xs
    pure sorted),
  ent "apply" (fun h _ a => do
    let f := (argN a 0).headD default
    match argN a 1 with
    | [.arr ms] =>
      if f.fnArity != some ms.length then err "FOAP0001" "wrong number of arguments for fn:apply"
      h.call f ms
    | _ => err "XPTY0004" "fn:apply expects an array"),
  ent "function-arity" (fun _ _ a => pure (match (argN a 0).headD default |>.fnArity with
    | some k => sInt k | none => [])),
  ent "function-name" (fun _ _ a => pure (match argN a 0 with
    | [.fn (.builtin q _)] => single (Atomic.ofQN q)
    | _ => [])),
  ent "while-do" (fun h _ a => do
    let p := (argN a 1).headD default
    let f := (argN a 2).headD default
    let mut v := argN a 0
    let mut i := 1
    for _ in [0:1000000] do
      if !(← h.pred p [v, sInt i]) then break
      v ← h.callN f [v, sInt i]
      i := i + 1
    pure v),
  ent "do-until" (fun h _ a => do
    let f := (argN a 1).headD default
    let p := (argN a 2).headD default
    let mut v := argN a 0
    let mut i := 1
    for _ in [0:1000000] do
      v ← h.callN f [v, sInt i]
      if ← h.pred p [v, sInt i] then break
      i := i + 1
    pure v),
  ent "partition" (fun h _ a => do
    let f := (argN a 1).headD default
    let xs := argN a 0
    let mut out : List Seq := []
    let mut cur : Seq := []
    for (x, i) in xs.zip (List.range xs.length) do
      if cur.isEmpty then cur := [x]
      else if ← h.pred f [cur, [x], sInt (i + 1)] then
        out := out ++ [cur]; cur := [x]
      else cur := cur ++ [x]
    if !cur.isEmpty then out := out ++ [cur]
    pure (out.map (fun s => .arr [s]))),
  ent "sequence-join" (fun _ _ a => do
    let xs := argN a 0
    let sep := argN a 1
    let mut out : Array Item := #[]
    for (x, i) in xs.zip (List.range xs.length) do
      if i > 0 then out := out ++ sep.toArray
      out := out.push x
    pure out.toList),
  ent "starts-with-subsequence" (fun h e a => do
    let xs := argN a 0
    let ys := argN a 1
    if ys.length > xs.length then pure (sBool false) else
    match argN a 2 with
    | [] => pure (sBool (e.deepEq (xs.take ys.length) ys))
    | f :: _ => pure (sBool (← (xs.zip ys).allM (fun (x, y) => h.pred f [[x], [y]])))),
  ent "ends-with-subsequence" (fun h e a => do
    let xs := argN a 0
    let ys := argN a 1
    if ys.length > xs.length then pure (sBool false) else
    let tl := xs.drop (xs.length - ys.length)
    match argN a 2 with
    | [] => pure (sBool (e.deepEq tl ys))
    | f :: _ => pure (sBool (← (tl.zip ys).allM (fun (x, y) => h.pred f [[x], [y]])))),
  ent "contains-subsequence" (fun h e a => do
    let xs := argN a 0
    let ys := argN a 1
    if ys.length > xs.length then pure (sBool false) else
    let mut found := false
    for k in List.range (xs.length - ys.length + 1) do
      let win := (xs.drop k).take ys.length
      let ok ← match argN a 2 with
        | [] => pure (e.deepEq win ys)
        | f :: _ => (win.zip ys).allM (fun (x, y) => h.pred f [[x], [y]])
      if ok then found := true; break
    pure (sBool found)),
  -- errors and diagnostics
  ent "error" (fun _ _ a => do
    let code := match optAtom (argN a 0) with
      | some ⟨_, .qn q⟩ => q.loc
      | _ => "FOER0000"
    err code (strOf (argN a 1))),
  ent "trace" (fun _ _ a => pure (argN a 0)),
  ent "message" (fun _ _ _ => pure []),
  ent "default-collation" (fun _ e _ => pure (sStr e.defaultCollation)),
  ent "default-language" (fun _ _ _ => pure (single ⟨.b .language, .str "en"⟩)),
  ent "static-base-uri" (fun _ e _ => pure (if e.baseUri == "" then [] else single (Atomic.ofUri e.baseUri))),
  ent "current-dateTime" (fun _ e _ => do pure (single (← castFromString e.now (.b .dateTimeStamp)))),
  ent "current-date" (fun _ e _ => do pure (single (← castAtomic (← castFromString e.now (.b .dateTime)) (.b .date)))),
  ent "current-time" (fun _ e _ => do pure (single (← castAtomic (← castFromString e.now (.b .dateTime)) (.b .time)))),
  ent "implicit-timezone" (fun _ e _ => pure (single ⟨.b .dayTimeDuration, .x (.dur { months := 0, seconds := Dec.ofInt (e.tz * 60) })⟩)),
  -- QNames
  ent "QName" (fun _ _ a => do
    let uri := strOf (argN a 0)
    let lex := strOf (argN a 1)
    match parseQNameLex lex with
    | some (p, l) =>
        if p != "" && uri == "" then err "FOCA0002" "prefix with no namespace"
        pure (single (Atomic.ofQN { uri, loc := l, pfx := p }))
    | none => err "FOCA0002" ("invalid QName " ++ lex)),
  ent "prefix-from-QName" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .qn q⟩ => if q.pfx == "" then [] else single ⟨.b .ncname, .str q.pfx⟩
    | _ => [])),
  ent "local-name-from-QName" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .qn q⟩ => single ⟨.b .ncname, .str q.loc⟩
    | _ => [])),
  ent "namespace-uri-from-QName" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .qn q⟩ => single (Atomic.ofUri q.uri)
    | _ => [])),
  ent "expanded-QName" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .qn q⟩ => sStr q.eqn
    | _ => [])),
  ent "parse-QName" (fun _ e a => do
    let s := trimWs (strOf (argN a 0))
    if s.startsWith "Q{" then
      match s.toList.findIdx? (· == '}') with
      | some i => pure (single (Atomic.ofQN { uri := String.ofList ((s.toList.drop 2).take (i - 2)), loc := String.ofList (s.toList.drop (i + 1)) }))
      | none => err "FOCA0002" "invalid EQName"
    else
      match parseQNameLex s with
      | some (p, l) => match e.nsResolve p with
          | some u => pure (single (Atomic.ofQN { uri := u, loc := l, pfx := p }))
          | none => if p == "" then pure (single (Atomic.ofQN { uri := "", loc := l })) else err "FONS0004" "undeclared prefix"
      | none => err "FOCA0002" "invalid QName"),
  -- nodes
  ent "name" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (sStr ((e.nodeName n).map QN.show |>.getD ""))
    | none => pure (sStr "")),
  ent "local-name" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (sStr ((e.nodeName n).map (·.loc) |>.getD ""))
    | none => pure (sStr "")),
  ent "namespace-uri" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (single (Atomic.ofUri ((e.nodeName n).map (·.uri) |>.getD "")))
    | none => pure (single (Atomic.ofUri ""))),
  ent "node-name" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (match e.nodeName n with | some q => single (Atomic.ofQN q) | none => [])
    | none => pure []),
  ent "root" (fun _ e a => do
    if let [j@(.jnode ..)] := argN a 0 then return [jrootOf j]
    match ← nodeArg e (argN a 0) with
    | some n => pure [.node (e.rootOf n)]
    | none => pure []),
  ent "has-children" (fun _ e a => do
    if let [j@(.jnode ..)] := argN a 0 then return sBool !(jchildren j).isEmpty
    match ← nodeArg e (argN a 0) with
    | some n => pure (sBool !(e.nrec n).children.isEmpty)
    | none => pure (sBool false)),
  ent "nilled" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (if (e.nrec n).kind == .element then sBool false else [])
    | none => pure []),
  ent "document-uri" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (if (e.nrec n).kind == .document && (e.doc n).uri != "" then single (Atomic.ofUri (e.doc n).uri) else [])
    | none => pure []),
  ent "base-uri" (fun _ e a => do
    match ← nodeArg e (argN a 0) with
    | some n => pure (if (e.doc n).uri != "" then single (Atomic.ofUri (e.doc n).uri) else [])
    | none => pure []),
  ent "innermost" (fun _ e a => do
    match nodesOf (argN a 0) with
    | some ns =>
      let ns := sortNodes ns
      pure ((ns.filter (fun n => !ns.any (fun m => (e.ancestors m).contains n))).map Item.node)
    | none =>
      match gnodesOf (argN a 0) with
      | some ns =>
        let ns := sortGNodes ns
        pure (ns.filter (fun n => !ns.any (fun m => (e.gAncestors m).any (gnodeEq n))))
      | none => err "XPTY0004" "fn:innermost expects nodes"),
  ent "outermost" (fun _ e a => do
    match nodesOf (argN a 0) with
    | some ns =>
      let ns := sortNodes ns
      pure ((ns.filter (fun n => !(e.ancestors n).any (fun m => ns.contains m))).map Item.node)
    | none =>
      match gnodesOf (argN a 0) with
      | some ns =>
        let ns := sortGNodes ns
        pure (ns.filter (fun n => !(e.gAncestors n).any (fun m => ns.any (gnodeEq m))))
      | none => err "XPTY0004" "fn:outermost expects nodes"),
  ent "in-scope-prefixes" (fun _ e a => do
    match argN a 0 with
    | [.node n] =>
        let sc := (e.nrec n).inscope
        let ps := (sc.map (·.1)).eraseDups.filter (fun p => (sc.lookup p).getD "" != "" || p == "xml")
        pure (ps.map (fun p => .atom (Atomic.ofStr p)))
    | _ => err "XPTY0004" "expected an element"),
  ent "namespace-uri-for-prefix" (fun _ e a => do
    match argN a 1 with
    | [.node n] =>
        match (e.nrec n).inscope.lookup (strOf (argN a 0)) with
        | some u => pure (if u == "" then [] else single (Atomic.ofUri u))
        | none => pure []
    | _ => err "XPTY0004" "expected an element"),
  ent "lang" (fun _ e a => do
    match ← nodeArg e (argN a 1) with
    | some n =>
        let chain := n :: e.ancestors n
        let lang := chain.findSome? (fun m =>
          (e.nrec m).attrs.toList.findSome? (fun x =>
            let r := e.nrec (m.at (x))
            if r.name.uri == nsXML && r.name.loc == "lang" then some r.value else none))
        let t := (strOf (argN a 0)).toLower
        pure (sBool (match lang with
          | some l => let l := l.toLower; l == t || l.startsWith (t ++ "-")
          | none => false))
    | none => err "XPDY0002" "no context node"),
  ent "doc" (fun _ e a => do
    let u := strOf (argN a 0)
    match e.docUris.lookup u with
    | some d => pure [.node (NodeRef.mk' d 0)]
    | none => err "FODC0002" ("document not available: " ++ u)),
  ent "doc-available" (fun _ e a => pure (sBool (e.docUris.lookup (strOf (argN a 0))).isSome)),
  -- date/time component accessors
  ent "year-from-date" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.year with | some y => sInt y | none => []
    | _ => [])),
  ent "year-from-dateTime" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.year with | some y => sInt y | none => []
    | _ => [])),
  ent "month-from-date" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.month with | some y => sInt y | none => []
    | _ => [])),
  ent "month-from-dateTime" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.month with | some y => sInt y | none => []
    | _ => [])),
  ent "day-from-date" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.day with | some y => sInt y | none => []
    | _ => [])),
  ent "day-from-dateTime" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.day with | some y => sInt y | none => []
    | _ => [])),
  ent "hours-from-dateTime" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.hour with | some y => sInt y | none => []
    | _ => [])),
  ent "hours-from-time" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.hour with | some y => sInt y | none => []
    | _ => [])),
  ent "minutes-from-dateTime" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.minute with | some y => sInt y | none => []
    | _ => [])),
  ent "minutes-from-time" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.minute with | some y => sInt y | none => []
    | _ => [])),
  ent "seconds-from-dateTime" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.second with | some y => single (Atomic.ofDec y) | none => []
    | _ => [])),
  ent "seconds-from-time" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.second with | some y => single (Atomic.ofDec y) | none => []
    | _ => [])),
  ent "years-from-duration" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ => sInt (Int.tdiv d.months 12) | _ => [])),
  ent "months-from-duration" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ => sInt (Int.tmod d.months 12) | _ => [])),
  ent "days-from-duration" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ => sInt (Int.tdiv (Int.tdiv d.seconds.mantissa ((10 : Int) ^ d.seconds.scale)) 86400) | _ => [])),
  ent "hours-from-duration" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ => sInt (Int.tmod (Int.tdiv (Int.tdiv d.seconds.mantissa ((10 : Int) ^ d.seconds.scale)) 3600) 24) | _ => [])),
  ent "minutes-from-duration" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ => sInt (Int.tmod (Int.tdiv (Int.tdiv d.seconds.mantissa ((10 : Int) ^ d.seconds.scale)) 60) 60) | _ => [])),
  ent "seconds-from-duration" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ =>
        let whole := Int.tdiv d.seconds.mantissa ((10 : Int) ^ d.seconds.scale)
        let r := Dec.sub d.seconds (Dec.ofInt (whole - Int.tmod whole 60))
        single (Atomic.ofDec r)
    | _ => []))
]

def htmlEntities : List (String × Nat) :=
  [("amp", 38), ("lt", 60), ("gt", 62), ("quot", 34), ("apos", 39), ("nbsp", 160),
   ("copy", 169), ("reg", 174), ("eacute", 233), ("egrave", 232), ("auml", 228), ("ouml", 246),
   ("uuml", 252), ("szlig", 223), ("euro", 8364), ("pi", 960), ("Pi", 928), ("tab", 9),
   ("NewLine", 10), ("deg", 176), ("micro", 181), ("para", 182), ("sect", 167), ("times", 215),
   ("divide", 247), ("hellip", 8230), ("mdash", 8212), ("ndash", 8211), ("lsquo", 8216),
   ("rsquo", 8217), ("ldquo", 8220), ("rdquo", 8221), ("bull", 8226), ("trade", 8482),
   ("alpha", 945), ("beta", 946), ("gamma", 947), ("delta", 948), ("Alpha", 913), ("Beta", 914),
   ("pound", 163), ("yen", 165), ("cent", 162), ("frac12", 189), ("frac14", 188), ("frac34", 190),
   ("iexcl", 161), ("iquest", 191), ("laquo", 171), ("raquo", 187), ("middot", 183)]

def daysInMonth (y : Int) (m : Nat) : Nat :=
  match m with
  | 2 => if (y % 4 == 0 && y % 100 != 0) || y % 400 == 0 then 29 else 28
  | 4 | 6 | 9 | 11 => 30
  | _ => 31

def hexDigitVal? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- UTF-8 decode, replacing invalid sequences with U+FFFD. -/
def utf8Decode : Nat → List Nat → List Char
  | 0, _ => []
  | _, [] => []
  | f + 1, b :: r =>
    if b < 0x80 then Char.ofNat b :: utf8Decode f r
    else
      let n := if b ≥ 0xF0 && b < 0xF8 then 3 else if b ≥ 0xE0 then 2 else if b ≥ 0xC0 then 1 else 0
      let cont := r.take n
      if n == 0 || cont.length < n || !cont.all (fun x => x ≥ 0x80 && x < 0xC0) then
        Char.ofNat 0xFFFD :: utf8Decode f r
      else
        let init := if n == 1 then b % 0x20 else if n == 2 then b % 0x10 else b % 0x08
        let cp := cont.foldl (fun acc x => acc * 64 + (x % 64)) init
        Char.ofNat cp :: utf8Decode f (r.drop n)

def decodeUri (s : String) : String :=
  let rec bytes (cs : List Char) (fuel : Nat) : List Nat :=
    match fuel, cs with
    | 0, _ => []
    | _, [] => []
    | f + 1, '%' :: a :: b :: rest =>
        match hexDigitVal? a, hexDigitVal? b with
        | some x, some y => (x * 16 + y) :: bytes rest f
        | _, _ => 0xFFFFFF :: bytes (a :: b :: rest) f
    | f + 1, '%' :: rest => 0xFFFFFF :: bytes rest f
    | f + 1, '+' :: rest => 32 :: bytes rest f
    | f + 1, c :: rest => (Fn.String.utf8Bytes c) ++ bytes rest f
  let bs := bytes s.toList (s.length + 1)
  String.ofList (utf8Decode (bs.length + 1) (bs.map (fun b => if b == 0xFFFFFF then 0xFF else b)))

def fnTable2 : List (String × LibFn) := [
  ent "char" (fun _ _ a => do
    match optAtom (argN a 0) with
    | some ⟨_, .int i⟩ =>
        if i > 0 && isXmlCp i.toNat then pure (sStr (String.ofList [Char.ofNat i.toNat]))
        else err "FOCH0005" ("invalid codepoint " ++ toString i)
    | some x =>
        let s := x.str
        match s with
        | "\\n" => pure (sStr "\n") | "\\t" => pure (sStr "\t") | "\\r" => pure (sStr "\r")
        | _ => match htmlEntities.lookup s with
          | some c => pure (sStr (String.ofList [Char.ofNat c]))
          | none => err "FOCH0005" ("unknown character name " ++ s)
    | none => err "XPTY0004" "fn:char"),
  ent "contains-token" (fun _ e a => do
    let c ← e.collation (argN a 2)
    let tok := trimWs (strOf (argN a 1))
    if tok == "" then pure (sBool false)
    else pure (sBool ((argN a 0).any (fun i => match i with
      | .atom x => (normSpace x.str).splitOn " " |>.any (fun t => t != "" && c.eq t tok)
      | _ => false)))),
  ent "atomic-equal" (fun _ _ a =>
    match optAtom (argN a 0), optAtom (argN a 1) with
    | some x, some y => pure (sBool (atomicEqual x y))
    | _, _ => err "XPTY0004" "fn:atomic-equal"),
  ent "function-lookup" (fun _ _ a => do
    match optAtom (argN a 0) with
    | some ⟨_, .qn q⟩ =>
        let k := intOf (argN a 1)
        if k < 0 then pure [] else
        if q.uri == nsXS then
          pure (if k == 1 && ((atypeOfName? q.loc).isSome || q.loc == "numeric") && q.loc != "anyAtomicType" && q.loc != "NOTATION" then [.fn (.builtin q 1)] else [])
        else if q.uri == nsFN && q.loc == "concat" then pure (if k ≥ 2 then [.fn (.builtin q k.toNat)] else [])
        else match findSig q k.toNat with
          | some _ => pure [.fn (.builtin q k.toNat)]
          | none => pure []
    | _ => pure []),
  ent "collation-available" (fun _ e a =>
    pure (sBool (match collationOf e.baseUri (strOf (argN a 0)) with | .ok _ => true | .error _ => false))),
  ent "collation-key" (fun _ e a => do
    let c ← e.collation (argN a 1)
    pure (single ⟨.b .base64Binary, .x (.bin false (c.key (strOf (argN a 0))))⟩)),
  ent "collation" (fun _ _ a => do
    let kvs ← asMap (argN a 0)
    let mut ps : Array String := #[]
    for (k, v) in kvs do
      if !(k.is .string || k.is .anyURI || k.ty == .untyped) then
        err "XPTY0004" "a collation option name must be a string"
      let val ← match v with
        | [.atom ⟨_, .bool b⟩] => pure (if b then "yes" else "no")
        | [.atom x] => pure x.str
        | _ => err "XPTY0004" ("the value of collation option " ++ k.str ++ " is not castable to xs:string")
      ps := ps.push (k.str ++ "=" ++ val)
    pure (sStr (if ps.isEmpty then ucaCollation else ucaCollation ++ "?" ++ String.intercalate ";" ps.toList))),
  ent "environment-variable" (fun _ _ _ => pure []),
  ent "available-environment-variables" (fun _ _ _ => pure []),
  ent "divide-decimals" (fun _ _ a => do
    match optAtom (argN a 0), optAtom (argN a 1) with
    | some x, some y =>
      let p := if (argN a 2).isEmpty then 0 else intOf (argN a 2)
      let dx := (x.num?.map Num.toDec).getD Dec.zero
      let dy := (y.num?.map Num.toDec).getD Dec.zero
      if dy.mantissa == 0 then err "FOAR0001" "division by zero" else
      -- quotient truncated toward zero at `p` fractional digits
      let sh : Nat := if p ≥ 0 then p.toNat else 0
      let num : Int := dx.mantissa * (10 : Int) ^ (dy.scale + sh)
      let den : Int := dy.mantissa * (10 : Int) ^ dx.scale
      let q0 := Int.tdiv num den
      let q : Dec := if p ≥ 0 then Dec.norm ⟨q0, sh⟩
        else
          let m := (10 : Int) ^ (-p).toNat
          Dec.ofInt (Int.tdiv (Int.tdiv dx.mantissa ((10 : Int) ^ dx.scale) |> fun _ => Int.tdiv num den) m * m)
      let r := Dec.norm (Dec.sub dx (Fn.Numeric.decMul q dy))
      pure (mapItem [(Atomic.ofStr "quotient", single (Atomic.ofDec q)), (Atomic.ofStr "remainder", single (Atomic.ofDec r))])
    | _, _ => err "XPTY0004" "fn:divide-decimals"),
  ent "days-in-month" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dt _ w)⟩ => match w.year, w.month with
        | some y, some m => sInt (daysInMonth y m)
        | _, _ => []
    | _ => [])),
  ent "dateTime" (fun _ _ a => do
    match optAtom (argN a 0), optAtom (argN a 1) with
    | some ⟨_, .x (.dt _ d)⟩, some ⟨_, .x (.dt _ t)⟩ =>
        let tz ← match d.tz, t.tz with
          | some x, some y => if x == y then pure (some x) else err "FORG0008" "different timezones"
          | some x, none => pure (some x)
          | none, y => pure y
        let w : DTValue := { year := d.year, month := d.month, day := d.day, hour := t.hour, minute := t.minute, second := t.second, tz := tz }
        pure (single ⟨.b .dateTime, .x (.dt .dateTime w)⟩)
    | _, _ => pure []),
  ent "seconds" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some x => single ⟨.b .dayTimeDuration, .x (.dur { months := 0, seconds := (x.num?.map Num.toDec).getD Dec.zero })⟩
    | none => [])),
  ent "parse-integer" (fun _ _ a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some x =>
      let radix := if (argN a 1).isEmpty then 10 else intOf (argN a 1)
      if radix < 2 || radix > 36 then err "FORG0011" "invalid radix"
      let s := String.ofList ((x.str.toList.filter (fun c => !isWs c && c != '_')))
      let (neg, ds) := match s.toList with
        | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
      if ds.isEmpty then err "FORG0012" "invalid digits"
      let mut v : Int := 0
      for c in ds do
        let d : Int := if c.isDigit then c.toNat - 48 else if c.isAlpha then (c.toLower.toNat - 87 : Nat) else 99
        if d ≥ radix then err "FORG0012" ("invalid digit " ++ String.ofList [c])
        v := v * radix + d
      pure (sInt (if neg then -v else v))),
  ent "decode-from-uri" (fun _ _ a => pure (sStr (decodeUri (strOf (argN a 0))))),
  ent "distinct-ordered-nodes" (fun _ _ a => do
    match nodesOf (argN a 0) with
    | some ns => pure ((sortNodes ns).map Item.node)
    | none =>
      match gnodesOf (argN a 0) with
      | some ns => pure (sortGNodes ns)
      | none => err "XPTY0004" "expected nodes"),
  ent "siblings" (fun _ e a => do
    if let [j@(.jnode _ st _ _)] := argN a 0 then
      return (match st, jparent j with
        | s :: _, some p => if s.pos == 0 then [j] else jchildren p
        | _, _ => [j])
    match ← nodeArg e (argN a 0) with
    | some n =>
      let r := e.nrec n
      if r.kind == NKind.attribute || r.kind == NKind.namespace then pure [.node n] else
      match r.parent with
      | some p => pure (((e.doc n).get p).children.toList.map (fun c => .node (n.at (c))))
      | none => pure [.node n]
    | none => pure [])
]

def opOfString : String → Option (Expr → Expr → Expr)
  | "," => some (fun a b => .seq [a, b])
  | "and" => some (.bin .and) | "or" => some (.bin .or)
  | "+" => some (.bin .add) | "-" => some (.bin .sub) | "*" => some (.bin .mul)
  | "div" => some (.bin .div) | "idiv" => some (.bin .idiv) | "mod" => some (.bin .mod)
  | "=" => some (.bin .geq) | "!=" => some (.bin .gne) | "<" => some (.bin .glt)
  | "<=" => some (.bin .gle) | ">" => some (.bin .ggt) | ">=" => some (.bin .gge)
  | "eq" => some (.bin .veq) | "ne" => some (.bin .vne) | "lt" => some (.bin .vlt)
  | "le" => some (.bin .vle) | "gt" => some (.bin .vgt) | "ge" => some (.bin .vge)
  | "<<" => some (.bin .precedes) | ">>" => some (.bin .follows) | "is" => some (.bin .is)
  | "is-not" => some (.bin .isNot) | "precedes" => some (.bin .precedes) | "follows" => some (.bin .follows)
  | "precedes-or-is" => some (.bin .precedesOrIs) | "follows-or-is" => some (.bin .followsOrIs)
  | "||" => some (.bin .concat) | "|" => some (.bin .union) | "union" => some (.bin .union)
  | "except" => some (.bin .except) | "intersect" => some (.bin .intersect)
  | "to" => some (.bin .to) | "otherwise" => some (.bin .otherwise)
  | "!" => some .smap | "/" => some .slash
  | "×" => some (.bin .mul) | "÷" => some (.bin .div)
  | _ => none

def indexOfSub (hay needle : List Char) : List Nat :=
  if needle.isEmpty then [] else
  (List.range (hay.length + 1 - min hay.length needle.length)).filter (fun i =>
    i + needle.length ≤ hay.length && (hay.drop i).take needle.length == needle)

def tzMinutes (s : Seq) : M (Option Int) :=
  match optAtom s with
  | none => pure none
  | some ⟨_, .x (.dur d)⟩ =>
      let secs := d.seconds
      if secs.scale != 0 && (Dec.norm secs).scale != 0 then err "FODT0003" "timezone with fractional seconds"
      else
        let total := Int.tdiv (Dec.norm secs).mantissa ((10 : Int) ^ (Dec.norm secs).scale)
        if total % 60 != 0 || total > 14 * 3600 || total < -14 * 3600 then err "FODT0003" "invalid timezone"
        else pure (some (total / 60))
  | _ => err "XPTY0004" "timezone must be xs:dayTimeDuration"

def adjustTz (k : DTKind) (a : List Seq) : M Seq := do
  match optAtom (argN a 0) with
  | none => pure []
  | some x =>
    match x.v with
    | .x (.dt _ w) =>
      let tz ← tzMinutes (argN a 1)
      let w' : DTValue ← match tz, w.tz with
        | none, _ => pure { w with tz := none }
        | some t, none => pure { w with tz := some t }
        | some t, some old =>
          let shifted := Fn.DateTime.plusDuration w { months := 0, seconds := Dec.ofInt ((t - old) * 60) }
          pure { shifted with tz := some t }
      pure (single ⟨x.ty, .x (.dt k (dtProject k w'))⟩)
    | _ => err "XPTY0004" "adjust-to-timezone"

def Env.pathOf (e : Env) (n : NodeRef) : String :=
  let chain := (n :: e.ancestors n).reverse
  let step (m : NodeRef) : String :=
    let r := e.nrec m
    let sameKind (c : Nat) : Bool :=
      let rc := e.nrec (m.at (c))
      rc.kind == r.kind && (r.kind != .element || rc.name == r.name) && (r.kind != .pi || rc.name.loc == r.name.loc)
    let pos : Nat := match r.parent with
      | some p => (((e.doc m).get p).children.toList.filter (fun c => c ≤ m.idx && sameKind c)).length
      | none => 1
    match r.kind with
    | .document => ""
    | .element => "Q{" ++ r.name.uri ++ "}" ++ r.name.loc ++ "[" ++ toString pos ++ "]"
    | .attribute => if r.name.uri == "" then "@" ++ r.name.loc else "@Q{" ++ r.name.uri ++ "}" ++ r.name.loc
    | .text => "text()[" ++ toString pos ++ "]"
    | .comment => "comment()[" ++ toString pos ++ "]"
    | .pi => "processing-instruction(" ++ r.name.loc ++ ")[" ++ toString pos ++ "]"
    | .namespace => "namespace::" ++ r.name.loc
  match chain with
  | [] => ""
  | top :: rest =>
    let topR := e.nrec top
    let pre := if topR.kind == .document then "" else "Q{http://www.w3.org/2005/xpath-functions}root()"
    if rest.isEmpty && topR.kind == .document then "/"
    else pre ++ String.join (rest.map (fun m => "/" ++ step m))

def resolveUri (base href : String) : String :=
  if (href.splitOn ":").length > 1 && ((href.splitOn ":").headD "").all Char.isAlpha && href != "" then href
  else if href.startsWith "/" then
    match (base.splitOn "//") with
    | sch :: rest :: _ => sch ++ "//" ++ ((rest.splitOn "/").headD "") ++ href
    | _ => href
  else
    let dir := match (base.splitOn "/").dropLast with | [] => "" | ps => String.intercalate "/" ps ++ "/"
    dir ++ href

/-- `fn:sort-by` / `array:sort-by`: sort `xs` (each viewed as a
    sequence by `view`) by a list of sort-key records. -/
def sortByKeys {α} (h : Hooks) (e : Env) (xs : List α) (view : α → Seq) (keys : Seq) : M (List α) := do
  let specs ← keys.mapM (fun k => do
    let m ← asMap [k]
    let kf := (mapGet m (Atomic.ofStr "key")).bind (·.head?)
    let c ← e.collation ((mapGet m (Atomic.ofStr "collation")).getD [])
    let ord := strOf ((mapGet m (Atomic.ofStr "order")).getD [])
    if ord != "" && ord != "ascending" && ord != "descending" then err "XPTY0004" "invalid sort order"
    pure (kf, ord == "descending", c))
  let specs ← if specs.isEmpty then pure [(none, false, ← e.collation [])] else pure specs
  let keyed ← xs.mapM (fun x => do
    let ks ← specs.mapM (fun (kf, _, c) => do
      match kf with
      | none => pure ((← e.atomize (view x)).map (collProxy c))
      | some f => pure ((← e.atomize (← h.callN f [view x])).map (collProxy c)))
    pure (x, ks))
  let lt (p q : α × List (List Atomic)) : M Bool := do
    let mut res := false
    for ((ka, kb), (_, desc, _)) in (p.2.zip q.2).zip specs do
      let o ← sortCmpKeys ka kb
      let o := if desc then o.swap else o
      if o == .lt then res := true; break
      if o == .gt then res := false; break
    pure res
  let sorted ← msortM lt 64 keyed
  pure (sorted.map (·.1))

def sortWithCmps {α} (h : Hooks) (xs : List α) (view : α → Seq) (fs : Seq) : M (List α) := do
  let cmpBy (x y : α) : M Ordering := do
    let mut res := Ordering.eq
    for f in fs do
      let r ← h.callN f [view x, view y]
      let v := intOf r
      if v < 0 then res := .lt; break
      if v > 0 then res := .gt; break
    pure res
  msortM (fun p q => do pure ((← cmpBy p q) == .lt)) 64 xs

def tzOf (a : List Seq) : Seq :=
  match optAtom (argN a 0) with
  | some ⟨_, .x (.dt _ w)⟩ => match w.tz with
    | some t => single ⟨.b .dayTimeDuration, .x (.dur { months := 0, seconds := Dec.ofInt (t * 60) })⟩
    | none => []
  | _ => []

def fnTable3 : List (String × LibFn) := [
  -- F&O 4.0 §16.1: fn:jtree, fn:jkey, fn:jvalue
  ent "jtree" (fun _ _ a => pure [mkJRoot 0 (argN a 0)]),
  ent "jkey" (fun _ _ a => pure (match argN a 0 with
    | [j@(.jnode ..)] => match jkeyOf j with | some k => [.atom k] | none => []
    | _ => [])),
  ent "jvalue" (fun _ _ a => pure (match argN a 0 with
    | [.jnode _ _ v _] => v
    | _ => [])),
  ent "sort-by" (fun h e a => sortByKeys h e (argN a 0) (fun x => [x]) (argN a 1)),
  ent "timezone-from-dateTime" (fun _ _ a => pure (tzOf a)),
  ent "timezone-from-date" (fun _ _ a => pure (tzOf a)),
  ent "timezone-from-time" (fun _ _ a => pure (tzOf a)),
  ent "op" (fun _ _ a => do
    let o := strOf (argN a 0)
    match opOfString o with
    | some mk =>
      let x : QN := { uri := "#op", loc := "a" }
      let y : QN := { uri := "#op", loc := "b" }
      pure [.fn (.inline [(x, .seq .item .star), (y, .seq .item .star)] (.seq .item .star) (mk (.var x) (.var y)) false [])]
    | none => err "FOAP0003" ("unknown operator " ++ o)),
  ent "partial-apply" (fun _ _ a => do
    let f := (argN a 0).headD default
    let m ← asMap (argN a 1)
    let k := (f.fnArity).getD 0
    let mut fixed : List (Option Seq) := []
    for i in List.range k do
      fixed := fixed ++ [mapGet m (Atomic.ofInt (i + 1))]
    for (key, _) in m do
      match key.v with
      | .int j => if j < 1 || j > k then err "FOAP0001" "partial-apply position out of range"
      | _ => err "XPTY0004" "partial-apply key"
    pure [.fn (.papp f fixed)]),
  ent "drop-while" (fun h _ a => do
    let f := (argN a 1).headD default
    let xs := argN a 0
    let mut i : Nat := 0
    for x in xs do
      if ← h.pred f [[x], sInt (i + 1)] then i := i + 1 else break
    pure (xs.drop i)),
  ent "index-of-substring" (fun _ _ a =>
    pure ((indexOfSub (cps (strOf (argN a 0))) (cps (strOf (argN a 1)))).map (fun (i : Nat) => .atom (Atomic.ofInt (i + 1))))),
  ent "substring-before-last" (fun _ e a => do
    let c ← e.collation (argN a 2)
    let h := cps (strOf (argN a 0)); let n := cps (strOf (argN a 1))
    -- F&O 4.0 §5.4.6: a zero-length $substring gives $value
    if n.isEmpty then pure (sStr (strOf (argN a 0))) else
    if !c.isCodepoint then
      let q := strOf (argN a 0)
      pure (sStr (match c.find q (strOf (argN a 1)) false with | some (st, _) => charsTake q st | none => ""))
    else
    match (indexOfSub h n).getLast? with
    | some i => pure (sStr (String.ofList (h.take i)))
    | none => pure (sStr "")),
  ent "substring-after-last" (fun _ e a => do
    let c ← e.collation (argN a 2)
    let h := cps (strOf (argN a 0)); let n := cps (strOf (argN a 1))
    if n.isEmpty then pure (sStr "") else
    if !c.isCodepoint then
      let q := strOf (argN a 0)
      pure (sStr (match c.find q (strOf (argN a 1)) false with | some (_, en) => charsDrop q en | none => ""))
    else
    match (indexOfSub h n).getLast? with
    | some i => pure (sStr (String.ofList (h.drop (i + n.length))))
    | none => pure (sStr "")),
  ent "insert-separator" (fun _ _ a => do
    let xs := argN a 0
    let sep := argN a 1
    let mut out : Array Item := #[]
    for (x, i) in xs.zip (List.range xs.length) do
      if i > 0 then out := out ++ sep.toArray
      out := out.push x
    pure out.toList),
  ent "transitive-closure" (fun h _ a => do
    let f := (argN a 1).headD default
    match argN a 0 with
    | [] => pure []
    | start =>
      let mut found : List Item := []
      let mut frontier := start
      for _ in [0:100000] do
        if frontier.isEmpty then break
        let next ← h.callN f [frontier.take 1]
        let rest := frontier.drop 1
        let mut newOnes : Seq := []
        for i in next do
          if !i.isGNode then err "XPTY0004" "transitive-closure step must return nodes"
          if !found.any (gnodeEq i) then
            found := found ++ [i]; newOnes := newOnes ++ [i]
        frontier := rest ++ newOnes
      pure (sortGNodes found)),
  ent "type-of" (fun _ e a => do
    let xs := argN a 0
    if xs.isEmpty then return sStr "empty-sequence()"
    let one (i : Item) : String := match i with
      | .atom x => "xs:" ++ x.ty.name
      | .node n => match (e.nrec n).kind with
        | .document => "document-node()" | .element => "element()" | .attribute => "attribute()"
        | .text => "text()" | .pi => "processing-instruction()" | .comment => "comment()"
        | .namespace => "namespace-node()"
      | .arr _ => "array(*)" | .map _ => "map(*)" | .fn _ => "fn(*)"
      | .jnode .. => "jnode()"
    let ss := (xs.map one).eraseDups
    let body := if ss.length == 1 then ss.headD "" else "(" ++ String.intercalate "|" ss ++ ")"
    pure (sStr (body ++ (if xs.length > 1 then "+" else "")))),
  ent "trim-space" (fun _ _ a => do
    match argN a 1 with
    | [] | [.map []] => pure (sStr (trimWs (strOf (argN a 0))))
    | _ => err "XPST0017" "fn:trim-space options are not implemented"),
  ent "graphemes" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some x => (Grapheme.graphemes x.str).map (fun g => .atom (Atomic.ofStr g))
    | none => [])),
  ent "generate-id" (fun _ e a => do
    if let [j@(.jnode r _ _ _)] := argN a 0 then
      return sStr ("j" ++ toString r ++ String.join ((jposPath j).map (fun p => "p" ++ toString p)))
    match ← nodeArg e (argN a 0) with
    | some n => pure (sStr ("d" ++ toString n.doc ++ "n" ++ toString n.idx))
    | none => pure (sStr "")),
  ent "path" (fun _ e a => do
    if let [j@(.jnode ..)] := argN a 0 then
      let origin ← match argN a 1 with
        | [.map kvs] => match mapGet kvs (Atomic.ofStr "origin") with
          | some [o] => pure (some o)
          | some [] | none => pure none
          | some _ => err "XPTY0004" "the origin option must be a single node"
        | _ => pure none
      return sStr (← jpathOf j origin)
    if !(argN a 1).isEmpty && !(match argN a 1 with | [.map []] => true | _ => false) then
      err "XPST0017" "fn:path options are not implemented"
    match ← nodeArg e (argN a 0) with
    | some n => pure (sStr (e.pathOf n))
    | none => pure []),
  ent "resolve-uri" (fun _ e a => do
    match optAtom (argN a 0) with
    | none => pure []
    | some h =>
      let base := if (argN a 1).isEmpty then e.baseUri else strOf (argN a 1)
      if base == "" && !(h.str.splitOn ":").length > 1 then err "FONS0005" "no base URI"
      else pure (single (Atomic.ofUri (resolveUri base h.str)))),
  ent "duration-to-seconds" (fun _ _ a => pure (match optAtom (argN a 0) with
    | some ⟨_, .x (.dur d)⟩ => single (Atomic.ofDec d.seconds)
    | _ => [])),
  ent "adjust-dateTime-to-timezone" (fun _ _ a => adjustTz .dateTime a),
  ent "adjust-date-to-timezone" (fun _ _ a => adjustTz .date a),
  ent "adjust-time-to-timezone" (fun _ _ a => adjustTz .time a)
]

def mathTable : List (String × LibFn) := [
  ent "pi" (fun _ _ _ => pure (single (Atomic.ofDbl 3.141592653589793))),
  ent "e" (fun _ _ _ => pure (single (Atomic.ofDbl 2.718281828459045))),
  ent "exp" (mathFn Float.exp),
  ent "exp10" (mathFn (fun x => Float.pow 10 x)),
  ent "log" (mathFn Float.log),
  ent "log10" (mathFn Float.log10),
  ent "sqrt" (mathFn Float.sqrt),
  ent "sin" (mathFn Float.sin), ent "cos" (mathFn Float.cos), ent "tan" (mathFn Float.tan),
  ent "asin" (mathFn Float.asin), ent "acos" (mathFn Float.acos), ent "atan" (mathFn Float.atan),
  ent "sinh" (mathFn Float.sinh), ent "cosh" (mathFn Float.cosh), ent "tanh" (mathFn Float.tanh),
  ent "atan2" (fun _ _ a => pure (single (Atomic.ofDbl (Float.atan2 (numFloat (argN a 0)) (numFloat (argN a 1)))))),
  ent "pow" (fun _ _ a =>
    match optAtom (argN a 0) with
    | none => pure []
    | some x =>
      let b := (x.num?.map Num.toFloat).getD 0
      let y := numFloat (argN a 1)
      pure (single (Atomic.ofDbl (if y == 0 then 1 else if b == 1 then 1 else if b == -1 && y.isInf then 1 else Float.pow b y))))
]

def mapTable : List (String × LibFn) := [
  ent "size" (fun _ _ a => do pure (sInt (← asMap (argN a 0)).length)),
  ent "keys" (fun _ _ a => do pure ((← asMap (argN a 0)).map (fun (k, _) => .atom k))),
  ent "items" (fun _ _ a => do pure ((← asMap (argN a 0)).flatMap (·.2))),
  ent "contains" (fun _ _ a => do
    let m ← asMap (argN a 0)
    match optAtom (argN a 1) with
    | some k => pure (sBool (mapGet m k).isSome)
    | none => pure (sBool false)),
  ent "get" (fun h _ a => do
    let m ← asMap (argN a 0)
    match optAtom (argN a 1) with
    | some k => match mapGet m k with
      | some v => pure v
      | none => match argN a 2 with
        | [] => pure []
        | f :: _ => h.callN f [[.atom k]]
    | none => pure []),
  ent "put" (fun _ _ a => do
    let m ← asMap (argN a 0)
    match optAtom (argN a 1) with
    | some k => pure (mapItem (mapPut m k (argN a 2)))
    | none => err "XPTY0004" "map:put key"),
  ent "remove" (fun _ _ a => do
    let m ← asMap (argN a 0)
    let ks := (argN a 1).filterMap (fun i => match i with | .atom x => some x | _ => none)
    pure (mapItem (ks.foldl mapRemove m))),
  ent "entry" (fun _ _ a =>
    match optAtom (argN a 0) with
    | some k => pure (mapItem [(k, argN a 1)])
    | none => err "XPTY0004" "map:entry key"),
  ent "pair" (fun _ _ a =>
    match optAtom (argN a 0) with
    | some k => pure (mapItem [(Atomic.ofStr "key", [.atom k]), (Atomic.ofStr "value", argN a 1)])
    | none => err "XPTY0004" "map:pair key"),
  ent "empty" (fun _ _ a => do pure (sBool (← asMap (argN a 0)).isEmpty)),
  ent "merge" (fun _ _ a => do
    let maps ← (argN a 0).mapM (fun i => asMap [i])
    let dup := optionStr (argN a 1) "duplicates" "use-first"
    pure (mapItem (← mergeMaps maps dup))),
  ent "of-pairs" (fun _ _ a => do
    let mut acc : MB := {}
    for p in argN a 0 do
      let m ← asMap [p]
      match mapGet m (Atomic.ofStr "key"), mapGet m (Atomic.ofStr "value") with
      | some [.atom k], some v =>
          match acc.get? k with
          | some old => acc := acc.set k (old ++ v)
          | none => acc := acc.set k v
      | _, _ => err "XPTY0004" "map:of-pairs expects key-value pairs"
    pure (mapItem acc.toList)),
  ent "entries" (fun _ _ a => do pure ((← asMap (argN a 0)).map (fun (k, v) => .map [(k, v)]))),
  ent "pairs" (fun _ _ a => do pure ((← asMap (argN a 0)).map (fun (k, v) => .map [(Atomic.ofStr "key", [.atom k]), (Atomic.ofStr "value", v)]))),
  ent "for-each" (fun h _ a => do
    let m ← asMap (argN a 0)
    let f := (argN a 1).headD default
    let mut out : Array Item := #[]
    for ((k, v), i) in m.zip (List.range m.length) do
      for r in ← h.callN f [[.atom k], v, sInt (i + 1)] do out := out.push r
    pure out.toList),
  ent "filter" (fun h _ a => do
    let m ← asMap (argN a 0)
    let f := (argN a 1).headD default
    let mut out : List (Atomic × Seq) := []
    for ((k, v), i) in m.zip (List.range m.length) do
      if ← h.pred f [[.atom k], v, sInt (i + 1)] then out := out ++ [(k, v)]
    pure (mapItem out)),
  ent "keys-where" (fun h _ a => do
    let m ← asMap (argN a 0)
    let f := (argN a 1).headD default
    let mut out : Array Item := #[]
    for ((k, v), i) in m.zip (List.range m.length) do
      if ← h.pred f [[.atom k], v, sInt (i + 1)] then out := out.push (.atom k)
    pure out.toList),
  ent "find" (fun _ _ a => do
    match optAtom (argN a 1) with
    | none => pure (arrItem [])
    | some k =>
      -- depth-first search through maps and arrays
      let rec go (fuel : Nat) (s : Seq) : List Seq :=
        match fuel with
        | 0 => []
        | f + 1 => s.foldl (fun acc i => match i with
          | .map kvs => acc ++ (kvs.foldl (fun acc2 (k2, v) =>
              acc2 ++ (if atomicEqual k k2 then [v] else []) ++ go f v) [])
          | .arr ms => acc ++ ms.foldl (fun acc2 m => acc2 ++ go f m) []
          | _ => acc) []
      pure (arrItem (go 1000 (argN a 0)))),
  ent "build" (fun h e a => do
    let xs := argN a 0
    let dup := optionStr (argN a 3) "duplicates" "combine"
    let combineFn : Option Item := match argN a 3 with
      | [.map kvs] => match mapGet kvs (Atomic.ofStr "duplicates") with
        | some [f] => if f.isFn then some f else none
        | _ => none
      | _ => none
    let mut acc : MB := {}
    for (x, i) in xs.zip (List.range xs.length) do
      let ks ← match argN a 1 with
        | [] => e.atomize [x]
        | f :: _ => e.atomize (← h.callN f [[x], sInt (i + 1)])
      let v ← match argN a 2 with
        | [] => pure [x]
        | f :: _ => h.callN f [[x], sInt (i + 1)]
      for k in ks do
        match acc.get? k with
        | some old =>
          match combineFn with
          | some f => acc := acc.set k (← h.callN f [old, v])
          | none =>
            match dup with
            | "combine" => acc := acc.set k (old ++ v)
            | "use-first" | "use-any" => pure ()
            | "use-last" => acc := acc.set k v
            | "reject" => err "FOJS0003" "duplicate key in map:build"
            | _ => err "FOJS0005" ("invalid duplicates option " ++ dup)
        | none => acc := acc.set k v
    pure (mapItem acc.toList))
]

def arrayTable : List (String × LibFn) := [
  ent "sort-by" (fun h e a => do pure (arrItem (← sortByKeys h e (← asArr (argN a 0)) id (argN a 1)))),
  ent "sort-with" (fun h _ a => do pure (arrItem (← sortWithCmps h (← asArr (argN a 0)) id (argN a 1)))),
  ent "size" (fun _ _ a => do pure (sInt (← asArr (argN a 0)).length)),
  ent "get" (fun h _ a => do
    let ms ← asArr (argN a 0)
    let i := intOf (argN a 1)
    if i ≥ 1 && i.toNat ≤ ms.length then pure (ms.getD (i.toNat - 1) [])
    else match argN a 2 with
      | [] => err "FOAY0001" ("array index " ++ toString i ++ " out of bounds")
      | f :: _ => h.callN f [sInt i]),
  ent "put" (fun _ _ a => do
    let ms ← asArr (argN a 0)
    let i := intOf (argN a 1)
    let _ ← arrIdx ms i
    pure (arrItem ((List.range ms.length).map (fun (j : Nat) => if (j : Int) + 1 == i then argN a 2 else ms.getD j [])))),
  ent "append" (fun _ _ a => do pure (arrItem ((← asArr (argN a 0)) ++ [argN a 1]))),
  ent "subarray" (fun _ _ a => do
    let ms ← asArr (argN a 0)
    let st := intOf (argN a 1)
    let len : Int := match argN a 2 with | [] => (ms.length : Int) - st + 1 | l => intOf l
    if st < 1 || st > (ms.length : Int) + 1 then err "FOAY0001" "subarray start out of bounds"
    if len < 0 then err "FOAY0002" "negative length"
    if st + len - 1 > ms.length then err "FOAY0001" "subarray end out of bounds"
    pure (arrItem ((ms.drop (st.toNat - 1)).take len.toNat))),
  ent "remove" (fun _ _ a => do
    let ms ← asArr (argN a 0)
    let ps := (argN a 1).map (fun i => intOf [i])
    for p in ps do
      if p < 1 || p > ms.length then err "FOAY0001" "array:remove position out of bounds"
    pure (arrItem ((List.range ms.length).filterMap (fun (i : Nat) => if ps.contains ((i : Int) + 1) then none else ms[i]?)))),
  ent "insert-before" (fun _ _ a => do
    let ms ← asArr (argN a 0)
    let p := intOf (argN a 1)
    if p < 1 || p > (ms.length : Int) + 1 then err "FOAY0001" "array:insert-before position out of bounds"
    let k := (p - 1).toNat
    pure (arrItem (ms.take k ++ [argN a 2] ++ ms.drop k))),
  ent "head" (fun _ _ a => do
    match ← asArr (argN a 0) with
    | m :: _ => pure m
    | [] => err "FOAY0001" "array:head of an empty array"),
  ent "foot" (fun _ _ a => do
    match (← asArr (argN a 0)).getLast? with
    | some m => pure m
    | none => err "FOAY0001" "array:foot of an empty array"),
  ent "tail" (fun _ _ a => do
    match ← asArr (argN a 0) with
    | _ :: r => pure (arrItem r)
    | [] => err "FOAY0001" "array:tail of an empty array"),
  ent "trunk" (fun _ _ a => do
    let ms ← asArr (argN a 0)
    if ms.isEmpty then err "FOAY0001" "array:trunk of an empty array"
    pure (arrItem ms.dropLast)),
  ent "reverse" (fun _ _ a => do pure (arrItem (← asArr (argN a 0)).reverse)),
  ent "empty" (fun _ _ a => do pure (sBool (← asArr (argN a 0)).isEmpty)),
  ent "join" (fun _ _ a => do
    let arrs ← (argN a 0).mapM (fun i => asArr [i])
    match argN a 1 with
    | [] => pure (arrItem arrs.flatten)
    | sep =>
      let sepMs ← asArr sep
      pure (arrItem ((arrs.zip (List.range arrs.length)).foldl (fun acc (m, i) => if i == 0 then m else acc ++ sepMs ++ m) []))),
  ent "flatten" (fun _ _ a => do
    let rec go (fuel : Nat) (s : Seq) (acc : Array Item) : Array Item :=
      match fuel with
      | 0 => acc ++ s.toArray
      | f + 1 => s.foldl (fun acc i => match i with
          | .arr ms => go f ms.flatten acc
          | x => acc.push x) acc
    pure (go 1000 (argN a 0) #[]).toList),
  -- F&O 4.0 §15.2.18, §15.2.19: the members as JNodes (`jtree($array)/child::*`),
  -- and an array from the ·jvalue·s of JNodes
  ent "members" (fun _ _ a => do
    match argN a 0 with
    | [x@(.arr _)] => pure (jchildren (mkJRoot 0 [x]))
    | _ => err "XPTY0004" "expected an array"),
  ent "of-members" (fun _ _ a => do
    let ms ← (argN a 0).mapM (fun i => do
      match i with
      | .jnode _ _ v _ => pure v
      | _ => err "XPTY0004" "array:of-members expects JNodes")
    pure (arrItem ms)),
  ent "split" (fun _ _ a => do pure ((← asArr (argN a 0)).map (fun m => .arr [m]))),
  ent "items" (fun _ _ a => do pure (← asArr (argN a 0)).flatten),
  ent "build" (fun h _ a => do
    let xs := argN a 0
    match argN a 1 with
    | [] => pure (arrItem (xs.map (fun x => [x])))
    | f :: _ =>
      let mut out : Array Seq := #[]
      for (x, i) in xs.zip (List.range xs.length) do
        out := out.push (← h.callN f [[x], sInt (i + 1)])
      pure (arrItem out.toList)),
  ent "for-each" (fun h _ a => do
    let ms ← asArr (argN a 0)
    let f := (argN a 1).headD default
    let mut out : Array Seq := #[]
    for (m, i) in ms.zip (List.range ms.length) do
      out := out.push (← h.callN f [m, sInt (i + 1)])
    pure (arrItem out.toList)),
  ent "filter" (fun h _ a => do
    let ms ← asArr (argN a 0)
    let f := (argN a 1).headD default
    let mut out : Array Seq := #[]
    for (m, i) in ms.zip (List.range ms.length) do
      if ← h.pred f [m, sInt (i + 1)] then out := out.push m
    pure (arrItem out.toList)),
  ent "index-where" (fun h _ a => do
    let ms ← asArr (argN a 0)
    let f := (argN a 1).headD default
    let mut out : Array Item := #[]
    for (m, i) in ms.zip (List.range ms.length) do
      if ← h.pred f [m, sInt (i + 1)] then out := out.push (.atom (Atomic.ofInt (i + 1)))
    pure out.toList),
  ent "index-of" (fun _ e a => do
    let ms ← asArr (argN a 0)
    let t := argN a 1
    pure ((List.range ms.length).filterMap (fun (i : Nat) =>
      if e.deepEq (ms.getD i []) t then some (.atom (Atomic.ofInt (i + 1))) else none))),
  ent "fold-left" (fun h _ a => do
    let ms ← asArr (argN a 0)
    let f := (argN a 2).headD default
    let mut acc := argN a 1
    for (m, i) in ms.zip (List.range ms.length) do
      acc ← h.callN f [acc, m, sInt (i + 1)]
    pure acc),
  ent "fold-right" (fun h _ a => do
    let ms ← asArr (argN a 0)
    let f := (argN a 2).headD default
    let mut acc := argN a 1
    for (m, i) in (ms.zip (List.range ms.length)).reverse do
      acc ← h.callN f [m, acc, sInt (i + 1)]
    pure acc),
  ent "for-each-pair" (fun h _ a => do
    let xs ← asArr (argN a 0)
    let ys ← asArr (argN a 1)
    let f := (argN a 2).headD default
    let mut out : Array Seq := #[]
    for ((x, y), i) in (xs.zip ys).zip (List.range (min xs.length ys.length)) do
      out := out.push (← h.callN f [x, y, sInt (i + 1)])
    pure (arrItem out.toList)),
  ent "sort" (fun h e a => do
    let c ← e.collation (argN a 1)
    let ms ← asArr (argN a 0)
    let keyed ← ms.mapM (fun m => do
      match argN a 2 with
      | [] => pure (m, (← e.atomize m).map (collProxy c))
      | f :: _ => pure (m, (← e.atomize (← h.callN f [m])).map (collProxy c)))
    let sorted ← msortM (fun p q => do pure ((← sortCmpKeys p.2 q.2) == .lt)) 64 keyed
    pure (arrItem (sorted.map (·.1)))),
  ent "slice" (fun _ _ a => do
    let ms ← asArr (argN a 0)
    pure (arrItem ((sliceIdx ms.length (argN a 1) (argN a 2) (argN a 3)).filterMap (fun i => ms[i]?))))
]

/-- Look up the implementation of a built-in function. -/
def libLookup (q : QN) : Option LibFn :=
  let tbl := if q.uri == nsFN then fnTable ++ fnTable2 ++ fnTable3
    else if q.uri == nsMATH then mathTable
    else if q.uri == nsMAP then mapTable
    else if q.uri == nsARR then arrayTable
    else []
  tbl.lookup q.loc

end L4Factoidal.XPath4
