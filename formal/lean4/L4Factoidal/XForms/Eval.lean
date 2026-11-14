/-
L4Factoidal.XForms.Eval — XPath 1.0 evaluation for XForms 1.1 (§7):
a fuel-bounded evaluator over the XPath 1.0 data model
(`XPath.Full`, the project's XML tree with node addresses) that records
the nodes each location step selects (the read set used for the
dependency graph, §4.3.2 / Appendix C) and adds the XForms function
library (§7.6 to §7.11).

XForms 1.1 expressions are XPath 1.0, so the XPath 1.0 evaluator's
rules decide: node tests, axes, comparisons, number formatting and the
core function library are the existing `XPath.Full` definitions, called
from here. Only the expression walk is new, because the existing walk
has a fixed function table and no read set.

Instance `k` is document number `k + 2` in node addresses.

`digest` and `hmac` use the hashes already in the tree
(`Crypto.md5`, `Crypto.sha1`, `Crypto.sha256`, `Crypto.sha384`,
`Crypto.sha512`, `Crypto.hmacWith`); nothing cryptographic is defined
here.
-/
import L4Factoidal.XPath.Eval
import L4Factoidal.Crypto.Hmac
import L4Factoidal.Crypto.MD5
import L4Factoidal.Crypto.SHA1

namespace L4Factoidal.XForms.Engine

open L4Factoidal.XML
open L4Factoidal.XPath
open L4Factoidal.XPath.Full

/-- What an expression is evaluated against. -/
structure Env where
  /-- Instance documents; instance `k` has document number `k + 2`. -/
  docs : List Doc := []
  /-- Instance id to instance number, for the instances of the
      expression's own model (§7.10.1). -/
  instIds : List (String × Nat) := []
  defaultInst : Option Nat := none
  nsctx : List (String × String) := []
  /-- Repeat id to its index (§7.7.5). -/
  indexes : List (String × Nat) := []
  /-- The context node the expression started from, for `current()` (§7.10.2). -/
  current : Option Item := none
  /-- The in-scope evaluation context node of the element that holds the
      expression, for `context()` (§7.10.4). -/
  context : Option Item := none
  /-- Event context information, for `event()` (§7.11.2). -/
  eventInfo : List (String × Value) := []
  /-- The host's clock reading, an xsd:dateTime in UTC. -/
  now : String := "1970-01-01T00:00:00Z"
  /-- The host's timezone offset in minutes. -/
  tz : Int := 0
  seed : Nat := 42

def Env.docOf (env : Env) (it : Item) : Doc := (env.docs[it.loc.doc - 2]?).getD []

def isElem : Node → Bool
  | .element .. => true
  | _ => false

/-- The root element node of instance `k`. -/
def instRoot (env : Env) (k : Nat) : Option Item :=
  match env.docs[k]? with
  | none => none
  | some d => (d.findIdx? isElem).bind (fun i =>
      (d[i]?).map (fun n => Item.tree { path := [i], doc := k + 2 } n))

/-! ## Dates and durations (§7.9) -/

def daysFromCivil (y m d : Int) : Int :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def civilFromDays (z0 : Int) : Int × Int × Int :=
  let z := z0 + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

#guard daysFromCivil 1970 1 1 == 0
#guard daysFromCivil 2002 1 1 == 11688
#guard daysFromCivil 1969 12 31 == -1
#guard civilFromDays 11688 == (2002, 1, 1)
#guard civilFromDays (-1) == (1969, 12, 31)

def padInt (w : Nat) (n : Int) : String :=
  let s := toString n.natAbs
  (if n < 0 then "-" else "") ++ String.ofList (List.replicate (w - s.length) '0') ++ s

def digitsNat? (s : String) : Option Int :=
  if s.isEmpty || !s.toList.all Char.isDigit then none else s.toNat?.map Int.ofNat

def digitVal (c : Char) : Int := Int.ofNat (c.toNat - 48)

/-- Split a trailing timezone (`Z` or `±hh:mm`) off a date or dateTime. -/
def splitTz (s : String) : String × Option Int :=
  let cs := s.toList
  let n := cs.length
  if cs.getLast? == some 'Z' then (String.ofList (cs.take (n - 1)), some 0)
  else if n ≥ 6 then
    match cs.drop (n - 6) with
    | [sg, h1, h2, ':', m1, m2] =>
      if (sg == '+' || sg == '-') && [h1, h2, m1, m2].all Char.isDigit then
        let off := (digitVal h1 * 10 + digitVal h2) * 60 + digitVal m1 * 10 + digitVal m2
        (String.ofList (cs.take (n - 6)), some (if sg == '-' then -off else off))
      else (s, none)
    | _ => (s, none)
  else (s, none)

/-- `YYYY-MM-DD` as days since 1970-01-01. -/
def parseYMD (s : String) : Option Int :=
  match s.splitOn "-" with
  | [y, m, d] =>
    if y.length < 4 || m.length != 2 || d.length != 2 then none else do
      let yi ← digitsNat? y
      let mi ← digitsNat? m
      let di ← digitsNat? d
      let days := daysFromCivil yi mi di
      if mi ≥ 1 && mi ≤ 12 && civilFromDays days == (yi, mi, di) then some days else none
  | _ => none

/-- `hh:mm:ss(.s+)?` as seconds of the day. -/
def parseHMS (s : String) : Option Num :=
  match s.splitOn ":" with
  | [h, m, sec] =>
    if h.length != 2 || m.length != 2 then none else do
      let hi ← digitsNat? h
      let mi ← digitsNat? m
      let sn ← (match sec.splitOn "." with
        | [a] => if a.length == 2 then (digitsNat? a).map (fun i => Num.finite i 0) else none
        | [a, b] => if a.length == 2 && !b.isEmpty then
            (digitsNat? (a ++ b)).map (fun i => Num.finite i b.length) else none
        | _ => none)
      if hi > 24 || mi > 59 then none
      else some (Num.add (Num.finite (hi * 3600 + mi * 60) 0) sn)
  | _ => none

structure DT where
  days : Int
  secs : Num
  tz : Option Int
  hasTime : Bool

def parseDT (s : String) : Option DT :=
  let (body, tz) := splitTz s
  match body.splitOn "T" with
  | [d] => (parseYMD d).map (fun x => { days := x, secs := .finite 0 0, tz := tz, hasTime := false })
  | [d, t] => do
      let x ← parseYMD d
      let y ← parseHMS t
      some { days := x, secs := y, tz := tz, hasTime := true }
  | _ => none

def numFloor? (n : Num) : Option Int :=
  match Num.floorN n with
  | .finite m s => some (m / (10 : Int) ^ s)
  | _ => none

def fmtTz (tz : Int) : String :=
  if tz == 0 then "Z"
  else (if tz < 0 then "-" else "+") ++ padInt 2 (Int.ofNat tz.natAbs / 60) ++ ":" ++
       padInt 2 (Int.ofNat tz.natAbs % 60)

def fmtDate (days : Int) : String :=
  let (y, m, d) := civilFromDays days
  padInt 4 y ++ "-" ++ padInt 2 m ++ "-" ++ padInt 2 d

/-- Seconds since the epoch (UTC) shown as a dateTime in the zone `tz`. -/
def fmtDateTime (total : Int) (tz : Int) : String :=
  let loc := total + tz * 60
  let days := loc / 86400
  let sod := loc - days * 86400
  fmtDate days ++ "T" ++ padInt 2 (sod / 3600) ++ ":" ++ padInt 2 (sod % 3600 / 60) ++ ":" ++
    padInt 2 (sod % 60) ++ fmtTz tz

/-- Seconds since the epoch of a dateTime; no timezone is read as UTC. -/
def epochSeconds (dt : DT) : Num :=
  Num.add (Num.finite (dt.days * 86400 - (dt.tz.getD 0) * 60) 0) dt.secs

structure Dur where
  neg : Bool := false
  y : Int := 0
  mo : Int := 0
  d : Int := 0
  h : Int := 0
  mi : Int := 0
  s : Num := .finite 0 0
  inTime : Bool := false
  buf : String := ""
  ok : Bool := true
  parts : Nat := 0

/-- An xsd:duration lexical form (lenient about component order). -/
def parseDur (str : String) : Option Dur :=
  let cs := str.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | r => (false, r)
  match cs with
  | 'P' :: body =>
    let st := body.foldl (fun (st : Dur) c =>
      if !st.ok then st
      else if c.isDigit || c == '.' then { st with buf := st.buf.push c }
      else if c == 'T' then
        if st.inTime || st.buf != "" then { st with ok := false } else { st with inTime := true }
      else
        match digitsNat? st.buf, c, st.inTime with
        | some n, 'Y', false => { st with y := n, buf := "", parts := st.parts + 1 }
        | some n, 'M', false => { st with mo := n, buf := "", parts := st.parts + 1 }
        | some n, 'D', false => { st with d := n, buf := "", parts := st.parts + 1 }
        | some n, 'H', true => { st with h := n, buf := "", parts := st.parts + 1 }
        | some n, 'M', true => { st with mi := n, buf := "", parts := st.parts + 1 }
        | _, 'S', true =>
          (match st.buf.splitOn "." with
           | [a] => (match digitsNat? a with
              | some n => { st with s := .finite n 0, buf := "", parts := st.parts + 1 }
              | none => { st with ok := false })
           | [a, b] => (match digitsNat? (a ++ b) with
              | some n => if a.isEmpty || b.isEmpty then { st with ok := false }
                          else { st with s := .finite n b.length, buf := "", parts := st.parts + 1 }
              | none => { st with ok := false })
           | _ => { st with ok := false })
        | _, _, _ => { st with ok := false }) ({ neg := neg } : Dur)
    if st.ok && st.buf == "" && st.parts > 0 then some st else none
  | _ => none

def durSeconds (d : Dur) : Num :=
  let n := Num.add (Num.finite (d.d * 86400 + d.h * 3600 + d.mi * 60) 0) d.s
  if d.neg then Num.neg n else n

def durMonths (d : Dur) : Num :=
  let n := d.y * 12 + d.mo
  Num.finite (if d.neg then -n else n) 0

#guard (parseDur "P3DT10H30M1.5S").map (fun d => Num.toXString (durSeconds d)) == some "297001.5"
#guard (parseDur "P1Y2M").map (fun d => Num.toXString (durMonths d)) == some "14"
#guard (parseDur "-P19M").map (fun d => Num.toXString (durMonths d)) == some "-19"
#guard (parseDur "3").isNone

/-! ## Other helpers -/

/-- §7.6.2: the Luhn check over 12 to 19 digits. -/
def luhn (s : String) : Bool :=
  let ds := s.toList
  if ds.length < 12 || ds.length > 19 || !ds.all Char.isDigit then false else
  let r := ds.reverse.foldl (fun (acc : Nat × Bool) c =>
      let d := c.toNat - 48
      let d' := if acc.2 then (if 2 * d > 9 then 2 * d - 9 else 2 * d) else d
      (acc.1 + d', !acc.2)) (0, false)
  r.1 % 10 == 0

#guard luhn "4111111111111111"
#guard !luhn "4111111111111112"

def b64chars : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

def b64c (n : Nat) : String := (b64chars[n]?.getD 'A').toString

/-- RFC 4648 base64 of a byte string (an encoding, not a cryptographic step). -/
def base64Enc (b : ByteArray) : String :=
  let r := b.toList.foldl (fun (acc : String × List Nat) (x8 : UInt8) =>
    let x := x8.toNat
    match acc.2 with
    | [a, c] => (acc.1 ++ b64c (a / 4) ++ b64c (a % 4 * 16 + c / 16) ++ b64c (c % 16 * 4 + x / 64)
                  ++ b64c (x % 64), [])
    | l => (acc.1, l ++ [x])) ("", [])
  match r.2 with
  | [a] => r.1 ++ b64c (a / 4) ++ b64c (a % 4 * 16) ++ "=="
  | [a, c] => r.1 ++ b64c (a / 4) ++ b64c (a % 4 * 16 + c / 16) ++ b64c (c % 16 * 4) ++ "="
  | _ => r.1

#guard base64Enc "foobar".toUTF8 == "Zm9vYmFy"
#guard base64Enc "fooba".toUTF8 == "Zm9vYmE="
#guard base64Enc "foob".toUTF8 == "Zm9vYg=="

/-- The hash an algorithm name selects (§7.8.3), with its block size in bytes. -/
def hashOf (alg : String) : Option ((ByteArray → ByteArray) × Nat) :=
  if alg == "MD5" then some (Crypto.md5, 64)
  else if alg == "SHA-1" then some (Crypto.sha1, 64)
  else if alg == "SHA-256" then some (Crypto.sha256, 64)
  else if alg == "SHA-384" then some (Crypto.sha384, 128)
  else if alg == "SHA-512" then some (Crypto.sha512, 128)
  else none

def encodeBytes (enc : String) (b : ByteArray) : Except String Value :=
  if enc == "hex" then .ok (.str (Crypto.bytesToHex b))
  else if enc == "base64" then .ok (.str (base64Enc b))
  else .error s!"unsupported encoding '{enc}'"

def valueStrings (v : Value) : List String :=
  match v with
  | .nodes ns => (normalize ns).map (·.stringValue)
  | o => [o.toStr]

def numIsNaN : Num → Bool
  | .nan => true
  | _ => false

def numNat? : Num → Option Nat
  | .finite m s => if m ≥ 0 && m % (10 : Int) ^ s == 0 then some (m / (10 : Int) ^ s).toNat else none
  | _ => none

/-- The XPath core library, through the XPath 1.0 evaluator: the
    argument values are bound to variables and the call is evaluated
    there. -/
def callCore (env : Env) (it : Item) (pos size : Nat) (f : String) (vals : List Value) : Option Value :=
  let names := (List.range vals.length).map (fun i => s!"a{i}")
  let c : Ctx := { doc := [], item := it, pos := pos, size := size, nsctx := env.nsctx,
                   docs := env.docs.map (fun d => ("", d)), vars := names.zip vals }
  evalExpr c (.call f (names.map Expr.varRef))

/-- A function call: the XForms function library (§7.6 to §7.11), then
    the XPath core library. -/
def callFn (env : Env) (it : Item) (pos size : Nat) (f0 : String) (vals : List Value) :
    Except String Value :=
  let f := localOf f0
  let nan : Value := .num .nan
  match f, vals with
  | "instance", args =>
      let id := (args.head?.map Value.toStr).getD ""
      let k := if id == "" then env.defaultInst else (env.instIds.find? (·.1 == id)).map (·.2)
      .ok (.nodes ((k.bind (instRoot env)).toList))
  | "current", [] => .ok (.nodes [env.current.getD it])
  | "context", [] => .ok (.nodes [env.context.getD (env.current.getD it)])
  | "id", v :: rest =>
      -- §7.10.3: the elements of type xsd:ID (here: `xsi:type` naming `ID`) or with
      -- an `xml:id` attribute whose value is one of the given IDs, in the documents
      -- of the second argument's nodes (default: the context node's document)
      let refs := match v with
        | .nodes ns => (normalize ns).flatMap (fun (i : Item) => splitWs i.stringValue)
        | other => splitWs other.toStr
      let roots : List Item := match rest with
        | [.nodes ns] => ns
        | _ => [it]
      let docNos := (roots.map (·.loc.doc)).eraseDups
      let found := docNos.flatMap (fun k =>
        (allItems (env.docOf (Item.doc [] k)) k).filter (fun x =>
          match x with
          | .tree _ (.element _ attrs _) =>
            (attrs.any (fun a => localOf a.name == "type" && prefixOf a.name != "" && localOf a.value == "ID")
              && refs.contains (normalizeSpaceStr x.stringValue)) ||
            attrs.any (fun a => a.name == "xml:id" && refs.contains a.value)
          | _ => false))
      .ok (.nodes (normalize found))
  | "index", [v] =>
      .ok (match env.indexes.find? (·.1 == v.toStr) with
        | some (_, i) => .num (.finite (Int.ofNat i) 0)
        | none => nan)
  | "boolean-from-string", [v] =>
      let s := v.toStr.toLower
      .ok (.bool (s == "true" || s == "1"))
  | "is-card-number", [] => .ok (.bool (luhn it.stringValue))
  | "is-card-number", [v] => .ok (.bool (luhn v.toStr))
  | "if", [c, a, b] => .ok (.str (if c.toBool then a.toStr else b.toStr))
  | "choose", [c, a, b] => .ok (if c.toBool then a else b)
  | "avg", [v] =>
      let xs := (valueStrings v).map Num.ofString
      .ok (if xs.isEmpty then nan
           else .num (Num.div (xs.foldl Num.add (.finite 0 0)) (.finite (Int.ofNat xs.length) 0)))
  | "min", [v] =>
      let xs := (valueStrings v).map Num.ofString
      .ok (match xs with
        | [] => nan
        | x :: r => if xs.any numIsNaN then nan
                    else .num (r.foldl (fun a b => if Num.lt b a then b else a) x))
  | "max", [v] =>
      let xs := (valueStrings v).map Num.ofString
      .ok (match xs with
        | [] => nan
        | x :: r => if xs.any numIsNaN then nan
                    else .num (r.foldl (fun a b => if Num.lt a b then b else a) x))
  | "count-non-empty", [v] =>
      .ok (.num (.finite (Int.ofNat ((valueStrings v).filter (· != "")).length) 0))
  | "power", [a, b] =>
      let base := a.toNum
      (match numNat? b.toNum with
       | some n => .ok (.num ((List.range n).foldl (fun acc _ => Num.mul acc base) (.finite 1 0)))
       | none =>
         match numNat? (Num.neg b.toNum) with
         | some n => .ok (.num (Num.div (.finite 1 0)
             ((List.range n).foldl (fun acc _ => Num.mul acc base) (.finite 1 0))))
         | none =>
           if Num.lt base (.finite 0 0) || numIsNaN base || numIsNaN b.toNum then .ok nan
           else .error "power(): a non-integer exponent is not supported")
  | "random", _ => .ok (.num (.finite (Int.ofNat ((env.seed * 1103515245 + 12345) % 1000000)) 6))
  | "compare", [a, b] =>
      let x := a.toStr
      let y := b.toStr
      .ok (.num (.finite (if x < y then -1 else if y < x then 1 else 0) 0))
  | "property", [v] =>
      let n := v.toStr
      if n == "version" then .ok (.str "1.1")
      else if n == "conformance-level" then .ok (.str "basic")
      else if prefixOf n != "" then .ok (.str "")
      else .error s!"property(): '{n}' is not a property name"
  | "digest", d :: a :: rest =>
      (match hashOf a.toStr, rest with
       | some (h, _), [] => encodeBytes "base64" (h d.toStr.toUTF8)
       | some (h, _), [e] => encodeBytes e.toStr (h d.toStr.toUTF8)
       | _, _ => .error s!"digest(): unsupported algorithm '{a.toStr}' or wrong arguments")
  | "hmac", k :: d :: a :: rest =>
      (match hashOf a.toStr, rest with
       | some (h, blk), [] => encodeBytes "base64" (Crypto.hmacWith h blk k.toStr.toUTF8 d.toStr.toUTF8)
       | some (h, blk), [e] => encodeBytes e.toStr (Crypto.hmacWith h blk k.toStr.toUTF8 d.toStr.toUTF8)
       | _, _ => .error s!"hmac(): unsupported algorithm '{a.toStr}' or wrong arguments")
  | "now", [] => .ok (.str env.now)
  | "local-date", [] =>
      .ok (.str (match (parseDT env.now).bind (fun dt => numFloor? (epochSeconds dt)) with
        | some t => fmtDate ((t + env.tz * 60) / 86400) ++ fmtTz env.tz
        | none => ""))
  | "local-dateTime", [] =>
      .ok (.str (match (parseDT env.now).bind (fun dt => numFloor? (epochSeconds dt)) with
        | some t => fmtDateTime t env.tz
        | none => ""))
  | "days-from-date", [v] =>
      .ok (match parseDT v.toStr with
        | some dt =>
          if dt.hasTime then
            (match numFloor? (epochSeconds dt) with
             | some t => .num (.finite (t / 86400) 0)
             | none => nan)
          else .num (.finite dt.days 0)
        | none => nan)
  | "days-to-date", [v] =>
      .ok (.str (match numFloor? (Num.roundN v.toNum) with
        | some d => fmtDate d
        | none => ""))
  | "seconds-from-dateTime", [v] =>
      .ok (match parseDT v.toStr with
        | some dt => if dt.hasTime then .num (epochSeconds dt) else nan
        | none => nan)
  | "seconds-to-dateTime", [v] =>
      .ok (.str (match numFloor? v.toNum with
        | some t => fmtDateTime t 0
        | none => ""))
  | "adjust-dateTime-to-timezone", [v] =>
      .ok (.str (match parseDT v.toStr with
        | some dt =>
          if !dt.hasTime then "" else
          (match numFloor? (epochSeconds dt), dt.tz with
           | some t, some _ => fmtDateTime t env.tz
           | some t, none => fmtDateTime (t - env.tz * 60) env.tz
           | none, _ => "")
        | none => ""))
  | "seconds", [v] => .ok (match parseDur v.toStr with
      | some d => .num (durSeconds d)
      | none => nan)
  | "months", [v] => .ok (match parseDur v.toStr with
      | some d => .num (durMonths d)
      | none => nan)
  | "event", [v] =>
      .ok (((env.eventInfo.find? (·.1 == v.toStr)).map (·.2)).getD (.nodes []))
  | _, _ =>
      match callCore env it pos size f0 vals with
      | some v => .ok v
      | none => .error s!"unknown function or wrong arguments: {f0}()"

/-- Evaluation with the read set as state. -/
abbrev EvalM := StateT (List Loc) (Except String)

/-- Evaluate an expression at a context (node, position, size). The
    first argument bounds the nesting depth of the expression. The
    state collects the address of every node a location step selects. -/
def evalE : Nat → Env → Item → Nat → Nat → Expr → EvalM Value
  | 0, _, _, _, _, _ => throw "XPath expression nested too deeply"
  | f + 1, env, it, pos, size, e =>
    let predE (cur : List Item) (p : Expr) : EvalM (List Item) := do
      let n := cur.length
      let kept ← cur.zipIdx.foldlM (fun (acc : List Item) (x : Item × Nat) => do
        let v ← evalE f env x.1 (x.2 + 1) n p
        let keep := match v with
          | .num k => Num.eq k (Num.finite ((x.2 : Int) + 1) 0)
          | other => other.toBool
        pure (if keep then x.1 :: acc else acc)) []
      pure kept.reverse
    let stepE (base : List Item) (s : Step) : EvalM (List Item) := do
      let out ← base.foldlM (fun (acc : List Item) (b : Item) => do
        let d := env.docOf b
        let cands := (axisItems d s.ax b).filter (matchesTest d env.nsctx s.ax s.test)
        let kept ← s.preds.foldlM predE cands
        pure (acc ++ kept)) []
      let res := normalize out
      modify (fun r => res.map (·.loc) ++ r)
      pure res
    match e with
    | .num n => pure (.num n)
    | .str s => pure (.str s)
    | .varRef v => throw s!"unbound variable ${v}"
    | .call name args => do
        let vals ← args.mapM (evalE f env it pos size)
        match callFn env it pos size name vals with
        | .ok v => pure v
        | .error m => throw m
    | .or a b => do
        let x ← evalE f env it pos size a
        if x.toBool then pure (.bool true) else do
          let y ← evalE f env it pos size b
          pure (.bool y.toBool)
    | .and a b => do
        let x ← evalE f env it pos size a
        if !x.toBool then pure (.bool false) else do
          let y ← evalE f env it pos size b
          pure (.bool y.toBool)
    | .cmp op a b => do
        let x ← evalE f env it pos size a
        let y ← evalE f env it pos size b
        pure (.bool (cmpValues op x y))
    | .arith op a b => do
        let x ← evalE f env it pos size a
        let y ← evalE f env it pos size b
        let m := x.toNum
        let n := y.toNum
        pure (.num (if op == "+" then Num.add m n
                    else if op == "-" then Num.sub m n
                    else if op == "*" then Num.mul m n
                    else if op == "div" then Num.div m n
                    else Num.modN m n))
    | .negate a => do
        let x ← evalE f env it pos size a
        pure (.num (Num.neg x.toNum))
    | .union a b => do
        let x ← evalE f env it pos size a
        let y ← evalE f env it pos size b
        match x, y with
        | .nodes p, .nodes q => pure (.nodes (normalize (p ++ q)))
        | _, _ => throw "the operands of | must be node-sets"
    | .filter base preds => do
        let v ← evalE f env it pos size base
        match v with
        | .nodes ns => do
            let r ← preds.foldlM predE (normalize ns)
            pure (.nodes r)
        | _ => throw "a predicate applies to a node-set only"
    | .path abs start steps =>
        let root : Item := Item.doc (env.docOf it) it.loc.doc
        match start with
        | none => do
            let r ← steps.foldlM stepE (if abs then [root] else [it])
            pure (.nodes r)
        | some e0 => do
            let v ← evalE f env it pos size e0
            match v with
            | .nodes ns => do
                let r ← steps.foldlM stepE (if abs then [root] else normalize ns)
                pure (.nodes r)
            | _ => throw "a location path applies to a node-set only"

/-- Parse and evaluate; the result carries the read set. -/
def evalStr (env : Env) (it : Item) (pos size : Nat) (src : String) :
    Except String (Value × List Loc) :=
  match parseExpr src with
  | none => .error s!"XPath syntax error in '{src}'"
  | some e => (evalE 256 env it pos size e).run []

end L4Factoidal.XForms.Engine
