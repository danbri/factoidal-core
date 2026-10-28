/-
L4Factoidal.XPath4.ElemMap — `fn:element-to-map`, `fn:element-to-map-plan`
and `fn:map-to-element` (F&O 4.0 §14.6, "Converting elements to maps").

Spec: F&O 4.0 editor's draft, sections 14.6.1 (layouts), 14.6.2 (creating a
conversion plan), 14.6.3 (inferring a data type), 14.6.5 (structure of the
plan), 14.6.7 (selecting a layout), 14.6.8 (names), 14.6.9 (content),
14.6.12 (maps to elements). Where the draft and the tests of
`qt4tests/fn/element-to-map*.xml` and `map-to-element.xml` disagree, the
tests decide (for example: without a plan, attributes are untyped, and the
`child` entry of a list layout is always present).

Not modelled: the schema-based layouts of 14.6.6 and the `nilled` property
(there are no type annotations: every element is untyped, so an
`xsi:nil="true"` attribute is only dropped, never mapped).

Elements built by `fn:map-to-element` are new parentless elements of a
runtime document (`NodeRef.rt`); the document number is derived from the
content (the dynamic context is read-only), so two calls with the same
map give nodes that are `is`-identical.
-/
import L4Factoidal.XPath4.Serialize
import L4Factoidal.XML.Wellformedness
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.XPath4

open L4Factoidal.XML
open L4Factoidal.XSD

/-! ## Names and constants -/

def nsXSI : String := "http://www.w3.org/2001/XMLSchema-instance"
def nsXMLNS : String := "http://www.w3.org/2000/xmlns/"

/-- The key of an element or attribute name in a conversion plan:
    `local` or `Q{uri}local`. -/
def e2mNameKey (q : QN) : String :=
  if q.uri == "" then q.loc else "Q{" ++ q.uri ++ "}" ++ q.loc

/-- Read a plan name: `local` or `Q{uri}local` (the URI is omitted for a
    name in no namespace). -/
def e2mPlanName? (s : String) : Option (String × String) :=
  if s.startsWith "Q{" then
    match (s.drop 2).toString.splitOn "}" with
    | [uri, l] => if uri != "" && isValidNCName l then some (uri, l) else none
    | _ => none
  else if isValidNCName s then some ("", s) else none

/-! ## Layouts and plans -/

inductive Layout where
  | empty | emptyPlus | simple | simplePlus | list | listPlus
  | record | sequence | mixed | xml | error | deepSkip
deriving DecidableEq, Repr, Inhabited

def Layout.ofName? : String → Option Layout
  | "empty" => some .empty | "empty-plus" => some .emptyPlus
  | "simple" => some .simple | "simple-plus" => some .simplePlus
  | "list" => some .list | "list-plus" => some .listPlus
  | "record" => some .record | "sequence" => some .sequence
  | "mixed" => some .mixed | "xml" => some .xml
  | "error" => some .error | "deep-skip" => some .deepSkip
  | _ => none

def Layout.name : Layout → String
  | .empty => "empty" | .emptyPlus => "empty-plus"
  | .simple => "simple" | .simplePlus => "simple-plus"
  | .list => "list" | .listPlus => "list-plus"
  | .record => "record" | .sequence => "sequence"
  | .mixed => "mixed" | .xml => "xml"
  | .error => "error" | .deepSkip => "deep-skip"

/-- An `fn:element-conversion-plan-record`. -/
structure ElemPlan where
  layout : Layout
  child : Option String := none
  ty : Option String := none
deriving Inhabited

/-- A conversion plan: element entries (keyed by plan name, or `*`) and
    attribute entries (keyed by plan name; the type, `none` for string). -/
structure Plan where
  elems : List (String × ElemPlan) := []
  attrs : List (String × Option String) := []
deriving Inhabited

/-- The options shared by the three functions. -/
structure E2MOpts where
  plan : Plan := {}
  marker : String := "@"
  contentKey : String := "#content"
  fmt : String := "default"
  escape : Bool := false
  liberal : Bool := false
deriving Inhabited

private def planStr? (s : Seq) : M (Option String) :=
  match s with
  | [] => pure none
  | [.atom a] =>
    if a.isStringLike then pure (some a.str)
    else err "XPTY0004" "a conversion plan entry must be a string"
  | _ => err "XPTY0004" "a conversion plan entry must be a single string"

private def planField (m : List (Atomic × Seq)) (k : String) : M (Option String) :=
  match mapGet m (Atomic.ofStr k) with
  | none => pure none
  | some s => planStr? s

private def planKeysOk (m : List (Atomic × Seq)) (allowed : List String) : M Unit := do
  for (k, _) in m do
    if !(k.isStringLike && allowed.contains k.str) then
      err "XPTY0004" ("unknown field " ++ k.str ++ " in a conversion plan entry")

def e2mTypes : List String := ["integer", "decimal", "double", "boolean", "string"]

def parseElemPlan (m : List (Atomic × Seq)) : M ElemPlan := do
  planKeysOk m ["layout", "child", "type"]
  let lname ← planField m "layout"
  let layout ← match lname with
    | none => err "XPTY0004" "a conversion plan entry has no layout"
    | some s => match Layout.ofName? s with
      | some l => pure l
      | none => err "XPTY0004" ("unknown layout " ++ s)
  let child ← planField m "child"
  let ty ← planField m "type"
  let isList := layout == .list || layout == .listPlus
  match child with
  | none => if isList then err "XPTY0004" "a list layout needs a child name"
  | some c =>
    if !isList then err "XPTY0004" "only a list layout has a child name"
    if (e2mPlanName? c).isNone then err "XPTY0004" ("invalid child name " ++ c)
  match ty with
  | none => pure ()
  | some t =>
    if !(layout == .simple || layout == .simplePlus) then
      err "XPTY0004" "only the simple layouts have a type"
    if !e2mTypes.contains t then err "XPTY0004" ("unknown type " ++ t)
  pure { layout, child, ty := if ty == some "string" then none else ty }

def parseAttrPlan (m : List (Atomic × Seq)) : M (Option String) := do
  planKeysOk m ["type"]
  match ← planField m "type" with
  | none => pure none
  | some t =>
    if t == "string" then pure none
    else if t == "skip" || e2mTypes.contains t then pure (some t)
    else err "XPTY0004" ("unknown attribute type " ++ t)

/-- The `plan` option. Every entry whose key has a valid form is checked,
    whether or not the conversion reaches it. -/
def parsePlan (s : Seq) : M Plan := do
  match s with
  | [] => pure {}
  | [.map kvs] =>
    let mut elems : Array (String × ElemPlan) := #[]
    let mut attrs : Array (String × Option String) := #[]
    for (k, v) in kvs do
      if !k.isStringLike then err "XPTY0004" "the keys of a conversion plan are strings"
      let ks := k.str
      let body : Option (List (Atomic × Seq)) ← match v with
        | [.map m] => pure (some m)
        | _ => pure none
      if ks == "*" then
        match body with
        | some m => elems := elems.push ("*", ← parseElemPlan m)
        | none => err "XPTY0004" "a conversion plan entry must be a map"
      else if ks.startsWith "@" then
        let nm := (ks.drop 1).toString
        if (e2mPlanName? nm).isSome then
          match body with
          | some m => attrs := attrs.push (nm, ← parseAttrPlan m)
          | none => err "XPTY0004" "a conversion plan entry must be a map"
      else if (e2mPlanName? ks).isSome then
        match body with
        | some m => elems := elems.push (ks, ← parseElemPlan m)
        | none => err "XPTY0004" "a conversion plan entry must be a map"
    pure { elems := elems.toList, attrs := attrs.toList }
  | _ => err "XPTY0004" "the plan option must be a map"

private def optString (opts : Seq) (key dflt : String) : M String :=
  match optLookup opts key with
  | none => pure dflt
  | some [] => pure dflt
  | some [.atom a] =>
    if a.isStringLike then pure a.str else err "XPTY0004" ("option " ++ key ++ " must be a string")
  | some _ => err "XPTY0004" ("option " ++ key ++ " must be a single string")

private def optBoolean (opts : Seq) (key : String) (dflt : Bool) : M Bool :=
  match optLookup opts key with
  | some [] => pure dflt
  | _ => optBool opts key dflt

def e2mOptionNames : List String :=
  ["plan", "attribute-marker", "content-key", "name-format", "escape-names", "liberal"]

def e2mOptions (opts : Seq) : M E2MOpts := do
  match opts with
  | [] | [.map _] => pure ()
  | _ => err "XPTY0004" "the options must be a map"
  checkOptionKeys opts e2mOptionNames
  let plan ← match optLookup opts "plan" with
    | some s => parsePlan s
    | none => pure {}
  let marker ← optString opts "attribute-marker" "@"
  let contentKey ← optString opts "content-key" "#content"
  let fmt ← optString opts "name-format" "default"
  if !["default", "eqname", "local", "lexical"].contains fmt then
    err "XPTY0004" ("unknown name-format " ++ fmt)
  let escape ← optBoolean opts "escape-names" false
  let liberal ← optBoolean opts "liberal" false
  pure { plan, marker, contentKey, fmt, escape, liberal }

/-! ## Escaping of names (14.6.8) -/

/-- Replace each `_xHHHH_` and `_xHHHHHH_` by its codepoint; `_x_` is the
    empty name. One pass over the input (the output is not rescanned). -/
def decodeEscAux : Nat → List Char → List Char → M (List Char)
  | 0, _, acc => pure acc.reverse
  | _ + 1, [], acc => pure acc.reverse
  | f + 1, '_' :: 'x' :: rest, acc =>
    let ds := rest.takeWhile (fun c => (hexDigitVal? c).isSome)
    let after := rest.drop ds.length
    if (ds.length == 4 || ds.length == 6) && after.head? == some '_' then
      let cp := ds.foldl (fun a c => a * 16 + (hexDigitVal? c).getD 0) 0
      if isXmlCp cp then decodeEscAux f (after.drop 1) (Char.ofNat cp :: acc)
      else err "FOCH0001" ("the escape sequence names a codepoint that is not an XML character: " ++ toString cp)
    else decodeEscAux f ('x' :: rest) ('_' :: acc)
  | f + 1, c :: rest, acc => decodeEscAux f rest (c :: acc)

def decodeEsc (s : String) : M String :=
  if s == "_x_" then pure "" else do
    let cs := s.toList
    pure (String.ofList (← decodeEscAux (cs.length + 1) cs []))

def hexUpperPad (n k : Nat) : String :=
  let ds := "0123456789ABCDEF".toList
  String.ofList ((List.range k).reverse.map (fun i => ds.getD ((n / 16 ^ i) % 16) '0'))

/-- The XML 1.0 `Char` production. -/
def isXml10Char (c : Char) : Bool :=
  let n := c.toNat
  n == 9 || n == 10 || n == 13 || (0x20 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) ||
    (0x10000 ≤ n && n ≤ 0x10FFFF)

def isXml10Str (s : String) : Bool := s.toList.all isXml10Char

def encodeEscAux : Nat → Bool → List Char → List String → List String
  | 0, _, _, acc => acc.reverse
  | _ + 1, _, [], acc => acc.reverse
  | f + 1, first, c :: rest, acc =>
    let ok := if first then isNCNameStartChar c else isNCNameChar c
    let esc := fun (cp : Nat) => "_x" ++ hexUpperPad cp (if cp > 0xFFFF then 6 else 4) ++ "_"
    if c == '_' && rest.head? == some 'x' then encodeEscAux f false rest (esc 0x5F :: acc)
    else if ok then encodeEscAux f false rest (String.ofList [c] :: acc)
    else encodeEscAux f false rest (esc c.toNat :: acc)

/-- The escape of a key as a local name (the inverse of `decodeEsc`). -/
def encodeEsc (s : String) : M String :=
  if s == "" then pure "_x_"
  else if !isXml10Str s then err "FOJS0009" "the key holds a character that is not an XML character"
  else
    let cs := s.toList
    pure (String.join (encodeEscAux (cs.length + 1) true cs []))

/-! ## Atomic helpers -/

def isNullAtom (a : Atomic) : Bool :=
  match a.v with
  | .qn q => q.uri == nsFN && q.loc == "null"
  | _ => false

def isNullSeq (v : Seq) : Bool :=
  match v with
  | [.atom a] => isNullAtom a
  | _ => false

def nullItem : Item := .atom (Atomic.ofQN { uri := nsFN, loc := "null" })

def untypedItem (s : String) : Item := .atom (Atomic.untypedOf s)
def stringItem (s : String) : Item := .atom (Atomic.ofStr s)

/-- A map item with one entry. -/
def single1 (k : String) (v : Item) : Item := .map [(Atomic.ofStr k, [v])]

/-! ## Accumulating map entries; equal keys are combined into an array -/

structure Acc where
  idx : Std.HashMap String Nat := {}
  ents : Array (String × Array Item) := #[]

def Acc.add (a : Acc) (k : String) (v : Item) : Acc :=
  match a.idx[k]? with
  | some i => { a with ents := a.ents.modify i (fun (k0, vs) => (k0, vs.push v)) }
  | none => { idx := a.idx.insert k a.ents.size, ents := a.ents.push (k, #[v]) }

def Acc.toItem (a : Acc) : Item :=
  .map (a.ents.toList.map fun (k, vs) =>
    (Atomic.ofStr k, [if vs.size == 1 then vs.getD 0 default else Item.arr (vs.toList.map (fun x => [x]))]))

/-- Prepend `#` to `k` until it is not in `used` (14.6.14, `content-key`). -/
def uniqueKey (k : String) (used : List String) : String :=
  go (used.length + 1) k
where
  go : Nat → String → String
    | 0, k => k
    | f + 1, k => if used.contains k then go f ("#" ++ k) else k

/-! ## Inferring a data type (14.6.3) -/

private def leadingZero (s : String) : Bool :=
  let t := trimWs s
  let body := match t.toList with
    | '-' :: r | '+' :: r => r
    | r => r
  match body with
  | '0' :: d :: _ => d.isDigit
  | _ => false

/-- The type selected for a set of strings: `none` is `string`. -/
def inferSimpleType (ss : List String) : Option String :=
  let dbls := ss.map (fun s => match castFromString s (.b .double) with
    | .ok a => match a.v with
        | .dbl f => some f
        | _ => none
    | .error _ => none)
  let allDbl := dbls.all Option.isSome
  let finite := dbls.all (fun o => match o with
    | some f => !(f.isNaN || f.isInf)
    | none => false)
  if allDbl && finite then
    if ss.all (fun s => (parseIntegerLex (trimWs s)).isSome) then
      if ss.any leadingZero then none else some "integer"
    else if ss.all (fun s => (parseDecimalLex (trimWs s)).isSome) then some "decimal"
    else some "double"
  else if ss.all (fun s => ["0", "1", "false", "true"].contains (trimWs s)) then some "boolean"
  else none

/-- The content of an element or attribute under the prescribed type
    (14.6.9). Empty and whitespace-only content is never cast. -/
def e2mContent (o : E2MOpts) (s : String) (ty : Option String) : M Atomic :=
  match ty with
  | none => pure (Atomic.untypedOf s)
  | some t =>
    if trimWs s == "" then pure (Atomic.untypedOf s)
    else
      let target : Option AType := match t with
        | "integer" => some (.b .integer) | "decimal" => some (.b .decimal)
        | "double" => some (.b .double) | "boolean" => some (.b .boolean)
        | _ => none
      match target with
      | none => pure (Atomic.untypedOf s)
      | some at_ =>
        match castFromString s at_ with
        | .ok a => pure a
        | .error _ =>
          if o.liberal then pure (Atomic.untypedOf s)
          else err "FOJS0010" ("cannot cast '" ++ s ++ "' to xs:" ++ t)

/-! ## Names of elements and attributes in the output (14.6.8) -/

def e2mLocal (o : E2MOpts) (l : String) : M String :=
  if o.escape then decodeEsc l else pure l

def e2mElemName (o : E2MOpts) (parentUri : Option String) (q : QN) : M String := do
  let l ← e2mLocal o q.loc
  let eq := if q.uri == "" then l else "Q{" ++ q.uri ++ "}" ++ l
  match o.fmt with
  | "eqname" => pure eq
  | "local" => pure l
  | "lexical" => pure (if q.pfx == "" then l else q.pfx ++ ":" ++ l)
  | _ =>
    match parentUri with
    | none => pure eq
    | some pu => pure (if q.uri == pu then l else "Q{" ++ q.uri ++ "}" ++ l)

def e2mAttrName (o : E2MOpts) (q : QN) : M String := do
  let l ← e2mLocal o q.loc
  if q.uri == nsXML then pure ("xml:" ++ l)
  else match o.fmt with
    | "local" => pure l
    | "lexical" => pure (if q.pfx == "" then l else q.pfx ++ ":" ++ l)
    | _ => pure (if q.uri == "" then l else "Q{" ++ q.uri ++ "}" ++ l)

/-! ## Serialization of an element (method xml, no indent, no declaration) -/

-- Used only to derive the identity key of a map-to-element result;
-- the `xml` layout uses `XPath4.Serialize`.
def e2mEscText (s : String) : String :=
  String.join (s.toList.map (fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '\r' => "&#xD;" | c => String.ofList [c]))

-- Used only to derive the identity key of a map-to-element result;
-- the `xml` layout uses `XPath4.Serialize`.
def e2mEscAttr (s : String) : String :=
  String.join (s.toList.map (fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '"' => "&quot;" | '\n' => "&#xA;"
    | '\t' => "&#x9;" | '\r' => "&#xD;" | c => String.ofList [c]))

/-- The prefix bindings of a scope list (newest first), one per prefix. -/
private def scopeDedup (sc : List (String × String)) : List (String × String) :=
  (sc.foldl (fun (acc : List (String × String)) (p, u) =>
    if acc.any (fun (q, _) => q == p) then acc else (p, u) :: acc) []).reverse

-- Used only to derive the identity key of a map-to-element result;
-- the `xml` layout uses `XPath4.Serialize`.
/-- Serialize a node subtree. `declared` is what the output has declared
    so far (newest first); an element declares only the bindings in scope
    that are not already declared. -/
def e2mSerNode (e : Env) : Nat → List (String × String) → NodeRef → String
  | 0, _, _ => ""
  | f + 1, declared, n =>
    let r := e.nrec n
    match r.kind with
    | .document =>
        String.join (r.children.toList.map (fun c => e2mSerNode e f declared (n.at c)))
    | .text => e2mEscText r.value
    | .comment => "<!--" ++ r.value ++ "-->"
    | .pi => "<?" ++ r.name.loc ++ (if r.value == "" then "" else " " ++ r.value) ++ "?>"
    | .attribute => r.name.show ++ "=\"" ++ e2mEscAttr r.value ++ "\""
    | .namespace => ""
    | .element =>
      let need := (scopeDedup r.inscope).reverse.filter (fun (p, u) =>
        p != "xml" && match declared.lookup p with
          | some u0 => u0 != u
          | none => !(p == "" && u == ""))
      let declared' := need ++ declared
      let decls := need.map (fun (p, u) =>
        " xmlns" ++ (if p == "" then "" else ":" ++ p) ++ "=\"" ++ e2mEscAttr u ++ "\"")
      let ats := r.attrs.toList.map (fun a =>
        let ra := e.nrec (n.at a)
        " " ++ ra.name.show ++ "=\"" ++ e2mEscAttr ra.value ++ "\"")
      let body := String.join (r.children.toList.map (fun c => e2mSerNode e f declared' (n.at c)))
      let nm := r.name.show
      "<" ++ nm ++ String.join decls ++ String.join ats ++
        (if body == "" then "/>" else ">" ++ body ++ "</" ++ nm ++ ">")

def e2mSerialize (e : Env) (n : NodeRef) : String := e2mSerNode e 100000 [] n

/-! ## Choosing a layout for an element: the rules of 14.6.2 -/

inductive KidK where
  | elem | wsText | text | comment | pi
deriving DecidableEq

def kidKind (e : Env) (c : NodeRef) : KidK :=
  let r := e.nrec c
  match r.kind with
  | .element => .elem
  | .text => if isXmlWs r.value then .wsText else .text
  | .pi => .pi
  | _ => .comment

def e2mKids (e : Env) (n : NodeRef) : List NodeRef :=
  ((e.nrec n).children.toList.map n.at)

/-- The attributes of an element that take part in a conversion: those
    outside the `xsi` namespace. -/
def e2mAttrNodes (e : Env) (n : NodeRef) : List NodeRef :=
  ((e.nrec n).attrs.toList.map n.at).filter (fun a => (e.nrec a).name.uri != nsXSI)

def e2mIsNilled (e : Env) (n : NodeRef) : Bool :=
  ((e.nrec n).attrs.toList.map n.at).any (fun a =>
    let r := e.nrec a
    r.name.uri == nsXSI && r.name.loc == "nil" && ["true", "1"].contains (trimWs r.value))

def allDistinct (xs : List String) : Bool := Id.run do
  let mut seen : Std.HashSet String := {}
  for x in xs do
    if seen.contains x then return false
    seen := seen.insert x
  return true

/-- The layout, child name and type for the elements `ees` of one name
    (14.6.2, 14.6.4). -/
def e2mInfer (e : Env) (ees : List NodeRef) : Layout × Option String × Option String :=
  let live := ees.filter (fun n => !e2mIsNilled e n)
  if live.isEmpty then (.mixed, none, none)
  else
    let kinds := live.map (fun n => (e2mKids e n).map (kidKind e))
    let noAttrs := live.all (fun n => (e2mAttrNodes e n).isEmpty)
    if kinds.all (fun ks => ks.all (fun k => k == .comment || k == .pi)) then
      ((if noAttrs then .empty else .emptyPlus), none, none)
    else if kinds.all (fun ks => ks.all (fun k => k != .elem)) then
      let strs := live.map (fun n => e.nodeString n)
      ((if noAttrs then .simple else .simplePlus), none, inferSimpleType strs)
    else if kinds.all (fun ks => ks.all (fun k => k != .text)) then
      let names : List (List String) := live.map (fun n =>
        (e2mKids e n).filter (fun c => kidKind e c == .elem) |>.map (fun c => e2mNameKey (e.nrec c).name))
      let flat := names.flatten
      let first := flat.headD ""
      if flat.all (· == first) && names.any (fun l => l.length ≥ 2) then
        ((if noAttrs then .list else .listPlus), some first, none)
      else if names.all allDistinct then (.record, none, none)
      else (.sequence, none, none)
    else (.mixed, none, none)

/-! ## fn:element-to-map -/

/-- Apply one layout to an element. `none` is "this layout cannot be used
    for this element". `conv` converts a child element to the value of its
    entry (`none` when the child is skipped). -/
def e2mApply (o : E2MOpts) (e : Env) (conv : NodeRef → M (Option Item))
    (n : NodeRef) (l : Layout) (child ty : Option String) : M (Option Item) := do
  let r := e.nrec n
  let kids := e2mKids e n
  let kinds := kids.map (kidKind e)
  let hasElem := kinds.any (· == .elem)
  let hasText := kinds.any (· == .text)
  -- the attributes: (formatted name, value)
  let attrs : M (List (String × Item)) := do
    let mut out : Array (String × Item) := #[]
    for a in e2mAttrNodes e n do
      let ra := e.nrec a
      let t := o.plan.attrs.lookup (e2mNameKey ra.name)
      match t with
      | some (some "skip") => pure ()
      | _ =>
        let v ← e2mContent o ra.value (t.bind id)
        out := out.push (← e2mAttrName o ra.name, Item.atom v)
    pure out.toList
  let elemKids := kids.filter (fun c => kidKind e c == .elem)
  let childKey : NodeRef → M String := fun c => e2mElemName o (some r.name.uri) (e.nrec c).name
  match l with
  | .empty =>
    if hasElem || hasText then pure none
    else pure (some (stringItem ""))
  | .emptyPlus =>
    if hasElem || hasText then pure none
    else
      let acc := (← attrs).foldl (fun (a : Acc) (k, v) => a.add (o.marker ++ k) v) {}
      pure (some acc.toItem)
  | .simple =>
    if hasElem then pure none
    else pure (some (.atom (← e2mContent o (e.nodeString n) ty)))
  | .simplePlus =>
    if hasElem then pure none
    else
      let ats := (← attrs).map (fun (k, v) => (o.marker ++ k, v))
      let ck := uniqueKey o.contentKey (ats.map (·.1))
      let acc := ats.foldl (fun (a : Acc) (k, v) => a.add k v) {}
      let acc := acc.add ck (.atom (← e2mContent o (e.nodeString n) ty))
      pure (some acc.toItem)
  | .list | .listPlus =>
    let cname := child.getD ""
    if hasText || elemKids.any (fun c => e2mNameKey (e.nrec c).name != cname) then pure none
    else
      let mut vals : Array Item := #[]
      for c in elemKids do
        match ← conv c with
        | some v => vals := vals.push v
        | none => pure ()
      let arr := Item.arr (vals.toList.map (fun v => [v]))
      if l == .list then pure (some arr)
      else
        let (cu, cl) := (e2mPlanName? cname).getD ("", cname)
        let pfx := match elemKids.head? with
          | some c => (e.nrec c).name.pfx
          | none => ""
        let key ← e2mElemName o (some r.name.uri) { uri := cu, loc := cl, pfx }
        let ats ← attrs
        let marker := if ats.any (fun (k, _) => o.marker ++ k == key) then "@" else o.marker
        let acc := ats.foldl (fun (a : Acc) (k, v) => a.add (marker ++ k) v) {}
        pure (some (acc.add key arr).toItem)
  | .record =>
    if hasText then pure none
    else
      let mut ents : Array (String × Item) := #[]
      for c in elemKids do
        match ← conv c with
        | some v => ents := ents.push (← childKey c, v)
        | none => pure ()
      let ats ← attrs
      let marker := if ats.any (fun (k, _) => ents.any (fun (ck, _) => o.marker ++ k == ck)) then "@" else o.marker
      let acc := ats.foldl (fun (a : Acc) (k, v) => a.add (marker ++ k) v) {}
      let acc := ents.foldl (fun (a : Acc) (k, v) => a.add k v) acc
      pure (some acc.toItem)
  | .sequence | .mixed =>
    if l == .sequence && hasText then pure none
    else
      let mut items : Array Item := #[]
      for (k, v) in (← attrs) do
        items := items.push (single1 (o.marker ++ k) v)
      for c in kids do
        let rc := e.nrec c
        match kidKind e c with
        | .elem =>
          match ← conv c with
          | some v => items := items.push (single1 (← childKey c) v)
          | none => pure ()
        | .wsText => if l == .mixed then items := items.push (untypedItem rc.value)
        | .text => items := items.push (untypedItem rc.value)
        | .comment => items := items.push (single1 "#comment" (stringItem rc.value))
        | .pi =>
          let t : Atomic := ⟨.b .ncname, .str rc.name.loc⟩
          items := items.push (single1 "#processing-instruction"
            (.map [(Atomic.ofStr "#target", [.atom t]), (Atomic.ofStr "#data", [stringItem rc.value])]))
      pure (some (Item.arr (items.toList.map (fun x => [x]))))
  | .xml => pure (some (stringItem (← e.serializeWith {} [.node n])))
  | .error | .deepSkip => pure none

/-- Convert an element to the value of its map entry (`none`: omitted). -/
def e2mElem (o : E2MOpts) (e : Env) : Nat → NodeRef → M (Option Item)
  | 0, _ => err "FOER0000" "the elements are nested too deeply"
  | f + 1, n => do
    let r := e.nrec n
    let conv := fun c => e2mElem o e f c
    let fb := o.plan.elems.lookup "*"
    -- outer none: the layout failed; inner none: skipped
    let run (p : ElemPlan) : M (Option (Option Item)) :=
      match p.layout with
      | .deepSkip => pure (some none)
      | .error => err "FOJS0008" ("the plan forbids the element " ++ e2mNameKey r.name)
      | l => do
        match ← e2mApply o e conv n l p.child p.ty with
        | some v => pure (some (some v))
        | none => pure none
    let fallback : M (Option Item) := do
      match fb with
      | none => err "FOJS0008" ("the element " ++ e2mNameKey r.name ++ " cannot be converted with its layout")
      | some q =>
        match ← run q with
        | some res => pure res
        | none => err "FOJS0008" ("the element " ++ e2mNameKey r.name ++ " cannot be converted with the fallback layout")
    match o.plan.elems.lookup (e2mNameKey r.name) with
    | some p =>
      match ← run p with
      | some res => pure res
      | none => fallback
    | none =>
      match fb with
      | some _ => fallback
      | none =>
        let (l, ch, ty) := e2mInfer e [n]
        match ← e2mApply o e conv n l ch ty with
        | some v => pure (some v)
        | none => err "FOJS0008" "no layout fits the element"

/-- The element a document node or element node argument stands for. -/
def e2mArgElement (e : Env) (n : NodeRef) : M NodeRef := do
  let r := e.nrec n
  match r.kind with
  | .element => pure n
  | .document =>
    let els := r.children.toList.filter (fun c => (e.nrec (n.at c)).kind == .element)
    let others := r.children.toList.any (fun c =>
      let k := (e.nrec (n.at c)).kind
      k == .text)
    match els with
    | [c] => if others then err "XPTY0004" "the document has text children" else pure (n.at c)
    | _ => err "XPTY0004" "the document node does not have a single element child"
  | _ => err "XPTY0004" "expected an element or a document node"

def elementToMapFn : LibFn := fun _ e a => do
  let o ← e2mOptions (argN a 1)
  match argN a 0 with
  | [] => pure []
  | [.node n0] =>
    let n ← e2mArgElement e n0
    match ← e2mElem o e 100000 n with
    | none => pure []
    | some v =>
      let key ← e2mElemName o none (e.nrec n).name
      pure [Item.map [(Atomic.ofStr key, [v])]]
  | _ => err "XPTY0004" "expected one element or document node"

/-! ## fn:element-to-map-plan -/

private def planEntry (l : Layout) (child ty : Option String) : Item :=
  .map [(Atomic.ofStr "layout", [stringItem l.name]),
        (Atomic.ofStr "child", child.toList.map stringItem),
        (Atomic.ofStr "type", ty.toList.map stringItem)]

/-- Every element of the trees rooted at the nodes, in document order. -/
def e2mAllElements (e : Env) (roots : List NodeRef) : M (List NodeRef) := do
  let mut out : Array NodeRef := #[]
  for n in roots do
    let r := e.nrec n
    if r.kind != .element && r.kind != .document then
      err "XPTY0004" "expected element or document nodes"
    for i in [n.idx:r.last + 1] do
      if (e.nrec (n.at i)).kind == .element then out := out.push (n.at i)
  pure out.toList

def elementToMapPlanFn : LibFn := fun _ e a => do
  let mut roots : Array NodeRef := #[]
  for it in argN a 0 do
    match it with
    | .node n => roots := roots.push n
    | _ => err "XPTY0004" "expected element or document nodes"
  let all ← e2mAllElements e roots.toList
  -- group by name, in order of first appearance
  let mut idx : Std.HashMap String Nat := {}
  let mut groups : Array (String × Array NodeRef) := #[]
  let mut aidx : Std.HashMap String Nat := {}
  let mut agroups : Array (String × Array String) := #[]
  for n in all do
    let k := e2mNameKey (e.nrec n).name
    match idx[k]? with
    | some i => groups := groups.modify i (fun (k0, vs) => (k0, vs.push n))
    | none =>
      idx := idx.insert k groups.size
      groups := groups.push (k, #[n])
    if !e2mIsNilled e n then
      for at_ in e2mAttrNodes e n do
        let ra := e.nrec at_
        let ak := e2mNameKey ra.name
        match aidx[ak]? with
        | some i => agroups := agroups.modify i (fun (k0, vs) => (k0, vs.push ra.value))
        | none =>
          aidx := aidx.insert ak agroups.size
          agroups := agroups.push (ak, #[ra.value])
  let mut ents : Array (Atomic × Seq) := #[]
  for (k, ns) in groups do
    let (l, ch, ty) := e2mInfer e ns.toList
    ents := ents.push (Atomic.ofStr k, [planEntry l ch ty])
  for (k, vs) in agroups do
    match inferSimpleType vs.toList with
    | some t => ents := ents.push (Atomic.ofStr ("@" ++ k), [.map [(Atomic.ofStr "type", [stringItem t])]])
    | none => pure ()
  pure [Item.map ents.toList]

/-! ## fn:map-to-element -/

structure M2ECtx where
  o : E2MOpts
  e : Env

/-- What a key of a map stands for (14.6.12). -/
inductive Role where
  | content | comment | pi | attr (name : String) | elem (key : String)

def normV (v : Seq) : Seq := if v.isEmpty then [stringItem ""] else v

private def keyIsContent (inArray : Bool) (ck k : String) : Bool :=
  if inArray then k == ck
  else k.endsWith ck && (k.toList.take (k.length - ck.length)).all (· == '#')

/-- The role of each entry of a map. Inside an array the content key must
    be equal to the `content-key` option; in a map on its own it is the
    longest key made of `#` characters and the content key. -/
def m2eRoles (c : M2ECtx) (kvs : List (Atomic × Seq)) (inArray : Bool) : M (List (Role × Seq)) := do
  let mut keys : Array String := #[]
  for (k, _) in kvs do
    if !k.isStringLike then err "FOJS0009" "the keys of the map must be strings"
    keys := keys.push k.str
  let ck := c.o.contentKey
  let chosen : Option String := (keys.toList.filter (keyIsContent inArray ck)).foldl
    (fun acc k => match acc with
      | none => some k
      | some b => if k.length > b.length then some k else some b) none
  let mk := if !c.o.marker.startsWith "@" && keys.any (fun k => some k != chosen && k.startsWith "@")
    then "@" else c.o.marker
  let mut out : Array (Role × Seq) := #[]
  for (k, v) in kvs do
    let ks := k.str
    let r : Role :=
      if some ks == chosen then .content
      else if inArray && ks == "#comment" then .comment
      else if inArray && ks == "#processing-instruction" then .pi
      else if ks.startsWith mk then .attr (ks.toList.drop mk.length |> String.ofList)
      else .elem ks
    out := out.push (r, v)
  pure out.toList

private def freshPrefix (scope : List (String × String)) : String :=
  go (scope.length + 2) 1
where
  go : Nat → Nat → String
    | 0, k => "ns" ++ toString k
    | f + 1, k => if (scope.lookup ("ns" ++ toString k)).isSome then go f (k + 1) else "ns" ++ toString k

/-- Decode a key into the expanded name of an element or attribute
    (14.6.12). `parentUri` is the namespace of the parent element (`""` for
    the top-level element); under the default `name-format` a local name
    alone takes it. -/
def m2eName (c : M2ECtx) (isAttr : Bool) (parentUri : String) (key : String) : M QN := do
  let o := c.o
  let bad {α : Type} (why : String) : M α := err "FOJS0009" ("the key " ++ key ++ " is not a valid name: " ++ why)
  let (uri?, pfx, raw) : Option String × String × String ←
    if key.startsWith "Q{" then
      match (key.drop 2).toString.splitOn "}" with
      | uri :: rest@(_ :: _) => pure (some uri, "", String.intercalate "}" rest)
      | _ => pure (none, "", key)
    else
      match key.splitOn ":" with
      | p :: rest@(_ :: _) =>
        if p == "xml" then pure (some nsXML, "xml", String.intercalate ":" rest)
        else if o.fmt == "lexical" then
          match c.e.nsResolve p with
          | some u => if p == "" then bad "empty prefix" else pure (some u, p, String.intercalate ":" rest)
          | none => bad ("the prefix " ++ p ++ " is not bound")
        else pure (none, "", key)
      | _ => pure (none, "", key)
  let uri := match uri? with
    | some u => u
    | none => if !isAttr && o.fmt == "default" then parentUri else ""
  let loc ← if o.escape then encodeEsc raw else pure raw
  if !isValidNCName loc then bad "not an NCName"
  if uri == nsXMLNS then bad "the namespace is reserved"
  if isAttr && uri == "" && loc == "xmlns" then bad "xmlns is reserved"
  pure { uri, loc, pfx }

def m2eCands (c : M2ECtx) (q : QN) : List ElemPlan :=
  let ok := fun (p : ElemPlan) => p.layout != .error && p.layout != .deepSkip
  let own := (c.o.plan.elems.lookup (e2mNameKey q)).filter ok
  let fb := (c.o.plan.elems.lookup "*").filter ok
  let l := own.toList ++ fb.toList
  if l.isEmpty then
    [Layout.simple, .simplePlus, .record, .mixed].map (fun l => { layout := l })
  else l

private def planChild (p : ElemPlan) : M QN :=
  match p.child.bind e2mPlanName? with
  | some (u, l) => pure { uri := u, loc := l }
  | none => err "XPTY0004" "a list layout needs a child name"

private def isSingleEntryMap (m : Seq) : Bool :=
  match m with
  | [.map [_]] => true
  | _ => false

private def isSimpleValue (v : Seq) : Bool :=
  match normV v with
  | [.atom _] => true
  | _ => false

/-- Does the value fit the layout? (14.6.12.2) -/
def m2eMatch (c : M2ECtx) : Nat → QN → ElemPlan → Seq → M Bool
  | 0, _, _, _ => err "FOER0000" "the map is nested too deeply"
  | f + 1, q, p, v0 => do
    let v := normV v0
    if isNullSeq v then return true
    match p.layout with
    | .empty => pure (match v with | [.atom a] => a.isStringLike && a.str == "" | _ => false)
    | .simple => pure (match v with | [.atom _] => true | _ => false)
    | .xml => pure (match v with | [.atom a] => a.isStringLike | _ => false)
    | .record | .emptyPlus | .simplePlus | .listPlus =>
      match v with
      | [.map kvs] =>
        let rs ← m2eRoles c kvs false
        let elems := rs.filter (fun (r, _) => match r with | .elem _ => true | _ => false)
        let contents := rs.filterMap (fun (r, cv) => match r with | .content => some cv | _ => none)
        let allNull := contents.all (fun cv => isNullSeq (normV cv))
        match p.layout with
        | .record => pure allNull
        | .emptyPlus => pure (elems.isEmpty && allNull)
        | .simplePlus =>
          pure (!contents.isEmpty && elems.isEmpty &&
            contents.all (fun cv => isNullSeq (normV cv) || isSimpleValue cv))
        | _ =>
          if !allNull then pure false
          else match elems with
            | [] => pure true
            | [(.elem key, ev)] =>
              let cq ← planChild p
              let nq ← m2eName c false q.uri key
              pure (nq.uri == cq.uri && nq.loc == cq.loc &&
                (match ev with | [.arr _] => true | _ => false))
            | _ => pure false
      | _ => pure false
    | .list =>
      match v with
      | [.arr ms] =>
        let cq ← planChild p
        let cands := m2eCands c cq
        for m in ms do
          let mut ok := false
          for cp in cands do
            if !ok then
              if ← m2eMatch c f cq cp m then ok := true
          if !ok then return false
        return true
      | _ => pure false
    | .mixed =>
      match v with
      | [.arr ms] => pure (ms.all (fun m => m.isEmpty || isSingleEntryMap m || (match m with | [.atom _] => true | _ => false)))
      | _ => pure false
    | .sequence =>
      match v with
      | [.arr ms] => pure (ms.all isSingleEntryMap)
      | _ => pure false
    | .error | .deepSkip => pure false

/-- What a value contributes to an element. -/
inductive Contrib where
  | attr (q : QN) (val : String)
  | text (s : String)
  | nilMark
  | comment (s : String)
  | pi (t d : String)
  | child (q : QN) (v : Seq)

private def atomStr (what : String) (v : Seq) : M String :=
  match normV v with
  | [.atom a] =>
    if isNullAtom a then err "FOJS0009" (what ++ " cannot be the null marker") else pure a.str
  | _ => err "FOJS0009" (what ++ " must be a single atomic item")

private def contentContrib (v : Seq) : M (List Contrib) := do
  if isNullSeq (normV v) then pure [.nilMark]
  else
    let s ← atomStr "the content" v
    pure (if s == "" then [] else [.text s])

private def piContrib (rv : Seq) : M Contrib := do
  match rv with
  | [.map kv] =>
    let t ← match mapGet kv (Atomic.ofStr "#target") with
      | some tv => atomStr "a processing instruction target" tv
      | none => err "FOJS0009" "a processing instruction needs #target"
    let d ← match mapGet kv (Atomic.ofStr "#data") with
      | some dv => atomStr "processing instruction data" dv
      | none => pure ""
    pure (.pi t d)
  | _ => err "FOJS0009" "a processing instruction is a map with #target and #data"

def m2eMatchAny (c : M2ECtx) (f : Nat) (cq : QN) (m : Seq) : M Bool := do
  for cp in m2eCands c cq do
    if ← m2eMatch c f cq cp m then return true
  return false

/-- The members of an array, as contributions (mixed and sequence layouts). -/
def m2eArrayContribs (c : M2ECtx) (q : QN) (ms : List Seq) : M (List Contrib) := do
  let mut out : Array Contrib := #[]
  let mut seenNonAttr := false
  let mut prevStr := false
  for m0 in ms do
    match m0 with
    | [] | [.atom _] =>
      let s := match m0 with | [.atom a] => a.str | _ => ""
      if prevStr then err "FOJS0009" "two strings are adjacent"
      prevStr := true
      seenNonAttr := true
      if s != "" then out := out.push (.text s)
    | [.map [(k, mv)]] =>
      prevStr := false
      for (r, rv) in (← m2eRoles c [(k, mv)] true) do
        match r with
        | .attr nm =>
          if seenNonAttr then err "FOJS0009" "an attribute follows other content"
          out := out.push (.attr (← m2eName c true q.uri nm) (← atomStr "an attribute value" rv))
        | .content =>
          if seenNonAttr then err "FOJS0009" "the nilled marker follows other content"
          if !isNullSeq (normV rv) then err "FOJS0009" "in an array the content key may only have the null marker"
          seenNonAttr := true
          out := out.push .nilMark
        | .comment =>
          seenNonAttr := true
          out := out.push (.comment (← atomStr "a comment" rv))
        | .pi =>
          seenNonAttr := true
          out := out.push (← piContrib rv)
        | .elem key =>
          seenNonAttr := true
          out := out.push (.child (← m2eName c false q.uri key) rv)
    | _ => err "FOJS0009" "an array member must be a string or a single-entry map"
  pure out.toList

def m2eContribs (c : M2ECtx) (f : Nat) (q : QN) (p : ElemPlan) (v : Seq) : M (List Contrib) := do
  if isNullSeq v then return [.nilMark]
  match p.layout with
  | .empty => pure []
  | .simple => contentContrib v
  | .record | .emptyPlus | .simplePlus | .listPlus =>
    match v with
    | [.map kvs] =>
      let mut out : Array Contrib := #[]
      for (r, rv) in (← m2eRoles c kvs false) do
        match r with
        | .content => out := out ++ (← contentContrib rv).toArray
        | .attr nm =>
          out := out.push (.attr (← m2eName c true q.uri nm) (← atomStr "an attribute value" rv))
        | .elem key =>
          let cq ← m2eName c false q.uri key
          match rv with
          | [.arr ms] =>
            if p.layout == .listPlus then
              out := out ++ (ms.map (fun m => Contrib.child cq m)).toArray
            else if p.layout == .record && !ms.isEmpty then
              let mut all := true
              for m in ms do
                if all then
                  if !(← m2eMatchAny c f cq m) then all := false
              if all then out := out ++ (ms.map (fun m => Contrib.child cq m)).toArray
              else out := out.push (.child cq rv)
            else out := out.push (.child cq rv)
          | _ => out := out.push (.child cq rv)
        | _ => pure ()
      pure out.toList
    | _ => err "FOJS0009" "the value does not fit the layout"
  | .list =>
    match v with
    | [.arr ms] =>
      let cq ← planChild p
      pure (ms.map (fun m => Contrib.child cq m))
    | _ => err "FOJS0009" "the value does not fit the layout"
  | .mixed | .sequence =>
    match v with
    | [.arr ms] => m2eArrayContribs c q ms
    | _ => err "FOJS0009" "the value does not fit the layout"
  | .xml | .error | .deepSkip => pure []

/-- The tag of an element and the namespace declarations it needs. -/
def m2eAllocElem (scope : List (String × String)) (q : QN) : String × List (String × String) :=
  if q.uri == "" then
    (q.loc, if (scope.lookup "").getD "" != "" then [("", "")] else [])
  else if q.uri == nsXML then ("xml:" ++ q.loc, [])
  else if q.pfx != "" then
    (q.pfx ++ ":" ++ q.loc, if scope.lookup q.pfx == some q.uri then [] else [(q.pfx, q.uri)])
  else if scope.lookup "" == some q.uri then (q.loc, [])
  else (q.loc, [("", q.uri)])

/-- The name of an attribute and the namespace declarations it needs;
    `declared` are the prefixes the element has already declared. -/
def m2eAllocAttr (scope declared : List (String × String)) (q : QN) : String × List (String × String) :=
  if q.uri == "" then (q.loc, [])
  else if q.uri == nsXML then ("xml:" ++ q.loc, [])
  else if q.pfx != "" && scope.lookup q.pfx == some q.uri then (q.pfx ++ ":" ++ q.loc, [])
  else if q.pfx != "" && (declared.lookup q.pfx).isNone then (q.pfx ++ ":" ++ q.loc, [(q.pfx, q.uri)])
  else
    match scope.find? (fun (p, u) => p != "" && u == q.uri && scope.lookup p == some u) with
    | some (p, _) => (p ++ ":" ++ q.loc, [])
    | none =>
      let p := freshPrefix scope
      (p ++ ":" ++ q.loc, [(p, q.uri)])

/-- The `xml` layout: the value is a serialized element. -/
def m2eXml (c : M2ECtx) (scope : List (String × String)) (v : Seq) : M Node := do
  match v with
  | [.atom a] =>
    if !a.isStringLike then err "FOJS0009" "the xml layout needs a string"
    match parseDocument c.e { baseUri := "" } (Atomic.ofStr a.str) with
    | .error ex => err "FOJS0009" ("the value is not well-formed XML: " ++ ex.msg)
    | .ok d =>
      if !d.prolog.isEmpty || !d.epilog.isEmpty then
        err "FOJS0009" "the value holds more than a single element"
      match d.root with
      | .element tag ats kids =>
        let hasDefault := ats.any (fun x => x.name == "xmlns")
        let ats' := if !hasDefault && ((scope.lookup "").getD "") != ""
          then { name := "xmlns", value := "" : Attribute } :: ats else ats
        pure (.element tag ats' kids)
      | _ => err "FOJS0009" "the value is not an element"
  | _ => err "FOJS0009" "the xml layout needs a string"

/-- Rebuild an element (14.6.12.2). `scope` holds the namespace bindings
    the output has declared (newest first). -/
def m2eBuild (c : M2ECtx) : Nat → List (String × String) → QN → Seq → M Node
  | 0, _, _, _ => err "FOER0000" "the map is nested too deeply"
  | f + 1, scope, q, v0 => do
    let v := normV v0
    let mut sel : Option ElemPlan := none
    for p in m2eCands c q do
      if sel.isNone then
        if ← m2eMatch c f q p v then sel := some p
    match sel with
    | none => err "FOJS0009" ("the value of " ++ e2mNameKey q ++ " does not fit any layout")
    | some p =>
      if p.layout == .xml && !isNullSeq v then m2eXml c scope v
      else
      let cs ← m2eContribs c f q p v
      -- well-formedness of the result
      let nilKey := e2mNameKey { uri := nsXSI, loc := "nil" }
      let mut seen : List String := []
      let mut nils := 0
      for ct in cs do
        match ct with
        | .attr aq val =>
          let k := e2mNameKey aq
          if seen.contains k then err "FOJS0009" ("the attribute " ++ k ++ " occurs twice")
          if !isXml10Str val then err "FOJS0009" "an attribute value holds a character that is not an XML character"
          seen := k :: seen
        | .nilMark => nils := nils + 1
        | .text s => if !isXml10Str s then err "FOJS0009" "text holds a character that is not an XML character"
        | .comment s =>
          if !isXml10Str s || (s.splitOn "--").length > 1 || s.endsWith "-" then
            err "FOJS0009" "invalid comment"
        | .pi t d =>
          if !isValidNCName t || t.toLower == "xml" || (d.splitOn "?>").length > 1 || !isXml10Str d then
            err "FOJS0009" "invalid processing instruction"
        | .child _ _ => pure ()
      if nils > 0 && seen.contains nilKey then err "FOJS0009" "xsi:nil is supplied twice"
      let (tag, d0) := m2eAllocElem scope q
      let mut sc := d0 ++ scope
      let mut declared := d0
      let mut ats : Array Attribute := #[]
      for ct in cs do
        match ct with
        | .attr aq val =>
          let (nm, ds) := m2eAllocAttr sc declared aq
          sc := ds ++ sc
          declared := ds ++ declared
          ats := ats.push { name := nm, value := val }
        | _ => pure ()
      if nils > 0 then
        let (nm, ds) := m2eAllocAttr sc declared { uri := nsXSI, loc := "nil", pfx := "xsi" }
        sc := ds ++ sc
        declared := ds ++ declared
        ats := ats.push { name := nm, value := "true" }
      let mut kids : Array Node := #[]
      for ct in cs do
        match ct with
        | .text s => kids := kids.push (.text s)
        | .comment s => kids := kids.push (.comment s)
        | .pi t d => kids := kids.push (.pi t d)
        | .child cq cv => kids := kids.push (← m2eBuild c f sc cq cv)
        | _ => pure ()
      let decls := declared.reverse.map (fun (p, u) =>
        ({ name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u } : Attribute))
      pure (.element tag (decls ++ ats.toList) kids.toList)

def mapToElementFn : LibFn := fun _ e a => do
  let o ← e2mOptions (argN a 1)
  let c : M2ECtx := { o, e }
  match argN a 0 with
  | [] => pure []
  | [.map kvs] =>
    match kvs with
    | [(k, v)] =>
      if !k.isStringLike then err "FOJS0009" "the key of the map must be a string"
      let q ← m2eName c false "" k.str
      let scope0 := [("xml", nsXML)]
      let node ← m2eBuild c 100000 scope0 q v
      let (_, arr) := (buildNode 100000 none scope0 node).run #[]
      let doc : Doc := { nodes := arr }
      let ser := e2mSerNode {} 100000 [] { doc := 0, idx := 0, rt := some doc }
      pure [.node { doc := runtimeDocId "map-to-element" ser, idx := 0, rt := some doc }]
    | _ => err "FOJS0009" "the map must have a single entry"
  | _ => err "XPTY0004" "expected a map"

def elemMapTable : List (String × LibFn) := [
  ent "element-to-map" elementToMapFn,
  ent "element-to-map-plan" elementToMapPlanFn,
  ent "map-to-element" mapToElementFn
]

end L4Factoidal.XPath4
