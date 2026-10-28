/-
L4Factoidal.XPath4.DeepEqual — `fn:deep-equal` with the options of
F&O 4.0 §2.2.4.

The options: `base-uri`, `collation`, `comments`, `debug` (accepted, no
output), `id-property`, `idrefs-property`, `nilled-property` and
`type-variety` (accepted: no node here has a schema type, so they never
change the result), `ignore-empty-entries`, `in-scope-namespaces`,
`items-equal`, `map-order`, `namespace-prefixes`, `normalization-form`,
`ordered`, `processing-instructions`, `timezones`, `type-annotations`,
`typed-values`, `unordered-elements`, `whitespace`. The rules are those
of §2.2.4 in their order: the `items-equal` callback first, then atomic
items (`equal-strings` for strings), maps, arrays, XNodes (with the
significant children: comments and processing instructions removed
unless the options keep them, adjacent text merged, whitespace-only text
removed under `strip` and `normalize` outside `xml:space="preserve"`),
JNodes (by their values), and function items.

Collations: the Unicode codepoint collation only (another raises
`FOCH0002`).
-/
import L4Factoidal.XPath4.Serialize

namespace L4Factoidal.XPath4

structure DEOpts where
  baseUri : Bool := false
  comments : Bool := false
  pis : Bool := false
  inScopeNs : Bool := false
  itemsEqual : Option Item := none
  mapOrder : Bool := false
  nsPrefixes : Bool := false
  normForm : String := ""
  ordered : Bool := true
  timezones : Bool := false
  typeAnnotations : Bool := false
  typedValues : Bool := true
  unordered : List QN := []
  whitespace : String := "preserve"
  ignoreEmpty : Bool := false
deriving Inhabited

def deBoolKeys : List String :=
  ["base-uri", "comments", "debug", "id-property", "idrefs-property", "ignore-empty-entries",
   "in-scope-namespaces", "map-order", "namespace-prefixes", "nilled-property", "ordered",
   "processing-instructions", "timezones", "type-annotations", "type-variety", "typed-values"]

def collationCheck (c : String) : M Unit :=
  if c == "http://www.w3.org/2005/xpath-functions/collation/codepoint" then pure ()
  else err "FOCH0002" ("unsupported collation " ++ c)

def parseDEOpts (e : Env) (opts : Seq) : M DEOpts := do
  match opts with
  | [] => pure {}
  | [.atom a] =>
    if a.isStringLike then collationCheck a.str; pure {}
    else err "XPTY0004" "the options of deep-equal must be a map or a collation name"
  | [.map kvs] =>
    let mut o : DEOpts := {}
    for (k, v) in kvs do
      let key := k.str
      let known := deBoolKeys.contains key || ["collation", "normalization-form", "whitespace",
        "unordered-elements", "items-equal"].contains key
      match k.v with
      | .qn q => if q.uri == "" then err "XPTY0004" ("option name " ++ q.loc ++ " must be a string") else continue
      | _ => if !known then err "XPTY0004" ("unknown deep-equal option " ++ key)
      if v.isEmpty then continue
      if deBoolKeys.contains key then
        let b ← match ← e.coerceTo "xs:boolean" v key with
          | [.atom ⟨_, .bool b⟩] => pure b
          | _ => err "XPTY0004" (key ++ " must be xs:boolean")
        o := match key with
          | "base-uri" => { o with baseUri := b }
          | "comments" => { o with comments := b }
          | "ignore-empty-entries" => { o with ignoreEmpty := b }
          | "in-scope-namespaces" => { o with inScopeNs := b }
          | "map-order" => { o with mapOrder := b }
          | "namespace-prefixes" => { o with nsPrefixes := b }
          | "ordered" => { o with ordered := b }
          | "processing-instructions" => { o with pis := b }
          | "timezones" => { o with timezones := b }
          | "type-annotations" => { o with typeAnnotations := b }
          | "typed-values" => { o with typedValues := b }
          | _ => o
      else match key with
        | "collation" =>
          match ← e.coerceTo "xs:string" v key with
          | [.atom a] => collationCheck a.str
          | _ => err "XPTY0004" "collation must be xs:string"
        | "normalization-form" =>
          match ← e.coerceTo "xs:string" v key with
          | [.atom a] =>
            let f := (trimWs a.str).toUpper
            if f != "" && !["NFC", "NFD", "NFKC", "NFKD"].contains f then
              err "XPTY0004" ("unsupported normalization form " ++ a.str)
            o := { o with normForm := f }
          | _ => err "XPTY0004" "normalization-form must be xs:string"
        | "whitespace" =>
          match ← e.coerceTo "xs:string" v key with
          | [.atom a] =>
            if !["preserve", "strip", "normalize"].contains a.str then
              err "FOJS0005" ("whitespace must be preserve, strip or normalize, not " ++ a.str)
            o := { o with whitespace := a.str }
          | _ => err "XPTY0004" "whitespace must be xs:string"
        | "unordered-elements" =>
          let qs ← e.coerceTo "xs:QName*" v key
          o := { o with unordered := qs.filterMap (fun i => match i with
            | .atom ⟨_, .qn q⟩ => some q
            | _ => none) }
        | "items-equal" =>
          match ← e.coerceTo "fn(item(), item()) as xs:boolean?" v key with
          | [f] => o := { o with itemsEqual := some f }
          | _ => err "XPTY0004" "items-equal must be a function"
        | _ => pure ()
    pure o
  | _ => err "XPTY0004" "the options of deep-equal must be a map or a collation name"

def DEOpts.equalStrings (o : DEOpts) (a b : String) : Bool :=
  let n1 (s : String) := if o.whitespace == "normalize" then normSpace s else s
  let n2 (s : String) := if o.normForm == "" then s else (Unicode.normalize o.normForm s).getD s
  n2 (n1 a) == n2 (n1 b)

def isDateTimeType (a : Atomic) : Bool :=
  match a.v with
  | .x (.dt _ _) => true
  | _ => false

def atomTzOf (a : Atomic) : Option Int :=
  match a.v with
  | .x (.dt _ v) => v.tz
  | _ => none

def DEOpts.atomEq (o : DEOpts) (a b : Atomic) : Bool :=
  let typeOk := !o.typeAnnotations || a.ty == b.ty
  let valOk :=
    if (a.isStringLike || a.is .anyURI) && (b.isStringLike || b.is .anyURI) then o.equalStrings a.str b.str
    else deepAtomEq a b
  let pfxOk := !o.nsPrefixes || (match a.v, b.v with
    | .qn p, .qn q => p.pfx == q.pfx
    | _, _ => true)
  let tzOk := !o.timezones || !(isDateTimeType a || isDateTimeType b) || atomTzOf a == atomTzOf b
  typeOk && valOk && pfxOk && tzOk

/-- A significant child: a node, or the merged text of adjacent text
    nodes. -/
inductive SChild where
  | node (n : NodeRef)
  /-- Merged text; the node when it is a single text node. -/
  | text (s : String) (n : Option NodeRef)

def Env.preserveSpace (e : Env) (n : NodeRef) : Bool :=
  let rec go : Nat → NodeRef → Bool
    | 0, _ => false
    | f + 1, m =>
      let r := e.nrec m
      match r.attrs.toList.find? (fun a => let ra := e.nrec (m.at a); ra.name.uri == nsXML && ra.name.loc == "space") with
      | some a => (e.nrec (m.at a)).value == "preserve"
      | none => match r.parent with
        | some p => go f (m.at p)
        | none => false
  go 10000 n

def Env.significantChildren (e : Env) (o : DEOpts) (n : NodeRef) : List SChild := Id.run do
  let r := e.nrec n
  let mut out : Array SChild := #[]
  let mut acc : Option (String × Option NodeRef) := none
  for c in r.children.toList do
    let m := n.at c
    let k := (e.nrec m).kind
    if k == .comment && !o.comments then continue
    if k == .pi && !o.pis then continue
    if k == .text then
      acc := match acc with
        | none => some ((e.nrec m).value, some m)
        | some (t, _) => some (t ++ (e.nrec m).value, none)
    else
      if let some (t, tn) := acc then out := out.push (.text t tn)
      acc := none
      out := out.push (.node m)
  if let some (t, tn) := acc then out := out.push (.text t tn)
  let strip := o.whitespace != "preserve" && !e.preserveSpace n
  return (out.toList.filter (fun c => match c with
    | .text t _ => !(strip && t.toList.all isWs) && t != ""
    | _ => true))

/-- One permutation test: every element of `xs` matched by a distinct
    element of `ys` (greedy; exact for an equivalence relation). -/
def matchAll {α} (eq : α → α → M Bool) : List α → List α → M Bool
  | [], ys => pure ys.isEmpty
  | x :: xs, ys => do
    let mut rest : List α := []
    let mut found := false
    for y in ys do
      if !found then
        if ← eq x y then found := true; continue
      rest := rest ++ [y]
    if !found then return false
    matchAll eq xs rest

mutual
def Env.deItem (e : Env) (h : Hooks) (o : DEOpts) : Nat → Item → Item → M Bool
  | 0, _, _ => pure false
  | f + 1, x, y => do
    if let some cb := o.itemsEqual then
      match ← h.callN cb [[x], [y]] with
      | [.atom ⟨_, .bool b⟩] => return b
      | [] => pure ()
      | _ => err "XPTY0004" "items-equal must return xs:boolean?"
    match x, y with
    | .atom a, .atom b => pure (o.atomEq a b)
    | .map ka, .map kb =>
      let sig (kv : Atomic × Seq) := !(o.ignoreEmpty && kv.2.isEmpty)
      let ka := ka.filter sig
      let kb := kb.filter sig
      if ka.length != kb.length then return false
      if o.mapOrder && !(ka.zip kb).all (fun (p, q) => atomicEqual p.1 q.1) then return false
      for (k, v) in ka do
        match kb.find? (fun (k2, _) => atomicEqual k k2) with
        | some (_, v2) => if !(← e.deSeq h o f v v2 true) then return false
        | none => return false
      pure true
    | .arr ma, .arr mb =>
      if ma.length != mb.length then return false
      for (p, q) in ma.zip mb do
        if !(← e.deSeq h o f p q true) then return false
      pure true
    | .node a, .node b => e.deNode h o f a b
    | .jnode _ _ v1 _, .jnode _ _ v2 _ => e.deSeq h o f v1 v2 true
    | .fn _, .fn _ => pure (e.deepEq [x] [y])
    | _, _ => pure false
def Env.deNode (e : Env) (h : Hooks) (o : DEOpts) : Nat → NodeRef → NodeRef → M Bool
  | 0, _, _ => pure false
  | f + 1, a, b => do
    let ra := e.nrec a
    let rb := e.nrec b
    if ra.kind != rb.kind then return false
    if o.baseUri then
      match xmlParseTable.lookup "base-uri" with
      | some bf =>
        let ba ← bf h e [[.node a]]
        let bb ← bf h e [[.node b]]
        if !(e.deepEq ba bb) then return false
      | none => pure ()
    match ra.kind with
    | .document => e.deChildren h o f a b false
    | .element =>
      if ra.name != rb.name then return false
      if o.nsPrefixes && ra.name.pfx != rb.name.pfx then return false
      if o.inScopeNs then
        let sa := (effectiveScope ra.inscope).filter (·.1 != "xml")
        let sb := (effectiveScope rb.inscope).filter (·.1 != "xml")
        if !(sa.length == sb.length && sa.all (fun p => sb.contains p)) then return false
      if ra.attrs.size != rb.attrs.size then return false
      for x in ra.attrs.toList do
        let ax := a.at x
        match rb.attrs.toList.find? (fun y => (e.nrec (b.at y)).name == (e.nrec ax).name) with
        | some y => if !(← e.deItem h o f (.node ax) (.node (b.at y))) then return false
        | none => return false
      e.deChildren h o f a b (qnIn ra.name o.unordered)
    | .attribute =>
      pure (ra.name == rb.name && (!o.nsPrefixes || ra.name.pfx == rb.name.pfx) &&
        o.equalStrings ra.value rb.value)
    | .pi => pure (ra.name == rb.name && o.equalStrings ra.value rb.value)
    | .namespace => pure (ra.name.loc == rb.name.loc && ra.value == rb.value)
    | .comment | .text => pure (o.equalStrings ra.value rb.value)
def Env.deChildren (e : Env) (h : Hooks) (o : DEOpts) : Nat → NodeRef → NodeRef → Bool → M Bool
  | 0, _, _, _ => pure false
  | f + 1, a, b, unord => do
    let ca := e.significantChildren o a
    let cb := e.significantChildren o b
    if ca.length != cb.length then return false
    let eq (x y : SChild) : M Bool := match x, y with
      | .text _ (some m), .text _ (some n) => e.deItem h o f (.node m) (.node n)
      | .text s _, .text t _ => pure (o.equalStrings s t)
      | .node m, .node n => e.deItem h o f (.node m) (.node n)
      | _, _ => pure false
    if unord then matchAll eq ca cb
    else
      for (x, y) in ca.zip cb do
        if !(← eq x y) then return false
      pure true
def Env.deSeq (e : Env) (h : Hooks) (o : DEOpts) : Nat → Seq → Seq → Bool → M Bool
  | 0, _, _, _ => pure false
  | f + 1, xs, ys, ordered => do
    if xs.length != ys.length then return false
    if ordered then
      for (x, y) in xs.zip ys do
        if !(← e.deItem h o f x y) then return false
      pure true
    else
      for x in xs do
        let mut any := false
        for y in ys do
          if !any then any ← e.deItem h o f x y
        if !any then return false
      for y in ys do
        let mut any := false
        for x in xs do
          if !any then any ← e.deItem h o f x y
        if !any then return false
      pure true
end

def deepEqualFn : LibFn := fun h e a => do
  let o ← parseDEOpts e (argN a 2)
  pure (sBool (← e.deSeq h o 100000 (argN a 0) (argN a 1) o.ordered))

def deepEqualTable : List (String × LibFn) := [("deep-equal", deepEqualFn)]

end L4Factoidal.XPath4
