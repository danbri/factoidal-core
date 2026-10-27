/-
L4Factoidal.XPath4.Core — the dynamic context and the value-level
operations every part of the evaluator uses: atomization (XPath 4.0
§2.5.3), effective boolean value (§2.5.4), sequence-type matching
(§3.2), the coercion rules (§3.4.3), the axes (§4.6.2) and
`fn:deep-equal` (F&O 4.0 §13.2.1, default options).
-/
import L4Factoidal.XPath4.Parser
import L4Factoidal.XPath4.Doc
import L4Factoidal.XPath4.Catalog

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-! ## The dynamic context -/

structure Env where
  docs : Array Doc := #[]
  vars : List (QN × Seq) := []
  /-- The context value (a single item except under `->`). -/
  ctx : Option Seq := none
  pos : Nat := 0
  size : Nat := 0
  ns : List (String × String) := []
  /-- Implicit timezone, in minutes. -/
  tz : Int := 0
  /-- The value `fn:current-dateTime()` returns (lexical). -/
  now : String := "2026-10-27T12:00:00Z"
  /-- Named documents for `fn:doc` and friends: (uri, doc index). -/
  docUris : List (String × Nat) := []
  defaultCollation : String := "http://www.w3.org/2005/xpath-functions/collation/codepoint"
  baseUri : String := ""
deriving Inhabited

def Env.doc (e : Env) (n : NodeRef) : Doc := e.docs.getD n.doc default
def Env.nrec (e : Env) (n : NodeRef) : NRec := (e.doc n).get n.idx

def Env.nsResolve (e : Env) (p : String) : Option String :=
  match e.ns.lookup p with
  | some u => some u
  | none => if p == "" then none else defaultNs.lookup p

/-! ## Item helpers -/

def Item.isNode : Item → Bool | .node _ => true | _ => false
def Item.isFn : Item → Bool | .fn _ | .map _ | .arr _ => true | _ => false

def nodeLt (a b : NodeRef) : Bool := a.doc < b.doc || (a.doc == b.doc && a.idx < b.idx)

def sortNodes (ns : List NodeRef) : List NodeRef :=
  let s := ns.mergeSort (fun a b => !(nodeLt b a))
  let rec dedup : List NodeRef → List NodeRef
    | a :: b :: r => if a == b then dedup (b :: r) else a :: dedup (b :: r)
    | l => l
  dedup s

def nodesOf (s : Seq) : Option (List NodeRef) :=
  s.foldr (fun i acc => match i, acc with
    | .node n, some l => some (n :: l)
    | _, _ => none) (some [])

def Env.nodeString (e : Env) (n : NodeRef) : String := (e.doc n).stringValue n.idx

def Env.typedValue (e : Env) (n : NodeRef) : Atomic :=
  let r := e.nrec n
  match r.kind with
  | .comment | .pi | .namespace => Atomic.ofStr (e.nodeString n)
  | _ => Atomic.untypedOf (e.nodeString n)

/-- Atomization (§2.5.3). -/
def Env.atomizeFuel (e : Env) : Nat → Seq → M (List Atomic)
  | 0, _ => err "FOER0000" "atomization too deep"
  | f + 1, s => do
    let mut out : Array Atomic := #[]
    for i in s do
      match i with
      | .atom a => out := out.push a
      | .node n => out := out.push (e.typedValue n)
      | .arr ms =>
          for m in ms do
            for a in ← e.atomizeFuel f m do out := out.push a
      | .map _ => err "FOTY0013" "cannot atomize a map"
      | .fn _ => err "FOTY0013" "cannot atomize a function item"
    pure out.toList

def Env.atomize (e : Env) (s : Seq) : M (List Atomic) := e.atomizeFuel 10000 s

def Env.atomizeOpt (e : Env) (s : Seq) : M (Option Atomic) := do
  match ← e.atomize s with
  | [] => pure none
  | [a] => pure (some a)
  | _ => err "XPTY0004" "a sequence of more than one item is not allowed here"

/-- Effective boolean value (§2.5.4). -/
def ebv (s : Seq) : M Bool :=
  match s with
  | [] => pure false
  | .node _ :: _ => pure true
  | [.atom a] =>
    match a.v with
    | .bool b => pure b
    | .str s => pure (s != "")
    | .int i => pure (i != 0)
    | .dec d => pure (d.mantissa != 0)
    | .dbl f => pure (!(f == 0) && !f.isNaN)
    | _ => err "FORG0006" ("no effective boolean value for xs:" ++ a.ty.name)
  | _ => err "FORG0006" "no effective boolean value for this sequence"

def seqOfAtoms (as : List Atomic) : Seq := as.map Item.atom
def single (a : Atomic) : Seq := [.atom a]
def sBool (b : Bool) : Seq := single (Atomic.ofBool b)
def sStr (s : String) : Seq := single (Atomic.ofStr s)
def sInt (i : Int) : Seq := single (Atomic.ofInt i)

/-! ## Node tests and axes -/

def nameTestMatches (t : NameTest) (q : QN) : Bool :=
  match t with
  | .any => true
  | .ns u => q.uri == u
  | .loc l => q.loc == l
  | .name n => n.uri == q.uri && n.loc == q.loc

def Env.kindMatches (e : Env) (n : NodeRef) : IType → Bool
  | .item | .anyNode => true
  | .elem t => (e.nrec n).kind == .element && (t.map (nameTestMatches · (e.nrec n).name)).getD true
  | .attr t => (e.nrec n).kind == .attribute && (t.map (nameTestMatches · (e.nrec n).name)).getD true
  | .text => (e.nrec n).kind == .text
  | .comment => (e.nrec n).kind == .comment
  | .nsNode => (e.nrec n).kind == .namespace
  | .pi t => (e.nrec n).kind == .pi && (t.map (· == (e.nrec n).name.loc)).getD true
  | .doc inner =>
      (e.nrec n).kind == .document &&
      (match inner with
       | none => true
       | some (.elem t) =>
          let els := (e.nrec n).children.toList.filter (fun c => (e.nrec ⟨n.doc, c⟩).kind == .element)
          match els with
          | [c] => (t.map (nameTestMatches · (e.nrec ⟨n.doc, c⟩).name)).getD true
          | _ => false
       | some _ => true)
  | _ => false

def Env.testMatches1 (e : Env) (ax : Axis) (n : NodeRef) : NodeTest → Bool
  | .name t =>
      let r := e.nrec n
      let principal := if ax == .attribute then r.kind == .attribute
                       else if ax == .namespace then r.kind == .namespace
                       else r.kind == .element
      principal && nameTestMatches t r.name
  | .kind t => e.kindMatches n t
  | .union _ => false

def Env.testMatches (e : Env) (ax : Axis) (n : NodeRef) : NodeTest → Bool
  | .union ts => ts.any (fun t => e.testMatches1 ax n t)
  | t => e.testMatches1 ax n t

def Env.ancestors (e : Env) (n : NodeRef) : List NodeRef :=
  let rec go (i : Option Nat) (fuel : Nat) (acc : List NodeRef) : List NodeRef :=
    match fuel, i with
    | 0, _ => acc
    | _, none => acc
    | f + 1, some j => go ((e.doc n).get j).parent f (acc ++ [⟨n.doc, j⟩])
  go (e.nrec n).parent 100000 []

def Env.rangeNodes (e : Env) (d : Nat) (lo hi : Nat) : List NodeRef :=
  if hi < lo then []
  else ((List.range (hi + 1 - lo)).map (fun k => (⟨d, lo + k⟩ : NodeRef))).filter
        (fun m => let k := (e.nrec m).kind; k != .attribute && k != .namespace)

/-- The nodes on an axis, in AXIS order (reverse document order for a
    reverse axis). -/
def Env.axis (e : Env) (ax : Axis) (n : NodeRef) : List NodeRef :=
  let r := e.nrec n
  let d := n.doc
  let kids := r.children.toList.map (fun c => (⟨d, c⟩ : NodeRef))
  let isAttrLike := r.kind == .attribute || r.kind == .namespace
  let sibs : List NodeRef :=
    if isAttrLike then [] else
    match r.parent with
    | some p => ((e.doc n).get p).children.toList.map (fun c => (⟨d, c⟩ : NodeRef))
    | none => []
  match ax with
  | .child => kids
  | .attribute => r.attrs.toList.map (fun c => ⟨d, c⟩)
  | .self => [n]
  | .descendant => if isAttrLike then [] else e.rangeNodes d (n.idx + 1) r.last
  | .descendantOrSelf => n :: (if isAttrLike then [] else e.rangeNodes d (n.idx + 1) r.last)
  | .parent => match r.parent with | some p => [⟨d, p⟩] | none => []
  | .ancestor => e.ancestors n
  | .ancestorOrSelf => n :: e.ancestors n
  | .followingSibling => sibs.filter (fun m => m.idx > n.idx)
  | .followingSiblingOrSelf => n :: sibs.filter (fun m => m.idx > n.idx)
  | .precedingSibling => (sibs.filter (fun m => m.idx < n.idx)).reverse
  | .precedingSiblingOrSelf => n :: (sibs.filter (fun m => m.idx < n.idx)).reverse
  | .following =>
      let start := if isAttrLike then (match r.parent with
        | some p => p + 1 | none => r.last + 1) else r.last + 1
      -- for an attribute, following starts after the parent's attributes but
      -- includes the parent's descendants
      let lst := ((e.doc n).nodes.size)
      let nodes := e.rangeNodes d start (lst - 1)
      if isAttrLike then nodes else nodes
  | .followingOrSelf =>
      n :: e.rangeNodes d (r.last + 1) ((e.doc n).nodes.size - 1)
  | .preceding =>
      let anc := e.ancestors n
      let upto := if isAttrLike then (match r.parent with | some p => p | none => 0) else n.idx
      ((e.rangeNodes d 0 (upto - 1)).filter (fun m => upto > 0 && !anc.contains m && (if isAttrLike then m.idx != upto else true))).reverse
  | .precedingOrSelf =>
      let anc := e.ancestors n
      n :: ((e.rangeNodes d 0 (n.idx - 1)).filter (fun m => n.idx > 0 && !anc.contains m)).reverse
  | .namespace => []

/-! ## Sequence types -/

def occOk (o : Occ) (n : Nat) : Bool :=
  match o with
  | .one => n == 1 | .opt => n ≤ 1 | .star => true | .plus => n ≥ 1

def splitST : IType → IType × Occ
  | .seq t o => (t, o)
  | .empty => (.empty, .opt)
  | t => (t, .one)

/-- Builtin function signatures: `(uri, local, minArity, maxArity, sig)`. -/
structure Param where
  name : String
  ty : IType
  dflt : Option Expr
deriving Inhabited

structure Sig where
  uri : String
  loc : String
  ret : IType
  ps : List Param
deriving Inhabited

def pfxUri : String → String
  | "fn" => nsFN | "math" => nsMATH | "map" => nsMAP | "array" => nsARR | "op" => nsOP | _ => ""

def parseTy (t : String) : IType :=
  match parseSeqType t with
  | .ok v => v
  | .error _ => .seq .item .star

def mkParam (y : String × String × Option String) : Param :=
  Param.mk y.1 (parseTy y.2.1) (y.2.2.bind (fun s => (parseXPath s).toOption))

def mkSig (x : String × String × String × List (String × String × Option String)) : Sig :=
  Sig.mk (pfxUri x.1) x.2.1 (parseTy x.2.2.1) (x.2.2.2.map mkParam)

def sigs : Array Sig := (catalogRaw.map mkSig).toArray

def Sig.minArity (s : Sig) : Nat := (s.ps.filter (·.dflt.isNone)).length
def Sig.maxArity (s : Sig) : Nat := s.ps.length

def findSig (q : QN) (arity : Nat) : Option Sig :=
  sigs.find? (fun s => s.uri == q.uri && s.loc == q.loc && s.minArity ≤ arity && arity ≤ s.maxArity)

def findSigAny (q : QN) : Option Sig :=
  sigs.find? (fun s => s.uri == q.uri && s.loc == q.loc)

def Item.fnArity : Item → Option Nat
  | .fn f => some f.arity
  | .map _ => some 1
  | .arr _ => some 1
  | _ => none

mutual
def Env.itemMatchesF (e : Env) : Nat → Item → IType → Bool
  | 0, _, _ => false
  | f + 1, i, t =>
  match t with
  | .item => true
  | .anyNode => i.isNode
  | .atomic t => match i with | .atom a => a.ty.derives t | _ => false
  | .anyFn => i.isFn
  | .fnT ps _ => i.fnArity == some ps.length
  | .anyMap => match i with | .map _ => true | _ => false
  | .mapT k v => match i with
      | .map kvs => kvs.all (fun (ka, vs) => e.itemMatchesF f (.atom ka) k && e.seqMatchesF f vs v)
      | _ => false
  | .anyArr => match i with | .arr _ => true | _ => false
  | .arrT m => match i with
      | .arr ms => ms.all (fun s => e.seqMatchesF f s m)
      | _ => false
  | .record fs ext => match i with
      | .map kvs =>
          fs.all (fun (nm, opt, t) =>
            match kvs.find? (fun (k, _) => k.isStringLike && k.str == nm) with
            | some (_, vs) => e.seqMatchesF f vs t
            | none => opt) &&
          (ext || kvs.all (fun (k, _) => k.isStringLike && fs.any (fun (nm, _, _) => nm == k.str)))
      | _ => false
  | .choice ts => ts.any (fun t => e.itemMatchesF f i t)
  | .enum vs => match i with
      | .atom a => a.is .string && vs.contains a.str
      | _ => false
  | .seq t _ => e.itemMatchesF f i t
  | .empty => false
  | t => match i with | .node n => e.kindMatches n t | _ => false

def Env.seqMatchesF (e : Env) : Nat → Seq → IType → Bool
  | 0, _, _ => false
  | f + 1, s, t =>
  match t with
  | .empty => s.isEmpty
  | .seq t o => occOk o s.length && s.all (fun i => e.itemMatchesF f i t)
  | t => s.length == 1 && s.all (fun i => e.itemMatchesF f i t)
end

def Env.itemMatches (e : Env) (i : Item) (t : IType) : Bool := e.itemMatchesF 1000 i t
def Env.seqMatches (e : Env) (s : Seq) (t : IType) : Bool := e.seqMatchesF 1000 s t

/-- The atomic target of an atomic(-ish) item type, for coercion. -/
def atomicTarget : IType → Option (List AType)
  | .atomic t => some [t]
  | .choice ts => ts.foldr (fun t acc => match t, acc with
      | .atomic a, some l => some (a :: l)
      | .enum _, some l => some (.b .string :: l)
      | _, _ => none) (some [])
  | .enum _ => some [.b .string]
  | _ => none

/-- Coerce one atomic value to one of the target types (§3.4.3 rules
    2–4: untyped casting, numeric promotion, URI promotion, and the
    4.0 relabelling of numeric values to a derived type in range). -/
def coerceAtom (ts : List AType) (a : Atomic) : M Atomic := do
  if ts.any (fun t => a.ty.derives t) then return a
  if a.ty == .untyped then
    let t := if ts.length > 1 && ts.all (fun t => t == .b .double || t == .b .float || t == .b .decimal)
             then .b .double else ts.headD (.b .string)
    return ← castAtomic a t
  for t in ts do
    match t with
    | .b .double => if a.isNumeric then return ← castAtomic a t
    | .b .float => if a.is .decimal || a.is .float then return ← castAtomic a t
    | .b .string => if a.is .anyURI then return Atomic.ofStr a.str
    | .b b =>
        if derivedFrom b .integer && a.is .integer then
          match a.v with
          | .int i => if inIntBounds b i then return ⟨t, .int i⟩
          | _ => pure ()
        else if derivedFrom b .decimal && a.is .decimal then
          -- relabel only integer subtypes of decimals that are integers
          pure ()
        else pure ()
    | _ => pure ()
  err "XPTY0004" ("cannot convert xs:" ++ a.ty.name ++ " value '" ++ a.str ++ "' to the required type")

def IType.isEmptyT : IType → Bool | .empty => true | _ => false

def Env.coerce (e : Env) (t : IType) (s : Seq) (what : String := "value") : M Seq := do
  let (it, o) := splitST t
  if it.isEmptyT then
    if s.isEmpty then return [] else err "XPTY0004" ("expected empty sequence for " ++ what)
  let s ← match atomicTarget it with
    | some ts => do
        let as ← e.atomize s
        let cs ← as.mapM (coerceAtom ts)
        -- enumerations check values
        match it with
        | .enum vs => if cs.all (fun a => vs.contains a.str) then pure (seqOfAtoms cs)
                      else err "XPTY0004" "value not in enumeration"
        | _ => pure (seqOfAtoms cs)
    | none => pure s
  if !occOk o s.length then
    err "XPTY0004" ("wrong number of items for " ++ what ++ ": " ++ toString s.length)
  else
  match it with
  | .item => pure s
  | .fnT _ _ | .anyFn =>
      if s.all (fun i => e.itemMatches i it) then pure s
      else err "XPTY0004" ("function item of wrong type for " ++ what)
  | _ =>
    if s.all (fun i => e.itemMatches i it) then pure s
    else err "XPTY0004" ("value of wrong type for " ++ what)


/-! ## deep-equal (default options) -/

def Env.nodeDeepEq (e : Env) : Nat → NodeRef → NodeRef → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    let ra := e.nrec a
    let rb := e.nrec b
    if ra.kind != rb.kind then false
    else match ra.kind with
    | .document | .element =>
        let nameOk := ra.kind == .document || ra.name == rb.name
        let attrsOk := ra.attrs.size == rb.attrs.size &&
          ra.attrs.toList.all (fun x =>
            let rx := e.nrec ⟨a.doc, x⟩
            rb.attrs.toList.any (fun y =>
              let ry := e.nrec ⟨b.doc, y⟩
              rx.name == ry.name && rx.value == ry.value))
        let kidsOf (n : NodeRef) (r : NRec) : List NodeRef :=
          (r.children.toList.map (fun c => (⟨n.doc, c⟩ : NodeRef))).filter
            (fun m => let k := (e.nrec m).kind; k != .comment && k != .pi)
        let ka := kidsOf a ra
        let kb := kidsOf b rb
        nameOk && attrsOk && ka.length == kb.length &&
          (ka.zip kb).all (fun (x, y) => e.nodeDeepEq f x y)
    | .attribute | .pi | .namespace => ra.name == rb.name && ra.value == rb.value
    | _ => ra.value == rb.value

def deepAtomEq (a b : Atomic) : Bool :=
  match atomicCmp a b with
  | .ok (some .eq) =>
      -- strings vs anyURI vs untyped compare equal; durations exact
      true
  | .ok none => (a.num?.map (·.toFloat.isNaN)).getD false && (b.num?.map (·.toFloat.isNaN)).getD false
  | _ => false

def Env.deepEqFuel (e : Env) : Nat → Seq → Seq → Bool
  | 0, _, _ => false
  | f + 1, xs, ys =>
    xs.length == ys.length &&
    (xs.zip ys).all (fun (x, y) =>
      match x, y with
      | .atom a, .atom b => deepAtomEq a b
      | .node a, .node b => e.nodeDeepEq 100000 a b
      | .map ka, .map kb =>
          ka.length == kb.length &&
          ka.all (fun (k, v) => match kb.find? (fun (k2, _) => atomicEqual k k2) with
            | some (_, v2) => e.deepEqFuel f v v2
            | none => false)
      | .arr ma, .arr mb => ma.length == mb.length && (ma.zip mb).all (fun (p, q) => e.deepEqFuel f p q)
      | _, _ => false)

def Env.deepEq (e : Env) (a b : Seq) : Bool := e.deepEqFuel 10000 a b

end L4Factoidal.XPath4
