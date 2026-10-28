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
import L4Factoidal.XPath4.JNode
import L4Factoidal.EXPath.File.FS
import Std.Data.HashMap

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-! ## The dynamic context -/

/-- The part of the dynamic context that a host function sees
    (`Env.host`): the variable bindings and the focus at the call. -/
structure HostCall where
  vars : List (QN × Seq) := []
  ctx : Option Seq := none
  pos : Nat := 0
  size : Nat := 0
  /-- The static namespace bindings in force (`Env.ns`). -/
  ns : List (String × String) := []

/-- A host function: called with the dynamic context of the call and
    the argument values. -/
abbrev HostFn := HostCall → List Seq → M Seq

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
  /-- Text resources the caller has read in advance (URI or relative
      reference as written, then the text): `fn:unparsed-text`,
      `fn:json-doc`, `fn:doc`, and external entities and DTDs when
      `trust-external` is true. The evaluator itself does no I/O. -/
  resources : List (String × String) := []
  /-- The decimal formats of the static context: the expanded name as
      `Q{uri}local` (`""` for the unnamed one) and its properties. -/
  decimalFormats : List (String × List (String × String)) := []
  defaultCollation : String := "http://www.w3.org/2005/xpath-functions/collation/codepoint"
  baseUri : String := ""
  /-- The octets of resources the caller read in advance (URI or relative
      reference as written, then the octets), for `fn:unparsed-text` and
      the other text readers, which decode them by the encoding rules of
      F&O 4.0 §17.1.5. A resource here takes precedence over `resources`. -/
  resourceBytes : List (String × ByteArray) := []
  /-- EXPath hook: the in-memory file system that the `file:` functions
      read (`L4Factoidal.EXPath.File`); `none` when there is none. -/
  fileSys : Option L4Factoidal.EXPath.File.FS := none
  /-- Host hook (XSLT 4.0, `L4Factoidal.XSLT4`): the functions of the
      host language by name and arity (`xsl:function`, `fn:current`,
      `fn:key`, ...). Consulted before the built-in library; empty for
      XPath. -/
  host : QN → Nat → Option HostFn := fun _ _ => none
deriving Inhabited

def Env.doc (e : Env) (n : NodeRef) : Doc :=
  match n.rt with
  | some d => d
  | none => e.docs.getD n.doc default
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

/-- Document order over GNodes (XPath 4.0 §2.7.1): XNodes by document and
    index, JNodes by root and path (`XPath4.JNode`); every XNode tree
    before every JTree. -/
def gnodeLt (a b : Item) : Bool :=
  match a, b with
  | .node x, .node y => nodeLt x y
  | .node _, .jnode .. => true
  | .jnode .., .jnode .. => jbefore a b
  | _, _ => false

/-- GNode identity. -/
def gnodeEq (a b : Item) : Bool :=
  match a, b with
  | .node x, .node y => x == y
  | .jnode .., .jnode .. => jsame a b
  | _, _ => false

/-- GNodes in document order, without duplicates. -/
def sortGNodes (ns : List Item) : List Item :=
  let s := ns.mergeSort (fun a b => !(gnodeLt b a))
  let rec dedup : List Item → List Item
    | a :: b :: r => if gnodeEq a b then dedup (b :: r) else a :: dedup (b :: r)
    | l => l
  dedup s

/-- The items of `s` when every one is a GNode. -/
def gnodesOf (s : Seq) : Option (List Item) :=
  if s.all Item.isGNode then some s else none

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
      | .jnode _ _ v _ =>
          for a in ← e.atomizeFuel f v do out := out.push a
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
  | .jnode .. :: _ => pure true
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
          let els := (e.nrec n).children.toList.filter (fun c => (e.nrec (n.at (c))).kind == .element)
          match els with
          | [c] => (t.map (nameTestMatches · (e.nrec (n.at (c))).name)).getD true
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
  | .ncname t _ =>
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
    | f + 1, some j => go ((e.doc n).get j).parent f (acc ++ [(n.at (j))])
  go (e.nrec n).parent 100000 []

def Env.rangeNodes (e : Env) (d : NodeRef) (lo hi : Nat) : List NodeRef :=
  if hi < lo then []
  else ((List.range (hi + 1 - lo)).map (fun k => (d.at (lo + k)))).filter
        (fun m => let k := (e.nrec m).kind; k != .attribute && k != .namespace)

/-- The nodes on an axis, in AXIS order (reverse document order for a
    reverse axis). -/
def Env.axis (e : Env) (ax : Axis) (n : NodeRef) : List NodeRef :=
  let r := e.nrec n
  let d := n
  let kids := r.children.toList.map (fun c => d.at c)
  let isAttrLike := r.kind == .attribute || r.kind == .namespace
  let sibs : List NodeRef :=
    if isAttrLike then [] else
    match r.parent with
    | some p => ((e.doc n).get p).children.toList.map (fun c => d.at c)
    | none => []
  match ax with
  | .child => kids
  | .attribute => r.attrs.toList.map (fun c => d.at c)
  | .self => [n]
  | .descendant => if isAttrLike then [] else e.rangeNodes d (n.idx + 1) r.last
  | .descendantOrSelf => n :: (if isAttrLike then [] else e.rangeNodes d (n.idx + 1) r.last)
  | .parent => match r.parent with | some p => [d.at p] | none => []
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
  | .item => []

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
  | "fn" => nsFN | "math" => nsMATH | "map" => nsMAP | "array" => nsARR | "op" => nsOP
  -- EXPath hook (`L4Factoidal.EXPath.Catalog`)
  | "bin" => "http://expath.org/ns/binary" | "file" => "http://expath.org/ns/file"
  | _ => ""

def parseTy (t : String) : IType :=
  match parseSeqType t with
  | .ok v => v
  | .error _ => .seq .item .star

def mkParam (y : String × String × Option String) : Param :=
  Param.mk y.1 (parseTy y.2.1) (y.2.2.bind (fun s => (parseXPath s).toOption))

def mkSig (x : String × String × String × List (String × String × Option String)) : Sig :=
  Sig.mk (pfxUri x.1) x.2.1 (parseTy x.2.2.1) (x.2.2.2.map mkParam)

def sigs : Array Sig := ((catalogRaw ++ catalogExt).map mkSig).toArray

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

/-- Occurrence inclusion: every count allowed by `a` is allowed by `b`. -/
def occLe (a b : Occ) : Bool :=
  match a, b with
  | _, .star => true
  | .one, _ => true
  | .opt, .opt => true
  | .plus, .plus => true
  | _, _ => false

/-- Sequence-type subtyping (XPath 4.0 §3.3), approximated: atomic
    derivation, node kinds, choices, and function/map/array types with
    the usual variance. -/
def subtypeF : Nat → IType → IType → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match a, b with
    | .empty, .empty => true
    | .empty, .seq _ o => o == .opt || o == .star
    | _, .empty => false
    | .seq t o, .seq u p => occLe o p && subtypeF f t u
    | .seq t o, u => o == .one && subtypeF f t u
    | t, .seq u p => occLe .one p && subtypeF f t u
    | _, .item => true
    | .choice ts, u => ts.all (fun t => subtypeF f t u)
    | t, .choice us => us.any (fun u => subtypeF f t u)
    | .atomic x, .atomic y => x.derives y
    | .enum _, .atomic y => (AType.b .string).derives y
    | .enum xs, .enum ys => xs.all (fun x => ys.contains x)
    | .elem _, .anyNode | .attr _, .anyNode | .text, .anyNode | .comment, .anyNode
    | .pi _, .anyNode | .doc _, .anyNode | .nsNode, .anyNode | .anyNode, .anyNode => true
    | .xnode, .anyNode | .xnode, .xnode | .jnodeT _ _, .anyNode => true
    | .elem _, .xnode | .attr _, .xnode | .text, .xnode | .comment, .xnode
    | .pi _, .xnode | .doc _, .xnode | .nsNode, .xnode => true
    | .jnodeT _ _, .jnodeT .any none => true
    | .jnodeT _ (some t), .jnodeT .any (some u) => subtypeF f t u
    | .elem none, .elem none | .attr none, .attr none | .text, .text | .comment, .comment
    | .nsNode, .nsNode | .doc none, .doc none | .pi none, .pi none => true
    | .elem (some _), .elem none | .attr (some _), .attr none | .pi (some _), .pi none
    | .doc (some _), .doc none => true
    | .fnT _ _, .anyFn | .anyMap, .anyFn | .mapT _ _, .anyFn | .anyArr, .anyFn | .arrT _, .anyFn
    | .record _ _, .anyFn | .anyFn, .anyFn => true
    | .fnT ps r, .fnT qs t =>
        ps.length == qs.length && (qs.zip ps).all (fun (q, p) => subtypeF f q p) && subtypeF f r t
    | .mapT _ _, .anyMap | .record _ _, .anyMap | .anyMap, .anyMap => true
    | .mapT k v, .mapT k2 v2 => subtypeF f k k2 && subtypeF f v v2
    -- XPath 4.0 §3.3.2.5: a record type is a subtype of a map type whose key
    -- type admits xs:string and whose value type admits every field
    | .record fs ext, .mapT k v =>
        subtypeF f (.atomic (.b .string)) k &&
        (if ext then subtypeF f (.seq .item .star) v else fs.all (fun (_, _, t) => subtypeF f t v))
    | .record fs e1, .record gs e2 =>
        gs.all (fun (n, opt, t) => match fs.find? (·.1 == n) with
          | some (_, o1, t1) => (opt || !o1) && subtypeF f t1 t
          | none => opt && !e1) &&
        (e2 || (!e1 && fs.all (fun (n, _, _) => gs.any (·.1 == n))))
    | .anyArr, .anyArr | .arrT _, .anyArr => true
    | .arrT m, .arrT m2 => subtypeF f m m2
    | .mapT k v, .fnT [p] r => subtypeF f p k && subtypeF f (.seq v .opt) r
    | .anyMap, .fnT [p] r => subtypeF f p (.atomic (.b .anyAtomicType)) && subtypeF f (.seq .item .star) r
    | .arrT m, .fnT [p] r => subtypeF f p (.atomic (.b .integer)) && subtypeF f m r
    | .anyArr, .fnT [p] r => subtypeF f p (.atomic (.b .integer)) && subtypeF f (.seq .item .star) r
    | _, _ => false

def subtype (a b : IType) : Bool := subtypeF 200 a b

/-- The declared signature of a function item, when known. -/
def fnSigOf : FnItem → Option (List IType × IType)
  | .builtin q k =>
    if q.uri == nsXS then
      match atypeOfName? q.loc with
      | some t => some ([.seq (.atomic (.b .anyAtomicType)) .opt], .seq (.atomic t) .opt)
      | none => none
    else (findSig q k).map (fun s => ((s.ps.take k).map (·.ty), s.ret))
  | .inline ps ret _ focus _ => if focus then some ([.seq .item .star], ret) else some (ps.map (·.2), ret)
  | .papp _ _ => none

mutual
def Env.itemMatchesF (e : Env) : Nat → Item → IType → Bool
  | 0, _, _ => false
  | f + 1, i, t =>
  match t with
  | .item => true
  | .anyNode => i.isGNode
  | .xnode => i.isNode
  | .jnodeT k vt => match i with
      | .jnode _ st v _ =>
        (match k, st with
         | .any, _ => true
         | .root, [] => true
         | .key a, s :: _ => atomicEqual a s.key
         | _, _ => false) &&
        (match vt with
         | some t => e.seqMatchesF f v t
         | none => true)
      | _ => false
  | .atomic t => match i with | .atom a => a.ty.derives t | _ => false
  | .anyFn => i.isFn
  | .fnT ps r => i.fnArity == some ps.length &&
      (match i with
       | .fn fi => match fnSigOf fi with
          | some (fps, fr) => (ps.zip fps).all (fun (p, q) => subtype p q) && subtype fr r
          | none => true
       | .map _ => subtype (.anyMap) (.fnT ps r) || true
       | .arr _ => true
       | _ => false)
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

/-- A node test on a JNode (XPath 4.0 §4.7.5.4 and §4.7.5.5): `*`
    matches every JNode; an NCName a string-like key equal to it; another
    name test or wildcard a QName key; a type test the JNode itself. -/
def Env.jtestMatches1 (e : Env) (j : Item) : NodeTest → Bool
  | .name .any => true
  | .name t => match jkeyOf j with
      | some ⟨_, .qn q⟩ => nameTestMatches t q
      | _ => false
  | .ncname _ l => match jkeyOf j with
      | some k => k.isStringLike && k.str == l
      | none => false
  | .kind t => e.itemMatches j t
  | .union _ => false

def Env.jtestMatches (e : Env) (j : Item) : NodeTest → Bool
  | .union ts => ts.any (fun t => e.jtestMatches1 j t)
  | t => e.jtestMatches1 j t

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
    -- XPath 4.0 §3.4.2, the implicit casting table
    | .b .double => if a.isNumeric then return ← castAtomic a t
    | .b .float => if a.isNumeric then return ← castAtomic a t
    | .b .decimal => if a.is .float || a.is .double then return ← castAtomic a t
    | .b .string => if a.is .anyURI then return Atomic.ofStr a.str
    | .b .anyURI => if a.is .string then return ← castAtomic a t
    | .b .hexBinary => if a.is .base64Binary then return ← castAtomic a t
    | .b .base64Binary => if a.is .hexBinary then return ← castAtomic a t
    | .b b =>
        if derivedFrom b .integer && a.is .integer then
          match a.v with
          | .int i => if inIntBounds b i then return ⟨t, .int i⟩
          | _ => pure ()
        else if b.primitive.isSome && !(derivedFrom b .decimal) &&
            (match a.ty with | .b ab => ab.primitive == b.primitive | .untyped => false) then
          -- relabeling: the datum of `a` is in the value space of the
          -- derived type (the cast keeps the lexical form)
          match castAtomic a t with
          | .ok r => if r.str == a.str then return r
          | .error _ => pure ()
        else pure ()
    | _ => pure ()
  err "XPTY0004" ("cannot convert xs:" ++ a.ty.name ++ " value '" ++ a.str ++ "' to the required type")

def IType.isEmptyT : IType → Bool | .empty => true | _ => false

/-- XPath 4.0 §3.4.3: a JNode that does not match the required item type
    is replaced by its ·jvalue·, whose items are coerced in turn. -/
def Env.unwrapJ (e : Env) : Nat → IType → Seq → Seq
  | 0, _, s => s
  | f + 1, it, s => s.flatMap (fun i => match i with
      | .jnode _ _ v _ => if e.itemMatches i it then [i] else e.unwrapJ f it v
      | _ => [i])

/-- The coercion rules (XPath 4.0 §3.4.3), applied recursively to the
    members of arrays and the entries of maps and records. -/
def Env.coerceF (e : Env) : Nat → IType → Seq → String → M Seq
  | 0, _, s, _ => pure s
  | f + 1, t, s, what => do
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
    | none => pure (e.unwrapJ 64 it s)
  if !occOk o s.length then
    err "XPTY0004" ("wrong number of items for " ++ what ++ ": " ++ toString s.length)
  else
  -- coerce inside maps, records and arrays
  let s ← s.mapM (fun i => do
    match it, i with
    | .arrT m, .arr ms => pure (Item.arr (← ms.mapM (fun x => e.coerceF f m x what)))
    | .mapT k v, .map kvs =>
        pure (Item.map (← kvs.mapM (fun (ka, va) => do
          let ka' ← match atomicTarget k with
            | some ts => coerceAtom ts ka
            | none => pure ka
          pure (ka', ← e.coerceF f v va what))))
    | .record fs _, .map kvs =>
        pure (Item.map (← kvs.mapM (fun (ka, va) => do
          match fs.find? (fun (nm, _, _) => ka.isStringLike && ka.str == nm) with
          | some (_, _, ft) => pure (ka, ← e.coerceF f ft va what)
          | none => pure (ka, va))))
    | _, _ => pure i)
  match it with
  | .item => pure s
  | .fnT ps _ =>
      -- XPath 4.0 §3.4.4: a function of lower arity is accepted
      if s.all (fun i => match i.fnArity with | some k => k ≤ ps.length | none => false) then pure s
      else err "XPTY0004" ("function item of wrong type for " ++ what)
  | .anyFn =>
      if s.all (fun i => e.itemMatches i it) then pure s
      else err "XPTY0004" ("function item of wrong type for " ++ what)
  | .choice ts =>
    if s.all (fun i => e.itemMatches i it) then pure s else
    -- only a choice that mixes atomic and function types is handled here;
    -- a choice of function types alone keeps the strict test
    if !(ts.any (fun t => match t with | .atomic _ | .enum _ => true | _ => false)) then
      err "XPTY0004" ("value of wrong type for " ++ what) else
    -- a choice of atomic types and function types (for example the
    -- `$replacement` of `fn:replace`): coerce each item to a member
    let atoms := ts.filterMap (fun t => match t with | .atomic a => some a | .enum _ => some (.b .string) | _ => none)
    let fnArity := ts.filterMap (fun t => match t with | .fnT ps _ => some ps.length | _ => none)
    s.mapM (fun i => do
      match i.fnArity with
      | some k =>
        if fnArity.any (k ≤ ·) || e.itemMatches i it then pure i
        else err "XPTY0004" ("function item of wrong type for " ++ what)
      | none =>
        if e.itemMatches i it then pure i
        else if atoms.isEmpty then err "XPTY0004" ("value of wrong type for " ++ what)
        else
          match ← e.atomize [i] with
          | [a] => pure (Item.atom (← coerceAtom atoms a))
          | _ => err "XPTY0004" ("value of wrong type for " ++ what))
  | _ =>
    if s.all (fun i => e.itemMatches i it) then pure s
    else err "XPTY0004" ("value of wrong type for " ++ what)

def Env.coerce (e : Env) (t : IType) (s : Seq) (what : String := "value") : M Seq :=
  e.coerceF 64 t s what

/-- A string key with `k a = k b ↔ atomicEqual a b` (untyped read as
    string), for the value kinds where one is cheap; `none` otherwise. -/
def sameKey (a : Atomic) : Option String :=
  match a.num? with
  | some n =>
    let f := n.toFloat
    if n.rank ≥ 2 && f.isNaN then some "NaN"
    else if n.rank ≥ 2 && f.isInf then some (if f > 0 then "INF" else "-INF")
    else some ("n" ++ Dec.canonical n.toDec)
  | none =>
    match a.v with
    | .str s => some ("s" ++ s)
    | .bool b => some (if b then "bT" else "bF")
    | .qn q => some ("q" ++ q.eqn)
    | .x (.bin _ bs) => some ("x" ++ hexOfBytes bs)
    | _ => none

/-- A map under construction: entries in insertion order, indexed by
    `sameKey` where the key has one (linear search otherwise). -/
structure MB where
  entries : Array (Atomic × Seq) := #[]
  index : Std.HashMap String Nat := {}

def MB.find? (m : MB) (k : Atomic) : Option Nat :=
  match sameKey k with
  | some s => m.index.get? s
  | none => m.entries.findIdx? (fun (k2, _) => atomicEqual k k2)

def MB.get? (m : MB) (k : Atomic) : Option Seq :=
  (m.find? k).map (fun i => (m.entries.getD i default).2)

def MB.set (m : MB) (k : Atomic) (v : Seq) : MB :=
  match m.find? k with
  | some i => { m with entries := m.entries.set! i (k, v) }
  | none =>
    let i := m.entries.size
    { entries := m.entries.push (k, v),
      index := match sameKey k with | some s => m.index.insert s i | none => m.index }

def MB.toList (m : MB) : List (Atomic × Seq) := m.entries.toList

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
            let rx := e.nrec (a.at (x))
            rb.attrs.toList.any (fun y =>
              let ry := e.nrec (b.at (y))
              rx.name == ry.name && rx.value == ry.value))
        let kidsOf (n : NodeRef) (r : NRec) : List NodeRef :=
          (r.children.toList.map (fun c => ((n.at (c)) : NodeRef))).filter
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
      | .fn (.builtin q1 k1), .fn (.builtin q2 k2) => q1 == q2 && k1 == k2
      | .jnode _ _ v1 _, .jnode _ _ v2 _ => e.deepEqFuel f v1 v2
      | .fn (.papp (.fn (.builtin q1 k1)) a1), .fn (.papp (.fn (.builtin q2 k2)) a2) =>
          q1 == q2 && k1 == k2 && a1.length == a2.length &&
          (a1.zip a2).all (fun (x, y) => match x, y with
            | none, none => true
            | some u, some w => e.deepEqFuel f u w
            | _, _ => false)
      | _, _ => false)

def Env.deepEq (e : Env) (a b : Seq) : Bool := e.deepEqFuel 10000 a b

end L4Factoidal.XPath4
