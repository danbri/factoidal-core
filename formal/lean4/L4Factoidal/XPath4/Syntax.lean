/-
L4Factoidal.XPath4.Syntax — the abstract syntax of XPath 4.0 and the
XDM 4.0 item model.

Spec: XPath 4.0 editor's draft (https://qt4cg.org/specifications/xquery-40/xpath-40.html,
qtspecs commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c), Appendix A
(grammar); XDM 4.0 §2 (items: atomic values, nodes, function items,
maps, arrays).

Names in the tree are already RESOLVED to expanded QNames by the
parser, which knows the static namespace bindings; the evaluator never
sees a prefix that it must look up, except in a string it casts to
`xs:QName`.

A NODE is a reference `(document, index)` into a document table
(`XPath4.Doc`); identity is the reference, document order is the pair
in lexicographic order.
-/
import L4Factoidal.XPath4.Atomic

namespace L4Factoidal.XPath4

/-! ## Axes and node tests -/

inductive Axis where
  | child | descendant | attribute | self | descendantOrSelf
  | followingSibling | following | namespace
  | parent | ancestor | precedingSibling | preceding | ancestorOrSelf
  | followingOrSelf | followingSiblingOrSelf | precedingOrSelf | precedingSiblingOrSelf
  /-- The item axis (XPath 4.0 §4.7.5.1), defined only for JNodes. -/
  | item
deriving DecidableEq, Repr, Inhabited

def Axis.reverse : Axis → Bool
  | .parent | .ancestor | .precedingSibling | .preceding | .ancestorOrSelf
  | .precedingOrSelf | .precedingSiblingOrSelf => true
  | _ => false

def axisOfName? : String → Option Axis
  | "child" => some .child | "descendant" => some .descendant
  | "attribute" => some .attribute | "self" => some .self
  | "descendant-or-self" => some .descendantOrSelf
  | "following-sibling" => some .followingSibling | "following" => some .following
  | "namespace" => some .namespace | "parent" => some .parent
  | "ancestor" => some .ancestor | "preceding-sibling" => some .precedingSibling
  | "preceding" => some .preceding | "ancestor-or-self" => some .ancestorOrSelf
  | "following-or-self" => some .followingOrSelf
  | "following-sibling-or-self" => some .followingSiblingOrSelf
  | "preceding-or-self" => some .precedingOrSelf
  | "preceding-sibling-or-self" => some .precedingSiblingOrSelf
  | "item" => some .item
  | _ => none

/-- `NameTest`: `*`, `prefix:*`, `*:local`, `Q{uri}*`, or a QName. -/
inductive NameTest where
  | any
  | ns (uri : String)
  | loc (l : String)
  | name (q : QN)
deriving Repr, Inhabited

/-- The key constraint of a `jnode(...)` type (XPath 4.0 §3.2.12): `*`
    (any key, or none), `()` (a root JNode), or a constant matched with
    `fn:atomic-equal`. -/
inductive JKeyTest where
  | any
  | root
  | key (a : Atomic)
deriving Repr, Inhabited

inductive Occ where
  | one | opt | star | plus
deriving DecidableEq, Repr, Inhabited

/-- Item types and sequence types (one inductive: `.seq t o` is a
    sequence type, `.empty` is `empty-sequence()`; a bare item type
    means exactly one). -/
inductive IType where
  | item
  | anyNode
  /-- `xnode()`: an XNode (a node of an XML tree), not a JNode. -/
  | xnode
  /-- `jnode(K, T)` (XPath 4.0 §3.2.12); `none` for an absent `T`. -/
  | jnodeT (k : JKeyTest) (vt : Option IType)
  | atomic (t : AType)
  | elem (n : Option NameTest)
  | attr (n : Option NameTest)
  /-- `element(N, T)` / `element(N, T?)` (XPath 4.0 §3.2.8.2): the type
      annotation must be `T` or derived from it (`Env.schema`); `nillable`
      is the `?`. -/
  | elemT (n : Option NameTest) (ty : QN) (nillable : Bool)
  /-- `attribute(N, T)` (XPath 4.0 §3.2.8.3). -/
  | attrT (n : Option NameTest) (ty : QN)
  /-- `schema-element(N)` (XPath 4.0 §3.2.8.4): needs the in-scope element
      declaration of `N` (`Env.schema`). -/
  | schemaElem (n : QN)
  /-- `schema-attribute(N)` (XPath 4.0 §3.2.8.5). -/
  | schemaAttr (n : QN)
  | text | comment | nsNode
  | pi (target : Option String)
  | doc (inner : Option IType)
  | anyFn
  | fnT (args : List IType) (ret : IType)
  | anyMap
  | mapT (k : IType) (v : IType)
  | anyArr
  | arrT (m : IType)
  | record (fields : List (String × Bool × IType)) (ext : Bool)
  | choice (ts : List IType)
  | enum (vals : List String)
  | seq (t : IType) (o : Occ)
  | empty
deriving Repr, Inhabited

/-- A node test in a step. -/
inductive NodeTest where
  | name (t : NameTest)
  /-- A name test written as an unprefixed NCName `l`: for an XNode it is
      the name test `t`; for a JNode it matches a string-like key equal
      to `l` (XPath 4.0 §4.7.5.4). -/
  | ncname (t : NameTest) (l : String)
  | kind (t : IType)
  | union (ts : List NodeTest)
deriving Repr, Inhabited

/-! ## Operators -/

inductive BOp where
  | or | and
  | geq | gne | glt | gle | ggt | gge
  | veq | vne | vlt | vle | vgt | vge
  | is | isNot | precedes | follows | precedesOrIs | followsOrIs
  | to | add | sub | mul | div | idiv | mod
  | union | intersect | except
  | concat | otherwise
deriving DecidableEq, Repr, Inhabited

inductive ForKind where
  | item | member | entry
deriving DecidableEq, Repr, Inhabited

/-! ## Expressions -/

inductive Expr where
  | lit (a : Atomic)
  | seq (es : List Expr)
  | var (q : QN)
  | ctx
  | root
  /-- `a / b`. -/
  | slash (a b : Expr)
  /-- An axis step with its predicates. -/
  | step (ax : Axis) (t : NodeTest) (preds : List Expr)
  /-- An axis step with a dynamic node test `ax::{e}` (XPath 4.0 §4.7.5.2). -/
  | dstep (ax : Axis) (e : Expr) (preds : List Expr)
  /-- A filter expression `e[p]`. -/
  | filter (e p : Expr)
  /-- A static function call. `none` in an argument is `?`. -/
  | call (q : QN) (args : List (Option Expr)) (kw : List (String × Option Expr))
  | dyn (f : Expr) (args : List (Option Expr))
  | fref (q : QN) (arity : Nat)
  /-- An inline function. `focus` is a focus function `fn { ... }`. -/
  | inline (ps : List (QN × IType)) (ret : IType) (body : Expr) (focus : Bool)
  | mapC (es : List (Expr × Expr))
  | arrS (es : List Expr)
  | arrC (e : Expr)
  /-- `e ? k`; `k` is `none` for the wildcard `*`. -/
  | lookup (e : Expr) (k : Option Expr)
  | ulookup (k : Option Expr)
  | bin (op : BOp) (a b : Expr)
  | neg (e : Expr)
  | plus (e : Expr)
  | ifE (c t e : Expr)
  | forE (kind : ForKind) (v : QN) (v2 : Option QN) (posv : Option QN) (vt : IType) (src body : Expr)
  | letE (v : QN) (vt : IType) (e body : Expr)
  | quant (every : Bool) (v : QN) (vt : IType) (src sat : Expr)
  | instOf (e : Expr) (t : IType)
  | treat (e : Expr) (t : IType)
  | cast (e : Expr) (t : IType) (opt : Bool)
  | castable (e : Expr) (t : IType) (opt : Bool)
  /-- `a ! b`. -/
  | smap (a b : Expr)
  /-- `a -> b`. -/
  | pipe (a b : Expr)
  /-- `=!>`: apply the target to each item. `f` is applied with the
      item prepended to `args`. -/
  | mapArrow (a : Expr) (f : Expr) (args : List (Option Expr))
  | tmpl (parts : List Expr)
  /-- An XQuery 4.0 construct (`L4Factoidal.XQuery4`): `tag` names it,
      `es` are its operand expressions, `ts` its types, `qs` its names
      and `ss` its strings. The XPath 4.0 grammar never builds one;
      `eval` gives it to `XQuery4.Runtime.evalExt`. -/
  | ext (tag : String) (es : List Expr) (ts : List IType) (qs : List QN) (ss : List String)
deriving Inhabited

/-! ## Items (XDM 4.0 §2) -/

/-! ## Document tables (the node store of `XPath4.Doc`) -/

inductive NKind where
  | document | element | attribute | text | comment | pi | namespace
deriving DecidableEq, Repr, Inhabited

structure NRec where
  kind : NKind
  name : QN := default
  value : String := ""
  parent : Option Nat := none
  children : Array Nat := #[]
  attrs : Array Nat := #[]
  inscope : List (String × String) := []
  last : Nat := 0
  /-- Hook for schema validation (`L4Factoidal.XSD11`): the type
      annotation of an element or attribute (XDM 4.0 §2.7, `dm:type-name`);
      `none` is `xs:untyped` (element) or `xs:untypedAtomic` (attribute). -/
  tann : Option QN := none
  /-- Hook for schema validation: the typed value (`dm:typed-value`);
      `none` means the string value as `xs:untypedAtomic`. -/
  tval : Option (List Atomic) := none
  /-- Hook for schema validation: `dm:nilled`. -/
  nilled : Bool := false
  /-- Hook for schema validation: the element has element-only content,
      so `dm:typed-value` is absent and atomization fails (FOTY0012). -/
  noTypedValue : Bool := false
deriving Inhabited

structure Doc where
  nodes : Array NRec
  /-- The document URI (`fn:document-uri`); empty when absent. -/
  uri : String := ""
  /-- The base URI of the document node when it differs from `uri`
      (`fn:parse-xml` with the `base-uri` option). -/
  baseUri : String := ""
  /-- `(element, attribute)` names (as written) that the DTD declares
      `ID`, and those it declares `IDREF` or `IDREFS` (`fn:id`, `fn:idref`). -/
  idAttrs : List (String × String) := []
  idrefAttrs : List (String × String) := []
deriving Inhabited

/-- A node reference: document number and node index. A document built
    at run time (`fn:parse-xml` and friends) travels WITH its nodes in
    `rt`, because the dynamic context is read-only; `doc` is then a
    number derived from the content, outside the range the caller's
    documents use. Identity and order use `doc` and `idx` only. -/
structure NodeRef where
  doc : Nat
  idx : Nat
  rt : Option Doc := none
deriving Inhabited

instance : BEq NodeRef := ⟨fun a b => a.doc == b.doc && a.idx == b.idx⟩

instance : Repr NodeRef := ⟨fun n _ => "node(" ++ repr n.doc ++ ", " ++ repr n.idx ++ ")"⟩

/-- Another node of the same document. -/
def NodeRef.at (n : NodeRef) (i : Nat) : NodeRef := { n with idx := i }

def NodeRef.mk' (d i : Nat) : NodeRef := { doc := d, idx := i }

/-- One step of a JNode's path from its parent (XDM 4.0 §8.5): the
    ·jkey· and the 1-based position among the parent's j-children.
    Position 0 marks the JNode that the item axis makes for a singleton
    value: its parent is the origin, but it is not a child. -/
structure JStep where
  key : Atomic
  pos : Nat
deriving Inhabited

mutual
inductive Item where
  | atom (a : Atomic)
  | node (n : NodeRef)
  /-- A map: entries in insertion order (XDM 4.0 maps are ordered). -/
  | map (kvs : List (Atomic × List Item))
  | arr (ms : List (List Item))
  | fn (f : FnItem)
  /-- A JNode (XDM 4.0 §8.5), kept as a zipper: `root` is the identity of
      the root JNode, `steps` the path from this JNode up to the root
      (nearest step first), `val` the ·jvalue·, and `up` the ·jvalue·s
      of the ancestors (nearest first; as long as `steps`). Identity is
      `root` with the step positions; ·jparent· drops the first step. -/
  | jnode (root : UInt64) (steps : List JStep) (val : List Item) (up : List (List Item))
inductive FnItem where
  | builtin (q : QN) (arity : Nat)
  | inline (ps : List (QN × IType)) (ret : IType) (body : Expr) (focus : Bool)
           (closure : List (QN × List Item))
  /-- A partial application: the function and the fixed arguments
      (`none` = still open). -/
  | papp (f : Item) (args : List (Option (List Item)))
end

instance : Inhabited Item := ⟨.atom default⟩

abbrev Seq := List Item

def FnItem.arity : FnItem → Nat
  | .builtin _ n => n
  | .inline ps _ _ focus _ => if focus then 1 else ps.length
  | .papp _ args => (args.filter Option.isNone).length

end L4Factoidal.XPath4
