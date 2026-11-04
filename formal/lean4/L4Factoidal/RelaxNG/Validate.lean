/-
L4Factoidal.RelaxNG.Validate — validation of an XML document against a
simplified RELAX NG grammar, by derivatives.

Algorithm: James Clark, "An algorithm for RELAX NG validation", 2002
(https://relaxng.org/jclark/derivative.html). The derivative of a pattern
with respect to a piece of the instance is a pattern that matches what may
follow it; the document is valid when the derivative of the start pattern
with respect to the document element is nullable. The semantics it decides
is that of RELAX NG Specification (3 December 2001) §6:

  * §6.2.1-§6.2.6: `choice`, `group`, `interleave`, `oneOrMore`, `empty`,
    `notAllowed` (the smart constructors `mkChoice`, `mkGroup`,
    `mkInterleave`, `mkAfter`, `mkOneOrMore` keep `notAllowed` and `empty`
    out of the derivatives);
  * §6.2.7 `text` and the whitespace rule: a child that is only whitespace
    is ignored when it is one of several children, and an element whose
    content is a single whitespace string (or nothing) may match either
    the string or nothing (`childDeriv`);
  * §6.2.8 `data` and `value`, through `L4Factoidal.RelaxNG.Datatypes`;
  * §6.2.9 `list`: the string is split at whitespace and each token is a
    derivative step (`listDeriv`);
  * §6.2.10 `element` and `attribute`. A `ref` names a `define` whose
    content is an `element`; it is looked up only when a start tag is
    matched against it, so the derivative of a recursive grammar is finite.

Instance names are expanded with the in-scope namespace declarations
(Namespaces in XML 1.0); `xmlns` and `xmlns:*` attributes are namespace
declarations, not attributes, for RELAX NG (§2). Comments and processing
instructions are not part of the data model (§2); text nodes that are next
to each other once they are removed are joined.
-/
import Std.Data.HashMap
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Namespaces
import L4Factoidal.RelaxNG.Datatypes
import L4Factoidal.RelaxNG.Simplify

namespace L4Factoidal.RelaxNG

open L4Factoidal.XML

/-! ## The instance -/

/-- §2: an element of the data model (name, context, attributes and
children) or a string. -/
inductive Inst where
  | elem (qn : QN) (cx : Context) (atts : List (QN × String)) (kids : List Inst)
  | text (s : String)
deriving Inhabited

/-- The context of an element: its in-scope namespace declarations; the
first binding of a prefix in `scope` is the innermost one. -/
def scopeContext (scope : NsScope) : Context :=
  let step (acc : List (String × String) × List String) (b : String × Option String) :=
    let (out, seen) := acc
    if seen.contains b.1 then acc
    else match b.2 with
      | some u => (out ++ [(b.1, u)], b.1 :: seen)
      | none => (out, b.1 :: seen)
  let (ns, _) := scope.foldl step ([], [])
  { ns := ns }

/-- Read an XML element into the data model. `none` when a name cannot be
expanded (an undeclared prefix). -/
def toInst (scope : NsScope) (n : Node) : Option Inst :=
  match n with
  | .element tag attrs children => do
    let scope' := (applyDeclarations "1.0" scope attrs).getD scope
    let en ← resolveElementName scope' tag
    let mut atts : List (QN × String) := []
    for a in attrs do
      if a.name == "xmlns" || a.name.startsWith "xmlns:" then continue
      let an ← resolveAttributeName scope' a.name
      atts := atts ++ [(⟨an.namespace_.getD "", an.localPart⟩, a.value)]
    let mut kids : Array Inst := #[]
    let mut pend : Option String := none
    for c in children do
      match c with
      | .text s => pend := some ((pend.getD "") ++ s)
      | .cdata s => pend := some ((pend.getD "") ++ s)
      | .element .. =>
        if let some s := pend then kids := kids.push (.text s)
        pend := none
        kids := kids.push (← toInst scope' c)
      | _ => pure ()
    if let some s := pend then kids := kids.push (.text s)
    return .elem ⟨en.namespace_.getD "", en.localPart⟩ (scopeContext scope') atts kids.toList
  | _ => none

/-! ## Smart constructors -/

/-- `choice` with `notAllowed` removed and equal sides merged. -/
def mkChoice : Pattern → Pattern → Pattern
  | .notAllowed, q => q
  | p, .notAllowed => p
  | p, q => if p == q then p else .choice p q

/-- `group` with `notAllowed` and `empty` removed. -/
def mkGroup : Pattern → Pattern → Pattern
  | .notAllowed, _ => .notAllowed
  | _, .notAllowed => .notAllowed
  | .empty, q => q
  | p, .empty => p
  | p, q => .group p q

/-- `interleave` with `notAllowed` and `empty` removed. -/
def mkInterleave : Pattern → Pattern → Pattern
  | .notAllowed, _ => .notAllowed
  | _, .notAllowed => .notAllowed
  | .empty, q => q
  | p, .empty => p
  | p, q => .interleave p q

/-- `after` with `notAllowed` removed. -/
def mkAfter : Pattern → Pattern → Pattern
  | .notAllowed, _ => .notAllowed
  | _, .notAllowed => .notAllowed
  | p, q => .after p q

/-- `oneOrMore` of `notAllowed` is `notAllowed`. -/
def mkOneOrMore : Pattern → Pattern
  | .notAllowed => .notAllowed
  | p => .oneOrMore p

/-! ## Derivatives -/

/-- Does the pattern match the empty sequence? -/
def nullable : Pattern → Bool
  | .group a b | .interleave a b => nullable a && nullable b
  | .choice a b => nullable a || nullable b
  | .oneOrMore p => nullable p
  | .empty | .text => true
  | _ => false

/-- The whitespace-separated tokens of a string (§6.2.9). -/
def tokens (s : String) : List String :=
  (String.ofList (s.toList.map (fun c => if isXmlSpace c then ' ' else c))).splitOn " "
    |>.filter (fun t => t != "")

/-- The derivative with respect to a string, with the `list` case given by
`onList`. -/
def textDerivWith (onList : Pattern → Pattern) (cx : Context) (s : String) : Pattern → Pattern
  | .choice a b => mkChoice (textDerivWith onList cx s a) (textDerivWith onList cx s b)
  | .interleave a b =>
    mkChoice (mkInterleave (textDerivWith onList cx s a) b)
      (mkInterleave a (textDerivWith onList cx s b))
  | .group a b =>
    let p := mkGroup (textDerivWith onList cx s a) b
    if nullable a then mkChoice p (textDerivWith onList cx s b) else p
  | .after a b => mkAfter (textDerivWith onList cx s a) b
  | .oneOrMore p => mkGroup (textDerivWith onList cx s p) (mkChoice (.oneOrMore p) .empty)
  | .text => .text
  | .value dt v vcx => if valueEq dt v vcx s cx then .empty else .notAllowed
  | .data dt ps => if dataAllows dt ps cx s then .empty else .notAllowed
  | .dataExcept dt ps e =>
    if dataAllows dt ps cx s && !nullable (textDerivWith onList cx s e) then .empty
    else .notAllowed
  | .list p => onList p
  | _ => .notAllowed

/-- The derivative with respect to a token inside a `list` (§7.1.3 refuses
a `list` inside a `list`). -/
def textDerivInList (cx : Context) (s : String) : Pattern → Pattern :=
  textDerivWith (fun _ => .notAllowed) cx s

/-- §6.2.9: the derivative with respect to a sequence of tokens. -/
def listDeriv (cx : Context) (toks : List String) (p : Pattern) : Pattern :=
  toks.foldl (fun q t => textDerivInList cx t q) p

/-- The derivative with respect to a string (§6.2.7-§6.2.9). -/
def textDeriv (cx : Context) (s : String) : Pattern → Pattern :=
  textDerivWith
    (fun p => if nullable (listDeriv cx (tokens s) p) then .empty else .notAllowed) cx s

/-- Apply `f` to the second side of every `after`. -/
def applyAfter (f : Pattern → Pattern) : Pattern → Pattern
  | .after a b => mkAfter a (f b)
  | .choice a b => mkChoice (applyAfter f a) (applyAfter f b)
  | _ => .notAllowed

/-- The table of element `define`s. -/
abbrev Defs := Std.HashMap String (NameClass × Pattern)

/-- The derivative with respect to a start tag with name `q` (before its
attributes). -/
def startTagOpenDeriv (defs : Defs) (q : QN) : Pattern → Pattern
  | .choice a b => mkChoice (startTagOpenDeriv defs q a) (startTagOpenDeriv defs q b)
  | .ref n =>
    match defs[n]? with
    | some (nc, body) => if nc.contains q then mkAfter body .empty else .notAllowed
    | none => .notAllowed
  | .element nc body => if nc.contains q then mkAfter body .empty else .notAllowed
  | .interleave a b =>
    mkChoice (applyAfter (fun x => mkInterleave x b) (startTagOpenDeriv defs q a))
      (applyAfter (fun x => mkInterleave a x) (startTagOpenDeriv defs q b))
  | .oneOrMore p =>
    applyAfter (fun x => mkGroup x (mkChoice (.oneOrMore p) .empty)) (startTagOpenDeriv defs q p)
  | .group a b =>
    let x := applyAfter (fun y => mkGroup y b) (startTagOpenDeriv defs q a)
    if nullable a then mkChoice x (startTagOpenDeriv defs q b) else x
  | .after a b => applyAfter (fun x => mkAfter x b) (startTagOpenDeriv defs q a)
  | _ => .notAllowed

/-- §6.2.7: an attribute value matches a pattern. -/
def valueMatch (cx : Context) (p : Pattern) (s : String) : Bool :=
  (nullable p && allWs s) || nullable (textDeriv cx s p)

/-- The derivative with respect to one attribute. -/
def attDeriv (cx : Context) (q : QN) (v : String) : Pattern → Pattern
  | .after a b => mkAfter (attDeriv cx q v a) b
  | .choice a b => mkChoice (attDeriv cx q v a) (attDeriv cx q v b)
  | .group a b => mkChoice (mkGroup (attDeriv cx q v a) b) (mkGroup a (attDeriv cx q v b))
  | .interleave a b =>
    mkChoice (mkInterleave (attDeriv cx q v a) b) (mkInterleave a (attDeriv cx q v b))
  | .oneOrMore p => mkGroup (attDeriv cx q v p) (mkChoice (.oneOrMore p) .empty)
  | .attribute nc p => if nc.contains q && valueMatch cx p v then .empty else .notAllowed
  | _ => .notAllowed

/-- The derivative with respect to the end of the attributes: an attribute
pattern that is still required fails. -/
def startTagCloseDeriv : Pattern → Pattern
  | .after a b => mkAfter (startTagCloseDeriv a) b
  | .choice a b => mkChoice (startTagCloseDeriv a) (startTagCloseDeriv b)
  | .group a b => mkGroup (startTagCloseDeriv a) (startTagCloseDeriv b)
  | .interleave a b => mkInterleave (startTagCloseDeriv a) (startTagCloseDeriv b)
  | .oneOrMore p => mkOneOrMore (startTagCloseDeriv p)
  | .attribute _ _ => .notAllowed
  | p => p

/-- The derivative with respect to an end tag. -/
def endTagDeriv : Pattern → Pattern
  | .choice a b => mkChoice (endTagDeriv a) (endTagDeriv b)
  | .after a b => if nullable a then b else .notAllowed
  | _ => .notAllowed

/-- The string of a content that is one string. -/
def singleText : List Inst → Option String
  | [.text s] => some s
  | _ => none

/-- The derivative with respect to one child (§6.2.7, §6.2.10). `cx` is the
context of the parent, for a string child. -/
def childDeriv (defs : Defs) (cx : Context) (p : Pattern) : Inst → Pattern
  | .text s => textDeriv cx s p
  | .elem qn cx' atts kids =>
    let p1 := startTagOpenDeriv defs qn p
    let p2 := atts.foldl (fun q (an, av) => attDeriv cx' an av q) p1
    let p3 := startTagCloseDeriv p2
    let p4 :=
      if kids.isEmpty then mkChoice p3 (textDeriv cx' "" p3)
      else match singleText kids with
        | some s =>
          let d := textDeriv cx' s p3
          if allWs s then mkChoice p3 d else d
        | none => kids.foldl (fun q k =>
            match k with
            | .text s => if allWs s then q else childDeriv defs cx' q k
            | .elem .. => childDeriv defs cx' q k) p3
    endTagDeriv p4
termination_by i => i

/-- Is the document element valid against the grammar? -/
def validInst (g : Grammar) (root : Inst) : Bool :=
  let defs : Defs := g.defs.foldl (fun m (n, nc, p) => m.insert n (nc, p)) {}
  nullable (childDeriv defs { ns := [] } g.start root)

/-- Is the element `root` (with the namespace declarations of
`initialScope`) valid against the grammar? -/
def validNode (g : Grammar) (root : Node) : Bool :=
  match toInst initialScope root with
  | some i => validInst g i
  | none => false

/-- Is the document text valid against the grammar? A document that is not
well-formed is not valid. -/
def validText (g : Grammar) (txt : String) : Bool :=
  match parseXML txt with
  | .ok d => validNode g d.root
  | .error _ => false

end L4Factoidal.RelaxNG
