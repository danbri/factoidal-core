/-
L4Factoidal.XSLT4.Strip — whitespace stripping of source documents
(XSLT 4.0 §4.3, `xsl:strip-space` and `xsl:preserve-space`). Moved from
`XSLT4.Transform` unchanged, so that `XSLT4.Interp` can strip the document
that `xsl:source-document` reads (§4.3 applies to every source document).

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28).
-/
import L4Factoidal.XSLT4.Ast

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-! ## Whitespace stripping (§4.3) -/

/-- A copy of `d` with only the nodes `keep` admits (indices remapped,
    document order kept). -/
def filterDoc (d : Doc) (keep : Nat → Bool) : Doc := Id.run do
  let sz := d.nodes.size
  let mut newIdx : Array (Option Nat) := Array.replicate sz none
  let mut pre : Array Nat := Array.replicate (sz + 1) 0
  let mut k := 0
  for i in [0:sz] do
    if keep i then
      newIdx := newIdx.set! i (some k)
      k := k + 1
    pre := pre.set! (i + 1) k
  let mut out : Array NRec := #[]
  for i in [0:sz] do
    if keep i then
      let r := d.get i
      let mp (j : Nat) : Option Nat := newIdx.getD j none
      let lastNew := pre.getD (r.last + 1) k
      let nl := if lastNew == 0 then 0 else lastNew - 1
      out := out.push { r with parent := r.parent.bind mp, children := r.children.filterMap mp, attrs := r.attrs.filterMap mp, last := nl }
  return { d with nodes := out }

def nameTestPrio : NameTest → Float
  | .name _ => 0
  | .ns _ | .loc _ => -0.25
  | .any => -0.5

/-- Is a whitespace text node with parent element `p` stripped? -/
def stripsUnder (S : Sheet) (d : Doc) (p : Nat) : Bool := Id.run do
  let r := d.get p
  if r.kind != .element then return false
  -- xml:space on the element or its nearest ancestor that has one
  let mut cur : Option Nat := some p
  for _ in [0:100000] do
    match cur with
    | none => break
    | some j =>
      let x := d.get j
      for a in x.attrs.toList do
        let ar := d.get a
        if ar.name.uri == nsXML && ar.name.loc == "space" then
          if ar.value.trimAscii.toString == "preserve" then return false
          if ar.value.trimAscii.toString == "default" then cur := none
      if cur.isNone then break
      cur := x.parent
  let mut best : Option (Nat × Float × Bool) := none
  for (t, strip, prec) in S.space do
    if !(nameTestMatches t r.name) then continue
    let pr := nameTestPrio t
    match best with
    | none => best := some (prec, pr, strip)
    | some (bp, bpr, _) =>
      if prec > bp || (prec == bp && pr ≥ bpr) then best := some (prec, pr, strip)
  match best with
  | some (_, _, s) => return s
  | none => return false

def stripDoc (S : Sheet) (d : Doc) : Doc :=
  if S.space.isEmpty || !(S.space.any (·.2.1)) then d else
  filterDoc d (fun i =>
    let r := d.get i
    if r.kind != .text || !(r.value.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')) then true
    else match r.parent with
      | some p => !(stripsUnder S d p)
      | none => true)

end L4Factoidal.XSLT4
