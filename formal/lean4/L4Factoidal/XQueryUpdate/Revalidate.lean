/-
L4Factoidal.XQueryUpdate.Revalidate — `upd:revalidate` (XQuery Update
Facility 3.0 §8.2.4, https://www.w3.org/TR/xquery-update-30/).

After `applyUpdates` has rebuilt a document or a copy, it is validated
again with the revalidation mode of the static context (§3.1):
`strict` and `lax` use the in-scope schema through the schema hook
(`XPath4.SchemaHook.validateIn`, `L4Factoidal.XSD11`); `skip` keeps the
result of `upd:removeType` (§8.2.5), which `applyUpdates` has applied.
The default mode is implementation-defined (§3.1, "Overwritable"); here
it is `skip`, so a module without `declare revalidation` does not
validate (`Expr.revalMode`).

The typed values and annotations of the validated tree are copied back
to the nodes of the updated tree when the two trees have the same
nodes; when validation added nodes (default attributes, §8.2.4 step 3),
the validated tree replaces the updated one.
-/
import L4Factoidal.XQueryUpdate.Expr

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4

/-- Does any node of the document carry a type annotation? -/
def docHasTypes (d : Doc) : Bool := d.nodes.any (fun r => r.tann.isSome)

/-- Copy the type properties of `v` (the validated tree, `off` records
    in front) to `d`. -/
def copyTypes (d v : Doc) (off : Nat) : Doc :=
  { d with nodes := d.nodes.mapIdx (fun i r =>
      let x := v.nodes.getD (i + off) r
      { r with tann := x.tann, tval := x.tval, nilled := x.nilled, noTypedValue := x.noTypedValue }) }

/-- Whitespace-only text children of an element with element-only
    content (`noTypedValue`, set by validation) are not part of the
    validated tree (XDM 3.1 §6.7.3, text nodes from a PSVI). -/
def stripElementOnlyWs : Nat → XT → XT
  | 0, t => t
  | f + 1, .el r ats ks =>
    let isWsText (k : XT) : Bool := match k with
      | .lf x => x.kind == .text && x.value.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
      | _ => false
    let ks := if r.kind == .element && r.noTypedValue then ks.filter (fun k => !isWsText k) else ks
    .el r ats (ks.map (stripElementOnlyWs f))
  | _, t => t

/-- A validated document without the whitespace of element-only content. -/
def stripDocWs (d : Doc) : Doc :=
  docOfXT d (stripElementOnlyWs 100000 (({ docs := #[d] } : Env).readXT 100000 (NodeRef.mk' 0 0)))

/-- Revalidate one rebuilt document. -/
def revalidateDoc (env : Env) (mode : String) (d : Doc) : M Doc := do
  if mode == "skip" then return d
  match env.schema.validateIn with
  | none => return d
  | some f =>
    let root := d.get 0
    let v ← match f mode d 0 d.uri with
      | .ok v => pure v
      | .error e => err (if e.code == "FODC0007" then "XQDY0027" else e.code) e.msg
    if root.kind == .document then
      if v.nodes.size == d.nodes.size then return stripDocWs (copyTypes d v 0)
      else return stripDocWs { v with uri := d.uri }
    else
      if v.nodes.size == d.nodes.size + 1 then return stripDocWs (copyTypes d v 1)
      else
        -- validation added nodes: the validated element is the new tree
        let t := ({ docs := #[v] } : Env).readXT 100000 (NodeRef.mk' 0 1)
        return docOfXT d (stripElementOnlyWs 100000 t)

/-- `upd:revalidate` for every document that `applyUpdates` changed. -/
def revalidate (env : Env) (mode : String) (a : Applied) : M Applied := do
  if mode == "skip" then return a
  let mut out := a
  for i in a.changed do
    let nd' ← revalidateDoc env mode (a.env.docs.getD i default)
    out := { out with env := { out.env with docs := out.env.docs.set! i nd' } }
  let mut rts : List (Nat × Doc) := []
  for (dn, nd) in a.rt do
    rts := rts ++ [(dn, ← revalidateDoc env mode nd)]
  pure { out with rt := rts }

end L4Factoidal.XQueryUpdate
