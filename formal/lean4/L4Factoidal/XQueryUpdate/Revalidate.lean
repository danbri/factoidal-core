/-
L4Factoidal.XQueryUpdate.Revalidate — `upd:revalidate` (XQuery Update
Facility 3.0 §8.2.4, https://www.w3.org/TR/xquery-update-30/).

After `applyUpdates` has rebuilt a document, a document that carried
type annotations before the update is validated again with the
revalidation mode of the static context (§3.1): `strict` and `lax` use
the in-scope schema through the schema hook (`XPath4.SchemaHook.validateIn`,
`L4Factoidal.XSD11`); `skip` keeps the result of `upd:removeType`
(§8.2.5), which `applyUpdates` has applied. A document with no type
annotation has no type information to recover, so it is not validated.

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

/-- Revalidate one rebuilt document; `old` is the document before the
    update. -/
def revalidateDoc (env : Env) (mode : String) (old d : Doc) : M Doc := do
  if mode == "skip" || !docHasTypes old then return d
  match env.schema.validateIn with
  | none => return d
  | some f =>
    let root := d.get 0
    let v ← match f mode d 0 d.uri with
      | .ok v => pure v
      | .error e => err (if e.code == "FODC0007" then "XQDY0027" else e.code) e.msg
    if root.kind == .document then
      if v.nodes.size == d.nodes.size then return copyTypes d v 0
      else return { v with uri := d.uri }
    else
      if v.nodes.size == d.nodes.size + 1 then return copyTypes d v 1
      else return d

/-- `upd:revalidate` for every document that `applyUpdates` changed. -/
def revalidate (env : Env) (mode : String) (a : Applied) : M Applied := do
  if mode == "skip" then return a
  let mut out := a
  for i in a.changed do
    let nd' ← revalidateDoc env mode (env.docs.getD i default) (a.env.docs.getD i default)
    out := { out with env := { out.env with docs := out.env.docs.set! i nd' } }
  pure out

end L4Factoidal.XQueryUpdate
