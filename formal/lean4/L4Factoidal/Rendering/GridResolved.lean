import L4Factoidal.Rendering.GridLayout
import L4Factoidal.Rendering.ComputedGeneric

/-! The resolved values of `grid-template-columns` and `grid-template-rows` (CSS Grid
Layout 2 §7.2.6): for a grid container that has a box, `getComputedStyle` answers the
used track sizes, not the computed track list. Grid layout leaves them in the
container's fragment as an empty group (`Layout.gridRecordName`); this module finds that
record in a laid-out scene. Nothing here runs unless a script reads one of the two
properties. -/
namespace L4Factoidal.Rendering.Layout

/-- The resolved columns and rows of the grid container `id` in a scene tree, when it
was laid out as one. The walk is a loop over a work list; `fuel` bounds the nodes
visited. -/
def gridRecord (id : Nat) : Nat → List Node → Option (String × String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, .paint _ :: rest => gridRecord id fuel rest
  | fuel + 1, .clipped _ _ _ kids :: rest => gridRecord id fuel (kids ++ rest)
  | fuel + 1, .group label _ kids :: rest =>
    match label with
    | none => gridRecord id fuel (kids ++ rest)
    | some l =>
      if l.startsWith "grid-tracks " then
        match l.splitOn "\t" with
        | [name, cols, rows] =>
          if name == gridRecordName id then some (cols, rows) else gridRecord id fuel (kids ++ rest)
        | _ => gridRecord id fuel (kids ++ rest)
      else gridRecord id fuel (kids ++ rest)

/-- The most scene nodes a search visits (the layout refuses more paint than this). -/
def gridRecordFuel : Nat := 4194304

/-- The resolved value of the `k`-th name of a computed style (`ComputedGeneric.nameLists`)
on `node`, when that name is `grid-template-columns` or `grid-template-rows` and the node
was laid out as a grid container; else `none` (the computed value stands). `tree` is
asked for only for those two names. -/
def gridResolvedAt (tree : Unit → List Node) (node k : Nat) : Option String :=
  let names := ComputedGeneric.nameLists.get
  let name := if k < names.1.size then names.1[k]? else names.2[k - names.1.size]?
  match name with
  | some "grid-template-columns" => (gridRecord node gridRecordFuel (tree ())).map (·.1)
  | some "grid-template-rows" => (gridRecord node gridRecordFuel (tree ())).map (·.2)
  | _ => none

end L4Factoidal.Rendering.Layout
