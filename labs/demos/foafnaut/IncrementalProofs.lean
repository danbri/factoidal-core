import SVG
import L4Factoidal.FrameCost.Cull
/-! # Incremental equals full: the tile edge lists and the retained compile (issue 513, item 2)

Record: `docs/designissues/2026-11-16-incremental-equals-full.md` (the inventory of cached and
incremental paths, the end-to-end statement and what is open).

`SVG.lean` proves that a filtered edge list gives the full fill wherever the filter keeps every
spanning edge (`pathHitList_eq`), and checks by raster guards that the lists of `tilesOf` do
keep them. This file proves the step between: the filter `edgesMeeting` keeps every spanning
edge at a sample whose local row is inside the band's interval. The order reasoning is
`L4Factoidal.FrameCost.Cull`, proved for any order with `Cull.Laws` and with no hypothesis for
`Int`. Lean's `Float` is opaque, so for `Float` the laws of IEEE 754 comparison are the
hypothesis `L`; nothing here adds an axiom.

Checked by Lean when the engine is built (`build-web-render.sh`). No runtime code. -/
namespace NativeSVG
open L4Factoidal.FrameCost

/-- `edgeMeets` is the generic interval test `Cull.meets` on the two stored end values. -/
theorem edgeMeets_eq_meets (edges : Array (Float × Float)) (lo hi : Float) (i : Nat) :
    edgeMeets edges lo hi i = Cull.meets (edges[i]!).1 (edges[i]!).2 lo hi := by
  unfold edgeMeets Cull.meets Cull.hiOf Cull.loOf; rfl

/-- Kind: equality of a culled path with the full one, under stated Float assumptions.
Says: the fill of a path at sample `q` from the edge list of a band (`edgesMeeting edges lo hi`,
what `Primitive.edgeBands` stores and the scene shader walks) is the fill from every edge, when
(`recorded`) the list was made from the end values the record holds, (`finite`) no end value is
NaN, and (`hlo`, `hhi`) the sample's local row is in the band's interval.
Does not say: that `Laws Float` holds (it is IEEE 754 comparison, assumed: `Float` is opaque);
that the margins of `Primitive.edgeBands` put every sample of the band inside `lo .. hi` (a
rounding bound on the inverse transform, still checked by the raster guards of `SVGRaster`);
anything of a path with a NaN coordinate; anything of the binary32 arithmetic of the GPU. -/
theorem edgesMeeting_fill_eq (L : Cull.Laws Float) (data : Array Float) (base count : Nat)
    (rule : FillRule) (edges : Array (Float × Float)) (lo hi : Float) (q : Float × Float)
    (size : edges.size = count)
    (recorded : ∀ i < count, edges[i]! =
      (data[base+(20+4*i)]!*Float.ofNat 0+data[base+(20+4*i+1)]!*Float.ofNat 1,
       data[base+(22+4*i)]!*Float.ofNat 0+data[base+(22+4*i+1)]!*Float.ofNat 1))
    (finite : ∀ i < count, (edges[i]!).1 ≤ (edges[i]!).1 ∧ (edges[i]!).2 ≤ (edges[i]!).2)
    (hlo : lo ≤ pathSampleY q) (hhi : pathSampleY q ≤ hi) :
    pathHitList data base rule (edgesMeeting edges lo hi) q =
      pathHitList data base rule (List.range count).toArray q := by
  have kept : ∀ i < count, pathEdgeSpans data base q i = true → edgeMeets edges lo hi i = true := by
    intro i hi' hs
    have f := finite i hi'
    rw [edgeMeets_eq_meets]
    rw [recorded i hi'] at f ⊢
    exact Cull.meets_of_spans L f.1 f.2 hlo hhi hs
  have culled := pathHitList_eq data base count rule (edgeMeets edges lo hi) q kept
  have full := pathHitList_eq data base count rule (fun _ => true) q (fun _ _ _ => rfl)
  have all : ∀ l : List Nat, l.filter (fun _ => true) = l := by
    intro l; induction l with
    | nil => rfl
    | cons x rest ih => simp [List.filter, ih]
  rw [all] at full
  rw [edgesMeeting_eq, size, culled, full]
#print axioms edgesMeeting_fill_eq

/-- Kind: equality of the incremental path with the full one, one primitive.
Says: when the item kept from the last frame is the item a fresh compile makes at this index
(up to its key), the reuse answer `Reuse.same` gives exactly the fresh item: the retained
compile's record, bytes, box and tile listing for this primitive are those of a full compile.
Does not say: that the kept item is the fresh one (that needs the reuse rule to imply equal
leaves, `WebPaint.reuseByValue_eq`, and `render` to be a function of the key); anything of
`Reuse.moved`; anything of the whole loop of `compileRetained`. -/
theorem retainItem_same_fresh {κ : Type} (mapping : Mapping) (width height cursor : Nat)
    (key old : κ) (render : Unit → Except String Primitive) (fresh : RetainedItem κ)
    (hk : fresh.key = key) :
    retainItem mapping width height cursor key render (some ({fresh with key := old},.same)) =
      .ok (fresh,false,false) := by
  subst hk; rfl
#print axioms retainItem_same_fresh

end NativeSVG
