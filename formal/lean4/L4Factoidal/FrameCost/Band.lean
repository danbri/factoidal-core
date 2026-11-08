/-! # The band of a page layer and the composite

The engine's own definitions: `WebDocument` (labs/demos/foafnaut/WebDocument.lean)
imports this module and uses these, so the cost theorems of `FrameCost` are about the
code that draws. Record: `docs/designissues/2026-11-08-cost-theorems.md`. Issue 1268.

With `layers:true` and a shell, a render answers two artifacts. The chrome layer holds
window rows `0 .. top`. The page layer holds the page rows `band.top ..
band.top+band.height`: the page moved up by `band.top`. Each present copies, with
`composite`: window row `y < top` from chrome row `y`, and window row `y ≥ top` from
page row `y-top+offset`, with `offset = scroll-band.top`. A scroll whose view stays in
the band changes only `offset`, so it needs no Lean call.

Only Lean core. -/
namespace L4Factoidal.FrameCost

/-- Page rows that a page layer keeps above and below the view. -/
def bandMargin : Nat := 512
/-- When the view comes this near to an edge of the band that the page goes on past,
the host asks for a new band. -/
def refreshMargin : Nat := 128
/-- A layer is at most this many rows: the texture side that the hosts ask for. -/
def maxLayerRows : Nat := 4096

/-- The page rows of a page layer: from page row `top`, `height` rows. -/
structure Band where
  top : Nat
  height : Nat
  deriving Repr, DecidableEq

/-- The margin of a band for a view of `view` rows. -/
def margin (view : Nat) : Nat := min bandMargin ((maxLayerRows-view)/2)

/-- The band around a view of `view` rows from page row `scroll`. -/
def band (scroll view : Nat) : Band :=
  ⟨scroll-min scroll (margin view),view+2*margin view⟩

/-- True when a view of `view` rows from page row `scroll` is in the band. -/
def Band.fits (b : Band) (view scroll : Nat) : Bool := b.top ≤ scroll && scroll+view ≤ b.top+b.height
/-- The scroll positions that the host shows from this band with no new one. -/
def Band.keepFrom (b : Band) : Nat := if b.top = 0 then 0 else b.top+refreshMargin
def Band.keepTo (b : Band) (view : Nat) : Nat := b.top+b.height-view-refreshMargin
/-- `layer_compositor.keeps`: the band shows this scroll with no new render. -/
def Band.keeps (b : Band) (view scroll : Nat) : Bool :=
  decide (b.keepFrom ≤ scroll) && decide (scroll ≤ b.keepTo view)

/-- Rows that a band made at scroll `s` keeps on each side of `s`
(`scroll_prefetch.keepReach`): 384 for a view of at most 3072 rows. -/
def reach (view : Nat) : Nat := margin view-refreshMargin

theorem band_fits (scroll view : Nat) : (band scroll view).fits view scroll = true := by
  dsimp only [band,Band.fits]
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true (by omega),decide_eq_true (by omega)⟩

theorem band_height_le (scroll view : Nat) (small : view ≤ maxLayerRows) :
    (band scroll view).height ≤ maxLayerRows := by
  simp only [band,margin,maxLayerRows,bandMargin] at *
  omega

/-- Every scroll that the host keeps is in the band. -/
theorem keep_fits (b : Band) (view scroll : Nat) (tall : view ≤ b.height)
    (low : b.keepFrom ≤ scroll) (high : scroll ≤ b.keepTo view) : b.fits view scroll = true := by
  simp only [Band.keepFrom,Band.keepTo,Band.fits,Bool.and_eq_true,decide_eq_true_eq] at *
  split at low <;> omega

/-- What the composite shader writes at window pixel `(x,y)`: `WebDocument.compositeShader`
states the same in WGSL. -/
def composite {α : Type} (chrome page : Nat → Nat → α) (top offset x y : Nat) : α :=
  if y < top then chrome x y else page x (y-top+offset)

/-- The composite is the window. Let `image` be the page drawn in page rows and let
the page layer be that image from row `b.top`. Then the composite at offset
`scroll-b.top` is the chrome over rows `0 .. top`, and below it the page from row
`scroll`: the frame that one render at `scroll` describes. The GPU part, that
drawing the page moved up by `b.top` gives `image` moved up by `b.top`, is checked
by pixel hashes (`scroll_layers_test.ts`), not proved here. -/
theorem composite_eq_frame {α : Type} (image chrome : Nat → Nat → α) (b : Band) (top scroll x y : Nat)
    (inside : b.top ≤ scroll) :
    composite chrome (fun x row => image x (row+b.top)) top (scroll-b.top) x y =
      if y < top then chrome x y else image x (y-top+scroll) := by
  unfold composite
  split
  · rfl
  · dsimp only
    rw [show y-top+(scroll-b.top)+b.top = y-top+scroll by omega]

/-- The composite reads only rows of the page layer, for a view in the band. -/
theorem composite_row_lt (b : Band) (top view scroll y : Nat) (fits : b.fits view scroll = true)
    (below : top ≤ y) (within : y < top+view) : y-top+(scroll-b.top) < b.height := by
  simp only [Band.fits,Bool.and_eq_true,decide_eq_true_eq] at fits
  omega

end L4Factoidal.FrameCost
