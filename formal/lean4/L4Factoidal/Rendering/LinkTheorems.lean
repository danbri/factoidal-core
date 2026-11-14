import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.FloatOrder
import L4Factoidal.FrameCost.Band

/-! # Every link of the page has a region (issue 1268)

2026-11-08: `linkRegions` was called with the viewport height, so a link below the first
screen had no region, and a click on it in the Hub (which scrolls a band of the page with
no new layout) did nothing. Commit 0e4f29e01 passed `max vh result.height`. These
theorems keep it fixed:

- `linkRegions_complete`: a box in an anchor, visible and not empty once clipped, inside
  `[0,width) × [0,height)`, has a region with its anchor's source node and address.
- `linkRegions_complete_document`: at the height `render` uses (`linkHeight`), the
  vertical condition is only that the box ends at or above the foot of the document, for
  any viewport. With the viewport alone this is false (`lowLink` in `Tests.lean`).
- `render_links`, `render_link_complete`: `render`'s links are `linkRegions` at
  `linkHeight vh h`, where `h` is the height of the layout whose boxes `render` returns.
- `moveLinks_*`, `pageLayer`-style moves: a band or a page under a chrome keeps every
  link, same source, address, column and size, moved in `y` only; and a hit at window row
  `y` in a band is the hit of the page's own links at page row `y - top + scroll`, given
  that the move is exact in `Float` (`hitLink_band`).

Record: `docs/designissues/2026-11-08-cost-theorems.md`, section 7. -/
set_option linter.unusedSimpArgs false
namespace L4Factoidal.Rendering.LinkTheorems
open L4Factoidal.Rendering.Layout DOM CSS

/-- The box a link region is cut from: the layout box clipped by its clipping ancestors. -/
def linkBox (dom : Dom) (styles : Array Computed) (boxes : Array Box) (box : Box) : Box :=
  clipLinkBox dom (linkClips dom styles boxes) (dom.size+1) box.source box

theorem clipLinkBox_source (dom : Dom) (clips : Std.TreeMap Nat Box) (fuel id : Nat) (box : Box) :
    (clipLinkBox dom clips fuel id box).source = box.source := by
  induction fuel generalizing id box with
  | zero => rfl
  | succ fuel ih =>
    unfold clipLinkBox
    cases (dom.get id).parent with
    | none => dsimp only; split <;> rfl
    | some p => dsimp only; rw [ih]; split <;> rfl

/-- The regions are the boxes' regions, one per box at most. -/
theorem mem_linkRegions {dom : Dom} {styles : Array Computed} {boxes : Array Box}
    {width height : Float} {r : LinkRegion} :
    r ∈ linkRegions dom styles boxes width height ↔
      ∃ box ∈ boxes, linkRegionOf dom styles (linkClips dom styles boxes) width height box = some r := by
  simp [linkRegions, Array.mem_filterMap]

/-- **Completeness.** A box whose source is in an anchor (`anchorAncestor`), visible, of
positive size once clipped by its ancestors (`c`), and inside `[0,width) × [0,height)` in
both directions, has a region with that anchor's source node and address, whose corner is
the box's corner (moved into the page when it starts above or left of it). -/
theorem linkRegions_complete {dom : Dom} {styles : Array Computed} {boxes : Array Box}
    {width height : Float} {box c : Box} {source : Nat} {href : String}
    (mem : box ∈ boxes)
    (anchor : anchorAncestor dom (dom.size+1) box.source = some (source,href))
    (clipped : c = linkBox dom styles boxes box)
    (visible : (styles[box.source]!).visible = true)
    (wide : 0 < c.width) (tall : 0 < c.height)
    (horizontal : max 0 c.x < min width (c.x+c.width))
    (vertical : max 0 c.y < min height (c.y+c.height)) :
    ∃ r ∈ linkRegions dom styles boxes width height,
      r.sourceNode = source ∧ r.href = href ∧ r.x = max 0 c.x ∧ r.y = max 0 c.y := by
  have same : c.source = box.source := by rw [clipped]; exact clipLinkBox_source ..
  refine ⟨⟨source,href,max 0 c.x,max 0 c.y,min width (c.x+c.width)-max 0 c.x,
    min height (c.y+c.height)-max 0 c.y⟩, ?_, rfl, rfl, rfl, rfl⟩
  refine mem_linkRegions.mpr ⟨box, mem, ?_⟩
  unfold linkRegionOf
  rw [anchor]
  simp only []
  rw [← linkBox, ← clipped, same]
  simp [visible, wide, tall, horizontal, vertical]

/-- **No viewport cut-off.** At the height that `render` passes (`linkHeight vh doc`), a
box that ends at or above the foot of the document `doc` keeps its region, whatever the
viewport height `vh` (`NaN` included). The vertical condition is only that the clipped box
reaches below the top of the page. With `vh` in place of `linkHeight vh doc` (the bug of
2026-11-08) this is false for a box below the viewport. -/
theorem linkRegions_complete_document {dom : Dom} {styles : Array Computed} {boxes : Array Box}
    {width vh doc : Float} {box c : Box} {source : Nat} {href : String}
    (mem : box ∈ boxes)
    (anchor : anchorAncestor dom (dom.size+1) box.source = some (source,href))
    (clipped : c = linkBox dom styles boxes box)
    (visible : (styles[box.source]!).visible = true)
    (wide : 0 < c.width) (tall : 0 < c.height)
    (horizontal : max 0 c.x < min width (c.x+c.width))
    (reaches : max 0 c.y < c.y+c.height)
    (inDocument : c.y+c.height ≤ doc) :
    ∃ r ∈ linkRegions dom styles boxes width (linkHeight vh doc),
      r.sourceNode = source ∧ r.href = href ∧ r.x = max 0 c.x ∧ r.y = max 0 c.y :=
  linkRegions_complete mem anchor clipped visible wide tall horizontal
    (FloatOrder.lt_min_max reaches inDocument)

private theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β}
    (h : x >>= f = .ok v) : ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => exact absurd h (by intro h; cases h)
  | ok a => exact ⟨a, rfl, h⟩

private theorem throw_bind_ne {ε α β : Type} {e : ε} {f : α → Except ε β} {v : β} :
    (throw e >>= f : Except ε β) ≠ .ok v := by
  intro h; cases h

/-- **`renderStyled` keeps links to the foot of the document.** The links of a scene that
it answers are `linkRegions` over the boxes it answers, at the viewport width and at
`linkHeight vh doc`, where `doc` is the height of the layout those boxes come from. -/
theorem renderStyled_links {dom : Dom} {computed : Array Computed} {font : FontProfile} {embedding : Embedding}
    {width height : Nat} {pictures : Pictures} {scene : Scene} {boxes : Array Box}
    (ok : renderStyled dom computed font embedding width height pictures = .ok (scene,boxes)) :
    ∃ (styles : Array Computed) (result : Result),
      layoutRoot dom styles font embedding pictures (Float.ofNat width) (Float.ofNat height) = .ok result ∧
      boxes = result.boxes ∧
      scene.links = linkRegions dom styles (linkSources dom styles boxes) (Float.ofNat width)
        (linkHeight (Float.ofNat height) result.height) := by
  unfold renderStyled at ok
  split at ok
  · exact absurd ok throw_bind_ne
  obtain ⟨result, made, ok⟩ := bind_ok ok
  refine ⟨_, result, made, ?_⟩
  split at ok <;>
  · simp only [] at ok
    split at ok
    · exact absurd ok throw_bind_ne
    split at ok
    · exact absurd ok throw_bind_ne
    cases ok
    exact ⟨rfl, rfl⟩

/-- **`render` keeps links to the foot of the document.** `render` lays out `tree`, the
page's tree with its generated content (`Generated.styled`); the boxes it answers are
boxes of that layout, and the links of its scene are `linkRegions` over all the boxes of
that layout, at the viewport width and at `linkHeight vh doc`, where `doc` is the height
of the layout. -/
theorem render_links {dom : Dom} {rules : List CSS.Rule} {font : FontProfile} {embedding : Embedding}
    {width height : Nat} {textScale : Float} {state : CSS.ElementState} {pictures : Pictures} {treeScope : Option CSS.TreeScope}
    {scene : Scene} {boxes : Array Box}
    (ok : render dom rules font embedding width height textScale state pictures treeScope = .ok (scene,boxes)) :
    ∃ (tree : Dom) (styles : Array Computed) (result : Result),
      layoutRoot tree styles font embedding pictures (Float.ofNat width) (Float.ofNat height) = .ok result ∧
      (∀ box ∈ boxes, box ∈ result.boxes) ∧
      scene.links = linkRegions tree styles (linkSources tree styles result.boxes) (Float.ofNat width)
        (linkHeight (Float.ofNat height) result.height) := by
  unfold render at ok
  obtain ⟨made, -, ok⟩ := bind_ok ok
  obtain ⟨drawn, drew, ok⟩ := bind_ok ok
  obtain ⟨styles, result, laid, same, links⟩ := renderStyled_links (scene := drawn.1) (boxes := drawn.2) drew
  cases ok
  refine ⟨Generated.flattenContents made.1 made.2, styles, result, laid, ?_, same ▸ links⟩
  intro box mem
  rw [← same]
  exact (Array.mem_filter.mp mem).1

/-- A box that link regions are cut from is a box of the layout, and not the box of an
inline box. -/
theorem mem_linkSources {dom : Dom} {styles : Array Computed} {boxes : Array Box} {box : Box} :
    box ∈ linkSources dom styles boxes ↔ box ∈ boxes ∧ isInlineBox dom styles box.source = false := by
  simp [linkSources, Array.mem_filter]

/-- **`render` with every link of the document.** For a scene that `render` answers, a box
of its layout in an anchor (the box of text, of a replaced element, of a block or an
atomic box: `linkSources`), visible, not empty once clipped, inside the viewport's width
and ending at or above the foot of that layout (`result.height`) has a region in the
scene's links, at any viewport height. -/
theorem render_link_complete {dom : Dom} {rules : List CSS.Rule} {font : FontProfile}
    {embedding : Embedding} {width height : Nat} {textScale : Float} {state : CSS.ElementState}
    {pictures : Pictures} {treeScope : Option CSS.TreeScope} {scene : Scene} {boxes : Array Box}
    (ok : render dom rules font embedding width height textScale state pictures treeScope = .ok (scene,boxes)) :
    ∃ (tree : Dom) (styles : Array Computed) (result : Result),
      layoutRoot tree styles font embedding pictures (Float.ofNat width) (Float.ofNat height) = .ok result ∧
      (∀ box ∈ boxes, box ∈ result.boxes) ∧
      ∀ box ∈ linkSources tree styles result.boxes, ∀ (c : Box) (source : Nat) (href : String),
        anchorAncestor tree (tree.size+1) box.source = some (source,href) →
        c = linkBox tree styles (linkSources tree styles result.boxes) box →
        (styles[box.source]!).visible = true → 0 < c.width → 0 < c.height →
        max 0 c.x < min (Float.ofNat width) (c.x+c.width) →
        max 0 c.y < c.y+c.height → c.y+c.height ≤ result.height →
        ∃ r ∈ scene.links, r.sourceNode = source ∧ r.href = href ∧ r.x = max 0 c.x ∧ r.y = max 0 c.y := by
  obtain ⟨tree, styles, result, made, same, links⟩ := render_links ok
  refine ⟨tree, styles, result, made, same, ?_⟩
  intro box mem c source href anchor clipped visible wide tall horizontal reaches inDocument
  rw [links]
  exact linkRegions_complete_document mem anchor clipped visible wide tall horizontal reaches inDocument

/-! ### The algorithm before the theorems

`linkRegions` was a fold that pushed each region; it is now `filterMap` of the region of
each box (`linkRegionOf`), so that the theorems above are about one box at a time. This is
the fold of 0e4f29e01, word for word, and `linkRegions_eq_before` says the two give the
same array: the change of shape changes no render. -/

/-- `linkRegions` as it was at 0e4f29e01. -/
def linkRegionsBefore (dom : Dom) (styles : Array Computed) (boxes : Array Box)
    (width height : Float) : Array LinkRegion :=
  let clipBoxes := boxes.foldl (fun (out : Std.TreeMap Nat Box) box =>
    if (styles[box.source]!).clipOverflow && (dom.get box.source).type == .element then out.insert box.source box else out) {}
  boxes.foldl (fun (out : Array LinkRegion) (box : Box) =>
    match anchorAncestor dom (dom.size+1) box.source with
    | none => out
    | some (source,href) =>
      let box := clipLinkBox dom clipBoxes (dom.size+1) box.source box
      if (styles[box.source]!).visible && box.width > 0 && box.height > 0 then
        let left := max 0 box.x
        let top := max 0 box.y
        let right := min width (box.x+box.width)
        let bottom := min height (box.y+box.height)
        if right > left && bottom > top then out.push ⟨source,href,left,top,right-left,bottom-top⟩ else out
      else out) #[]

private theorem filterMap_eq_foldl {α β : Type} (f : α → Option β) (xs : Array α) :
    xs.filterMap f = xs.foldl (fun out a => match f a with | some b => out.push b | none => out) #[] := by
  apply Array.toList_inj.mp
  rw [Array.toList_filterMap, ← Array.foldl_toList]
  generalize xs.toList = l
  suffices h : ∀ acc : Array β,
      (l.foldl (fun out a => match f a with | some b => out.push b | none => out) acc).toList =
        acc.toList ++ l.filterMap f by simpa using (h #[]).symm
  induction l with
  | nil => intro acc; simp
  | cons a l ih =>
    intro acc
    cases fa : f a with
    | none => simp [List.foldl_cons, fa, ih]
    | some b => simp [List.foldl_cons, fa, ih]

theorem linkRegions_eq_before (dom : Dom) (styles : Array Computed) (boxes : Array Box)
    (width height : Float) :
    linkRegions dom styles boxes width height = linkRegionsBefore dom styles boxes width height := by
  unfold linkRegions linkRegionsBefore linkClips
  rw [filterMap_eq_foldl]
  congr 1
  funext out box
  unfold linkRegionOf
  cases anchorAncestor dom (dom.size+1) box.source with
  | none => rfl
  | some p =>
    obtain ⟨source, href⟩ := p
    dsimp only
    symm
    split
    · rename_i h1
      split
      · rename_i h2; simp only [h1, h2, ↓reduceIte]
      · rename_i h2; simp only [h1, h2, ↓reduceIte]
    · rename_i h1; simp only [h1, ↓reduceIte]

/-! ### A band of the page and a page under the chrome keep every link -/

@[simp] theorem moveLinks_size (f : Float → Float) (links : Array LinkRegion) :
    (moveLinks f links).size = links.size := Array.size_map ..

theorem moveLinks_toList (f : Float → Float) (links : Array LinkRegion) :
    (moveLinks f links).toList = links.toList.map (LinkRegion.moveY f) := Array.toList_map ..

/-- The `i`-th link after the move is the `i`-th link before it: same source node,
address, column, width and height, and the row moved by `f`. -/
theorem moveLinks_getElem (f : Float → Float) (links : Array LinkRegion) (i : Nat)
    (h : i < links.size) :
    (moveLinks f links)[i]'(by simpa using h) = links[i].moveY f ∧
      (links[i].moveY f).sourceNode = links[i].sourceNode ∧ (links[i].moveY f).href = links[i].href ∧
      (links[i].moveY f).x = links[i].x ∧ (links[i].moveY f).width = links[i].width ∧
      (links[i].moveY f).height = links[i].height ∧ (links[i].moveY f).y = f links[i].y :=
  ⟨Array.getElem_map .., rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every link of the page is in the moved list, and nothing else is. -/
theorem mem_moveLinks (f : Float → Float) (links : Array LinkRegion) (r : LinkRegion) :
    r ∈ moveLinks f links ↔ ∃ l ∈ links, l.moveY f = r := Array.mem_map

/-- Window row `y` below the chrome (`top` rows) shows page-layer row `y-top+offset`, with
`offset = scroll-b.top` (`FrameCost.composite`); that is page row `y-top+scroll`. -/
theorem band_row (b : FrameCost.Band) (top scroll y : Nat) (inside : b.top ≤ scroll) :
    y-top+(scroll-b.top)+b.top = y-top+scroll := by omega

/-- **A click in a band is a click on the page.** The page layer of band `b` holds the
page's links moved up by `b.top` (`WebDocument.pageLayer`, `pageLayer_links`). A hit at
page-layer row `row` is the hit of the page's own links at page row `row+b.top`, moved,
when the move is exact in `Float` for each link at that point (`exact`; it holds when the
rows and the link's edges are whole numbers below 2^53). With `band_row`, a click at
window row `y` in the band is the page's link at row `y-top+scroll`. -/
theorem hitLink_band (links : Array LinkRegion) (b : FrameCost.Band) (x : Float) (row : Nat)
    (exact : ∀ r ∈ links.toList,
      (r.moveY (· - Float.ofNat b.top)).contains x (Float.ofNat row) =
        r.contains x (Float.ofNat (row+b.top))) :
    hitLink (moveLinks (· - Float.ofNat b.top) links).toList x (Float.ofNat row) =
      (hitLink links.toList x (Float.ofNat (row+b.top))).map (LinkRegion.moveY (· - Float.ofNat b.top)) := by
  rw [moveLinks_toList]
  exact hitLink_moveY _ _ _ _ _ exact

end L4Factoidal.Rendering.LinkTheorems
