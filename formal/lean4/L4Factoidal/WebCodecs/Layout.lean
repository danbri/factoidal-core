/-
L4Factoidal.WebCodecs.Layout: where the bytes of a video frame are, and which byte ranges a copy
reads and writes (WebCodecs §9.4.6, "Parse Visible Rect", "Verify Rect Offset Alignment" and
"Compute Layout and Allocation Size"; record: docs/designissues/2026-11-14-webgl-webcodecs.md,
section 4).

A frame's own bytes (its media resource) are its planes one after another, each row with no
padding: plane `p` of a frame of coded size `cw` × `ch` has `p.codedRows ch` rows of
`p.codedStride cw` bytes. `copyPlan` answers, for a rectangle of the frame and an optional layout
the page asks for, one `Move` for each plane: the rows to copy, with their place in the resource
and their place in the other buffer. The page glue moves those rows and decides nothing: the same
plan serves `copyTo` (resource to the page's buffer) and the constructor (the page's buffer, in the
layout it gives, to the resource; `Move.swap`).

`copyPlan_inBounds` is the security statement: a plan that `copyPlan` answers reads only inside a
resource of `resourceSize` bytes and writes only inside `allocationSize` bytes, for every format,
size, rectangle and layout. The caller's one remaining check is `allocationSize ≤` the size of
the page's buffer.
-/
import L4Factoidal.WebCodecs.Format

namespace L4Factoidal.WebCodecs

structure Rect where
  x : Nat
  y : Nat
  width : Nat
  height : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `PlaneLayout` (§9.7): where a plane starts in a buffer and the bytes from one row to the next. -/
structure PlaneLayout where
  offset : Nat
  stride : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The rows of one plane to copy: `rows` rows of `widthBytes` bytes; row `r` is at
`srcOffset + r * srcStride` in the source and at `dstOffset + r * dstStride` in the destination. -/
structure Move where
  srcOffset : Nat
  srcStride : Nat
  dstOffset : Nat
  dstStride : Nat
  widthBytes : Nat
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Every row of the move lies inside a source of `srcSize` bytes and a destination of `dstSize`. -/
def Move.InBounds (m : Move) (srcSize dstSize : Nat) : Prop :=
  ∀ r, r < m.rows →
    m.srcOffset + r * m.srcStride + m.widthBytes ≤ srcSize ∧
    m.dstOffset + r * m.dstStride + m.widthBytes ≤ dstSize

/-- The same rows copied the other way. -/
def Move.swap (m : Move) : Move :=
  { m with srcOffset := m.dstOffset, srcStride := m.dstStride, dstOffset := m.srcOffset, dstStride := m.srcStride }

/-- `a / b` rounded up. -/
def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The largest `unsigned long` (Web IDL). -/
def maxU32 : Nat := 4294967295

/-- Bytes of one row of the plane in a frame `cw` wide. -/
def Plane.codedStride (p : Plane) (cw : Nat) : Nat := ceilDiv cw p.subW * p.sampleBytes

/-- Rows of the plane in a frame `ch` high. -/
def Plane.codedRows (p : Plane) (ch : Nat) : Nat := ceilDiv ch p.subH

/-- Bytes of a resource with these planes at this coded size. -/
def planesSize (planes : List Plane) (cw ch : Nat) : Nat :=
  planes.foldl (fun a p => a + p.codedStride cw * p.codedRows ch) 0

/-- Bytes of the media resource of a frame of this format and coded size. -/
def resourceSize (f : PixelFormat) (cw ch : Nat) : Nat := planesSize f.planes cw ch

/-- "Verify Rect Offset Alignment": the rectangle starts on a whole sample of every plane. -/
def aligned (planes : List Plane) (r : Rect) : Bool :=
  planes.all fun p => r.x % p.subW == 0 && r.y % p.subH == 0

/-- "Parse Visible Rect", the checks: not empty, inside the coded size, aligned. -/
def rectOk (planes : List Plane) (cw ch : Nat) (r : Rect) : Bool :=
  r.width != 0 && r.height != 0 && decide (r.x + r.width ≤ cw) && decide (r.y + r.height ≤ ch) && aligned planes r

/-- "Compute Layout and Allocation Size", step 6 for one plane: the move of plane `p`, given the
layout the page gave for it (`none`: after what is allocated so far, rows packed), the moves made
before it, the allocation size so far and the bytes of the resource before this plane. `none`: the
layout is refused (a stride smaller than a row, a size over `unsigned long`, or an overlap with an
earlier plane). -/
def planStep (cw : Nat) (rect : Rect) (p : Plane) (l : Option PlaneLayout) (acc : List Move) (alloc src : Nat) :
    Option Move :=
  let rows := ceilDiv rect.height p.subH
  let widthBytes := ceilDiv rect.width p.subW * p.sampleBytes
  let off := (l.map (·.offset)).getD alloc
  let stride := (l.map (·.stride)).getD widthBytes
  if decide (stride < widthBytes) || decide (stride * rows > maxU32) || decide (off + stride * rows > maxU32) ||
      acc.any (fun m => !(decide (off + stride * rows ≤ m.dstOffset) || decide (m.dstOffset + m.dstStride * m.rows ≤ off)))
  then none
  else some
    { srcOffset := src + rect.y / p.subH * p.codedStride cw + rect.x / p.subW * p.sampleBytes,
      srcStride := p.codedStride cw, dstOffset := off, dstStride := stride, widthBytes := widthBytes, rows := rows }

/-- "Compute Layout and Allocation Size", step 6, over the planes. `ls` holds the layouts the page
gave for the planes still to do; `acc` the moves made (latest first), `alloc` the allocation size
so far, `src` the bytes of the resource before the next plane. -/
def planGo (cw ch : Nat) (rect : Rect) :
    List Plane → List (Option PlaneLayout) → List Move → Nat → Nat → Option (List Move × Nat × Nat)
  | [], _, acc, alloc, src => some (acc.reverse, alloc, src)
  | p :: ps, ls, acc, alloc, src =>
    match planStep cw rect p ls.head?.join acc alloc src with
    | none => none
    | some m =>
      planGo cw ch rect ps ls.tail (m :: acc) (max alloc (m.dstOffset + m.dstStride * m.rows))
        (src + p.codedStride cw * p.codedRows ch)

structure Plan where
  /-- One move for each plane, in plane order: resource (source) to the page's buffer (destination). -/
  moves : List Move
  /-- The bytes the page's buffer must have. -/
  allocationSize : Nat
  /-- The bytes of the frame's resource. -/
  resourceSize : Nat
  deriving Repr, Inhabited

/-- The layouts the page gave, one for each plane; `none` when their number is not the planes'. -/
def layoutsOf (planes : List Plane) (layout : Option (List PlaneLayout)) : Option (List (Option PlaneLayout)) :=
  match layout with
  | none => some []
  | some l => if l.length != planes.length then none else some (l.map some)

/-- The plan of a copy of `rect` of a frame with these planes and coded size, into a buffer with
the layout the page gave (`none`: planes packed one after another). `none`: a TypeError of the
API (an empty, outside or unaligned rectangle; a layout with the wrong number of planes; a layout
that `planStep` refuses). -/
def planOf (planes : List Plane) (cw ch : Nat) (rect : Rect) (layout : Option (List PlaneLayout)) : Option Plan :=
  if !rectOk planes cw ch rect then none else
  match layoutsOf planes layout with
  | none => none
  | some ls =>
    (planGo cw ch rect planes ls [] 0 0).map fun r => { moves := r.1, allocationSize := r.2.1, resourceSize := r.2.2 }

def copyPlan (f : PixelFormat) (cw ch : Nat) (rect : Rect) (layout : Option (List PlaneLayout)) : Option Plan :=
  planOf f.planes cw ch rect layout

/-- The layout a plan answers to the page (`copyTo`'s result). -/
def Plan.layout (p : Plan) : List PlaneLayout := p.moves.map fun m => ⟨m.dstOffset, m.dstStride⟩

/-- The reference meaning of a plan: the destination after its rows are copied. The page glue does
the same moves on the page's own buffers; the tests below compare this with the Web Platform Tests'
expected bytes. -/
def applyMoves (src dst : ByteArray) (moves : List Move) : ByteArray :=
  moves.foldl (fun d m =>
    (List.range m.rows).foldl (fun d r =>
      src.copySlice (m.srcOffset + r * m.srcStride) d (m.dstOffset + r * m.dstStride) m.widthBytes) d) dst

/-! ## Theorems -/

/-- A rectangle that starts on a multiple of `s` and ends inside `c`: its samples, counted with
rounding up, end inside the samples of `c`. -/
theorem ceilDiv_split {x w c s : Nat} (hs : 0 < s) (hx : x % s = 0) (h : x + w ≤ c) :
    x / s + ceilDiv w s ≤ ceilDiv c s := by
  unfold ceilDiv
  have hx' : s * (x / s) = x := by
    have := Nat.div_add_mod x s
    omega
  have h1 : (w + s - 1 + s * (x / s)) / s = (w + s - 1) / s + x / s := Nat.add_mul_div_left _ _ hs
  have hle : w + s - 1 + s * (x / s) ≤ c + s - 1 := by omega
  have h2 := Nat.div_le_div_right (c := s) hle
  omega

theorem Move.InBounds.mono {m : Move} {a b a' b' : Nat} (h : m.InBounds a b) (ha : a ≤ a') (hb : b ≤ b') :
    m.InBounds a' b' := by
  intro r hr
  have := h r hr
  exact ⟨Nat.le_trans this.1 ha, Nat.le_trans this.2 hb⟩

theorem Move.InBounds.swap {m : Move} {a b : Nat} (h : m.InBounds a b) : m.swap.InBounds b a := by
  intro r hr
  have := h r hr
  exact ⟨this.2, this.1⟩

/-- What `planStep` answers: the rows of the rectangle in plane `p`, read from the plane's place in
the resource, with a destination stride that holds a row. -/
theorem planStep_spec {cw : Nat} {rect : Rect} {p : Plane} {l : Option PlaneLayout} {acc : List Move}
    {alloc src : Nat} {m : Move} (h : planStep cw rect p l acc alloc src = some m) :
    m.srcOffset = src + rect.y / p.subH * p.codedStride cw + rect.x / p.subW * p.sampleBytes ∧
    m.srcStride = p.codedStride cw ∧ m.widthBytes = ceilDiv rect.width p.subW * p.sampleBytes ∧
    m.rows = ceilDiv rect.height p.subH ∧ m.widthBytes ≤ m.dstStride := by
  simp only [planStep] at h
  split at h
  · cases h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hc
    exact ⟨rfl, rfl, rfl, rfl, hc.1.1.1⟩

/-- The loop invariant of `planGo`: when the moves made so far are in bounds of the resource bytes
and allocation so far, so are all the moves of the answer in the final sizes. -/
theorem planGo_inBounds (cw ch : Nat) (rect : Rect) (hw : rect.x + rect.width ≤ cw) (hh : rect.y + rect.height ≤ ch) :
    ∀ (ps : List Plane) (ls : List (Option PlaneLayout)) (acc : List Move) (alloc src : Nat)
      (moves : List Move) (alloc' src' : Nat),
      (∀ p ∈ ps, 0 < p.subW ∧ 0 < p.subH) →
      (∀ p ∈ ps, rect.x % p.subW = 0 ∧ rect.y % p.subH = 0) →
      (∀ m ∈ acc, m.InBounds src alloc) →
      planGo cw ch rect ps ls acc alloc src = some (moves, alloc', src') →
      ∀ m ∈ moves, m.InBounds src' alloc' := by
  intro ps
  induction ps with
  | nil =>
    intro ls acc alloc src moves alloc' src' _ _ hacc h m hm
    simp only [planGo, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hacc m (List.mem_reverse.mp hm)
  | cons p ps ih =>
    intro ls acc alloc src moves alloc' src' hpos hal hacc h
    have hp := hpos p (List.mem_cons_self)
    have ha := hal p (List.mem_cons_self)
    simp only [planGo] at h
    split at h
    · cases h
    · rename_i m0 hstep
      obtain ⟨hso, hss, hwb, hrows, hfit⟩ := planStep_spec hstep
      refine ih _ _ _ _ _ _ _ (fun q hq => hpos q (List.mem_cons_of_mem _ hq))
        (fun q hq => hal q (List.mem_cons_of_mem _ hq)) ?_ h
      intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · intro r hr
        have hrows' := ceilDiv_split hp.2 ha.2 hh
        have hcols := ceilDiv_split hp.1 ha.1 hw
        constructor
        · -- the source row is inside this plane of the resource
          have hS : rect.x / p.subW * p.sampleBytes + ceilDiv rect.width p.subW * p.sampleBytes ≤ p.codedStride cw := by
            unfold Plane.codedStride
            rw [← Nat.add_mul]
            exact Nat.mul_le_mul_right _ hcols
          have hR : (rect.y / p.subH + r + 1) * p.codedStride cw ≤ p.codedRows ch * p.codedStride cw := by
            apply Nat.mul_le_mul_right
            unfold Plane.codedRows
            omega
          have e1 : (rect.y / p.subH + r + 1) * p.codedStride cw =
              rect.y / p.subH * p.codedStride cw + r * p.codedStride cw + p.codedStride cw := by
            rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          have e2 : p.codedStride cw * p.codedRows ch = p.codedRows ch * p.codedStride cw := Nat.mul_comm _ _
          rw [hso, hss, hwb]
          omega
        · -- the destination row is inside this plane's allocation
          have hD : (r + 1) * m.dstStride ≤ m.rows * m.dstStride := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hD
          have e3 := Nat.mul_comm m.dstStride m.rows
          have hmax := Nat.le_max_right alloc (m.dstOffset + m.dstStride * m.rows)
          omega
      · exact (hacc m hm).mono (Nat.le_add_right _ _) (Nat.le_max_left _ _)

/-- The resource bytes `planGo` answers are those before it plus the planes' sizes: they do not
depend on the rectangle or on the layout asked for. -/
theorem planGo_src (cw ch : Nat) (rect : Rect) :
    ∀ (ps : List Plane) (ls : List (Option PlaneLayout)) (acc : List Move) (alloc src : Nat)
      (moves : List Move) (alloc' src' : Nat),
      planGo cw ch rect ps ls acc alloc src = some (moves, alloc', src') →
      src' = ps.foldl (fun a p => a + p.codedStride cw * p.codedRows ch) src := by
  intro ps
  induction ps with
  | nil =>
    intro ls acc alloc src moves alloc' src' h
    simp only [planGo, Option.some.injEq, Prod.mk.injEq] at h
    simp [h.2.2]
  | cons p ps ih =>
    intro ls acc alloc src moves alloc' src' h
    simp only [planGo] at h
    split at h
    · cases h
    · simpa using ih _ _ _ _ _ _ _ h

theorem rectOk_spec {planes : List Plane} {cw ch : Nat} {r : Rect} (h : rectOk planes cw ch r = true) :
    r.x + r.width ≤ cw ∧ r.y + r.height ≤ ch ∧ ∀ p ∈ planes, r.x % p.subW = 0 ∧ r.y % p.subH = 0 := by
  unfold rectOk aligned at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

/-- Bounds, for any planes with positive sub-sampling factors. -/
theorem planOf_inBounds (planes : List Plane) (hpos : ∀ p ∈ planes, 0 < p.subW ∧ 0 < p.subH)
    (cw ch : Nat) (rect : Rect) (layout : Option (List PlaneLayout)) (pl : Plan)
    (h : planOf planes cw ch rect layout = some pl) :
    (∀ m ∈ pl.moves, m.InBounds pl.resourceSize pl.allocationSize) ∧ pl.resourceSize = planesSize planes cw ch := by
  unfold planOf at h
  split at h
  · cases h
  · rename_i hr
    have hok := rectOk_spec (by simpa using hr)
    split at h
    · cases h
    · rename_i ls _
      cases hgo : planGo cw ch rect planes ls [] 0 0 with
      | none => simp [hgo] at h
      | some t =>
        obtain ⟨moves, alloc, src⟩ := t
        simp only [hgo, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨planGo_inBounds cw ch rect hok.1 hok.2.1 planes ls [] 0 0 moves alloc src hpos hok.2.2
            (fun _ hm => by cases hm) hgo,
          planGo_src cw ch rect planes ls [] 0 0 moves alloc src hgo⟩

/-- Security statement of `copyTo` and of the buffer constructor. Says: for every pixel format,
coded size, rectangle and layout, when `copyPlan` answers a plan, every row of every move of the
plan lies inside a resource of `resourceSize f cw ch` bytes and inside `allocationSize` bytes of
the other buffer. So a caller that holds a resource of that size and checks that the page's buffer
has at least `allocationSize` bytes reads and writes only inside the two buffers. Does not say:
that the page glue performs exactly these moves (it is tested, not proved), nor that the bytes are
the right pixels (`applyMoves` and the tests). -/
theorem copyPlan_inBounds (f : PixelFormat) (cw ch : Nat) (rect : Rect) (layout : Option (List PlaneLayout))
    (pl : Plan) (h : copyPlan f cw ch rect layout = some pl) :
    (∀ m ∈ pl.moves, m.InBounds (resourceSize f cw ch) pl.allocationSize) := by
  have hpos : ∀ p ∈ f.planes, 0 < p.subW ∧ 0 < p.subH := fun p hp =>
    ⟨(f.planes_pos p hp).1, (f.planes_pos p hp).2.1⟩
  have := planOf_inBounds f.planes hpos cw ch rect layout pl h
  unfold resourceSize
  rw [← this.2]
  exact this.1

/-- The same for the constructor, which copies the other way: the page's buffer is the source. -/
theorem copyPlan_inBounds_swap (f : PixelFormat) (cw ch : Nat) (rect : Rect) (layout : Option (List PlaneLayout))
    (pl : Plan) (h : copyPlan f cw ch rect layout = some pl) :
    (∀ m ∈ pl.moves.map Move.swap, m.InBounds pl.allocationSize (resourceSize f cw ch)) := by
  intro m hm
  obtain ⟨m0, hm0, rfl⟩ := List.mem_map.mp hm
  exact (copyPlan_inBounds f cw ch rect layout pl h m0 hm0).swap

/-! ## Tests (`webcodecs/videoFrame-copyTo.any.js`) -/

private def i420 : PixelFormat := .yuv .c420 false .d8
private def bytes (xs : List Nat) : ByteArray := ⟨(xs.map (·.toUInt8)).toArray⟩
private def i420Data : ByteArray := bytes [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
private def run (f : PixelFormat) (cw ch : Nat) (rect : Rect) (layout : Option (List PlaneLayout)) (src : ByteArray)
    (fill : Nat := 0) : Option (List Nat × List (Nat × Nat)) :=
  (copyPlan f cw ch rect layout).map fun pl =>
    ((applyMoves src ⟨Array.replicate pl.allocationSize fill.toUInt8⟩ pl.moves).toList.map (·.toNat),
     pl.layout.map fun l => (l.offset, l.stride))

#guard resourceSize i420 4 2 == 12
-- "Test I420 frame" (default layout).
#guard run i420 4 2 ⟨0, 0, 4, 2⟩ none i420Data == some ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], [(0, 4), (8, 2), (10, 2)])
-- "Test I420 stride and offset work."
#guard run i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨4, 4⟩, ⟨0, 2⟩, ⟨2, 2⟩]) i420Data ==
  some ([9, 10, 11, 12, 1, 2, 3, 4, 5, 6, 7, 8], [(4, 4), (0, 2), (2, 2)])
-- "Test I420 stride and offset with padding."
#guard run i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨9, 5⟩, ⟨1, 3⟩, ⟨5, 3⟩]) i420Data ==
  some ([0, 9, 10, 0, 0, 11, 12, 0, 0, 1, 2, 3, 4, 0, 5, 6, 7, 8, 0], [(9, 5), (1, 3), (5, 3)])
-- "Test incorrect plane count.", "Test invalid stride.", "Test address overflow."
#guard (copyPlan i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨0, 4⟩])).isNone
#guard (copyPlan i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨0, 1⟩, ⟨8, 2⟩, ⟨10, 2⟩])).isNone
#guard (copyPlan i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨0, 4⟩, ⟨8, 2⟩, ⟨4294967294, 2⟩])).isNone
-- "Test empty rect.", "Test invalid rect.", "Test left crop."
#guard (copyPlan i420 4 2 ⟨0, 0, 4, 0⟩ none).isNone
#guard (copyPlan i420 4 2 ⟨0, 0, 4, 4⟩ none).isNone
#guard run i420 4 2 ⟨2, 0, 2, 2⟩ none i420Data == some ([3, 4, 7, 8, 10, 12], [(0, 2), (4, 1), (5, 1)])
-- A rectangle that starts on an odd column is not aligned for 4:2:0.
#guard (copyPlan i420 4 2 ⟨1, 0, 2, 2⟩ none).isNone
-- Overlapping planes are refused.
#guard (copyPlan i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨0, 4⟩, ⟨7, 2⟩, ⟨11, 2⟩])).isNone
-- "Test NV12 stride and offset work."
#guard run .nv12 4 2 ⟨0, 0, 4, 2⟩ (some [⟨4, 4⟩, ⟨0, 4⟩]) i420Data ==
  some ([9, 10, 11, 12, 1, 2, 3, 4, 5, 6, 7, 8], [(4, 4), (0, 4)])
-- "Test RGBA frame."
#guard (run .rgba 2 2 ⟨0, 0, 2, 2⟩ none (bytes (List.range 16))).map (·.2) == some [(0, 8)]
-- Padding keeps what the destination held (the 0xAA test).
#guard (run i420 4 2 ⟨0, 0, 4, 2⟩ (some [⟨9, 5⟩, ⟨1, 3⟩, ⟨5, 3⟩]) i420Data 170).map (·.1.take 4) == some [170, 9, 10, 170]
-- An odd size: chroma rows and columns round up (3 × 3 has 2 × 2 chroma samples).
#guard resourceSize i420 3 3 == 9 + 4 + 4
#guard (copyPlan i420 3 3 ⟨0, 0, 3, 3⟩ none).map (·.allocationSize) == some 17
-- 10-bit samples are two bytes.
#guard resourceSize (.yuv .c420 false .d10) 4 2 == 24

end L4Factoidal.WebCodecs
