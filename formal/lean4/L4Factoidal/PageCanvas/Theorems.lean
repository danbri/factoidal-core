/-
L4Factoidal.PageCanvas.Theorems: what Lean proves about Canvas 2D
(record: docs/designissues/2026-11-08-canvas-2d.md, section "Theorems").

1. A canvas draws only inside itself:
   - `Raster.coverage_within`, `Raster.rectCoverage_within`: the pixels a fill covers are
     inside the canvas; `Raster.Draw.visits_within`: so are the pixels a draw visits;
   - `Raster.blendPixel_outside_clip`: a pixel outside the clip region keeps its value;
   - `run_size`: after any display list every canvas's bitmap has `width × height × 4`
     bytes; `Canvas.onBitmap_size`: a draw keeps the size of the bitmap it draws on;
   - `Canvas.emit_pixels`: the host gets pixels only of a canvas's own size, in a rectangle
     inside it (`Box.within_le`; the rectangle is the canvas's damage, issue 1098).
2. `save`/`restore` is a stack: `State.Stack.restore_save`, `restore_setters_save`.
3. Origin-clean flags (HTML §4.12.5.6; origin isolation C2, issue 524, lemma L13 of
   docs/designissues/2026-11-16-origin-isolation.md):
   - `Taint.step_drawImage`, `Run.stepT_drawImage`: `drawImage` of a source that is not
     origin-clean marks the canvas it draws on (the run's current canvas, which the command
     keeps current); `Taint.step_setPattern`, `Taint.step_fillPattern`: so do setting
     `fillStyle`/`strokeStyle` to a pattern that is not origin-clean and a fill with one;
     `Taint.step_bitmapNew`, `Store.answer_pattern`: an `ImageBitmap` or a pattern made from
     a source that is not origin-clean is not;
   - `Taint.step_keeps`, `run_keeps`: a mark stays through every command but new bitmap
     dimensions of that canvas (`init`, HTML: "the bitmap is cleared and its origin-clean
     flag is reset"), `reset()` of it (which clears its bitmap too) and its release;
   - `Store.answer_refused`, `Wire.call_refused`, `Wire.callWords_refused`: every read-back
     of a marked canvas (`getImageData`, `toDataURL`, `toBlob`, `convertToBlob`) answers the
     refusal; `readback_noninterference`, `callWords_noninterference`: so two stores that
     differ in anything but the mark (pixels above all) answer it the same.
   - `Run.frame_marks`, `run_frame_marks`, `Wire.frame_readback_refused`,
     `Wire.frame_readback_noninterference` (origin isolation C2e): a batch that gives a canvas its
     dimensions (`init`) and draws on it a source that is not origin-clean, as the prelude does to
     read a `VideoFrame`'s pixels from a canvas image source (WebCodecs §9.4.2), leaves that canvas
     marked, so op 202 on it is refused whatever any canvas holds.
   Not proved here: that the commands read pixels only of the sources they name (by reading of
   `Run.step` and `Run.source`), and that the prelude turns the refusal into a `SecurityError`
   (a page that changes that can only lose the answer, never get pixels).
-/
import L4Factoidal.PageCanvas.Wire

namespace L4Factoidal.PageCanvas

/-- After any display list, every canvas of the page has a bitmap of its own size. -/
theorem run_size (s : Store) (env : Env) (cmds : Array Cmd) (id : Nat) (c : Canvas)
    (h : (s.run env cmds).canvases[id]? = some c) : c.bitmap.size = c.width * c.height * 4 := by
  simp only [Store.run, Std.HashMap.getElem?_map] at h
  cases hc : ((cmds.foldl Run.stepT { store := s, env, taint := s.taint }).put.store.canvases[id]?) with
  | none => simp [hc] at h
  | some c0 =>
    simp [hc] at h
    subst h
    exact Canvas.fix_size c0

/-- Restore after save with any setters between them gives the canvas's state of the save. -/
theorem canvas_restore_save (c : Canvas) (fs : List (DrawState → DrawState)) (h : c.stack.saved.length < maxSaved) :
    (fs.foldl Stack.set c.stack.save).restore = c.stack := Stack.restore_setters_save c.stack fs h

/-! ### Origin-clean flags -/

theorem markIn_keeps (cs : Std.HashSet Nat) (cur : Option (Nat × Canvas)) (b : Bool) (id : Nat)
    (h : cs.contains id = true) : (markIn cs cur b).contains id = true := by
  unfold markIn
  split
  · rcases cur with _ | ⟨j, c⟩
    · exact h
    · simp [h]
  · exact h

theorem markIn_marks (cs : Std.HashSet Nat) (id : Nat) (c : Canvas) : (markIn cs (some (id, c)) true).contains id = true := by
  simp [markIn]

theorem clearIn_keeps (cs : Std.HashSet Nat) (o : Option Nat) (id : Nat) (h : cs.contains id = true) (ho : o ≠ some id) :
    (clearIn cs o).contains id = true := by
  rcases o with _ | i
  · exact h
  · have : i ≠ id := fun e => ho (e ▸ rfl)
    simp [clearIn, h, this]

theorem Taint.step_canvases (t : Taint) (env : Env) (cur : Option (Nat × Canvas)) (bm : Std.HashMap Nat Bitmap) (cmd : Cmd) :
    (t.step env cur bm cmd).canvases = markIn (clearIn t.canvases (Taint.cleared cur cmd)) cur (t.marks env cur cmd) := rfl

theorem Taint.step_bitmaps (t : Taint) (env : Env) (cur : Option (Nat × Canvas)) (bm : Std.HashMap Nat Bitmap) (cmd : Cmd) :
    (t.step env cur bm cmd).bitmaps = (t.objects env bm cmd).1 := rfl

/-- Kind: security theorem (origin isolation C2). Says: a command that marks (`Taint.marks`) marks
the current canvas, whatever else it does. -/
theorem Taint.step_marks (t : Taint) (env : Env) (id : Nat) (c : Canvas) (bm : Std.HashMap Nat Bitmap) (cmd : Cmd)
    (h : t.marks env (some (id, c)) cmd = true) : (t.step env (some (id, c)) bm cmd).canvases.contains id = true := by
  rw [Taint.step_canvases, h]
  exact markIn_marks _ _ _

/-- Kind: security theorem (origin isolation C2). Says: `drawImage` of a source that is not
origin-clean marks the current canvas. -/
theorem Taint.step_drawImage (t : Taint) (env : Env) (id : Nat) (c : Canvas) (bm : Std.HashMap Nat Bitmap)
    (kind src : Nat) (key : String) (sx sy sw sh dx dy dw dh : Float) (h : t.unclean env kind src key = true) :
    (t.step env (some (id, c)) bm (.drawImage kind src key sx sy sw sh dx dy dw dh)).canvases.contains id = true :=
  Taint.step_marks _ _ _ _ _ _ h

/-- Kind: security theorem (origin isolation C2). Says: setting `fillStyle` or `strokeStyle` to a
pattern that is not origin-clean marks the current canvas (HTML §4.12.5.1.10, the setters). -/
theorem Taint.step_setPattern (t : Taint) (env : Env) (id : Nat) (c : Canvas) (bm : Std.HashMap Nat Bitmap)
    (p : Nat) (h : t.patterns.contains p = true) :
    (t.step env (some (id, c)) bm (.fillObj 2 p)).canvases.contains id = true ∧
    (t.step env (some (id, c)) bm (.strokeObj 2 p)).canvases.contains id = true :=
  ⟨Taint.step_marks _ _ _ _ _ _ (by simp [Taint.marks, h]), Taint.step_marks _ _ _ _ _ _ (by simp [Taint.marks, h])⟩

/-- Kind: security theorem (origin isolation C2). Says: a fill of the current canvas whose fill
style is a pattern that is not origin-clean marks it (whatever named that pattern's id when the
style was set). -/
theorem Taint.step_fillPattern (t : Taint) (env : Env) (id : Nat) (c : Canvas) (bm : Std.HashMap Nat Bitmap)
    (p : Nat) (hs : c.stack.cur.fill = .pattern p) (h : t.patterns.contains p = true) (x y w hh : Float) :
    (t.step env (some (id, c)) bm (.fillRect x y w hh)).canvases.contains id = true :=
  Taint.step_marks _ _ _ _ _ _ (by simp [Taint.marks, Taint.patternIn, hs, h])

/-- Kind: security theorem (origin isolation C2). Says: an `ImageBitmap` made from a source that
is not origin-clean is not origin-clean (HTML §8.10.4 createImageBitmap, OffscreenCanvas
`transferToImageBitmap`). -/
theorem Taint.step_bitmapNew (t : Taint) (env : Env) (cur : Option (Nat × Canvas)) (bm : Std.HashMap Nat Bitmap)
    (id kind src : Nat) (key : String) (data : ByteArray) (sx sy sw sh : Float) (h : t.unclean env kind src key = true) :
    (t.step env cur bm (.bitmapNew id kind src key data sx sy sw sh)).bitmaps.contains id = true := by
  rw [Taint.step_bitmaps]
  simp [Taint.objects, h]

/-- Only new dimensions of a canvas, `reset()` of the current one and a release clear a flag. -/
theorem Taint.cleared_ne (cur : Option (Nat × Canvas)) (cmd : Cmd) (id : Nat)
    (hi : ∀ w hh e, cmd ≠ .init id w hh e) (hr : cmd = .reset → cur.map (·.1) ≠ some id) (hl : cmd ≠ .release 5 id) :
    Taint.cleared cur cmd ≠ some id := by
  cases cmd with
  | init i w hh e =>
    intro hc
    simp only [Taint.cleared, Option.some.injEq] at hc
    exact hi w hh e (hc ▸ rfl)
  | reset => exact hr rfl
  | release k i =>
    intro hc
    simp only [Taint.cleared] at hc
    split at hc
    · next hk =>
      simp only [Option.some.injEq] at hc
      exact hl (by rw [beq_iff_eq.mp hk, hc])
    · exact absurd hc (by simp)
  | _ => simp [Taint.cleared]

/-- Kind: security theorem (origin isolation C2). Says: a mark on a canvas stays through any
command but new bitmap dimensions of that canvas, `reset()` while it is current, and its
release (each of which leaves no pixels of it: a cleared bitmap, or none). -/
theorem Taint.step_keeps (t : Taint) (env : Env) (cur : Option (Nat × Canvas)) (bm : Std.HashMap Nat Bitmap)
    (cmd : Cmd) (id : Nat) (h : t.canvases.contains id = true)
    (hi : ∀ w hh e, cmd ≠ .init id w hh e) (hr : cmd = .reset → cur.map (·.1) ≠ some id) (hl : cmd ≠ .release 5 id) :
    (t.step env cur bm cmd).canvases.contains id = true := by
  rw [Taint.step_canvases]
  exact markIn_keeps _ _ _ _ (clearIn_keeps _ _ _ h (Taint.cleared_ne cur cmd id hi hr hl))

/-- The flags after a command are `Taint.step` of the flags before it. -/
theorem Run.stepT_taint (r : Run) (cmd : Cmd) : (r.stepT cmd).taint = r.taint.step r.env r.cur r.store.bitmaps cmd := rfl

theorem Run.sourceKept_cur (r : Run) (kind src : Nat) (key : String) : (r.sourceKept kind src key).1.cur = r.cur := by
  unfold Run.sourceKept
  dsimp only
  split
  · rfl
  · rcases r.source kind src key with _ | _ <;> rfl

theorem Run.withCur_cur (r : Run) (f : Canvas → Run → Canvas × Run) : (r.withCur f).cur.map (·.1) = r.cur.map (·.1) := by
  unfold Run.withCur
  split <;> simp_all

/-- `drawImage` keeps the current canvas current: the canvas whose pixels it changes. -/
theorem Run.step_drawImage_cur (r : Run) (kind src : Nat) (key : String) (sx sy sw sh dx dy dw dh : Float) :
    (r.step (.drawImage kind src key sx sy sw sh dx dy dw dh)).cur.map (·.1) = r.cur.map (·.1) := by
  have := Run.sourceKept_cur r kind src key
  simp only [Run.step]
  rcases hk : r.sourceKept kind src key with ⟨r', _ | img⟩
  · rw [hk] at this
    exact congrArg (Option.map (·.1)) this
  · rw [hk] at this
    dsimp only
    rw [Run.withCur_cur]
    exact congrArg (Option.map (·.1)) this

/-- Kind: security theorem (origin isolation C2). Says: after `drawImage` of a source that is not
origin-clean on a run whose current canvas is `id`, `id` is still the current canvas (the one
the image was drawn on) and it is marked. -/
theorem Run.stepT_drawImage (r : Run) (id : Nat) (c : Canvas) (hc : r.cur = some (id, c))
    (kind src : Nat) (key : String) (sx sy sw sh dx dy dw dh : Float) (h : r.taint.unclean r.env kind src key = true) :
    (r.stepT (.drawImage kind src key sx sy sw sh dx dy dw dh)).taint.canvases.contains id = true ∧
    (r.stepT (.drawImage kind src key sx sy sw sh dx dy dw dh)).cur.map (·.1) = some id := by
  refine ⟨?_, ?_⟩
  · rw [Run.stepT_taint, hc]; exact Taint.step_drawImage _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  · show (r.step _).cur.map (·.1) = _
    rw [Run.step_drawImage_cur, hc]; rfl

/-- The flags `Store.run` leaves are those the run of its commands ends with. -/
theorem run_taint (s : Store) (env : Env) (cmds : Array Cmd) :
    (s.run env cmds).taint = (cmds.foldl Run.stepT { store := s, env, taint := s.taint }).taint := by
  simp only [Store.run, Run.put]
  split <;> rfl

/-- Kind: security theorem (origin isolation C2). Says: a canvas marked before a display list
is marked after it, when the list gives that canvas no new dimensions, has no `reset()` and
does not release it. -/
theorem run_keeps (s : Store) (env : Env) (cmds : Array Cmd) (id : Nat) (h : s.taint.canvases.contains id = true)
    (hcmds : ∀ cmd ∈ cmds, (∀ w hh e, cmd ≠ .init id w hh e) ∧ cmd ≠ .reset ∧ cmd ≠ .release 5 id) :
    (s.run env cmds).taint.canvases.contains id = true := by
  rw [run_taint]
  apply Array.foldl_induction (motive := fun _ (r : Run) => r.taint.canvases.contains id = true)
  · exact h
  · intro i r hr
    have hm := hcmds cmds[i] (Array.getElem_mem i.isLt)
    rw [Run.stepT_taint]
    exact Taint.step_keeps _ _ _ _ _ _ hr hm.1 (fun e => absurd e hm.2.1) hm.2.2

/-- Kind: security theorem (origin isolation C2). Says: a read-back of a canvas that is not
origin-clean answers nothing and changes nothing. -/
theorem Store.answer_refused (s : Store) (env : Env) (q : Query) (h : s.refuses q = true) : s.answer env q = (s, "") := by
  simp [Store.answer, h]

/-- The read-backs: `getImageData` (by text) and the encodings (`toDataURL`, `toBlob`, `convertToBlob`). -/
theorem Store.refuses_readback (s : Store) (id : Nat) (x y : Int) (w h : Nat) (type : String) :
    s.refuses (.imageData id x y w h) = s.taint.canvases.contains id ∧ s.refuses (.dataURL id type) = s.taint.canvases.contains id :=
  ⟨rfl, rfl⟩

/-- Kind: security theorem (origin isolation C2, noninterference). Says: two stores whose canvas
`q` reads is not origin-clean answer the read-back the same, whatever else they hold (their
pixels above all). -/
theorem readback_noninterference (s s' : Store) (env env' : Env) (q : Query) (h : s.refuses q = true)
    (h' : s'.refuses q = true) : (s.answer env q).2 = (s'.answer env' q).2 := by
  rw [Store.answer_refused s env q h, Store.answer_refused s' env' q h']

/-- Kind: security theorem (origin isolation C2). Says: `createPattern` of a source that is not
origin-clean makes a pattern that is not (HTML §4.12.5.1.10: "If image is not origin-clean, then
mark pattern as not origin-clean"). -/
theorem Store.answer_pattern (s : Store) (env : Env) (id kind src : Nat) (key rep : String)
    (h : s.taint.unclean env kind src key = true) :
    (s.answer env (.pattern id kind src key rep)).1.taint.patterns.contains id = true := by
  simp only [Store.answer, Store.refuses, Bool.false_eq_true, if_false, h, if_true]
  split <;> (try split) <;> (try split) <;> simp

namespace Wire

/-- Kind: security theorem (origin isolation C2). Says: the import's query of a read-back of a
canvas that is not origin-clean answers the refusal and leaves the store as it was. -/
theorem call_refused (s : Store) (env : Env) (op : Nat) (bytes : ByteArray) (p : Parts) (q : Query)
    (hp : parts bytes (op == textBatchOp) = .ok p) (hb : (op == batchOp || op == textBatchOp) = false)
    (hq : query p = .ok q) (h : s.refuses q = true) : call s env op bytes = (s, refusal) := by
  simp [call, hp, hb, hq, h]

/-- Kind: security theorem (origin isolation C2). Says: op 202 (`getImageData` as bytes) of a
canvas that is not origin-clean is refused with "SecurityError", whatever the canvas holds. -/
theorem callWords_refused (s : Store) (bytes : ByteArray) (p : Parts) (id : Nat) (x y : Int) (w h : Nat)
    (hp : parts bytes = .ok p) (hq : query p = .ok (.imageData id x y w h)) (ht : s.taint.canvases.contains id = true) :
    callWords s wordsOp bytes = .error "SecurityError" := by
  simp [callWords, hp, hq, ht, bind, Except.bind] <;> rfl

/-- Kind: security theorem (origin isolation C2, noninterference). Says: two stores in which the
canvas op 202 names is not origin-clean answer it the same. -/
theorem callWords_noninterference (s s' : Store) (bytes : ByteArray) (p : Parts) (id : Nat) (x y : Int) (w h : Nat)
    (hp : parts bytes = .ok p) (hq : query p = .ok (.imageData id x y w h)) (ht : s.taint.canvases.contains id = true)
    (ht' : s'.taint.canvases.contains id = true) : callWords s wordsOp bytes = callWords s' wordsOp bytes := by
  rw [callWords_refused s bytes p id x y w h hp hq ht, callWords_refused s' bytes p id x y w h hp hq ht']

end Wire

/-! ### A frame of a source that is not origin-clean (origin isolation C2e)

The prelude reads the pixels of a canvas image source for a `VideoFrame` (WebCodecs §9.4.2,
"Initialize Frame From Other Frame", the image case; `pixelsOf`) by one batch that gives a
scratch canvas its dimensions (`init`) and draws the source on it (`drawImage`), then op 202 on
the scratch canvas. These theorems say that for a source that is not origin-clean, that read is
refused, whatever any canvas holds. -/

theorem Run.put_cur (r : Run) : r.put.cur = none := by
  unfold Run.put
  split <;> simp_all

theorem Run.put_env (r : Run) : r.put.env = r.env := by
  unfold Run.put
  split <;> rfl

theorem Run.put_of_none (r : Run) (h : r.cur = none) : r.put = r := by
  unfold Run.put
  split <;> simp_all

theorem Run.take_env (r : Run) (id : Nat) : (r.take id).env = r.env := by
  unfold Run.take
  dsimp only
  split <;> exact Run.put_env r

/-- `init` gives the canvas its dimensions and makes it the current one; the run's other
fields stay. -/
theorem Run.step_init_cur (r : Run) (id w h : Nat) (e : Bool) :
    (r.step (.init id w h e)).cur.map (·.1) = some id := by
  simp only [Run.step, Run.take]
  rw [Run.put_of_none _ (by simp [Run.put_cur])]
  simp

theorem Run.step_init_env (r : Run) (id w h : Nat) (e : Bool) : (r.step (.init id w h e)).env = r.env := by
  simp only [Run.step]
  rw [Run.take_env]
  exact Run.put_env r

/-- `init` clears the mark of its own canvas and of no other; bitmap flags stay. -/
theorem Run.stepT_init_taint (r : Run) (id w h : Nat) (e : Bool) :
    (r.stepT (.init id w h e)).taint.canvases = r.taint.canvases.erase id ∧
    (r.stepT (.init id w h e)).taint.bitmaps = r.taint.bitmaps := by
  refine ⟨?_, ?_⟩
  · rw [Run.stepT_taint, Taint.step_canvases]
    simp [Taint.cleared, Taint.marks, clearIn, markIn]
  · rw [Run.stepT_taint, Taint.step_bitmaps]
    simp [Taint.objects]

/-- A source that is not origin-clean before `init` of another canvas is not after it. -/
theorem Run.stepT_init_unclean (r : Run) (id w h : Nat) (e : Bool) (kind src : Nat) (key : String)
    (hu : r.taint.unclean r.env kind src key = true) (hne : kind = 1 → src ≠ id) :
    (r.stepT (.init id w h e)).taint.unclean (r.stepT (.init id w h e)).env kind src key = true := by
  have ⟨hc, hb⟩ := Run.stepT_init_taint r id w h e
  have he : (r.stepT (.init id w h e)).env = r.env := Run.step_init_env r id w h e
  rw [he]
  unfold Taint.unclean at hu ⊢
  rw [hc, hb]
  split at hu
  · have hs : src ≠ id := hne rfl
    have hb' : (id == src) = false := beq_false_of_ne (Ne.symm hs)
    simp [Std.HashSet.contains_erase, hu, hb']
  · simpa using hu
  · simpa using hu
  · simp at hu

/-- Kind: security theorem (origin isolation C2e). Says: in any batch, `init` of a canvas and
then `drawImage` on it of a source that is not origin-clean (another canvas, an `ImageBitmap`
or an image) leaves that canvas current and marked. -/
theorem Run.frame_marks (r : Run) (id w h : Nat) (e : Bool) (kind src : Nat) (key : String)
    (sx sy sw sh dx dy dw dh : Float) (hu : r.taint.unclean r.env kind src key = true)
    (hne : kind = 1 → src ≠ id) :
    (((r.stepT (.init id w h e)).stepT (.drawImage kind src key sx sy sw sh dx dy dw dh)).taint.canvases.contains id = true) ∧
    ((r.stepT (.init id w h e)).stepT (.drawImage kind src key sx sy sw sh dx dy dw dh)).cur.map (·.1) = some id := by
  have hcur : (r.stepT (.init id w h e)).cur.map (·.1) = some id := Run.step_init_cur r id w h e
  rcases hk : (r.stepT (.init id w h e)).cur with _ | ⟨j, c⟩
  · rw [hk] at hcur; simp at hcur
  · rw [hk] at hcur
    simp only [Option.map_some, Option.some.injEq] at hcur
    subst hcur
    exact Run.stepT_drawImage _ j c hk kind src key sx sy sw sh dx dy dw dh
      (Run.stepT_init_unclean r j w h e kind src key hu hne)

/-- Kind: security theorem (origin isolation C2e). Says: after a batch that ends with `init` of
canvas `id` and `drawImage` on it of a source that is not origin-clean when the batch reaches
them, `id` is not origin-clean. -/
theorem run_frame_marks (s : Store) (env : Env) (pre : Array Cmd) (id w h : Nat) (e : Bool) (kind src : Nat)
    (key : String) (sx sy sw sh dx dy dw dh : Float)
    (hu : (pre.foldl Run.stepT { store := s, env, taint := s.taint }).taint.unclean
      (pre.foldl Run.stepT { store := s, env, taint := s.taint }).env kind src key = true)
    (hne : kind = 1 → src ≠ id) :
    (s.run env (pre ++ #[.init id w h e, .drawImage kind src key sx sy sw sh dx dy dw dh])).taint.canvases.contains id = true := by
  rw [run_taint, Array.foldl_append]
  exact (Run.frame_marks _ id w h e kind src key sx sy sw sh dx dy dw dh hu hne).1

/-- The batch of `pixelsOf` alone: a source that is not origin-clean in the store. -/
theorem run_frame_marks_alone (s : Store) (env : Env) (id w h : Nat) (e : Bool) (kind src : Nat)
    (key : String) (sx sy sw sh dx dy dw dh : Float) (hu : s.taint.unclean env kind src key = true)
    (hne : kind = 1 → src ≠ id) :
    (s.run env #[.init id w h e, .drawImage kind src key sx sy sw sh dx dy dw dh]).taint.canvases.contains id = true :=
  run_frame_marks s env #[] id w h e kind src key sx sy sw sh dx dy dw dh hu hne

namespace Wire

/-- Kind: security theorem (origin isolation C2e). Says: op 202 on the scratch canvas of a
`VideoFrame` read (a batch ending with its `init` and a `drawImage` of a source that is not
origin-clean) is refused with "SecurityError", whatever the canvases hold. -/
theorem frame_readback_refused (s : Store) (env : Env) (pre : Array Cmd) (id w h : Nat) (e : Bool) (kind src : Nat)
    (key : String) (sx sy sw sh dx dy dw dh : Float)
    (hu : (pre.foldl Run.stepT { store := s, env, taint := s.taint }).taint.unclean
      (pre.foldl Run.stepT { store := s, env, taint := s.taint }).env kind src key = true)
    (hne : kind = 1 → src ≠ id) (bytes : ByteArray) (p : Parts) (x y : Int) (qw qh : Nat)
    (hp : parts bytes = .ok p) (hq : query p = .ok (.imageData id x y qw qh)) :
    callWords (s.run env (pre ++ #[.init id w h e, .drawImage kind src key sx sy sw sh dx dy dw dh])) wordsOp bytes =
      .error "SecurityError" :=
  callWords_refused _ bytes p id x y qw qh hp hq (run_frame_marks s env pre id w h e kind src key sx sy sw sh dx dy dw dh hu hne)

/-- Kind: security theorem (origin isolation C2e, noninterference). Says: two pages whose
`VideoFrame` read draws a source that is not origin-clean get the same answer to it, whatever
their pixels (so no pixel of the source reaches the frame). -/
theorem frame_readback_noninterference (s s' : Store) (env env' : Env) (pre pre' : Array Cmd) (id w h : Nat) (e : Bool)
    (kind src : Nat) (key : String) (sx sy sw sh dx dy dw dh : Float)
    (hu : (pre.foldl Run.stepT { store := s, env, taint := s.taint }).taint.unclean
      (pre.foldl Run.stepT { store := s, env, taint := s.taint }).env kind src key = true)
    (hu' : (pre'.foldl Run.stepT { store := s', env := env', taint := s'.taint }).taint.unclean
      (pre'.foldl Run.stepT { store := s', env := env', taint := s'.taint }).env kind src key = true)
    (hne : kind = 1 → src ≠ id) (bytes : ByteArray) (p : Parts) (x y : Int) (qw qh : Nat)
    (hp : parts bytes = .ok p) (hq : query p = .ok (.imageData id x y qw qh)) :
    callWords (s.run env (pre ++ #[.init id w h e, .drawImage kind src key sx sy sw sh dx dy dw dh])) wordsOp bytes =
      callWords (s'.run env' (pre' ++ #[.init id w h e, .drawImage kind src key sx sy sw sh dx dy dw dh])) wordsOp bytes := by
  rw [frame_readback_refused s env pre id w h e kind src key sx sy sw sh dx dy dw dh hu hne bytes p x y qw qh hp hq,
    frame_readback_refused s' env' pre' id w h e kind src key sx sy sw sh dx dy dw dh hu' hne bytes p x y qw qh hp hq]

end Wire

#print axioms Taint.step_marks
#print axioms Taint.step_drawImage
#print axioms Taint.step_setPattern
#print axioms Taint.step_fillPattern
#print axioms Taint.step_bitmapNew
#print axioms Taint.step_keeps
#print axioms Run.stepT_drawImage
#print axioms run_keeps
#print axioms Store.answer_refused
#print axioms readback_noninterference
#print axioms Store.answer_pattern
#print axioms Wire.call_refused
#print axioms Wire.callWords_refused
#print axioms Wire.callWords_noninterference
#print axioms Run.frame_marks
#print axioms run_frame_marks
#print axioms run_frame_marks_alone
#print axioms Wire.frame_readback_refused
#print axioms Wire.frame_readback_noninterference

#print axioms coverage_within
#print axioms rectCoverage_within
#print axioms Draw.visits_within
#print axioms blendPixel_outside_clip
#print axioms run_size
#print axioms Canvas.onBitmap_size
#print axioms emit_pixels
#print axioms Stack.restore_save
#print axioms Stack.restore_setters_save
#print axioms canvas_restore_save

end L4Factoidal.PageCanvas
