/-
L4Factoidal.PageCanvas.Theorems: what Lean proves about Canvas 2D
(record: docs/designissues/2026-11-08-canvas-2d.md, section "Theorems").

1. A canvas draws only inside itself:
   - `Raster.coverage_within`, `Raster.rectCoverage_within`: the pixels a fill covers are
     inside the canvas; `Raster.Draw.visits_within`: so are the pixels a draw visits;
   - `Raster.blendPixel_outside_clip`: a pixel outside the clip region keeps its value;
   - `run_size`: after any display list every canvas's bitmap has `width × height × 4`
     bytes; `Canvas.onBitmap_size`: a draw keeps the size of the bitmap it draws on;
   - `emit_pixels`: the host gets only rectangles inside a canvas of the page.
2. `save`/`restore` is a stack: `State.Stack.restore_save`, `restore_setters_save`.
-/
import L4Factoidal.PageCanvas.Wire

namespace L4Factoidal.PageCanvas

/-- After any display list, every canvas of the page has a bitmap of its own size. -/
theorem run_size (s : Store) (env : Env) (cmds : Array Cmd) (id : Nat) (c : Canvas)
    (h : (s.run env cmds).canvases[id]? = some c) : c.bitmap.size = c.width * c.height * 4 := by
  simp only [Store.run, Std.HashMap.getElem?_map] at h
  cases hc : ((cmds.foldl Run.step { store := s, env }).put.store.canvases[id]?) with
  | none => simp [hc] at h
  | some c0 =>
    simp [hc] at h
    subst h
    exact Canvas.fix_size c0

/-- Restore after save with any setters between them gives the canvas's state of the save. -/
theorem canvas_restore_save (c : Canvas) (fs : List (DrawState → DrawState)) (h : c.stack.saved.length < maxSaved) :
    (fs.foldl Stack.set c.stack.save).restore = c.stack := Stack.restore_setters_save c.stack fs h

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
