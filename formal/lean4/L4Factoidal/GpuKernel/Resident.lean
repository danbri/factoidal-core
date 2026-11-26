/-
L4Factoidal.GpuKernel.Resident — data that stays on the GPU across frames and pages, with a
memory bound and an upload-once contract (core issue 398).

What is resident: glyph outlines (curve buffers, one entry a glyph of a font), atlas pages,
the retained scene's primitive records, tile bins and decoded images. Each is an `Entry`:
a key (font and glyph id, primitive id, image id), a version (the content's hash: a changed
primitive is a new version of its key) and a size in bytes. A frame names the entries it
needs; `plan` answers what to upload and the new resident set.

- `plan_noReupload`: an entry already resident with the same key and version is never in the
  frame's uploads. The cost theorem of the retained form: an unchanged glyph or primitive is
  not uploaded again.
- `plan_budget`: the resident set never holds more than `budget` bytes, whatever the frames
  ask (eviction keeps the frame's needs first, then the most recently used of the rest, while
  they fit).
- `plan_keeps_needed`: when what a frame needs fits in the budget, all of it is resident after
  the frame (so it was uploaded at most once).
- `plan_steady`: an unchanged frame that fits uploads nothing: 0 bytes a frame.

A frame whose needs do not fit is not refused here: the entries that did not fit are left out
of the resident set and the frame draws them by the per-frame route (uploaded and dropped).
-/
namespace L4Factoidal.GpuKernel.Resident

structure Entry where
  key : Nat
  ver : Nat
  bytes : Nat
  deriving DecidableEq, Repr

def has (rs : List Entry) (e : Entry) : Bool := rs.any fun r => r.key == e.key && r.ver == e.ver

def total (es : List Entry) : Nat := (es.map Entry.bytes).sum

/-- Keep entries in order while they fit in `b` bytes; skip one that does not. -/
def fit : Nat → List Entry → List Entry
  | _, [] => []
  | b, e :: es => if e.bytes ≤ b then e :: fit (b - e.bytes) es else fit b es

/-- `total` as a loop with an accumulator: one frame for any number of entries. -/
def totalGo : List Entry → Nat → Nat
  | [], a => a
  | e :: es, a => totalGo es (a + e.bytes)

theorem totalGo_eq : ∀ (es : List Entry) (a : Nat), totalGo es a = a + total es
  | [], a => by simp [totalGo, total]
  | e :: es, a => by simp [totalGo, total, totalGo_eq es]; omega

/-- `total` as a loop (`total_eq_loop` is the `@[csimp]` equation). -/
def totalLoop (es : List Entry) : Nat := totalGo es 0

@[csimp] theorem total_eq_loop : @total = @totalLoop := by
  funext es; simp [totalLoop, totalGo_eq]

/-- `fit` in reverse order onto `acc`, as a loop: one frame for any number of entries. -/
def fitRev : Nat → List Entry → List Entry → List Entry
  | _, [], acc => acc
  | b, e :: es, acc => if e.bytes ≤ b then fitRev (b - e.bytes) es (e :: acc) else fitRev b es acc

theorem fitRev_eq : ∀ (b : Nat) (es acc : List Entry), fitRev b es acc = (fit b es).reverse ++ acc
  | _, [], _ => rfl
  | b, e :: es, acc => by
    by_cases h : e.bytes ≤ b <;> simp [fitRev, fit, h, fitRev_eq]

/-- `fit` as a loop (`fit_eq_loop` is the `@[csimp]` equation). -/
def fitLoop (b : Nat) (es : List Entry) : List Entry := (fitRev b es []).reverse

@[csimp] theorem fit_eq_loop : @fit = @fitLoop := by
  funext b es; simp [fitLoop, fitRev_eq]

/-- One frame: what to upload, and the new resident set (needs first, then the rest of the
old set that the frame did not name, most recent first, while they fit). -/
def plan (budget : Nat) (resident need : List Entry) : List Entry × List Entry :=
  (need.filter fun e => !has resident e,
   fit budget (need ++ resident.filter fun r => !need.any fun e => e.key == r.key))

theorem plan_noReupload (budget : Nat) (resident need : List Entry) (e : Entry)
    (h : has resident e = true) : e ∉ (plan budget resident need).1 := by
  simp [plan, h]

theorem fit_total : ∀ (b : Nat) (es : List Entry), total (fit b es) ≤ b
  | _, [] => by simp [fit, total]
  | b, e :: es => by
    unfold fit
    split
    · have := fit_total (b - e.bytes) es
      simp only [total, List.map_cons, List.sum_cons] at this ⊢
      omega
    · exact fit_total b es

theorem plan_budget (budget : Nat) (resident need : List Entry) :
    total (plan budget resident need).2 ≤ budget := fit_total _ _

theorem fit_append_prefix : ∀ (b : Nat) (xs ys : List Entry), total xs ≤ b →
    ∀ e ∈ xs, e ∈ fit b (xs ++ ys)
  | _, [], _, _ => by simp
  | b, x :: xs, ys, h => by
    intro e he
    simp only [total, List.map_cons, List.sum_cons] at h
    have hx : x.bytes ≤ b := by omega
    simp only [List.cons_append, fit, hx, if_true, List.mem_cons] at he ⊢
    rcases he with rfl | he
    · exact Or.inl rfl
    · exact Or.inr (fit_append_prefix (b - x.bytes) xs ys (by simp only [total]; omega) e he)

theorem plan_keeps_needed (budget : Nat) (resident need : List Entry) (h : total need ≤ budget) :
    ∀ e ∈ need, e ∈ (plan budget resident need).2 :=
  fit_append_prefix budget need _ h

theorem has_of_mem (rs : List Entry) (e : Entry) (h : e ∈ rs) : has rs e = true := by
  simp only [has, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨e, h, rfl, rfl⟩

/-- An unchanged frame that fits uploads nothing. -/
theorem plan_steady (budget : Nat) (resident need : List Entry) (h : total need ≤ budget) :
    (plan budget (plan budget resident need).2 need).1 = [] := by
  simp only [plan, List.filter_eq_nil_iff, Bool.not_eq_eq_eq_not, Bool.not_true]
  intro e he
  have := has_of_mem _ e (plan_keeps_needed budget resident need h e he)
  simp only [plan] at this
  simp [this]

#guard (plan 100 [] [⟨1, 7, 40⟩, ⟨2, 7, 40⟩]).1.length == 2
#guard (plan 100 (plan 100 [] [⟨1, 7, 40⟩, ⟨2, 7, 40⟩]).2 [⟨1, 7, 40⟩, ⟨2, 7, 40⟩]).1 == []
#guard (plan 100 (plan 100 [] [⟨1, 7, 40⟩, ⟨2, 7, 40⟩]).2 [⟨1, 8, 40⟩, ⟨2, 7, 40⟩]).1 == [⟨1, 8, 40⟩]
#guard total (plan 100 [⟨5, 0, 90⟩] [⟨1, 7, 40⟩, ⟨2, 7, 40⟩]).2 == 80

end L4Factoidal.GpuKernel.Resident
