/-
L4Factoidal.PageGl.Idl: the two WebGL rendering context interfaces as the page sees them
(record: docs/designissues/2026-11-14-webgl-webcodecs.md, section 3).

`WebGLRenderingContext` is the mixins `WebGLRenderingContextBase` and
`WebGLRenderingContextOverloads`; `WebGL2RenderingContext` is those of WebGL 1's base, its own base
and its own overloads (WebGL 2.0 §3.7). An operation that several mixins or overloads give has one
function, whose `length` is the fewest arguments any of them takes (Web IDL §3.7.6): `mergeOps`.

The page glue builds the interface objects from `Interface.text` (web_api op 100), and the state
machine (`PageGl.State`) reads its enum values from the same lists, so the page and the validator
cannot disagree about a constant.
-/
import L4Factoidal.PageGl.Table

namespace L4Factoidal.PageGl.Idl

/-- One step of `mergeOps`: a name seen before keeps the smaller length; a new name goes last. -/
def mergeStep (acc : List (String × Nat)) (o : String × Nat) : List (String × Nat) :=
  if acc.any (·.1 == o.1) then acc.map (fun p => if p.1 == o.1 then (p.1, min p.2 o.2) else p)
  else acc ++ [o]

/-- The operations of an interface from those of its mixins: each name once, in the order first
seen, with the fewest arguments of its overloads. -/
def mergeOps (xs : List (String × Nat)) : List (String × Nat) := xs.foldl mergeStep []

/-! ## Theorems about `mergeOps` -/

theorem mergeStep_names (acc : List (String × Nat)) (o : String × Nat) :
    (mergeStep acc o).map (·.1) =
      if acc.any (·.1 == o.1) then acc.map (·.1) else acc.map (·.1) ++ [o.1] := by
  unfold mergeStep
  split
  · rw [List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp]
    split <;> rfl
  · simp

/-- Invariant. Says: the names `mergeOps` answers are pairwise different, for every input, so the
page glue defines each operation once. Does not say: which length a name gets (`mergeOps_le`). -/
theorem mergeOps_nodup (xs : List (String × Nat)) : ((mergeOps xs).map (·.1)).Nodup := by
  unfold mergeOps
  suffices h : ∀ acc : List (String × Nat), (acc.map (·.1)).Nodup → ((xs.foldl mergeStep acc).map (·.1)).Nodup by
    exact h [] (by simp)
  induction xs with
  | nil => intro acc h; simpa using h
  | cons o xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rw [mergeStep_names]
    split
    · exact h
    · rename_i hn
      rw [List.nodup_append]
      refine ⟨h, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      apply hn
      simp only [List.any_eq_true]
      obtain ⟨p, hp, hpe⟩ := List.mem_map.mp ha
      exact ⟨p, hp, by simp [hpe, hab, hb]⟩

/-- A name in the accumulator stays, with a length no larger. -/
theorem mergeStep_keeps (acc : List (String × Nat)) (o : String × Nat) (n : String) (k : Nat)
    (h : (n, k) ∈ acc) : ∃ k', k' ≤ k ∧ (n, k') ∈ mergeStep acc o := by
  unfold mergeStep
  split
  · by_cases hn : n == o.1
    · refine ⟨min k o.2, Nat.min_le_left _ _, ?_⟩
      simp only [List.mem_map]
      exact ⟨(n, k), h, by simp [hn]⟩
    · refine ⟨k, Nat.le_refl _, ?_⟩
      simp only [List.mem_map]
      exact ⟨(n, k), h, by simp [hn]⟩
  · exact ⟨k, Nat.le_refl _, by simp [h]⟩

/-- The new operation is in the result, with a length no larger than its own. -/
theorem mergeStep_adds (acc : List (String × Nat)) (o : String × Nat) :
    ∃ k', k' ≤ o.2 ∧ (o.1, k') ∈ mergeStep acc o := by
  unfold mergeStep
  split
  · rename_i h
    simp only [List.any_eq_true] at h
    obtain ⟨p, hp, hpn⟩ := h
    refine ⟨min p.2 o.2, Nat.min_le_right _ _, ?_⟩
    simp only [List.mem_map]
    refine ⟨p, hp, ?_⟩
    have : p.1 = o.1 := by simpa using hpn
    simp [this]
  · exact ⟨o.2, Nat.le_refl _, by simp⟩

theorem foldl_mergeStep_keeps (xs acc : List (String × Nat)) (n : String) (k : Nat)
    (h : (n, k) ∈ acc) : ∃ k', k' ≤ k ∧ (n, k') ∈ xs.foldl mergeStep acc := by
  induction xs generalizing acc k with
  | nil => exact ⟨k, Nat.le_refl _, h⟩
  | cons o xs ih =>
    obtain ⟨k1, hk1, hm⟩ := mergeStep_keeps acc o n k h
    obtain ⟨k2, hk2, hm2⟩ := ih (mergeStep acc o) k1 hm
    exact ⟨k2, Nat.le_trans hk2 hk1, hm2⟩

/-- Specification. Says: every operation (overload) given to `mergeOps` is in its answer under the
same name, with a length that is at most that overload's argument count: the function's `length`
is a lower bound of every overload, as Web IDL §3.7.6 asks. Does not say: that the length is
reached by some overload (it is, by construction: only `min` of given lengths is ever stored). -/
theorem mergeOps_le (xs : List (String × Nat)) (n : String) (k : Nat) (h : (n, k) ∈ xs) :
    ∃ k', k' ≤ k ∧ (n, k') ∈ mergeOps xs := by
  unfold mergeOps
  suffices hs : ∀ acc : List (String × Nat), ∃ k', k' ≤ k ∧ (n, k') ∈ xs.foldl mergeStep acc by
    exact hs []
  induction xs with
  | nil => cases h
  | cons o xs ih =>
    intro acc
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h'
    · obtain ⟨k1, hk1, hm⟩ := mergeStep_adds acc (n, k)
      obtain ⟨k2, hk2, hm2⟩ := foldl_mergeStep_keeps xs (mergeStep acc (n, k)) n k1 hm
      exact ⟨k2, Nat.le_trans hk2 hk1, hm2⟩
    · exact ih h' (mergeStep acc o)

/- From here `mergeOps` is opaque to unification: a goal about an interface's operations is closed
by the theorems above, never by evaluating the fold over the table. -/
attribute [irreducible] mergeOps

/-! ## The interfaces -/

structure Interface where
  name : String
  consts : List (String × Int)
  attrs : List (String × Bool)
  ops : List (String × Nat)

def webgl1 : Interface where
  name := "WebGLRenderingContext"
  consts := Table.baseConsts ++ Table.overloads1Consts
  attrs := Table.baseAttrs ++ Table.overloads1Attrs
  ops := mergeOps (Table.baseOps ++ Table.overloads1Ops)

def webgl2 : Interface where
  name := "WebGL2RenderingContext"
  consts := Table.baseConsts ++ Table.overloads1Consts ++ (Table.base2Consts ++ Table.overloads2Consts)
  attrs := Table.baseAttrs ++ Table.base2Attrs ++ Table.overloads2Attrs
  ops := mergeOps (Table.baseOps ++ Table.base2Ops ++ Table.overloads2Ops)

/-- The interface a context version (1 or 2) has. -/
def ofVersion (v : Nat) : Interface := if v == 2 then webgl2 else webgl1

def Interface.const? (i : Interface) (n : String) : Option Int := (i.consts.find? (·.1 == n)).map (·.2)

def Interface.length? (i : Interface) (n : String) : Option Nat := (i.ops.find? (·.1 == n)).map (·.2)

/-- The interface as text for the page glue: a line `c NAME VALUE` for each constant,
`a NAME 0|1` for each attribute (1: read-only) and `o NAME LENGTH` for each operation. -/
def Interface.text (i : Interface) : String :=
  "\n".intercalate
    (i.consts.map (fun c => s!"c {c.1} {c.2}") ++
     i.attrs.map (fun a => s!"a {a.1} {if a.2 then 1 else 0}") ++
     i.ops.map (fun o => s!"o {o.1} {o.2}"))

/-! ## Theorems about the interfaces -/

/-- Invariant. Says: every constant of WebGL 1 is a constant of WebGL 2 with the same value
(WebGL 2.0 §3.7: the WebGL 2 context includes the WebGL 1 base). Does not say: the reverse. -/
theorem webgl2_has_webgl1_consts (c : String × Int) (h : c ∈ webgl1.consts) : c ∈ webgl2.consts := by
  exact List.mem_append_left (Table.base2Consts ++ Table.overloads2Consts) h

/-- Invariant. Says: both interfaces name each operation once. -/
theorem ops_nodup (v : Nat) : ((ofVersion v).ops.map (·.1)).Nodup := by
  unfold ofVersion
  split
  · exact mergeOps_nodup _
  · exact mergeOps_nodup _

/-! ## Tests (values from the IDL and from `webgl/idlharness.any.js`) -/

#guard webgl1.consts.length == 297
#guard webgl2.consts.length == 559
#guard webgl1.ops.length == 137
#guard webgl2.ops.length == 225
#guard webgl1.const? "ARRAY_BUFFER" == some 0x8892
#guard webgl1.const? "READ_BUFFER" == none
#guard webgl2.const? "READ_BUFFER" == some 0xC02
#guard webgl2.const? "TIMEOUT_IGNORED" == some (-1)
#guard webgl1.length? "bufferData" == some 3
#guard webgl1.length? "texImage2D" == some 6
#guard webgl2.length? "texImage2D" == some 6
#guard webgl1.length? "readPixels" == some 7
#guard webgl2.length? "getBufferSubData" == some 3
#guard webgl1.length? "getBufferSubData" == none
#guard webgl2.length? "uniform1fv" == some 2
#guard mergeOps [("a", 3), ("b", 1), ("a", 2)] == [("a", 2), ("b", 1)]
-- Each constant name once in each interface (a test: the lists are data).
#guard (webgl2.consts.map (·.1)).eraseDups.length == webgl2.consts.length
#guard webgl2.consts.all fun c => -1 ≤ c.2 && c.2 < 4294967296
#guard (webgl1.text.splitOn "\n").length == 297 + 6 + webgl1.ops.length

end L4Factoidal.PageGl.Idl
