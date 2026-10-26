/-
L4Factoidal.RDF.CanonicalSet — the canonical N-Quads document has no repeated
line.

RDFC-1.0 §3: the canonical N-Quads form is the quads of the normalized
dataset, one line each, sorted in code point order. A dataset is a set of
quads (RDF 1.1 Concepts §4), so no line occurs two times. `canonicalLinesOf`
sorts the lines (`sortStrings`) and drops adjacent equal lines (`dedupAdj`).
`canonicalLines_strict` proves that the result is strictly increasing in code
point order, so `canonicalLines_nodup` holds for every dataset and hash
algorithm, and `canonicalize_nquads` states that the `nquads` text is those
lines joined.

Tracking: https://github.com/danbri/factoidal/issues/973.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.CanonicalTheorems

namespace L4Factoidal.RDF.Canonical

open L4Factoidal.Crypto

theorem strLe_iff (a b : String) : strLe a b = true ↔ a ≤ b := by
  rw [strLe_eq_not_lt]
  simp

/-- In a list sorted by `strLe`, the head is below every later line. -/
theorem sortedB_head_le : ∀ (a : String) (l : List String),
    sortedB strLe (a :: l) = true → ∀ z ∈ l, a ≤ z
  | _, [], _, z, hz => by cases hz
  | a, b :: l, h, z, hz => by
      rw [sortedB_cons] at h
      have h1 : headOk strLe a (b :: l) = true := (Bool.and_eq_true _ _ ▸ h).1
      have h2 : sortedB strLe (b :: l) = true := (Bool.and_eq_true _ _ ▸ h).2
      have hab : a ≤ b := (strLe_iff a b).mp (by simpa [headOk] using h1)
      rcases List.mem_cons.mp hz with e | hz
      · subst e; exact hab
      · exact String.le_trans hab (sortedB_head_le b l h2 z hz)

/-- `dedupAdj` keeps only lines of its input. -/
theorem mem_dedupAdj : ∀ (l : List String), ∀ z ∈ dedupAdj l, z ∈ l
  | [], z, hz => by simp [dedupAdj] at hz
  | [x], z, hz => hz
  | x :: y :: rest, z, hz => by
      unfold dedupAdj at hz
      split at hz
      · exact List.mem_cons_of_mem _ (mem_dedupAdj (y :: rest) z hz)
      · rcases List.mem_cons.mp hz with e | hz
        · exact e ▸ List.mem_cons_self
        · exact List.mem_cons_of_mem _ (mem_dedupAdj (y :: rest) z hz)

/-- A sorted list without adjacent repeats is strictly increasing. -/
theorem dedupAdj_strict : ∀ (l : List String), sortedB strLe l = true →
    (dedupAdj l).Pairwise (· < ·)
  | [], _ => by simp [dedupAdj]
  | [x], _ => by simp [dedupAdj]
  | x :: y :: rest, h => by
      have htail : sortedB strLe (y :: rest) = true := by
        rw [sortedB_cons] at h; exact (Bool.and_eq_true _ _ ▸ h).2
      unfold dedupAdj
      split
      · exact dedupAdj_strict (y :: rest) htail
      · next hne =>
        refine List.pairwise_cons.mpr ⟨?_, dedupAdj_strict (y :: rest) htail⟩
        intro z hz
        have hxz : x ≤ z := sortedB_head_le x (y :: rest) h z (mem_dedupAdj _ z hz)
        by_cases e : x = z
        · -- `z` is in `dedupAdj (y :: rest)`, so `y ≤ z`; `x ≤ y` and `x ≠ y`.
          subst e
          have hyz : y ≤ x := by
            rcases List.mem_cons.mp (mem_dedupAdj _ x hz) with e | hm
            · exact e ▸ String.le_refl _
            · exact sortedB_head_le y rest htail x hm
          have hxy : x ≤ y := sortedB_head_le x (y :: rest) h y List.mem_cons_self
          exact absurd (String.le_antisymm hxy hyz) (fun e => hne (by simp [e]))
        · exact String.not_le.mp (fun hzx => e (String.le_antisymm hxz hzx))

theorem canonicalLinesOf_strict (ds : Dataset) : (canonicalLinesOf ds).Pairwise (· < ·) :=
  dedupAdj_strict _ (sortedB_sortStrings _)

/-- RDFC-1.0 §3: the lines of the canonical N-Quads document are strictly
increasing in code point order, for every dataset and hash algorithm. -/
theorem canonicalLines_strict (ds : Dataset) (alg : HashAlgorithm) :
    (ds.canonicalLines alg).Pairwise (· < ·) := by
  unfold L4Factoidal.RDF.Dataset.canonicalLines
  split <;> exact canonicalLinesOf_strict _

/-- No line of the canonical N-Quads document occurs two times. -/
theorem canonicalLines_nodup (ds : Dataset) (alg : HashAlgorithm) :
    (ds.canonicalLines alg).Nodup :=
  (canonicalLines_strict ds alg).imp String.ne_of_lt

/-- The `nquads` text of `canonicalize` is the canonical lines joined. -/
theorem canonicalize_nquads (ds : Dataset) (alg : HashAlgorithm) :
    (canonicalize ds alg).nquads = joinStrings (ds.canonicalLines alg) := by
  unfold canonicalize L4Factoidal.RDF.Dataset.canonicalLines
  split <;> rfl

#guard dedupAdj (sortStrings ["b", "a", "b", "a"]) == ["a", "b"]

#print axioms canonicalLines_nodup
#print axioms canonicalize_nquads

end L4Factoidal.RDF.Canonical
