import Init

/-!
# GSSL: equality joins under finite-scope integer encoding

This is a workload-independent relational operator. It can support RDF BGP
joins, DOM parent/child joins, glyph/atlas lookup, or other applications.

Only equality comparisons between keys actually compared by the join must be
preserved by the codebook. Requiring an injective mapping of *all* RDF terms
(or all strings) into a bounded integer space would be impossible; the finite admitted scope is
the important distinction.

This is a theorem about pure data and integer semantics, not about WGSL code
or hardware execution. The caller must separately establish that GPU kernels
implement the integer join and that output payload encoding/decoding is valid.
-/
namespace L4Factoidal.GpuDomainSpecificLanguage.EncodedJoin

universe u v w

variable {Key : Type u} [BEq Key]
variable {LeftValue : Type v} {RightValue : Type w}

/-- Stable right-side filtering for a single left record.
    The output preserves the right relation's order and duplicates. -/
def rowMatches (left : Key × LeftValue)
    (right : List (Key × RightValue)) : List (LeftValue × RightValue) :=
  right.filterMap fun r =>
    if left.1 == r.1 then some (left.2, r.2) else none

/-- Stable left-major/right-major equijoin (bag, not set, semantics). -/
def joinRows (left : List (Key × LeftValue))
    (right : List (Key × RightValue)) : List (LeftValue × RightValue) :=
  left.flatMap (fun l => rowMatches l right)

/-- Encoding a single join key to a target code type preserves the output whenever it
    preserves the equality comparisons needed for that left record. -/
theorem rowMatches_encode {Code : Type} [BEq Code] (code : Key → Code)
    (left : Key × LeftValue) (right : List (Key × RightValue))
    (agree : ∀ r, r ∈ right →
      ((code left.1 == code r.1) = (left.1 == r.1))) :
    rowMatches (code left.1, left.2)
      (right.map (fun r => (code r.1, r.2))) =
    rowMatches left right := by
  induction right with
  | nil => rfl
  | cons r rest ih =>
      have head : (code left.1 == code r.1) = (left.1 == r.1) :=
        agree r (by simp)
      have tail : ∀ t, t ∈ rest →
          ((code left.1 == code t.1) = (left.1 == t.1)) := by
        intro t ht
        exact agree t (by simp [ht])
      cases h : (left.1 == r.1) with
      | false =>
          have hc : (code left.1 == code r.1) = false := head.trans h
          simpa [rowMatches, h, hc] using ih tail
      | true =>
          have hc : (code left.1 == code r.1) = true := head.trans h
          simpa [rowMatches, h, hc] using
            congrArg (fun xs => (left.2, r.2) :: xs) (ih tail)

/-- The whole ordered bag join is unchanged by an integer encoding provided
    equality is preserved for the FINITE cross-product of admitted join keys.
    The premises are deliberately scoped to the actual left/right relations,
    not to an impossible universal bounded integer encoding of all source values.

    Payloads are unchanged here; their separate encoding and round-trip
    obligations remain with the enclosing domain adapter. -/
theorem joinRows_encode {Code : Type} [BEq Code] (code : Key → Code)
    (right : List (Key × RightValue)) :
    ∀ (left : List (Key × LeftValue)),
      (∀ l, l ∈ left → ∀ r, r ∈ right →
        ((code l.1 == code r.1) = (l.1 == r.1))) →
      joinRows (left.map (fun l => (code l.1, l.2)))
        (right.map (fun r => (code r.1, r.2))) =
      joinRows left right := by
  intro left
  induction left with
  | nil =>
      intro _
      rfl
  | cons l rest ih =>
      intro agree
      have head : ∀ r, r ∈ right →
          ((code l.1 == code r.1) = (l.1 == r.1)) := by
        intro r hr
        exact agree l (by simp) r hr
      have tail : ∀ t, t ∈ rest → ∀ r, r ∈ right →
          ((code t.1 == code r.1) = (t.1 == r.1)) := by
        intro t ht r hr
        exact agree t (by simp [ht]) r hr
      calc
        joinRows ((l :: rest).map (fun x => (code x.1, x.2)))
            (right.map (fun r => (code r.1, r.2))) =
          rowMatches (code l.1, l.2)
            (right.map (fun r => (code r.1, r.2))) ++
          joinRows (rest.map (fun x => (code x.1, x.2)))
            (right.map (fun r => (code r.1, r.2))) := by
              rfl
        _ = rowMatches l right ++ joinRows rest right := by
              rw [rowMatches_encode code l right head, ih tail]
        _ = joinRows (l :: rest) right := by
              rfl

/-- Executable finite admission check for a proposed key encoding. This is
    deliberately quadratic: useful as a reference oracle, test gate, or small
    workload fallback. A scalable dictionary constructor must discharge the
    same equality obligation using its own proved invariants. -/
def checkAgreement {Code : Type} [BEq Code] (code : Key → Code)
    (left : List (Key × LeftValue))
    (right : List (Key × RightValue)) : Bool :=
  left.all fun l =>
    right.all fun r =>
      ((code l.1 == code r.1) == (l.1 == r.1))

/-- A positive executable admission check supplies precisely the premise
    required by the general encoded-join refinement theorem. -/
theorem checkAgreement_sound {Code : Type} [BEq Code] (code : Key → Code)
    (left : List (Key × LeftValue)) (right : List (Key × RightValue))
    (valid : checkAgreement code left right = true) :
    ∀ l, l ∈ left → ∀ r, r ∈ right →
      ((code l.1 == code r.1) = (l.1 == r.1)) := by
  unfold checkAgreement at valid
  intro l hl r hr
  have lvalid := List.all_eq_true.mp valid l hl
  have rvalid := List.all_eq_true.mp lvalid r hr
  exact beq_iff_eq.mp rvalid

/-- No external equality assumption: admission is established by executing
    the finite check. The result remains a *logical integer join*, not proof
    of source-code lowering or a physical GPU execution. -/
theorem joinRows_encode_checked {Code : Type} [BEq Code] (code : Key → Code)
    (left : List (Key × LeftValue)) (right : List (Key × RightValue))
    (valid : checkAgreement code left right = true) :
    joinRows (left.map (fun l => (code l.1, l.2)))
      (right.map (fun r => (code r.1, r.2))) =
    joinRows left right :=
  joinRows_encode code right left (checkAgreement_sound code left right valid)

/-- Collision example: an incorrect codebook can introduce spurious joins. -/
example : joinRows [("a", 10)] [("b", 20)] = ([] : List (Nat × Nat)) := by decide
example : joinRows [((1 : UInt32), (10 : Nat))] [((1 : UInt32), (20 : Nat))] =
  ([(10, 20)] : List (Nat × Nat)) := by decide

#print axioms rowMatches_encode
#print axioms joinRows_encode
#print axioms checkAgreement_sound
#print axioms joinRows_encode_checked

end L4Factoidal.GpuDomainSpecificLanguage.EncodedJoin
