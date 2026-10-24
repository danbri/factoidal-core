/-
L4Factoidal.Storage.Sbm11.HeldFoldedTheorems — the open hypothesis
`Overlay.HeldFolded` of phase A1 (https://github.com/danbri/factoidal/issues/975),
proved for SBM11 from the checks of a generation.

`Overlay.overlayDen_remove_sbm11` (`DenotationTheorems.lean`) takes
`HeldFolded (OverlayDict.ovHeld keys baseUsed ov)`: every term that the
overlaid generation holds is its own join key (its language tags are in lower
case). The held terms are of two kinds (`OverlayDict.ovDec`):

* the entries of the overlay vocabulary `ov`. The harness builds `ov` with
  `vocabAdd` (`Session.idOrNew`), which appends `normalizeTerm t`, never `t`.
  `vocabAddAll_folded`: every entry of `vocabAddAll keys [] ts` is folded. This
  part is PROVED, from `normalizeTerm_eq_joinKey`: `normalizeTerm` is
  `Term.joinKey` (both lower the language tags with `String.toLower`, inside
  triple terms too).
* the terms of the base ids in use, `ofCode? keys n` (`BaseFolded`).
  `baseFolded_of_keysOk`: they are folded when the dictionary passes
  `MemGen.keysOk` (every key decodes to a term that `normalizeTerm` fixes;
  `PackSpec.keysOk_of` proves this for the keys that the packer makes) and the
  base ids pass `MemGen.idOkB`, the hypothesis `overlay_dictInjective` already
  takes. This part is PROVED too, from `MemGen.code_norm`.

`heldFolded_of`: `BaseFolded` and a folded vocabulary give `HeldFolded`.
`heldFolded_sbm11`: `HeldFolded` for the SBM11 overlay with the vocabulary of
the harness, from `keysOk` and `idOkB`. `overlayDen_remove_sbm11_vocab`: DELETE
DATA for that overlay with no `HeldFolded` hypothesis.

Not proved here: that the `IO` steps of the harness compute `vocabAdd`
(`OverlayDict.lean` states the same limit).

No SBM11 code changes; this module adds theorems only.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DenotationTheorems

namespace L4Factoidal.Storage.Sbm11.Overlay

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block (Row)
open L4Factoidal.Storage.Sbm11.OverlayDict
open L4Factoidal.Storage.Sbm11.OverlayTheorems

/-- `normalizeTerm` is the join key: both lower every language tag, inside
triple terms too. -/
theorem normalizeTerm_eq_joinKey : ∀ t : Term, normalizeTerm t = t.joinKey
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal l => by
      obtain ⟨⟨lex, dt, tag, dr⟩, hwf⟩ := l
      cases tag with
      | none => rfl
      | some tg =>
        let v0 : Literal := { lexicalForm := lex, datatype := dt, langTag := some tg, direction := dr }
        have hv : literalWf { v0 with langTag := some tg.toLower } = true :=
          literalWf_joinKey v0 hwf
        simp only [normalizeTerm, normalizeLit]
        rw [dif_pos hv]
        rfl
  | .tripleTerm s p o => by
      simp only [normalizeTerm, Term.joinKey, normalizeTerm_eq_joinKey o]

/-- A folded term is its own join key. -/
theorem joinKey_normalizeTerm_self (t : Term) : (normalizeTerm t).joinKey = normalizeTerm t := by
  rw [PackSpec.joinKey_normalizeTerm, normalizeTerm_eq_joinKey]

theorem vocabAdd_folded (keys : List Key) (ov : List Term) (t : Term)
    (hov : ∀ u ∈ ov, u.joinKey = u) : ∀ u ∈ vocabAdd keys ov t, u.joinKey = u := by
  intro u hu
  simp only [vocabAdd] at hu
  split at hu
  · exact hov u hu
  · rcases List.mem_append.mp hu with hu | hu
    · exact hov u hu
    · rw [List.mem_singleton] at hu
      subst hu
      exact joinKey_normalizeTerm_self t

/-- **The overlay vocabulary of the harness is folded.** -/
theorem vocabAddAll_folded (keys : List Key) :
    ∀ (ts : List Term) (ov : List Term), (∀ u ∈ ov, u.joinKey = u) →
      ∀ u ∈ vocabAddAll keys ov ts, u.joinKey = u
  | [], ov, hov => hov
  | t :: ts, ov, hov => by
      unfold vocabAddAll
      simp only [List.foldl_cons]
      exact vocabAddAll_folded keys ts _ (vocabAdd_folded keys ov t hov)

/-- The terms of the base ids in use are folded: a condition on the dictionary
keys of a generation (`baseFolded_of_keysOk`). -/
def BaseFolded (keys : List Key) (baseUsed : Nat → Prop) : Prop :=
  ∀ n t, baseUsed n → n / two60 ≠ tagDelta → ofCode? keys n = some t → t.joinKey = t

/-- **`HeldFolded` from the base and the vocabulary.** -/
theorem heldFolded_of {keys : List Key} {baseUsed : Nat → Prop} {ov : List Term}
    (hbase : BaseFolded keys baseUsed) (hov : ∀ u ∈ ov, u.joinKey = u) :
    HeldFolded (ovHeld keys baseUsed ov) := by
  rintro t ⟨n, hn, hd⟩
  unfold ovDec at hd
  split at hd
  · exact hov t (List.mem_of_getElem? hd)
  · rename_i htag
    rcases hn with hn | ⟨htag', _⟩
    · exact hbase n t hn htag hd
    · exact absurd htag' htag

/-- **The base ids are folded** for a dictionary that passes `keysOk`. -/
theorem baseFolded_of_keysOk {keys : List Key} {baseUsed : Nat → Prop}
    (hk : MemGen.keysOk keys = true) (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true) :
    BaseFolded keys baseUsed := by
  intro n t hn _ hd
  have hok := hb n hn
  unfold MemGen.idOkB at hok
  rw [hd] at hok
  have hc : toCode? keys t = some n := by simpa using hok
  have hnorm := MemGen.code_norm keys hk t n hc
  rw [← normalizeTerm_eq_joinKey, hnorm]

/-- **`HeldFolded` for the SBM11 overlay** whose vocabulary the harness built
(`vocabAddAll keys [] ts`), from the checks of the generation. -/
theorem heldFolded_sbm11 (keys : List Key) (ts : List Term) (baseUsed : Nat → Prop)
    (hk : MemGen.keysOk keys = true) (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true) :
    HeldFolded (ovHeld keys baseUsed (vocabAddAll keys [] ts)) :=
  heldFolded_of (baseFolded_of_keysOk hk hb)
    (vocabAddAll_folded keys ts [] (fun _ h => absurd h List.not_mem_nil))

/-- DELETE DATA for the SBM11 overlay whose vocabulary the harness built
(`vocabAddAll keys [] ts`), with no `HeldFolded` hypothesis. -/
theorem overlayDen_remove_sbm11_vocab (keys : List Key) (ts : List Term) (baseUsed : Nat → Prop)
    (hv : OverlayDict.vocabOk keys (vocabAddAll keys [] ts) = true)
    (hb : ∀ n, baseUsed n → MemGen.idOkB keys n = true)
    (hk : MemGen.keysOk keys = true)
    (base : Row → Bool) (bn : Nat → Bool) (st : State) (q : Row)
    (hq : RowInUse (OverlayDict.ovUsed baseUsed (vocabAddAll keys [] ts)) q)
    (hrows : ∀ r, denote base st r = true →
      RowInUse (OverlayDict.ovUsed baseUsed (vocabAddAll keys [] ts)) r)
    (gn : Option Subject) (t : Triple) :
    (overlayDen (OverlayDict.ovDec keys (vocabAddAll keys [] ts)) base bn (step st (.remove q))).graph gn t ↔
      (overlayDen (OverlayDict.ovDec keys (vocabAddAll keys [] ts)) base bn st).graph gn t ∧
        ¬ ∃ u, rowQuad? (OverlayDict.ovDec keys (vocabAddAll keys [] ts)) q = some (gn, u) ∧
          u.key = t.key :=
  overlayDen_remove_sbm11 keys _ baseUsed hv hb (heldFolded_sbm11 keys ts baseUsed hk hb)
    base bn st q hq hrows gn t

#print axioms normalizeTerm_eq_joinKey
#print axioms vocabAddAll_folded
#print axioms heldFolded_of
#print axioms baseFolded_of_keysOk
#print axioms heldFolded_sbm11
#print axioms overlayDen_remove_sbm11_vocab

end L4Factoidal.Storage.Sbm11.Overlay
