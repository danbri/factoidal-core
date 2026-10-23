/-
L4Factoidal.Storage.Sbm11.OverlayDict — the term ids of an SBM11 generation
with its delta overlay, as pure functions
(https://github.com/danbri/factoidal/issues/975, step 2; stage 5 of
https://github.com/danbri/factoidal/issues/791).

The replay of a delta log gives an id to every term of the log. A term with
a base id (an inline code or a dictionary rank, `toCode?`) keeps it. A term
without one gets the next entry of the overlay vocabulary `ov`, and its id is
`tagDelta · 2^60 + k` for its index `k` in `ov` (`Overlay.tagDelta` = 14).

`Harness/Sbm11Query.lean` does these steps in `IO`:

* `Session.idOf`: fold the language tags to lower case (`normalizeTerm`),
  then the inline code, then the dictionary (`Dict.lookupM`, equal to the
  rank of `toCode?` by `DictLookupTheorems.lookupM_encodeDict`), then the
  overlay vocabulary (`Session.overlayIdOf`). This is `ovEnc` of the folded
  term.
* `Session.idOrNew`: when `idOf` gives no id, push the folded term on
  `ovVocab` and give it the index as id. This is `vocabAdd`.
* `Session.termOf` for a tag-14 id: the entry of `ovVocab`. This is `ovDec`.

`vocabOk` is the check of an overlay vocabulary: no duplicate entry, no entry
with a base id, at most `2^60` entries. `DictInjectiveTheorems` proves that
`vocabAdd` keeps `vocabOk` (while fewer than `2^60` entries), and that under
`vocabOk` the ids are injective with `ovDec` as inverse.

Not proved: that the `IO` steps of the harness compute these functions. The
harness keeps the vocabulary in an `IO.Ref` and a hash map; the
correspondence is by reading, and the update tests of `tests/sbm11` exercise
it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.Sbm11.Overlay

namespace L4Factoidal.Storage.Sbm11.OverlayDict

open L4Factoidal.RDF

/-- The id of a term: its base id (`toCode?` over the dictionary keys), else
    `tagDelta · 2^60 + k` for its index `k` in the overlay vocabulary. -/
def ovEnc (keys : List Key) (ov : List Term) (t : Term) : Option Nat :=
  match toCode? keys t with
  | some n => some n
  | none =>
    if t ∈ ov ∧ ov.idxOf t < two60 then some (Overlay.tagDelta * two60 + ov.idxOf t) else none

/-- The term of an id: an entry of the overlay vocabulary for tag 14, else
    `ofCode?` over the dictionary keys. -/
def ovDec (keys : List Key) (ov : List Term) (n : Nat) : Option Term :=
  if n / two60 = Overlay.tagDelta then ov[n % two60]? else ofCode? keys n

/-- The check of an overlay vocabulary: no duplicate entry, no entry with a
    base id, at most `2^60` entries. -/
def vocabOk (keys : List Key) (ov : List Term) : Bool :=
  decide ov.Nodup && ov.all (fun t => (toCode? keys t).isNone) && decide (ov.length ≤ two60)

/-- One step of `Session.idOrNew`: the folded term gets an entry when it has
    no id yet. -/
def vocabAdd (keys : List Key) (ov : List Term) (t : Term) : List Term :=
  let u := normalizeTerm t
  if (ovEnc keys ov u).isSome then ov else ov ++ [u]

/-- The id `Session.idOrNew` gives `t` after the step. -/
def idOrNew (keys : List Key) (ov : List Term) (t : Term) : Option Nat :=
  ovEnc keys (vocabAdd keys ov t) (normalizeTerm t)

/-- The vocabulary after the terms `ts`, in order. -/
def vocabAddAll (keys : List Key) (ov : List Term) (ts : List Term) : List Term :=
  ts.foldl (vocabAdd keys) ov

/-- The ids in use: the ids of the rows of the base that are codes of terms
    (`baseUsed`, from the generation's check), and the overlay ids. -/
def ovUsed (baseUsed : Nat → Prop) (ov : List Term) (n : Nat) : Prop :=
  baseUsed n ∨ (n / two60 = Overlay.tagDelta ∧ n % two60 < ov.length)

/-- The terms the overlaid generation holds: the terms of the ids in use. -/
def ovHeld (keys : List Key) (baseUsed : Nat → Prop) (ov : List Term) (t : Term) : Prop :=
  ∃ n, ovUsed baseUsed ov n ∧ ovDec keys ov n = some t

end L4Factoidal.Storage.Sbm11.OverlayDict
