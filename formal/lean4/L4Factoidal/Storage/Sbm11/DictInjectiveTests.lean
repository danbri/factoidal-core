/-
L4Factoidal.Storage.Sbm11.DictInjectiveTests — tests of the SBM11 term
dictionary contract (https://github.com/danbri/factoidal/issues/975, step 2).

* A generation packed from a literal with the tag `EN`: its dictionary holds
  the tag in lower case, and the lookup `MemGen.cid` gives `"x"@EN` and
  `"x"@en` one id (RDF 1.1 Concepts section 3.3). The raw code `toCode?` of
  the term with the upper-case tag is `none`: the dictionary holds only the
  folded term.
* A delta overlay on that generation: new terms get distinct tag-14 ids, a
  term of the base keeps its base id, a term whose tag differs only in case
  from a base term or an earlier new term gets no new entry, and every id
  decodes to its folded term.
* The theorems apply to the generation (`example`s).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DictInjectiveTheorems

namespace L4Factoidal.Storage.Sbm11.DictInjectiveTests

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.PackSpec
open L4Factoidal.Storage.Sbm11.OverlayDict

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def litEN : Term := .literal (Literal.langString "x" "EN")
private def liten : Term := .literal (Literal.langString "x" "en")
private def iriA : Term := .iri (exI "http://ex.org/a")
private def iriG : Term := .iri (exI "http://ex.org/g")

private def q1 : PackSpec.Quad := (⟨.iri (exI "http://ex.org/a"), exI "http://ex.org/p", litEN⟩, none)
private def q2 : PackSpec.Quad := (⟨.iri (exI "http://ex.org/b"), exI "http://ex.org/p", iriA⟩,
  some (.iri (exI "http://ex.org/g")))

private def gen : MemGen :=
  match packSpec 4096 [q1, q2] [] with
  | some (G, _) => G
  | none => { keys := [], prb := fun _ => ByteArray.empty, ms := fun _ => [], named := #[] }

/-! ## The base dictionary and language tags -/

#guard gen.check
#guard gen.keys.length == 5
-- one id for `"x"@EN` and `"x"@en`, and it decodes to the folded term
#guard (gen.cid litEN).isSome && gen.cid litEN == gen.cid liten
#guard (gen.cid litEN).map gen.dec == some liten
-- the dictionary holds the folded term; since issue 1001 `litEN` is that term
#guard litEN == liten
#guard (toCode? gen.keys liten).isSome
-- every rank of the dictionary is an id whose term has that id
#guard (List.range gen.keys.length).all fun r =>
  match gen.keys[r]? with
  | some k => idOkB gen.keys (dictCode k r)
  | none => false

/-! ## The delta overlay -/

private def newB : Term := .iri (exI "http://ex.org/new")
private def litYFR : Term := .literal (Literal.langString "y" "FR")
private def litYfr : Term := .literal (Literal.langString "y" "fr")
private def bn : Term := .bnode "n1"

/-- The log meets: a new IRI, a base IRI, the base literal with tag `EN`, a
    new literal with tag `FR`, the same with tag `fr`, a new blank node, the
    new IRI again. -/
private def logTerms : List Term := [newB, iriA, litEN, litYFR, litYfr, bn, newB]

private def ov : List Term := vocabAddAll gen.keys [] logTerms

#guard ov == [newB, litYfr, bn]
#guard vocabOk gen.keys ov
-- the base terms keep their base ids
#guard ovEnc gen.keys ov iriA == toCode? gen.keys iriA
#guard ovEnc gen.keys ov (normalizeTerm litEN) == toCode? gen.keys liten
-- `"y"@FR` and `"y"@fr`: one overlay id
#guard idOrNew gen.keys ov litYFR == idOrNew gen.keys ov litYfr
-- the new ids: tag 14, pairwise distinct, none a base id
private def newIds : List Nat := ov.filterMap (ovEnc gen.keys ov)
private def baseIds : List Nat :=
  (List.range gen.keys.length).filterMap fun r => gen.keys[r]?.map (dictCode · r)

#guard newIds.length == 3 && newIds.all (· / two60 == Overlay.tagDelta)
#guard decide newIds.Nodup
#guard newIds.all fun n => !baseIds.contains n
-- every id of a log term decodes to the folded term
#guard logTerms.all fun t =>
  match idOrNew gen.keys ov t with
  | some n => ovDec gen.keys ov n == some (normalizeTerm t)
  | none => false

/-! ## The theorems apply -/

example (G : MemGen) (h : G.check = true) :
    DictInjective (toCode? G.keys) (ofCode? G.keys) G.termHeld G.idUsed :=
  memGen_dictInjective G h

example (G : MemGen) (h : G.check = true) (ov : List Term) (hv : vocabOk G.keys ov = true) :
    DictInjective (ovEnc G.keys ov) (ovDec G.keys ov) (ovHeld G.keys G.idUsed ov) (ovUsed G.idUsed ov) :=
  overlay_dictInjective G.keys ov G.idUsed hv (idUsed_idOkB G h)

example (G : MemGen) (h : G.check = true) (t u : Term) (x y : UInt64)
    (hx : G.cid t = some x) (hy : G.cid u = some y) : x = y ↔ t.eqb u = true :=
  cid_eq_iff_eqb G (check_keys G h) t u x y hx hy

end L4Factoidal.Storage.Sbm11.DictInjectiveTests
