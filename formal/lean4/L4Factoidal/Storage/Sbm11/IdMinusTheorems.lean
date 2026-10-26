/-
L4Factoidal.Storage.Sbm11.IdMinusTheorems — MINUS on the SBM11 id path
(https://github.com/danbri/factoidal/issues/956, SPARQL 1.1 sections 8 and
18.5).

SPARQL 1.1 section 18.5:

    Minus(Ω1, Ω2) = { μ1 in Ω1 | for every μ2 in Ω2, μ1 and μ2 are not
                      compatible or dom(μ1) and dom(μ2) are disjoint }

The reference evaluates `P MINUS { B }` as `hashMinus` of the two sides,
which `IndexedEvalRefinement.hashMinus_eq_minus` proves equal to
`SPARQL.minus`, list order included. Unlike EXISTS, MINUS does not substitute:
both sides are evaluated by themselves, so no row is outside the fragment.

* `idMinus`: Minus over rows of ids (compatibility by id equality,
  `OptJoin.idCompatible`; disjoint domains by the variables present,
  `idDisjoint`).
* `disjoint_decRow`: `domainsDisjoint` of decoded rows is `idDisjoint`.
* `minus_decode`: decoding `idMinus L R` is `SPARQL.minus` of the decoded
  rows, as a list (same rows, same order), when `Term.eqb` of two decoded ids
  is id equality on the ids that occur.
* `minus_bgp_decode`: when the rows of `L` decode to the left side's
  solutions and the rows of `R` to `evalBgp B g`, decoding `idMinus L R` is
  the reference's `(GraphPattern.minus l (.bgp B)).evalIn ds g`.

Not proved here (open, lemma L5a′ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md): that the `Table`
step (`IdQuery.semiMatches` with `needShared`, per-mask hash sets) denotes
`idMinus`, and that the right side's scans decode to `evalBgp B g`. Tested by
the `#guard`s below and by `tests/sbm11/run.sh` part (d), the `ids-minus-*`
queries.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdExistsTheorems
import L4Factoidal.Storage.Sbm11.IdQuery

namespace L4Factoidal.Storage.Sbm11.IdMinus

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible decRow RowIds compatible_decRow
  lookup_decRow)

/-- dom(μ1) ∩ dom(μ2) = ∅ over rows of ids (`domainsDisjoint`). -/
def idDisjoint : IdRow → IdRow → Bool
  | [], _ => true
  | (v, _) :: rest, r2 => (idLookup v r2).isNone && idDisjoint rest r2

/-- Minus(Ω1, Ω2) over rows of ids. -/
def idMinus (L R : List IdRow) : List IdRow :=
  L.filter fun r1 => !R.any fun r2 => idCompatible r1 r2 && !idDisjoint r1 r2

theorem disjoint_decRow (dec : UInt64 → Term) :
    ∀ (r1 r2 : IdRow), domainsDisjoint (decRow dec r1) (decRow dec r2) = idDisjoint r1 r2
  | [], _ => rfl
  | (v, x) :: rest, r2 => by
    have e : decRow dec ((v, x) :: rest) = (v, dec x) :: decRow dec rest := rfl
    rw [e]
    simp only [domainsDisjoint, idDisjoint]
    rw [lookup_decRow, disjoint_decRow dec rest r2]
    cases idLookup v r2 <;> rfl

/-- **MINUS on ids.** Decoding the id-level Minus gives SPARQL 1.1 Minus of
    the decoded rows, row for row, when `Term.eqb` of two decoded ids is id
    equality on the ids that occur. -/
theorem minus_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    (idMinus L R).map (decRow dec) = minus (L.map (decRow dec)) (R.map (decRow dec)) := by
  unfold idMinus minus
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro r1 h1
  simp only [Function.comp_def, List.any_map]
  congr 1
  apply IdExists.any_congr'
  intro r2 h2
  rw [compatible_decRow dec ok hdec r1 r2 (hL r1 h1) (hR r2 h2), disjoint_decRow]

/-- The reference evaluation of `P MINUS { B }`, `B` a basic graph pattern,
    is the id-level Minus of the rows of `P` and of `B`, decoded. -/
theorem minus_bgp_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (ds : Dataset) (g : Graph) (l : GraphPattern) (b : Bgp)
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r)
    (hleft : L.map (decRow dec) = l.evalIn ds g)
    (hbody : R.map (decRow dec) = evalBgp b g) :
    (idMinus L R).map (decRow dec) = (GraphPattern.minus l (.bgp b)).evalIn ds g := by
  rw [minus_decode dec ok hdec L R hL hR, hleft, hbody, GraphPattern.evalIn, hashMinus_eq_minus,
    evalIn_bgp]

#print axioms disjoint_decRow
#print axioms minus_decode
#print axioms minus_bgp_decode

/-! ## Checks

`IdQuery.semiMatches` with `needShared` on sample tables against `idMinus`
on their rows (`OptJoin.unbound`, id 0, read as absent). -/

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (unbound)

private def col (xs : List Nat) : ByteArray :=
  xs.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x.toUInt64) ByteArray.empty

private def tab (vars : Array String) (cs : List (List Nat)) : Table :=
  { vars, cols := (cs.map col).toArray, rows := (cs.headD []).length }

private def rowsOfTable (t : Table) : List IdRow :=
  (List.range t.rows).map fun i =>
    (List.range t.vars.size).filterMap fun c =>
      let x := t.at c i
      if x == unbound then none else some (t.vars[c]!, x)

private def agrees (l r : Table) : Bool :=
  let hits := IdQuery.semiMatches l r true
  let kept := (List.range l.rows).filter fun i => !hits[i]!
  kept.map (fun i => (rowsOfTable l)[i]!) == idMinus (rowsOfTable l) (rowsOfTable r)

private def L1 : Table := tab #["s", "a"] [[1, 1, 2, 3, 5], [10, 11, 12, 13, 14]]
private def R1 : Table := tab #["s", "o"] [[1, 3, 3], [20, 21, 22]]
private def R3 : Table := tab #["z"] [[7]]
private def R5 : Table := { vars := #[], cols := #[], rows := 1 }
private def Lu : Table := tab #["s", "a"] [[1, 0, 2, 0], [0, 11, 0, 0]]
private def Ru : Table := tab #["s", "a"] [[2, 0], [11, 12]]

#guard agrees L1 R1 && agrees L1 R3 && agrees L1 R5 && agrees Lu Ru && agrees Lu R1
-- no shared variable: dom(μ1) and dom(μ2) disjoint, every row kept
#guard (IdQuery.semiMatches L1 R3 true).toList == [false, false, false, false, false]
-- the row with no bound shared variable is kept; the others removed by a compatible row
#guard (IdQuery.semiMatches Lu Ru true).toList == [false, true, true, false]
#guard idMinus [[("s", 1)], [("s", 2)], []] [[("s", 2)]] == [[("s", 1)], []]

end L4Factoidal.Storage.Sbm11.IdMinus
