/-
L4Factoidal.Storage.Sbm11.IdJoinTheorems — inline VALUES on the SBM11 id path
(https://github.com/danbri/factoidal/issues/950, parent
https://github.com/danbri/factoidal/issues/775): the decoding theorems for the
join of `IdJoin.joinIds` and for the id rows of a VALUES block, against
SPARQL 1.1 section 18.5 (`SPARQL/Algebra.lean`).

## Over rows of ids

The rows of ids are those of `OptJoinTheorems` (`IdRow`: (variable, id), an
unbound variable absent; `decRow` decodes each id).

* `idJoin L R`: Join(Ω1, Ω2) over ids, compatibility by id equality
  (`idCompatible`), merge by `idMerge`.
* `join_decode`: decoding `idJoin L R` gives SPARQL 1.1 `join` of the decoded
  rows, as a list (same rows, same order), when `Term.eqb` of two decoded ids
  is id equality on the ids of `L` and `R` (the hypothesis of
  `OptJoinTheorems.leftJoin_decode`).
* `idZip`, `idValues`: the rows of a VALUES block with each term replaced by
  its id, built as `zipBindings` and `evalValues` build the reference rows
  (an UNDEF cell leaves its variable out).
* `values_decode`: decoding `idValues` gives `evalValues` (SPARQL 1.1
  section 10.2, eval(VALUES)) when each term of the block decodes back from
  its id.

`IdQuery.resolveValuesM` gives a VALUES term its id in the generation
(`Store.idOf`), or, when the generation has no id for it, a query-local id
(`IdQuery.tagLocal`, one per distinct normalised term) that `Store.withLocal`
decodes. Both hypotheses then hold on the ids that occur, with the exception
already stated for the stored terms (`Term.eqb` identifies two
`rdf:XMLLiteral` forms with one exclusive canonical form) and with the
terms in the language-tag case the packer folds to (`normalizeTerm`; the
reference compares language tags without case, `Term.eqb`).

Not proved (open, the step of lemma L5g″): that the `Table` that
`IdJoin.joinIds` builds denotes the rows of `idJoin` of the tables' rows,
`unbound` read as absent. Tested by the `#guard`s at the end of this file
and by the gate queries `tests/sbm11/gate/ids-values-*.rq` against the
reference engine.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdJoin
import L4Factoidal.Storage.Sbm11.OptJoinTheorems

namespace L4Factoidal.Storage.Sbm11.IdJoin

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idCompatible idMerge decRow RowIds compatible_decRow
  merge_decRow filterMap_congr' unbound)
open L4Factoidal.SPARQL (Binding SolutionSeq join union evalValues zipBindings)
open L4Factoidal.RDF (Term)

/-! ## Join over ids -/

/-- Join(Ω1, Ω2) over ids (SPARQL 1.1 section 18.5): per left row in order,
    the merges with the compatible right rows in order. -/
def idJoin (L R : List IdRow) : List IdRow :=
  L.flatMap fun r1 => R.filterMap fun r2 => if idCompatible r1 r2 then some (idMerge r1 r2) else none

/-- Decoding the id-level join gives SPARQL 1.1 Join of the decoded
    solutions, row for row, when `Term.eqb` of two decoded ids is id equality
    on the ids that occur. -/
theorem join_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    (idJoin L R).map (decRow dec) = join (L.map (decRow dec)) (R.map (decRow dec)) := by
  unfold idJoin join
  rw [List.map_flatMap, List.flatMap_map]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro r1 h1
  rw [List.filterMap_map, List.map_filterMap]
  apply filterMap_congr'
  intro r2 h2
  simp only [Function.comp_def]
  rw [compatible_decRow dec ok hdec r1 r2 (hL r1 h1) (hR r2 h2), merge_decRow]
  cases idCompatible r1 r2 <;> simp

/-! ## VALUES over ids -/

/-- `zipBindings` over ids: one VALUES row, `none` an UNDEF cell. -/
def idZip : List String → List (Option UInt64) → IdRow → IdRow
  | v :: vs, some x :: xs, r => idZip vs xs ((v, x) :: r)
  | _ :: vs, _ :: xs, r => idZip vs xs r
  | _, _, r => r

/-- `evalValues` over ids: one row of ids per VALUES row. -/
def idValues (vars : List String) (rows : List (List (Option UInt64))) : List IdRow :=
  rows.map fun row => idZip vars row []

theorem zip_decode (dec : UInt64 → Term) (idv : Term → UInt64) :
    ∀ (vars : List String) (row : List (Option Term)) (r : IdRow),
      (∀ t, some t ∈ row → dec (idv t) = t) →
      decRow dec (idZip vars (row.map (·.map idv)) r) = zipBindings vars row (decRow dec r) := by
  intro vars
  induction vars with
  | nil =>
    intro row r _
    cases row with
    | nil => rfl
    | cons c cs => cases c <;> rfl
  | cons v vs ih =>
    intro row r h
    cases row with
    | nil => rfl
    | cons c cs =>
      have hcs : ∀ t, some t ∈ cs → dec (idv t) = t := fun t ht => h t (List.mem_cons_of_mem _ ht)
      cases c with
      | none =>
        simp only [List.map_cons, Option.map_none, idZip, zipBindings]
        exact ih cs r hcs
      | some t =>
        simp only [List.map_cons, Option.map_some, idZip, zipBindings]
        rw [ih cs ((v, idv t) :: r) hcs]
        have ht : dec (idv t) = t := h t (List.mem_cons_self ..)
        simp [decRow, Binding.bind, ht]

/-- Decoding the id rows of a VALUES block gives eval(VALUES) (SPARQL 1.1
    sections 10.2 and 18.6, `evalValues`) when every term of the block decodes
    back from its id. -/
theorem values_decode (dec : UInt64 → Term) (idv : Term → UInt64) (vars : List String)
    (rows : List (List (Option Term)))
    (h : ∀ row ∈ rows, ∀ t, some t ∈ row → dec (idv t) = t) :
    (idValues vars (rows.map fun row => row.map (·.map idv))).map (decRow dec) =
      evalValues vars rows := by
  unfold idValues evalValues
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro row hrow
  simp only [Function.comp_def]
  exact zip_decode dec idv vars row [] (h row hrow)

/-! ## UNION over ids -/

/-- Decoding a concatenation of id rows gives SPARQL 1.1 Union (section 18.5,
    multiset union) of the decoded rows, as a list. -/
theorem union_decode (dec : UInt64 → Term) (L R : List IdRow) :
    (L ++ R).map (decRow dec) = union (L.map (decRow dec)) (R.map (decRow dec)) := by
  unfold union
  exact List.map_append

/-- A chain `{ P1 } UNION { P2 } UNION ... UNION { Pk }` parses as
    `Union(... Union(P1, P2) ..., Pk)`: decoding the concatenation of the
    branches' id rows (`IdJoin.unionIds`) is that left-nested Union of the
    decoded branches, after any rows `acc` already decoded. -/
theorem unionChain_decode (f : IdRow → Binding) :
    ∀ (Ls : List (List IdRow)) (acc : SolutionSeq),
      acc ++ Ls.flatten.map f = Ls.foldl (fun a L => union a (L.map f)) acc := by
  intro Ls
  induction Ls with
  | nil => intro acc; simp
  | cons L Ls ih =>
    intro acc
    rw [List.flatten_cons, List.map_append, List.foldl_cons, ← ih (union acc (L.map f))]
    unfold union
    rw [List.append_assoc]

/-! ## The `Table` implementation against `idJoin`, on samples

The step from `Table` columns to rows is not proved (module header). Here
`joinIds` (the hash path with every shared column bound, rows with UNDEF on
either side, no shared column, an empty side, a VALUES block with no
variable, a WHERE clause of VALUES blocks only) is compared with `idJoin`
over the rows of the sample tables: the same rows in the same order, each
row's bindings compared as a set. -/

private def col (xs : List Nat) : ByteArray :=
  xs.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x.toUInt64) ByteArray.empty

private def tab (vars : Array String) (cs : List (List Nat)) (sortVar : Option String := none) : Table :=
  { vars, cols := (cs.map col).toArray, rows := (cs.headD []).length, sortVar }

private def sortRow (r : IdRow) : IdRow := r.mergeSort fun a b => decide (a.1 ≤ b.1)

private def rowsOfTable (t : Table) : List IdRow :=
  (List.range t.rows).map fun i =>
    sortRow ((List.range t.vars.size).filterMap fun c =>
      let x := t.at c i
      if x == unbound then none else some (t.vars[c]!, x))

private def agrees (l r : Table) : Bool :=
  rowsOfTable (joinIds l r) == (idJoin (rowsOfTable l) (rowsOfTable r)).map sortRow

private def L1 : Table := tab #["s", "a"] [[1, 1, 2, 3, 5], [10, 11, 12, 13, 14]] (some "s")
private def V1 : Table := tab #["s"] [[1, 0, 2, 9]]
private def V2 : Table := tab #["s", "z"] [[2, 0, 1], [70, 71, 0]]
private def V3 : Table := tab #["a", "z"] [[0, 13], [80, 0]]
private def V4 : Table := { vars := #[], cols := #[], rows := 2 }
private def V5 : Table := tab #["s"] [[]]
private def V6 : Table := tab #["q"] [[40, 0, 41]]
private def L0 : Table := { vars := #[], cols := #[], rows := 1 }
private def Lu : Table := tab #["x", "y"] [[1, 0, 2], [0, 5, 6]]
private def Ru : Table := tab #["x", "y"] [[1, 0, 2], [5, 6, 0]]

#guard agrees L1 V1 && (joinIds L1 V1).rows == 8
#guard agrees L1 V2 && agrees L1 V3 && agrees L1 V6
#guard agrees L1 V4 && (joinIds L1 V4).rows == 10
#guard agrees L1 V5 && (joinIds L1 V5).rows == 0
#guard agrees V5 L1 && agrees V2 L1 && agrees V3 V2
#guard agrees L0 V2 && agrees (joinIds L0 V2) V3 && (joinIds L0 V2).rows == 3
#guard agrees Lu Ru && agrees Ru Lu
-- the left sort variable is kept when the right table does not have it
#guard (joinIds L1 V3).sortVar == some "s" && (joinIds L1 V1).sortVar == none
-- a shared column takes the right id where the left one is unbound
#guard (rowsOfTable (joinIds Lu Ru)).contains [("x", 1), ("y", 5)]

-- `unionIds` against the concatenation of the rows: branches with different
-- variables, an empty branch, a branch with unbound ids, a single branch
private def agreesUnion (ts : List Table) : Bool :=
  rowsOfTable (unionIds ts.toArray) == (ts.map rowsOfTable).flatten

#guard agreesUnion [L1, V2, V3] && (unionIds #[L1, V2, V3]).rows == 10
#guard agreesUnion [V5, L1] && agreesUnion [Lu, Ru, V6] && agreesUnion [L1] && agreesUnion []
#guard (unionIds #[L1, V2]).vars == #["s", "a", "z"]
-- a union joined with a left table (the shape `{ P { A } UNION { B } }`)
#guard agrees L1 (unionIds #[V1, V3])

end L4Factoidal.Storage.Sbm11.IdJoin
