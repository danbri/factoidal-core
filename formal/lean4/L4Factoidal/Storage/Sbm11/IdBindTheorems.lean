/-
L4Factoidal.Storage.Sbm11.IdBindTheorems — BIND on the SBM11 id path
(https://github.com/danbri/factoidal/issues/953, parent
https://github.com/danbri/factoidal/issues/775): the decoding theorem for
`IdQuery.extendM` against SPARQL 1.1 section 18.5 Extend as the reference
evaluator computes it (`bindRowsFresh`, `SPARQL/Algebra.lean`).

## Theorems

* `lower_bind`: at the top level of a WHERE clause the reference lowers
  `BIND(e AS ?v)` over `P` to `GraphPattern.bind (IdQuery.refBinder env e) v
  P'`; so the id path evaluates the reference's own binder.
* `refBinder_active`: for an EXISTS-free `e` the binder does not read the
  active graph (`IdPostTheorems.substituteExistentials_existsFree`), so the
  id path, which has none, passes the empty graph.
* `extend_decode`: over rows of ids (`OptJoinTheorems.IdRow`), `idExtendRows`
  (per row: the binder on the decoded row with the freshness context of the
  row's index; a value gets its id, an error leaves the variable unbound, a
  row that binds the variable keeps it), decoded, is `bindRowsFresh` of the
  decoded rows, when the binder does not read the active graph and each value
  decodes back from its id (`Store.idOf` or a query-local id,
  `IdQuery.termIdM`; the exceptions of `IdJoinTheorems`: language tags in
  the case the packer folds to).
* `bind_decode`: `extend_decode` for the reference binder of an EXISTS-free
  expression.

Not proved (open, the step of lemma L5g″ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md): that the column
`IdQuery.extendM` builds is that of `idExtendRows` of the table's rows. The
implementation decodes only the variables `e` reads and evaluates `e` once per
distinct tuple of their ids; that equals the binder on the whole row with the
freshness context of each row when `Expr.evalIn` reads only those variables
and, for an expression without `UUID()`, `STRUUID()` or `BNODE()`
(`IdQuery.readsRowIndex`; `translate` refuses those), not the freshness
context. Tested by the gate queries `tests/sbm11/gate/ids-bind-*.rq` and by the
census (`tests/sbm11/census.sh`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPostTheorems
import L4Factoidal.Storage.Sbm11.OptJoinTheorems

namespace L4Factoidal.Storage.Sbm11.IdBind

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow decRow idLookup lookup_decRow)
open L4Factoidal.Storage.Sbm11.IdQuery (refBinder)

/-- The reference lowers a top-level `BIND(e AS ?v)` over `q` with
    `IdQuery.refBinder`. -/
theorem lower_bind (env : EvalEnv) (e : Expr) (v : VarName) (q : QueryPattern)
    (h : e.mentionsService = false) :
    QueryPattern.lowerWith env Binding.empty (.bind e v q) =
      .bind (refBinder env e) v (QueryPattern.lowerWith env Binding.empty q) none := by
  simp [QueryPattern.lowerWith, h]
  rfl

/-- For an EXISTS-free expression the binder does not read the active
    graph. -/
theorem refBinder_active (env : EvalEnv) (e : Expr) (he : e.existsFree = true) (active : Graph)
    (row : Binding) : refBinder env e active row = refBinder env e Graph.empty row := by
  unfold refBinder
  dsimp only
  rw [IdPostTheorems.substituteExistentials_existsFree env active _ e he,
    IdPostTheorems.substituteExistentials_existsFree env Graph.empty _ e he]

/-- Extend over rows of ids: per row `r` at index `i`, `f r i` is the id of
    the value, `none` an error (the variable stays unbound); a row that binds
    `v` keeps it. -/
def idExtendRows (f : IdRow → Nat → Option UInt64) (v : String) : List IdRow → Nat → List IdRow
  | [], _ => []
  | r :: rest, i =>
    (match f r i with
     | some x =>
       match idLookup v r with
       | some _ => r
       | none => (v, x) :: r
     | none => r) :: idExtendRows f v rest (i + 1)

/-- Decoding `idExtendRows` gives `bindRowsFresh` (SPARQL 1.1 section 18.5
    Extend, as the reference evaluator computes it) of the decoded rows. -/
theorem extend_decode (dec : UInt64 → Term) (binder : Graph → Binding → Option Term) (active : Graph)
    (v : String) (idv : Term → UInt64)
    (hact : ∀ mu, binder active mu = binder Graph.empty mu)
    (hid : ∀ mu t, binder Graph.empty mu = some t → dec (idv t) = t) :
    ∀ (L : List IdRow) (i : Nat),
      (idExtendRows (fun r j => (binder Graph.empty ((decRow dec r).withFreshnessCtx (toString j) v)).map idv)
          v L i).map (decRow dec) =
        bindRowsFresh binder active v (L.map (decRow dec)) i
  | [], _ => rfl
  | r :: rest, i => by
    simp only [idExtendRows, List.map_cons, bindRowsFresh, hact]
    congr 1
    · cases hb : binder Graph.empty ((decRow dec r).withFreshnessCtx (toString i) v) with
      | none => rfl
      | some t =>
        simp only [Option.map_some, lookup_decRow]
        cases hl : idLookup v r with
        | some _ => rfl
        | none => simp [decRow, Binding.bind, hid _ t hb]
    · exact extend_decode dec binder active v idv hact hid rest (i + 1)

/-- `extend_decode` for the reference binder of an EXISTS-free BIND
    expression (the binder of `lower_bind`). -/
theorem bind_decode (env : EvalEnv) (e : Expr) (he : e.existsFree = true) (dec : UInt64 → Term)
    (idv : Term → UInt64) (active : Graph) (v : String)
    (hid : ∀ mu t, refBinder env e Graph.empty mu = some t → dec (idv t) = t) (L : List IdRow) :
    (idExtendRows (fun r j => (refBinder env e Graph.empty ((decRow dec r).withFreshnessCtx (toString j) v)).map idv)
        v L 0).map (decRow dec) =
      bindRowsFresh (refBinder env e) active v (L.map (decRow dec)) 0 :=
  extend_decode dec (refBinder env e) active v idv (fun mu => refBinder_active env e he active mu) hid L 0

end L4Factoidal.Storage.Sbm11.IdBind
