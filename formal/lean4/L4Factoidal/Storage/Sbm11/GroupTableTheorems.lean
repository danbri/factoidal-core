/-
L4Factoidal.Storage.Sbm11.GroupTableTheorems — the `Table` operators of the
nested evaluator `IdGroup.evalGroupM` and the WHERE clause it returns
(https://github.com/danbri/factoidal/issues/776; lemma L5t of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`ExecLeafTheorems` executes the leaves of the WHERE clause (L4m, L4n) and a
join whose right side is a property path (L4o); the operators above them
were the list evaluator `IdGroup.evalGroupIds`. This file proves the
operators that `evalGroupM` runs on `Table`s and composes them by
induction on the pattern:

* MINUS: `SemiTableTheorems.minus_rows` (moved there on 2026-10-23 with
  `semiMatches_spec`).
* `query_where_allowed_exec`: for every pattern built from basic graph
  patterns, property paths, `{}`, Join, LeftJoin (OPTIONAL) with the
  condition `true` (`LeftJoinTableTheorems`) or with a condition whose
  conjuncts are EXISTS-free conjuncts, `EXISTS { B }` and `NOT EXISTS { B }`
  of a basic graph pattern, `EXISTS {}` and `NOT EXISTS {}`, FILTER with such
  a condition (`FilterTableTheorems`, `ExistsTableTheorems`),
  Union, MINUS, GRAPH with an IRI, GRAPH with a variable over a pattern that
  is not a nonempty basic graph pattern, `{}` included (`graphVar_ends`,
  `GraphVarTableTheorems`) and
  over a nonempty basic graph pattern (`graphBgp_ends`, one scan per triple
  pattern with the graph as a column, `GraphBgpTableTheorems`), VALUES and
  BIND (`LocalTableTheorems`), and a sub-SELECT (`SubSelectTableTheorems`:
  a projection of variables on ids, or `SELECT` with a list of items whose
  variables are distinct and no EXISTS outside its WHERE clause, with any
  GROUP BY, HAVING, aggregate, expression, ORDER BY, OFFSET, LIMIT,
  DISTINCT or REDUCED; or `SELECT *` with no GROUP BY and no EXISTS outside
  its WHERE clause, whose rows bind only variables in scope,
  `ScopeTheorems`), at any depth (`ExecHyps`),
  `evalGroupM` run from any state that keeps the invariant of the
  query-local vocabulary (`LocalVocab.Inv`) refuses with a refusal of that
  vocabulary (`LocalVocab.LocalRefusal`), or returns a well-formed table
  whose rows decode, with the decoder of the final state
  (`LocalVocab.decV`), to an answer SPARQL 1.1 allows (`IdGroup.Allowed`),
  with ids of that state; the final state keeps the invariant and extends
  the vocabulary (`WhereOk`). The hypotheses are on the store, the
  dictionary, the dataset, the environment, the first state and the syntax
  of the conditions only; none states the table of a pattern or of a
  subpattern. `Table.select` is `FilterTableTheorems.select_spec`.

## Why the statement is `Allowed`, not `IdEquiv` to `evalGroupIds`

The induction composes each `Table` operator with the decoding lemma of its
list form (`IdJoin.join_decode`, `IdMinus.minus_decode`, ...) and the rule
`Allowed.equiv`, each with the decoder of the state after the operator
(`LocalVocabTheorems`: the decoder of a later state decodes the ids of an
earlier one the same). It does not state the table as `IdEquiv` to
`evalGroupIds`: (1) `evalGroupIds` encodes terms with one function `idv`,
while `evalGroupM` gives a term with no store id a query-local id that
depends on the state (`termIdM`), so for BIND, VALUES and a sub-SELECT the
two encodings differ; (2) for a FILTER or a LeftJoin condition, `IdEquiv`
of the inputs gives the output only if the condition has the same value on
two rows that are the same solution mapping with their pairs in another
order (proved since: `ExprLocalTheorems.evalIn_bindEq`). `Allowed` needs
neither; the FILTER and LeftJoin cases use the locality lemma only for the
memoised conjuncts and for the merged rows of a pair.

## Not proved here

FILTER and LeftJoin conditions with EXISTS of a pattern that is not a basic
graph pattern or `{}`, or EXISTS inside an expression (`filterKindsM` refuses
both), with a blank node in an EXISTS body (`ExecLeafTheorems.ExecTp`), with a
UUID, STRUUID or BNODE call, or with a STRSTARTS, STRENDS or CONTAINS test on
dictionary keys (`FilterIdTheorems.StrForm`); a `SELECT *` sub-SELECT with
GROUP BY, or over a WHERE clause with a `text:query` pattern or a nested
`SELECT *` with GROUP BY (`ScopeTheorems.ScopeOk`), and a sub-SELECT with a
variable projected twice: `ExecHyps` is `False` for them. VALUES with a variable twice
and BIND with an expression that reads a freshness key (UUID, STRUUID,
BNODE): `ExecHyps` is `False`. A VALUES term or a BIND value with a
language tag not in lower case is refused at run time (`IdQuery.valueIdM`;
until 2026-10-23 the id path folded the tag and `LANG` read `"en"` where the
reference reads `"EN"`). Tested by `tests/sbm11/gate/ids-*.rq` and the W3C
census.


No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ExistsTableTheorems
import L4Factoidal.Storage.Sbm11.ScopeTheorems
import L4Factoidal.Storage.Sbm11.GraphVarTableTheorems
import L4Factoidal.Storage.Sbm11.GraphBgpTableTheorems
import L4Factoidal.Storage.Sbm11.SubSelectTableTheorems

namespace L4Factoidal.Storage.Sbm11.GroupTableTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound RowIds decRow)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq RowsEq ColHolds forIn_range_inv range'_succ_filter
  gather_at)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd)
open L4Factoidal.Storage.Sbm11.FilterTableTheorems (select_spec)
open L4Factoidal.Storage.Sbm11.SemiTableTheorems (minus_rows)
open L4Factoidal.Storage.Sbm11.ExistsTableTheorems (cidOkV FilterExOk HasExists ExistsBgp TagKind)

/-! ## The WHERE clause as `evalGroupM` runs it -/

section main

open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt GCtx evalGroupM unitTable Allowed)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems
open L4Factoidal.Storage.Sbm11.IdLeaf (Listings spo StoreGraph StoreLeaf CidOk)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem)
open L4Factoidal.Storage.Sbm11.IdMinus (idMinus)
open L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems (note_run leftJoinTrue_run leftJoinTrue_rows ljTable)
open L4Factoidal.Storage.Sbm11.LocalVocab

/-- `CidOk` on a larger set of ids gives it on a smaller one. -/
theorem cidOk_sok {dec : UInt64 → Term} {sok ok : UInt64 → Prop} (hsok : ∀ x, sok x → ok x)
    {cid : Term → Option UInt64} (h : ∀ c, CidOk dec ok c (cid c)) : ∀ c, CidOk dec sok c (cid c) := by
  intro c
  have := h c
  cases e : cid c with
  | none => rw [e] at this; exact fun y hy => this y (hsok y hy)
  | some x => rw [e] at this; exact fun y hy => this y (hsok y hy)

/-- The store's rows with a graph id other than 0 are in the named graphs
    `cx.named` lists: `GRAPH ?g` over a basic graph pattern scans every such
    row (`IdGroup.bgpGraphVarM`). -/
def NamedRows (cx : NCx Id) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta) : Prop :=
  ∀ k, k < 4 → ∀ r ∈ (ms k).flatMap (ScanFoldTheorems.blockRows (prb k)), r.g ≠ 0 → r.g.toUInt64 ∈ cx.named.toList

/-- The patterns this file proves, with what each node needs: at a leaf
    (basic graph pattern, property path) the condition `LP`; at GRAPH with
    an IRI, a store that lists its named graphs, and the IRI is a named graph
    of the dataset exactly when the dictionary gives it an id among the
    query's named graphs (`cx.named`), the id of the active graph `gof g`;
    at LeftJoin, the condition `true`, or the conditions of FILTER; at
    FILTER, `ExistsTableTheorems.FilterExOk` (each conjunct an EXISTS-free
    `FilterIdTheorems.CjOk` conjunct, `EXISTS { B }` or `NOT EXISTS { B }` of
    a basic graph pattern with positions that are variables, IRIs or
    literals and no `text:query` predicate, `EXISTS {}` or `NOT EXISTS {}`),
    `XD` when some conjunct has EXISTS (the environment has a dataset, which
    the reference reads for EXISTS), and `LP` of each EXISTS body `B` in the
    active graph; at VALUES, distinct variables; at BIND, an
    EXISTS-free expression whose variables `residualVars` lists and that
    reads no freshness key (no UUID, STRUUID or BNODE; `translate` refuses
    those). A VALUES term or a BIND value with a language tag not in lower
    case (`STRLANG("a", "EN")`) is refused at run time (`IdQuery.valueIdM`:
    the id path folds tags, RDF 1.1 Concepts 3.3, and `Allowed` compares
    terms exactly), and the harness runs the reference evaluator. At a
    sub-SELECT: the conditions of its WHERE clause, and a projection of
    variables (`IdGroup.plainProjection?`), or `SELECT items` with the
    variables of `items` distinct and no EXISTS outside the WHERE clause
    (`Query.expressionsOutsidePatternExistsFree`, which `nestedRefusal?`
    checks), or `SELECT *` with no GROUP BY, no EXISTS outside the WHERE
    clause and a WHERE clause that is `ScopeTheorems.ScopeOk`. `False` for the constructors not proved here (LATERAL,
    SERVICE). At
    GRAPH with a variable over a nonempty basic graph pattern
    (`IdGroup.bgpGraphVarM`, one scan per triple pattern with the graph as a
    column): triple patterns whose positions are variables, IRIs or
    literals, distinct ids in `cx.named`, `cx.named` listing in the order of
    `ds.named` the ids the dictionary gives their names, each the active
    graph `gof` gives the graph, `NG` (the store's rows with a graph id other
    than 0 are in those graphs, `NamedRows`), and `LP` of the basic graph
    pattern in each named graph. At GRAPH with a variable over a pattern
    that is not a nonempty basic graph pattern (`{}` included: one row per
    named graph): a store that lists its named graphs,
    distinct named graphs in the dataset, the same `cx.named`, and the
    pattern's conditions in each named graph. -/
def ExecHyps (LP : QueryPattern → Graph → Prop) (NG : Prop) (XD : Prop) (cx : NCx Id)
    (cid : Term → Option UInt64) (ds : Dataset)
    (gof : Graph → GCtx) : QueryPattern → Graph → Prop
  | .bgp b, a => LP (.bgp b) a
  | .propertyPath s path o, a => LP (.propertyPath s path o) a
  | .empty, _ => True
  | .join l r, a => ExecHyps LP NG XD cx cid ds gof l a ∧ ExecHyps LP NG XD cx cid ds gof r a
  | .leftJoin l r c, a => (c = .boolLit true ∨
      (FilterExOk c ∧ (HasExists c → XD) ∧ ∀ b, ExistsBgp c b → LP (.bgp b) a)) ∧
      ExecHyps LP NG XD cx cid ds gof l a ∧ ExecHyps LP NG XD cx cid ds gof r a
  | .filter c q, a => FilterExOk c ∧ (HasExists c → XD) ∧ (∀ b, ExistsBgp c b → LP (.bgp b) a) ∧
      ExecHyps LP NG XD cx cid ds gof q a
  | .union l r, a => ExecHyps LP NG XD cx cid ds gof l a ∧ ExecHyps LP NG XD cx cid ds gof r a
  | .minus l r, a => ExecHyps LP NG XD cx cid ds gof l a ∧ ExecHyps LP NG XD cx cid ds gof r a
  | .graph (.iri i) q, _ => cx.st.namedGraphs.isSome ∧
    match ds.lookupNamedIri i.val with
    | some g => (∃ x, cid (.iri i) = some x ∧ cx.named.contains x = true ∧ gof g = .named x) ∧
        ExecHyps LP NG XD cx cid ds gof q g
    | none => ∀ x, cid (.iri i) = some x → cx.named.contains x = false
  | .graph (.var _) q, _ =>
    (∃ b, q = .bgp b ∧ b ≠ [] ∧ (∀ tp ∈ b, ExecTp tp) ∧ cx.named.toList.Nodup ∧
      FilterTableTheorems.Fa2 (fun x (ng : NamedGraph) => cid ng.name.toTerm = some x ∧ gof ng.graph = .named x)
        cx.named.toList ds.named ∧ NG ∧ ∀ ng ∈ ds.named, LP (.bgp b) ng.graph) ∨
    (cx.st.namedGraphs.isSome ∧ (∀ tps, q = .bgp tps → tps = []) ∧ ds.named.Nodup ∧
      FilterTableTheorems.Fa2 (fun x (ng : NamedGraph) => cid ng.name.toTerm = some x ∧ gof ng.graph = .named x)
        cx.named.toList ds.named ∧
      ∀ ng ∈ ds.named, ExecHyps LP NG XD cx cid ds gof q ng.graph)
  | .values vars _, _ => vars.Nodup
  | .bind e _ q, a => e.existsFree = true ∧ (∃ vs, residualVars e = some vs) ∧
      (∀ w ∈ e.refVars, ¬ ExprLocalTheorems.IsFx w) ∧ ExecHyps LP NG XD cx cid ds gof q a
  | .subSelect (.mk form dcs inner gb hv md pv bs), a => ExecHyps LP NG XD cx cid ds gof inner a ∧
      ((IdGroup.plainProjection? (.mk form dcs inner gb hv md pv bs)).isSome ∨
        (∃ items, form = .select (.vars items) ∧ (selectItemVars items).Nodup ∧
          (Query.mk form dcs inner gb hv md pv bs).expressionsOutsidePatternExistsFree = true) ∨
        (form = .select .all ∧ gb = none ∧
          (Query.mk form dcs inner gb hv md pv bs).expressionsOutsidePatternExistsFree = true ∧
          ScopeTheorems.ScopeOk inner))
  | _, _ => False

/-- What the nested evaluator gives for `p` from the state `nst1`: a
    well-formed table whose rows decode, with the decoder of the final state
    `nst2` (`LocalVocab.decV`), to an answer SPARQL 1.1 allows, with ids of
    that state (`LocalVocab.okV`); the final state keeps the invariant of the
    query-local vocabulary and extends the vocabulary of `nst1`. -/
def WhereOk (env : EvalEnv) (ds : Dataset) (cid : Term → Option UInt64) (dec : UInt64 → Term)
    (ok : UInt64 → Prop) (p : QueryPattern) (a : Graph) (nst1 : NSt) (t : Table) (nst2 : NSt) : Prop :=
  t.WF ∧ Allowed env ds p a (t.idRows.map (decRow (decV dec nst2.vocab))) ∧
    (∀ r ∈ t.idRows, RowIds (okV ok nst2.vocab) r) ∧ LocalVocab.Inv cid nst2 ∧
    nst1.vocab.toList <+: nst2.vocab.toList

theorem allowed_mono (env : EvalEnv) (ds : Dataset) (dec : UInt64 → Term) {ok : UInt64 → Prop}
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) {p : QueryPattern} {a : Graph} {L : List IdRow}
    {voc1 voc2 : Array Term} (hp : voc1.toList <+: voc2.toList) (hsz : voc2.size ≤ two60)
    (hA : Allowed env ds p a (L.map (decRow (decV dec voc1)))) (hL : ∀ r ∈ L, RowIds (okV ok voc1) r) :
    Allowed env ds p a (L.map (decRow (decV dec voc2))) ∧ ∀ r ∈ L, RowIds (okV ok voc2) r := by
  rw [← rows_mono dec hloc hp hsz L hL] at hA
  exact ⟨hA, fun r hr => rowIds_mono hp (hL r hr)⟩

/-- Rows of ids in `ok` decode with the decoder of any state as with `dec`. -/
theorem rows_ok (dec : UInt64 → Term) {ok : UInt64 → Prop} (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (voc : Array Term) (L : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) :
    L.map (decRow (decV dec voc)) = L.map (decRow dec) := by
  apply List.map_congr_left
  intro r hr
  unfold decRow
  apply List.map_congr_left
  intro p hp
  obtain ⟨v, x⟩ := p
  simp only [decV_ok dec hloc voc (hL r hr (v, x) hp)]

theorem inv_congr {cid : Term → Option UInt64} {s1 s2 : NSt} (h1 : s2.vocab = s1.vocab)
    (h2 : s2.localIdx = s1.localIdx) (h : LocalVocab.Inv cid s1) : LocalVocab.Inv cid s2 := by
  unfold LocalVocab.Inv; rw [h1, h2]; exact h

section
variable (cx : NCx Id) (gof : Graph → GCtx) (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta)
  (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)

theorem pw_map {α β : Type} {R : α → α → Prop} {S : β → β → Prop} (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b)) :
    ∀ {A B : List α}, IdGroup.Pw R A B → IdGroup.Pw S (A.map f) (B.map f)
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (hf _ _ h) (pw_map f hf t)

/-- Decoding the rows `IdGroup.idBindG` gives is `Binding.bindIfCompatible` on
    the decoded rows. -/
theorem bindG_rows (D : UInt64 → Term) (okD : UInt64 → Prop)
    (hdec : ∀ x y, okD x → okD y → (D x).eqb (D y) = (x == y)) (v : String) (x : UInt64) (hx : okD x)
    (R : List IdRow) (hR : ∀ r ∈ R, RowIds okD r) :
    (R.filterMap (IdGroup.idBindG v x)).map (decRow D) =
      (R.map (decRow D)).filterMap (Binding.bindIfCompatible v (D x)) := by
  rw [List.filterMap_map, List.map_filterMap]
  apply OptJoin.filterMap_congr'
  intro r hr
  simp only [Function.comp_def]
  rw [IdGroup.bindG_decode D okD hdec v x hx r (hR r hr)]

/-- The arm of `evalGroupM` for `GRAPH ?v q` when `q` is not a nonempty
    basic graph pattern: per id of `cx.named`, `q` with that named graph
    active and `?v` bound, the tables concatenated. -/
def graphVarLoop (cx : NCx Id) (v : String) (q : QueryPattern) : IdGroup.NM Id Table := do
  if cx.st.namedGraphs.isNone then throw "refused: GRAPH on a store with no list of named graphs"
  let mut parts : Array Table := #[]
  for x in cx.named do
    let t ← evalGroupM cx q (.named x)
    parts := parts.push (IdGroup.bindGraph t v x)
  let u := IdJoin.unionIds parts
  IdGroup.note s!"GRAPH ?{v}: {cx.named.size} named graphs, {u.rows} rows"
  return u

/-- `evalGroupM` of `GRAPH ?v q` for `q` not a nonempty basic graph pattern
    (`{}` included) is `graphVarLoop`. -/
theorem graphVar_eq (cx : NCx Id) (v : String) (q : QueryPattern) (g : GCtx)
    (hnb : ∀ tps, q = .bgp tps → tps = []) : evalGroupM cx (.graph (.var v) q) g = graphVarLoop cx v q := by
  by_cases hq : ∃ tps, q = .bgp tps
  · obtain ⟨tps, rfl⟩ := hq
    obtain rfl := hnb tps rfl
    rw [evalGroupM]
    rfl
  · rw [evalGroupM]
    · rfl
    · exact fun tps e => hq ⟨tps, e⟩

/-- **GRAPH with a variable as the nested evaluator runs it**, for a pattern
    that is not a nonempty basic graph pattern (one of those is one scan with the
    graph as a column, `graphBgp_ends`; `{}` is not one): per id of
    `cx.named` in order, the pattern with that named graph active, `?v`
    bound to the id (`IdGroup.bindGraph`), the tables concatenated
    (`IdJoin.unionIds`). Hypotheses besides those of the pattern
    (`IH`, per named graph of the dataset): the store lists its named graphs,
    the dataset's named graphs are distinct, and `cx.named` lists, in the
    order of `ds.named`, the ids the dictionary gives their names, each the
    active graph `gof` gives the graph. -/
theorem graphVar_ends (env : EvalEnv) (ds : Dataset)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hcid : ∀ c, CidOk dec ok c (cid c))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (v : String) (q : QueryPattern) (hng : cx.st.namedGraphs.isSome) (hnb : ∀ tps, q = .bgp tps → tps = [])
    (hnd : ds.named.Nodup)
    (hfa : FilterTableTheorems.Fa2 (fun x (ng : NamedGraph) => cid ng.name.toTerm = some x ∧ gof ng.graph = .named x)
      cx.named.toList ds.named)
    (IH : ∀ ng ∈ ds.named, ∀ s, LocalVocab.Inv cid s →
      Ends ((evalGroupM cx q (gof ng.graph)).run s) (WhereOk env ds cid dec ok q ng.graph s))
    (a : Graph) (nst1 : NSt) (hi1 : LocalVocab.Inv cid nst1) :
    Ends ((evalGroupM cx (.graph (.var v) q) (gof a)).run nst1)
      (WhereOk env ds cid dec ok (.graph (.var v) q) a nst1) := by
  obtain ⟨hlen, hR⟩ := GraphVar.fa2_get hfa
  have hnone : cx.st.namedGraphs.isNone = false := by
    cases e : cx.st.namedGraphs with
    | none => rw [e] at hng; cases hng
    | some _ => rfl
  let P : Nat → Array Table → NSt → Prop := fun k parts s =>
    LocalVocab.Inv cid s ∧ nst1.vocab.toList <+: s.vocab.toList ∧ parts.size = k ∧
    ∀ j, j < k → ∃ (tj : Table) (x : UInt64) (ng : NamedGraph), cx.named.toList[j]? = some x ∧
      ds.named[j]? = some ng ∧ parts[j]? = some (IdGroup.bindGraph tj v x) ∧ tj.WF ∧
      Allowed env ds q ng.graph (tj.idRows.map (decRow (decV dec s.vocab))) ∧
      ∀ r ∈ tj.idRows, RowIds (okV ok s.vocab) r
  have hx0 : ∀ (x : UInt64) (ng : NamedGraph), cid ng.name.toTerm = some x → x ≠ OptJoin.unbound :=
    fun x ng h => hcid0 _ x h
  rw [graphVar_eq cx v q (gof a) hnb]
  unfold graphVarLoop
  · simp only [hnone, Bool.false_eq_true, if_false]
    rw [← Array.forIn_toList]
    refine ends_bind (GraphVar.forIn_nm_ends _ cx.named.toList P #[] nst1
      ⟨hi1, List.prefix_refl _, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_) fun parts sF hP => ?_
    · -- one named graph
      intro k hk parts s ⟨hs1, hs2, hs3, hs4⟩
      have hkL : k < ds.named.length := by rw [← hlen]; exact hk
      obtain ⟨hcx, hgx⟩ := hR k cx.named.toList[k] ds.named[k] (List.getElem?_eq_getElem hk)
        (List.getElem?_eq_getElem hkL)
      show Ends ((evalGroupM cx q (.named cx.named.toList[k]) >>= fun t =>
        pure (ForInStep.yield (parts.push (IdGroup.bindGraph t v cx.named.toList[k])))).run s) _
      rw [← hgx]
      refine ends_bind (IH ds.named[k] (List.getElem_mem hkL) s hs1) fun t s' ⟨hwt, hAt, hot, hi', hp'⟩ =>
        ends_pure rfl ⟨_, rfl, hi', hs2.trans hp', by simp [hs3], fun j hj => ?_⟩
      by_cases hjk : j < k
      · obtain ⟨tj, x, ng, h1, h2, h3, h4, h5, h6⟩ := hs4 j hjk
        obtain ⟨h5', h6'⟩ := allowed_mono env ds dec hloc hp' hi'.size h5 h6
        refine ⟨tj, x, ng, h1, h2, ?_, h4, h5', h6'⟩
        rw [Array.getElem?_push, if_neg (by omega)]; exact h3
      · have : j = k := by omega
        subst this
        refine ⟨t, _, _, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hkL, ?_, hwt, hAt, hot⟩
        rw [Array.getElem?_push, if_pos (by omega)]
    · -- the union of the parts
      obtain ⟨hiF, hpF, hszF, hF⟩ := hP
      have hdecV' := hdecV cid dec ok hdec hcid hloc hiF
      -- each part
      have hpart : ∀ j (hj : j < parts.size), ∃ (tj : Table) (x : UInt64) (ng : NamedGraph),
          cx.named.toList[j]? = some x ∧ ds.named[j]? = some ng ∧ parts[j] = IdGroup.bindGraph tj v x ∧ tj.WF ∧
          Allowed env ds q ng.graph (tj.idRows.map (decRow (decV dec sF.vocab))) ∧
          (∀ r ∈ tj.idRows, RowIds (okV ok sF.vocab) r) ∧ cid ng.name.toTerm = some x := by
        intro j hj
        obtain ⟨tj, x, ng, h1, h2, h3, h4, h5, h6⟩ := hF j (by rw [← hszF]; exact hj)
        rw [Array.getElem?_eq_getElem hj] at h3
        exact ⟨tj, x, ng, h1, h2, Option.some.inj h3, h4, h5, h6, (hR j x ng h1 h2).1⟩
      -- what a part gives
      have hpart2 : ∀ j (hj : j < parts.size), ∃ (tj : Table) (x : UInt64) (ng : NamedGraph),
          ds.named[j]? = some ng ∧ (parts[j]).WF ∧
          Allowed env ds q ng.graph (tj.idRows.map (decRow (decV dec sF.vocab))) ∧
          IdGroup.PermPw IdGroup.BindEq
            ((tj.idRows.map (decRow (decV dec sF.vocab))).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
            ((parts[j]).idRows.map (decRow (decV dec sF.vocab))) ∧
          ∀ r ∈ (parts[j]).idRows, RowIds (okV ok sF.vocab) r := by
        intro j hj
        obtain ⟨tj, x, ng, _, h2, h3, h4, h5, h6, h7⟩ := hpart j hj
        have hxok : okV ok sF.vocab x := ok_okV (hcidok _ x h7)
        have hdx : decV dec sF.vocab x = ng.name.toTerm := by
          rw [decV_ok dec hloc _ (hcidok _ x h7), hcidN _ x h7]
          cases ng.name <;> rfl
        obtain ⟨hbw, hbp⟩ := GraphVar.bindGraph_rows tj h4 v x (hx0 x ng h7)
        rw [h3]
        refine ⟨tj, x, ng, h2, hbw, h5, ?_, ?_⟩
        · rw [← hdx, ← bindG_rows _ _ hdecV' v x hxok _ h6]
          exact IdGroup.PermPw.of_pw (IdGroup.Pw.symm (fun _ _ h => IdGroup.BindEq.symm h)
            (pw_map (decRow (decV dec sF.vocab)) (fun _ _ h => IdLeaf.rowEq_bindEq _ h) hbp))
        · exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hbw.nodup) (IdEquiv.of_pw hbp)
            (fun r hr => by
              obtain ⟨r0, h0, e0⟩ := List.mem_filterMap.mp hr
              exact IdGroup.rowIds_idBindG _ v x hxok r0 r (h6 r0 h0) e0)
      have hall : ∀ t ∈ parts.toList, t.WF := by
        intro t ht
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem ht
        simp only [Array.length_toList] at hj
        obtain ⟨_, _, _, _, hw, _⟩ := hpart2 j hj
        rw [← e]; simpa using hw
      obtain ⟨huwf, hur⟩ := TableTheorems.unionIds_rows parts hall
      have heq : IdEquiv (IdJoin.unionIds parts).idRows (parts.toList.flatMap Table.idRows) :=
        BgpTableTheorems.idEquiv_of_rowsEq_perm hur (List.Perm.refl _)
      refine ends_pure (a := IdJoin.unionIds parts) (s := { sF with lines := _ }) rfl ⟨huwf, ?_, ?_, hiF, hpF⟩
      · show Allowed env ds _ a ((IdJoin.unionIds parts).idRows.map (decRow (decV dec sF.vocab)))
        classical
        let Rj : Nat → SolutionSeq := fun j =>
          if hj : j < parts.size then (Classical.choose (hpart2 j hj)).idRows.map (decRow (decV dec sF.vocab)) else []
        let F : NamedGraph → SolutionSeq := fun ng =>
          if h : ∃ j, j < parts.size ∧ ds.named[j]? = some ng then Rj (Classical.choose h) else []
        have hRj : ∀ j (hj : j < parts.size), ∃ (x : UInt64) (ng : NamedGraph), ds.named[j]? = some ng ∧
            Allowed env ds q ng.graph (Rj j) ∧
            IdGroup.PermPw IdGroup.BindEq ((Rj j).filterMap (Binding.bindIfCompatible v ng.name.toTerm))
              ((parts[j]).idRows.map (decRow (decV dec sF.vocab))) := by
          intro j hj
          have := Classical.choose_spec (hpart2 j hj)
          obtain ⟨x, ng, h1, _, h3, h4, _⟩ := this
          refine ⟨x, ng, h1, ?_, ?_⟩
          · simp only [Rj, dif_pos hj]; exact h3
          · simp only [Rj, dif_pos hj]; exact h4
        have hFj : ∀ j (hj : j < parts.size) (ng : NamedGraph), ds.named[j]? = some ng → F ng = Rj j := by
          intro j hj ng hng'
          have hex : ∃ j, j < parts.size ∧ ds.named[j]? = some ng := ⟨j, hj, hng'⟩
          simp only [F, dif_pos hex]
          obtain ⟨h1, h2⟩ := Classical.choose_spec hex
          have : Classical.choose hex = j := by
            have hl : Classical.choose hex < ds.named.length := by rw [← hlen]; simpa [← hszF] using h1
            exact (List.getElem?_inj hl hnd).mp (h2.trans hng'.symm)
          rw [this]
        have hA : Allowed env ds (.graph (.var v) q) a
            (ds.named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)) := by
          refine .graphVar F fun ng hng' => ?_
          obtain ⟨j, hj, e⟩ := List.getElem_of_mem hng'
          have hj' : j < parts.size := by rw [hszF, hlen]; exact hj
          rw [hFj j hj' ng (by rw [List.getElem?_eq_getElem hj, e])]
          obtain ⟨x, ng', h1, h2, _⟩ := hRj j hj'
          rw [List.getElem?_eq_getElem hj, e] at h1
          cases h1
          exact h2
        refine .equiv hA (IdGroup.SolEquiv.trans ?_ (IdLeaf.solEquiv_decode _ heq).symm)
        rw [List.map_flatMap, GraphVar.flatMap_range _ ds.named, GraphVar.flatMap_range _ parts.toList,
          Array.length_toList, hszF, hlen]
        apply IdGroup.PermPw.flatMap
        intro j hj
        rw [List.mem_range] at hj
        have hj' : j < parts.size := by rw [hszF, hlen]; exact hj
        obtain ⟨x, ng, h1, _, h3⟩ := hRj j hj'
        rw [h1, Array.getElem?_toList, Array.getElem?_eq_getElem hj']
        simp only []
        rw [hFj j hj' ng h1]
        exact h3
      · show ∀ r ∈ (IdJoin.unionIds parts).idRows, RowIds (okV ok sF.vocab) r
        refine rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ huwf.nodup) heq ?_
        intro r hr
        obtain ⟨t, ht, hrt⟩ := List.mem_flatMap.mp hr
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem ht
        simp only [Array.length_toList] at hj
        obtain ⟨_, _, _, _, _, _, _, h6⟩ := hpart2 j hj
        rw [← e] at hrt
        exact h6 r (by simpa using hrt)

theorem flatMap_fa2 {α β γ : Type} {R : α → β → Prop} (f : α → List γ) (g : β → List γ) :
    ∀ {l : List α} {l' : List β}, FilterTableTheorems.Fa2 R l l' → (∀ a ∈ l, ∀ b ∈ l', R a b → f a = g b) →
      l.flatMap f = l'.flatMap g
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons h1 h2, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h _ List.mem_cons_self _ List.mem_cons_self h1,
      flatMap_fa2 f g h2 (fun a ha b hb hab => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab)]

/-- **GRAPH with a variable over a basic graph pattern as the nested
    evaluator runs it** (`IdGroup.bgpGraphVarM`: one scan per triple pattern
    with the graph as a column). Hypotheses besides those of the store: the
    basic graph pattern is not empty and its positions are variables, IRIs or
    literals; `cx.named` lists distinct ids, in the order of `ds.named` the
    ids the dictionary gives their names, each the active graph `gof` gives
    the graph; the store's rows with a graph id other than 0 are in those
    graphs (`NamedRows`); the leaf conditions of the pattern in each named
    graph (`ExecLeaf`: the store invariant of the graph). -/
theorem graphBgp_ends (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hloc : ∀ x, ok x → tagOf x ≠ tagLocal) (hcidok : ∀ t x, cid t = some x → ok x)
    (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (v : String) (b : Bgp) (hb : b ≠ []) (htp : ∀ tp ∈ b, ExecTp tp) (hcn : cx.named.toList.Nodup)
    (hfa : FilterTableTheorems.Fa2 (fun x (ng : NamedGraph) => cid ng.name.toTerm = some x ∧ gof ng.graph = .named x)
      cx.named.toList ds.named)
    (hnr : NamedRows cx prb ms)
    (hq : ∀ ng ∈ ds.named, ExecLeaf cid dec sok ok idv (listingsOf gof prb ms) (.bgp b) ng.graph)
    (a : Graph) (nst1 : NSt) (hi1 : LocalVocab.Inv cid nst1) :
    Ends ((evalGroupM cx (.graph (.var v) (.bgp b)) (gof a)).run nst1)
      (WhereOk env ds cid dec ok (.graph (.var v) (.bgp b)) a nst1) := by
  obtain ⟨hlen, hR⟩ := GraphVar.fa2_get hfa
  let R : Nat → List Block.Row := fun k => (ms k).flatMap (ScanFoldTheorems.blockRows (prb k))
  let L : UInt64 → List IdPath.IdTriple := fun x => ScanTableTheorems.permListing 2 x (R 2)
  -- each id of `cx.named` and its named graph, and back
  have hGng : ∀ x ∈ cx.named.toList, ∃ ng ∈ ds.named, cid ng.name.toTerm = some x ∧ gof ng.graph = .named x := by
    intro x hx
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
    have hj' : j < ds.named.length := by rw [← hlen]; exact hj
    exact ⟨ds.named[j], List.getElem_mem hj',
      hR j x ds.named[j] (by rw [List.getElem?_eq_getElem hj, e]) (List.getElem?_eq_getElem hj')⟩
  have hngG : ∀ ng ∈ ds.named, ∃ x, cid ng.name.toTerm = some x ∧ gof ng.graph = .named x := by
    intro ng hng
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hng
    have hj' : j < cx.named.toList.length := by rw [hlen]; exact hj
    exact ⟨cx.named.toList[j], hR j _ ng (List.getElem?_eq_getElem hj') (by rw [List.getElem?_eq_getElem hj, e])⟩
  have hG0 : ∀ x ∈ cx.named.toList, x ≠ 0 := by
    intro x hx
    obtain ⟨ng, _, h1, _⟩ := hGng x hx
    exact hcid0 _ x h1
  -- the listing of a named graph
  have hlist : ∀ (ng : NamedGraph) (x : UInt64), gof ng.graph = .named x → ∀ k : Fin 4,
      listingsOf gof prb ms k ng.graph = ScanTableTheorems.permListing k.val x (R k.val) := by
    intro ng x hg k
    show ScanTableTheorems.permListing k.val (gctxId (gof ng.graph)) _ = _
    rw [hg]
    rfl
  have hL : ∀ x ∈ cx.named.toList, ∀ k, k < 4 → (ScanTableTheorems.permListing k x (R k)).Perm (L x) := by
    intro x hx k hk
    obtain ⟨ng, hng, _, hg⟩ := hGng x hx
    have := (hq ng hng).1.1.2 ⟨k, hk⟩
    rw [hlist ng x hg, hlist ng x hg] at this
    exact this
  have hst := GraphBgp.named_scanStore cx.st prb ms hpm hscan v cx.named.toList hcn hG0 hnr L hL
  obtain ⟨tab, nst2, hrun, hv1, hv2, hwf, hnd, heq⟩ :=
    GraphBgp.bgpGraphVarM_rows cx cid hid hds v cx.named.toList L hcn hst b htp hb nst1
  have hbe : b.isEmpty = false := by
    cases b with
    | nil => exact absurd rfl hb
    | cons _ _ => rfl
  have hrun' : (evalGroupM cx (.graph (.var v) (.bgp b)) (gof a)).run nst1 = pure (tab, nst2) := by
    rw [evalGroupM]
    simp only [hbe, Bool.not_false, if_true]
    exact hrun
  -- per graph `x`: the model's rows of `b` (`M x`)
  let ps := b.map (IdLeaf.ipat cid)
  let M : UInt64 → List IdRow := fun x => IdLeaf.bgpJoin (fun _ => L x) ps [[]]
  have hnd0 : ∀ r ∈ ([[]] : List IdRow), Nd r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact List.nodup_nil
  have hM : ∀ x, IdEquiv (M x) (IdLeaf.idBgpFrom (L x) ps []) := by
    intro x
    have h1 := IdLeaf.bgpJoin_equiv (L x) (fun _ => L x) (fun _ => List.Perm.refl _) ps [[]] hnd0
    rw [List.flatMap_singleton] at h1
    exact h1
  have hstore := IdLeaf.leafRel_of_store env ds (listingsOf gof prb ms) (fun _ => spo)
    (fun _ b => ⟨b, List.Perm.refl b⟩) cid dec idv sok ok hdec hsok (cidOk_sok hsok hcid)
  have hleaf : ∀ ng ∈ ds.named, ∀ x, gof ng.graph = .named x →
      Allowed env ds (.bgp b) ng.graph ((M x).map (decRow dec)) ∧ ∀ r ∈ M x, RowIds ok r := by
    intro ng hng x hg
    obtain ⟨h1, h2⟩ := hstore (.bgp b) ng.graph (hq ng hng).1
    have e : (IdLeaf.storeLeaves (listingsOf gof prb ms) (fun _ => spo) (fun _ b => ⟨b, List.Perm.refl b⟩) cid
        dec idv).bgp ng.graph b = M x := by
      show IdLeaf.bgpJoin (fun _ => listingsOf gof prb ms spo ng.graph) (b.map (IdLeaf.ipat cid)) [[]] = _
      rw [hlist ng x hg spo]
      rfl
    rw [e] at h1 h2
    exact ⟨.equiv (.bgp b ng.graph) h1, h2⟩
  have hrowsM : ∀ x ∈ cx.named.toList, ∀ r ∈ M x, RowIds ok r := by
    intro x hx
    obtain ⟨ng, hng, _, hg⟩ := hGng x hx
    exact (hleaf ng hng x hg).2
  -- the rows of the table: per graph `x`, `M x` with `?v` bound to `x`
  have heq2 : IdEquiv tab.idRows (cx.named.toList.flatMap fun x => (M x).filterMap (IdGroup.idBindG v x)) := by
    refine IdEquiv.trans heq (IdLeaf.flatMap_equiv _ _ _ fun x _ => ?_)
    exact IdEquiv.trans (GraphBgp.seed_top (L x) v x ps).symm (GraphBgp.idEquiv_bindG v x (hM x).symm)
  have hok : ∀ r ∈ tab.idRows, RowIds ok r := by
    refine rowIds_of_equiv ok hnd heq2 ?_
    intro r hr
    obtain ⟨x, hx, hr'⟩ := List.mem_flatMap.mp hr
    obtain ⟨r0, h0, e0⟩ := List.mem_filterMap.mp hr'
    obtain ⟨ng, _, h1, _⟩ := hGng x hx
    exact IdGroup.rowIds_idBindG ok v x (hcidok _ x h1) r0 r (hrowsM x hx r0 h0) e0
  refine ends_pure hrun' ⟨hwf, ?_, fun r hr p hp => ok_okV (hok r hr p hp), inv_congr hv1 hv2 hi1,
    by rw [hv1]; exact List.prefix_refl _⟩
  rw [rows_ok dec hloc _ _ hok]
  let F : NamedGraph → SolutionSeq := fun ng =>
    (IdLeaf.bgpJoin (fun _ => listingsOf gof prb ms spo ng.graph) ps [[]]).map (decRow dec)
  have hFx : ∀ (ng : NamedGraph) (x : UInt64), gof ng.graph = .named x → F ng = (M x).map (decRow dec) := by
    intro ng x hg
    show (IdLeaf.bgpJoin (fun _ => listingsOf gof prb ms spo ng.graph) ps [[]]).map (decRow dec) = _
    rw [hlist ng x hg spo]
    rfl
  have hA : Allowed env ds (.graph (.var v) (.bgp b)) a
      (ds.named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)) := by
    refine .graphVar F fun ng hng => ?_
    obtain ⟨x, _, hg⟩ := hngG ng hng
    rw [hFx ng x hg]
    exact (hleaf ng hng x hg).1
  refine .equiv hA ?_
  have hflat : (ds.named.flatMap fun ng => (F ng).filterMap (Binding.bindIfCompatible v ng.name.toTerm)) =
      (cx.named.toList.flatMap fun x => (M x).filterMap (IdGroup.idBindG v x)).map (decRow dec) := by
    rw [List.map_flatMap]
    symm
    apply flatMap_fa2 _ _ hfa
    intro x hx ng _ ⟨h1, hg⟩
    have hdx : dec x = ng.name.toTerm := by
      rw [hcidN _ x h1]
      cases ng.name <;> rfl
    rw [hFx ng x hg, ← hdx]
    exact bindG_rows dec ok hdec v x (hcidok _ x h1) (M x) (hrowsM x hx)
  rw [hflat]
  exact IdLeaf.solEquiv_decode dec heq2.symm

/-- **The WHERE clause on ids as the nested evaluator runs it.** For every
    pattern built from basic graph patterns, property paths, `{}`, Join,
    LeftJoin with the condition `true` or a FILTER condition, FILTER with a
    condition of EXISTS-free conjuncts and EXISTS or NOT EXISTS of a basic
    graph pattern or `{}` (`ExistsTableTheorems.FilterExOk`), Union, MINUS, GRAPH with an IRI or a
    variable, VALUES, BIND and sub-SELECT, at any depth (`ExecHyps`),
    `IdGroup.evalGroupM` run from any state that keeps the
    invariant of the query-local vocabulary (`LocalVocab.Inv`) refuses with
    a refusal of that vocabulary (`LocalVocab.LocalRefusal`), or returns a
    well-formed table whose rows decode, with the decoder of the final state,
    to an answer SPARQL 1.1 allows for the pattern (`Allowed`), with ids of
    that state; the final state keeps the invariant and extends the
    vocabulary (`WhereOk`). Each operator is the executed `Table` operator
    (`IdJoin.joinIds`, `IdGroup.pathM` with candidates from the left rows,
    `IdGroup.leftJoinCondM`, `IdGroup.filterM`, `IdJoin.unionIds`,
    `Table.select` of `IdQuery.semiMatches`, `IdGroup.subSelectM`). Hypotheses:
    those of `ExecLeafTheorems.where_allowed_exec` for the store (`PermMem`
    of each permutation, single-thread scans, no dataset clause, a
    dictionary lookup `cid` that never fails, `hdec`, `hsok`, `hidv`,
    `hcid0`, `htag`), with `CidOk` on the ids in `ok` (`hcid`, which gives
    the leaves' `CidOk` on `sok`) and the ids the lookup gives in `ok`
    (`hcidok`); for the conditions: the lookup answers the tag-folded term
    itself (`hcidN`), the evaluator's environment is the query's (`henv`),
    and `termOf` decodes the ids in `ok` as `dec` does, none with the
    query-local tag (`htermOf`, `hloc`); for EXISTS, the tag of a store id
    says whether it is an IRI or blank node, or a literal
    (`ExistsTableTheorems.TagKind`, `htagk`); and `ExecHyps ExecLeaf
    NamedRows XD` of the pattern, with `XD` that the environment has a
    dataset. No hypothesis states the table of a pattern or of a subpattern,
    or the vocabulary of a state other than the first. -/
theorem query_where_allowed_exec (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (henv : cx.env = env)
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) (htagk : ∀ x, ok x → TagKind x (dec x)) :
    ∀ (p : QueryPattern) (a : Graph),
      ExecHyps (ExecLeaf cid dec sok ok idv (listingsOf gof prb ms)) (NamedRows cx prb ms)
        (∃ ds0, env.dataset = some ds0) cx cid ds gof p a →
      ∀ (nst1 : NSt), LocalVocab.Inv cid nst1 →
        Ends ((evalGroupM cx p (gof a)).run nst1) (WhereOk env ds cid dec ok p a nst1)
  | .bgp b, a, h, nst1, hi1 => by
    obtain ⟨hs, htp⟩ := h
    have hst : BgpTableTheorems.BgpStore cx.st (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
      ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hs.1.2 ⟨k, hk⟩⟩, hscan⟩
    obtain ⟨tab, nst2, hrun, hv1, hv2, hwf, _, _⟩ := bgpM_rows cx cid hid hds (gof a) _ hst b htp nst1
    obtain ⟨hlr1, hlr2⟩ := leafRel_exec cx nst1 gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok
      (cidOk_sok hsok hcid) hidv hcid0 htag (.bgp b) a ⟨hs, htp⟩
    have hrows : (execLeaves cx nst1 gof).bgp a b = tab.idRows := by
      show (match ((IdGroup.bgpM cx (gof a) b).run nst1).run with | .ok p => p.1.idRows | .error _ => []) = _
      rw [hrun]; rfl
    rw [hrows] at hlr1 hlr2
    refine ends_pure hrun ⟨hwf, ?_, fun r hr p hp => ok_okV (hlr2 r hr p hp), inv_congr hv1 hv2 hi1,
      by rw [hv1]; exact List.prefix_refl _⟩
    rw [rows_ok dec hloc _ _ hlr2]
    exact .equiv (.bgp b a) hlr1
  | .propertyPath s path o, a, h, nst1, hi1 => by
    obtain ⟨hl, hs, ho⟩ := h
    have hst : BgpTableTheorems.BgpStore cx.st (gctxId (gof a)) (listingsOf gof prb ms spo a) :=
      ⟨fun k hk => ⟨prb k, ms k, hpm k hk, hl.1.2 ⟨k, hk⟩⟩, hscan⟩
    have hlit : ∀ x ∈ IdPath.idGraphNodes (listingsOf gof prb ms spo a),
        IdPathEval.litTag x = some (!isNotLiteral (dec x)) := by
      intro x hx
      rw [IdPathScanTheorems.mem_graphNodes] at hx
      obtain ⟨t, ht, e | e⟩ := hx
      · rw [← e]; exact htag _ (graphDec_sok dec sok _ a hl.1.1 t ht).1
      · rw [← e]; exact htag _ (graphDec_sok dec sok _ a hl.1.1 t ht).2
    obtain ⟨tab, nst2, hrun, hv1, hv2, hwf, _, _⟩ := pathM_rows cx cid hid hds (gof a) _ hst dec idv hidv hcid0 hlit
      s path o hs ho nst1
    obtain ⟨hlr1, hlr2⟩ := leafRel_exec cx nst1 gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok
      (cidOk_sok hsok hcid) hidv hcid0 htag (.propertyPath s path o) a ⟨hl, hs, ho⟩
    have hrows : (execLeaves cx nst1 gof).path a s path o = tab.idRows := by
      show (match ((IdGroup.pathM cx (gof a) s path o unitTable).run nst1).run with
        | .ok p => p.1.idRows | .error _ => []) = _
      rw [hrun]; rfl
    rw [hrows] at hlr1 hlr2
    refine ends_pure hrun ⟨hwf, ?_, fun r hr p hp => ok_okV (hlr2 r hr p hp), inv_congr hv1 hv2 hi1,
      by rw [hv1]; exact List.prefix_refl _⟩
    rw [rows_ok dec hloc _ _ hlr2]
    exact .equiv (.path s path o a) hlr1
  | .empty, a, _, nst1, hi1 => by
    refine ends_pure rfl ⟨unitTable_wf, .empty a, ?_, hi1, List.prefix_refl _⟩
    intro r hr
    rw [unitTable_idRows, List.mem_singleton] at hr
    subst hr
    intro b hb; cases hb
  | .join l r, a, h, nst1, hi1 => by
    by_cases hrp : ∃ s path o, r = .propertyPath s path o
    · obtain ⟨s, path, o, rfl⟩ := hrp
      obtain ⟨hgl, hs, ho⟩ := h.2
      rw [evalGroupM]
      refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok htagk l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
      obtain ⟨tp, nst3, hrun, hv1, hv2, hjwf, hjeq⟩ := join_path_exec cx nst2 gof prb ms cid dec idv sok hpm hscan hds
        hid hidv hcid0 htag a s path o hgl.1 hs ho tl hwl nst2
      obtain ⟨hlr1, hlr2⟩ := leafRel_exec cx nst2 gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok
        (cidOk_sok hsok hcid) hidv hcid0 htag (.propertyPath s path o) a ⟨hgl, hs, ho⟩
      have hi3 : LocalVocab.Inv cid nst3 := inv_congr hv1 hv2 hi2
      have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
      have hlr2' : ∀ r ∈ (execLeaves cx nst2 gof).path a s path o, RowIds (okV ok nst3.vocab) r :=
        fun r hr p hp => ok_okV (hlr2 r hr p hp)
      have hol' : ∀ r ∈ tl.idRows, RowIds (okV ok nst3.vocab) r := by rw [hv1]; exact hol
      refine ends_pure (a := IdJoin.joinIds tl tp) (s := nst3) ?_ ⟨hjwf, ?_, ?_, hi3, by rw [hv1]; exact hp12⟩
      · rw [StateT.run_bind, hrun, pure_bind]
        rfl
      · have hj : Allowed env ds (.join l (.propertyPath s path o)) a
            ((IdJoin.idJoin tl.idRows ((execLeaves cx nst2 gof).path a s path o)).map (decRow (decV dec nst3.vocab))) := by
          rw [IdJoin.join_decode _ _ hdecV' _ _ hol' hlr2', rows_ok dec hloc _ _ hlr2, hv1]
          exact .join hAl (.equiv (.path s path o a) hlr1)
        exact .equiv hj (IdLeaf.solEquiv_decode _ hjeq.symm)
      · exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hjwf.nodup) hjeq
          (IdGroup.rowIds_idJoin _ _ _ hol' hlr2')
    · have hr : ∀ s path o, r ≠ .propertyPath s path o := fun s path o e => hrp ⟨s, path, o, e⟩
      rw [evalGroupM.eq_4 cx _ l r (fun s path o e => hr s path o e)]
      refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok htagk l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
      refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok htagk r a h.2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
      obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
      have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
      obtain ⟨hjwf, hjr⟩ := TableTheorems.joinIds_rows tl tr hwl hwr
      have heq : IdEquiv (IdJoin.joinIds tl tr).idRows (IdJoin.idJoin tl.idRows tr.idRows) :=
        BgpTableTheorems.idEquiv_of_rowsEq_perm hjr (List.Perm.refl _)
      obtain ⟨nst4, hn, hv1, hv2⟩ := note_run s!"join: {tl.rows} and {tr.rows} rows: {(IdJoin.joinIds tl tr).rows} rows" nst3
      refine ends_pure (a := IdJoin.joinIds tl tr) (s := nst4) ?_ ⟨hjwf, ?_, ?_, inv_congr hv1 hv2 hi3,
        by rw [hv1]; exact hp12.trans hp23⟩
      · rw [StateT.run_bind, hn, pure_bind]
        rfl
      · rw [hv1]
        have hj : Allowed env ds (.join l r) a ((IdJoin.idJoin tl.idRows tr.idRows).map (decRow (decV dec nst3.vocab))) := by
          rw [IdJoin.join_decode _ _ hdecV' _ _ hol hor]
          exact .join hAl hAr
        exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
      · rw [hv1]
        exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hjwf.nodup) heq
          (IdGroup.rowIds_idJoin _ _ _ hol hor)
  | .union l r, a, h, nst1, hi1 => by
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk r a h.2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
    obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
    obtain ⟨huwf, hur⟩ := TableTheorems.unionIds_rows #[tl, tr] (by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hwl
      · exact hwr)
    have hfl : (#[tl, tr].toList.flatMap Table.idRows) = tl.idRows ++ tr.idRows := by simp
    rw [hfl] at hur
    have heq : IdEquiv (IdJoin.unionIds #[tl, tr]).idRows (tl.idRows ++ tr.idRows) :=
      BgpTableTheorems.idEquiv_of_rowsEq_perm hur (List.Perm.refl _)
    refine ends_pure rfl ⟨huwf, ?_, ?_, hi3, hp12.trans hp23⟩
    · have hj : Allowed env ds (.union l r) a ((tl.idRows ++ tr.idRows).map (decRow (decV dec nst3.vocab))) := by
        rw [List.map_append]
        exact .union hAl hAr
      exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
    · refine rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ huwf.nodup) heq ?_
      intro x hx
      rcases List.mem_append.mp hx with e | e
      · exact hol x e
      · exact hor x e
  | .minus l r, a, h, nst1, hi1 => by
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk l a h.1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk r a h.2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
    obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
    have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
    obtain ⟨hmwf, hmr⟩ := minus_rows tl tr hwl hwr
    obtain ⟨nst4, hn, hv1, hv2⟩ := note_run s!"MINUS: {tl.rows} rows, right {tr.rows} rows: {(tl.select fun i => !(semiMatches tl tr true)[i]!).rows} rows" nst3
    refine ends_pure (a := tl.select fun i => !(semiMatches tl tr true)[i]!) (s := nst4) ?_
      ⟨hmwf, ?_, ?_, inv_congr hv1 hv2 hi3, by rw [hv1]; exact hp12.trans hp23⟩
    · rw [StateT.run_bind, hn, pure_bind]
      rfl
    · rw [hv1, hmr, IdMinus.minus_decode _ _ hdecV' _ _ hol hor]
      exact .minus hAl hAr
    · rw [hv1, hmr]
      exact fun x hx => hol x ((List.mem_filter.mp hx).1)
  | .graph (.iri i) q, a, h, nst1, hi1 => by
    obtain ⟨hng, hq⟩ := h
    have hnone : cx.st.namedGraphs.isNone = false := by
      cases e : cx.st.namedGraphs with
      | none => rw [e] at hng; cases hng
      | some _ => rfl
    have hnid : ∀ nst, (IdGroup.namedIdOf cx (.iri i)).run nst =
        pure ((match cid (.iri i) with
          | some x => if cx.named.contains x then some x else none
          | none => none), nst) := by
      intro nst
      unfold IdGroup.namedIdOf IdGroup.liftE
      rw [StateT.run_bind, StateT.run_lift, hid, pure_bind, pure_bind]
      cases cid (.iri i) <;> rfl
    rw [evalGroupM]
    simp only [hnone, Bool.false_eq_true, if_false]
    rw [StateT.run_bind, hnid, pure_bind]
    simp only []
    cases hg : ds.lookupNamedIri i.val with
    | some g =>
      rw [hg] at hq
      obtain ⟨⟨x, hx, hxn, hgx⟩, hq'⟩ := hq
      have := query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
        htermOf hloc hcidok htagk q g hq' nst1 hi1
      rw [hgx] at this
      simp only [hx, hxn, if_true]
      exact ends_mono this fun t s ⟨hwf, hA, hok, hi, hp⟩ => ⟨hwf, .graphIri hg hA, hok, hi, hp⟩
    | none =>
      simp only [hg] at hq
      have hm : (match cid (.iri i) with
          | some x => if cx.named.contains x then some x else none
          | none => none) = none := by
        cases e : cid (.iri i) with
        | none => rfl
        | some x =>
          have hx := hq x e
          simp only [hx, Bool.false_eq_true, if_false]
      rw [hm]
      obtain ⟨nst2, hn, hv1, hv2⟩ := note_run s!"GRAPH <{i.val}>: not a named graph of the dataset" nst1
      refine ends_pure (a := Table.empty #[]) (s := nst2) ?_ ⟨BgpTableTheorems.empty_wf _ List.nodup_nil,
        .graphIriNone hg, ?_, inv_congr hv1 hv2 hi1, by rw [hv1]; exact List.prefix_refl _⟩
      · simp only []
        rw [StateT.run_bind, hn, pure_bind]
        rfl
      · intro r hr
        simp [Table.idRows, Table.empty] at hr
  | .graph (.var v) q, a, h, nst1, hi1 => by
    rcases h with ⟨b, rfl, hb, htp, hcn, hfa, hnr, hq⟩ | ⟨hng, hnb, hnd, hfa, hq⟩
    · exact graphBgp_ends cx gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok hcid hcidN hloc hcidok
        hcid0 v b hb htp hcn hfa hnr hq a nst1 hi1
    exact graphVar_ends cx gof cid dec ok env ds hdec hcid hcidN hloc hcidok hcid0 v q hng hnb hnd hfa
      (fun ng hng' s hs => query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN
        henv htermOf hloc hcidok htagk q ng.graph (hq ng hng') s hs) a nst1 hi1
  | .graph (.bnode _) _, _, h, _, _ => h.elim
  | .graph (.literal _) _, _, h, _, _ => h.elim
  | .graph (.tripleTerm _ _ _) _, _, h, _, _ => h.elim
  | .leftJoin l r c, a, h, nst1, hi1 => by
    obtain ⟨hc, h1, h2⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk l a h1 nst1 hi1) fun tl nst2 ⟨hwl, hAl, hol, hi2, hp12⟩ => ?_
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk r a h2 nst2 hi2) fun tr nst3 ⟨hwr, hAr, hor, hi3, hp23⟩ => ?_
    obtain ⟨hAl, hol⟩ := allowed_mono env ds dec hloc hp23 hi3.size hAl hol
    have hdecV' := hdecV cid dec ok hdec hcid hloc hi3
    by_cases htc : c = .boolLit true
    · subst htc
      obtain ⟨nst4, hrun, hv1, hv2⟩ := leftJoinTrue_run cx (gof a) tl tr nst3
      obtain ⟨htwf, hpw⟩ := leftJoinTrue_rows tl tr hwl hwr
      have heq := IdEquiv.of_pw hpw
      refine ends_pure hrun ⟨htwf, ?_, ?_, inv_congr hv1 hv2 hi3, by rw [hv1]; exact hp12.trans hp23⟩
      · rw [hv1]
        have e : (fun m => IdGroup.filterFn env (.boolLit true) a (decRow (decV dec nst3.vocab) m)) =
            fun _ => true := funext fun _ => rfl
        have hj : Allowed env ds (.leftJoin l r (.boolLit true)) a
            ((IdGroup.idLeftJoinC (fun m => IdGroup.filterFn env (.boolLit true) a (decRow (decV dec nst3.vocab) m))
              tl.idRows tr.idRows).map (decRow (decV dec nst3.vocab))) := by
          rw [IdGroup.leftJoinC_decode _ _ hdecV' (IdGroup.filterFn env (.boolLit true) a) _ _ hol hor]
          exact .leftJoin hAl hAr
        rw [e] at hj
        exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
      · rw [hv1]
        exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ htwf.nodup) heq
          (IdGroup.rowIds_idLeftJoinC _ _ _ _ hol hor)
    · obtain ⟨hfc, hxd, hb⟩ := hc.resolve_left htc
      obtain ⟨hjwf, hjr⟩ := TableTheorems.joinIds_rows tl tr hwl hwr
      have heqj : IdEquiv (IdJoin.joinIds tl tr).idRows (IdJoin.idJoin tl.idRows tr.idRows) :=
        BgpTableTheorems.idEquiv_of_rowsEq_perm hjr (List.Perm.refl _)
      have hjok : ∀ q ∈ (IdJoin.joinIds tl tr).idRows, RowIds (okV ok nst3.vocab) q :=
        rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ hjwf.nodup) heqj (IdGroup.rowIds_idJoin _ _ _ hol hor)
      refine ends_mono (ExistsTableTheorems.leftJoinCond_run cx gof prb ms cid dec idv sok ok env ds henv hpm hscan
        hds hid hdec hsok hcid (cidOk_sok hsok hcid) htermOf hloc htagk hcidN hcidok nst3 hi3 a tl tr hjwf hjok c hfc
        hxd htc hb) fun T nst4 ⟨keep, hT, hv1, hv2, _, hkeep⟩ => ?_
      subst hT
      have hcond : ∀ r1 r2, RowEq r1 r2 →
          IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) r1) =
            IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) r2) := by
        intro r1 r2 hr12
        exact ExistsTableTheorems.filterFn_bindEq env c a hfc _ _ (fun v => by
          simp only [OptJoin.lookup_decRow, hr12 v])
      obtain ⟨htwf, hpw⟩ := FilterTableTheorems.leftJoinCond_rows tl tr hwl hwr keep
        (fun m => IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) m)) hkeep hcond
      have heq := IdEquiv.of_pw hpw
      refine ⟨htwf, ?_, ?_, inv_congr hv1 hv2 hi3, by rw [hv1]; exact hp12.trans hp23⟩
      · rw [hv1]
        have hj : Allowed env ds (.leftJoin l r c) a
            ((IdGroup.idLeftJoinC (fun m => IdGroup.filterFn env c a (decRow (decV dec nst3.vocab) m))
              tl.idRows tr.idRows).map (decRow (decV dec nst3.vocab))) := by
          rw [IdGroup.leftJoinC_decode _ _ hdecV' (IdGroup.filterFn env c a) _ _ hol hor]
          exact .leftJoin hAl hAr
        exact .equiv hj (IdLeaf.solEquiv_decode _ heq.symm)
      · rw [hv1]
        exact rowIds_of_equiv _ (BgpTableTheorems.nd_idRows _ htwf.nodup) heq
          (IdGroup.rowIds_idLeftJoinC _ _ _ _ hol hor)
  | .filter c q, a, h, nst1, hi1 => by
    obtain ⟨hc, hxd, hb, hq⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk q a hq nst1 hi1) fun tq nst2 ⟨hwq, hAq, hoq, hi2, hp12⟩ => ?_
    refine ends_mono (ExistsTableTheorems.filterM_run cx gof prb ms cid dec idv sok ok env ds henv hpm hscan hds hid
      hdec hsok hcid (cidOk_sok hsok hcid) htermOf hloc htagk hcidN hcidok nst2 hi2 a tq hwq hoq c hc hxd hb)
      fun t' nst3 ⟨hwf, hrows, hv1, hv2⟩ => ⟨hwf, ?_, ?_, inv_congr hv1 hv2 hi2, by rw [hv1]; exact hp12⟩
    · rw [hv1, hrows, show (tq.idRows.filter fun r => IdGroup.filterFn env c a (decRow (decV dec nst2.vocab) r)).map
          (decRow (decV dec nst2.vocab)) =
          (tq.idRows.map (decRow (decV dec nst2.vocab))).filter (IdGroup.filterFn env c a) by
        rw [List.filter_map]; rfl]
      exact .filter hAq
    · rw [hv1, hrows]
      exact fun r hr => hoq r (List.mem_filter.mp hr).1
  | .lateral _ _, _, h, _, _ => h.elim
  | .bind e v q, a, h, nst1, hi1 => by
    obtain ⟨hef, ⟨vs, hvs⟩, hfx, hq⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk q a hq nst1 hi1) fun tq nst2 ⟨hwq, hAq, hoq, hi2, hp12⟩ => ?_
    refine ends_mono (LocalTable.extendNM_spec cid dec ok cx hid hcid hcidok hcidN htermOf hloc hcid0 env henv e v vs
      hvs hef hfx tq hwq nst2 hi2 hoq a) fun T s ⟨hwf, hpw, hok, hi, hp⟩ => ⟨hwf, ?_, hok, hi, hp12.trans hp⟩
    obtain ⟨hAq', _⟩ := allowed_mono env ds dec hloc hp hi.size hAq hoq
    exact .equiv (.bind hAq') (IdGroup.PermPw.of_pw hpw)
  | .values vars rows, a, h, nst1, hi1 => by
    rw [evalGroupM]
    exact ends_mono (LocalTable.valuesNM_spec cid dec ok cx hid hcid hcidok hcidN hloc hcid0 vars rows h nst1 hi1)
      fun T s ⟨hwf, hpw, hok, hi, hp⟩ =>
        ⟨hwf, .equiv (.values vars rows a) (IdGroup.PermPw.of_pw hpw), hok, hi, hp⟩
  | .service _ _ _, _, h, _, _ => h.elim
  | .serviceVar _ _ _, _, h, _, _ => h.elim
  | .subSelect (.mk form dcs inner gb hv md pv bs), a, h, nst1, hi1 => by
    obtain ⟨hq, hs⟩ := h
    rw [evalGroupM]
    refine ends_bind (query_where_allowed_exec env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag hcidN henv
      htermOf hloc hcidok htagk inner a hq nst1 hi1) fun tq nst2 ⟨hwq, hAq, hoq, hi2, hp12⟩ => ?_
    cases hpp : IdGroup.plainProjection? (.mk form dcs inner gb hv md pv bs) with
    | some pr =>
      -- a projection of variables: on ids
      obtain ⟨vs, d⟩ := pr
      refine ends_mono (SubSelect.subSelectM_plain cid dec ok cx a _ vs d hpp tq hwq nst2 hi2 hoq
        (hdecV cid dec ok hdec hcid hloc hi2)) fun T s ⟨hwf, heq, hok, hi, hp⟩ => ⟨hwf, ?_, hok, hi, hp12.trans hp⟩
      rw [henv] at heq
      exact .equiv (.subSelect hAq) heq
    | none =>
      -- any other sub-SELECT: the reference post-processing on the decoded rows
      rcases hs with hs | ⟨items, rfl, hnd, hef⟩ | ⟨rfl, rfl, hef, hso⟩
      · rw [hpp] at hs; cases hs
      · refine ends_mono (SubSelect.subSelectM_post cid dec ok cx hid hcid hcidok hcidN hloc hcid0 htermOf _ hpp hnd
          tq nst2 hi2 hoq
          (fun mu hmu p hp => SubSelect.selectPost_dom cx.env Graph.empty items dcs inner gb hv md pv bs _ mu hmu p hp))
          fun T s ⟨hwf, hpw, hok, hi, hp⟩ => ⟨hwf, ?_, hok, hi, hp12.trans hp⟩
        rw [henv, ← SubSelect.selectPost_active env a Graph.empty _ hef] at hpw
        exact .equiv (.subSelect hAq) (IdGroup.PermPw.of_pw hpw)
      · -- `SELECT *` with no GROUP BY: its rows bind only variables in scope
        -- of the WHERE clause, an allowed answer (`ScopeTheorems`)
        have hnd : (Query.mk (.select .all) dcs inner none hv md pv bs).projectedVars.Nodup :=
          projectedVars_star_nodup dcs inner none hv md pv bs
        have hkeys := ScopeTheorems.allowed_keys env ds hAq hso
        refine ends_mono (SubSelect.subSelectM_post cid dec ok cx hid hcid hcidok hcidN hloc hcid0 htermOf _ hpp hnd
          tq nst2 hi2 hoq (ScopeTheorems.selectPost_all_keys cx.env Graph.empty dcs inner hv md pv bs _ hkeys))
          fun T s ⟨hwf, hpw, hok, hi, hp⟩ => ⟨hwf, ?_, hok, hi, hp12.trans hp⟩
        rw [henv, ← SubSelect.selectPost_active env a Graph.empty _ hef] at hpw
        exact .equiv (.subSelect hAq) (IdGroup.PermPw.of_pw hpw)

/-- `query_where_allowed_exec` from the state a query starts in (`{}`, the
    state `IdGroup.nestedTableM` runs from): no local id yet. -/
theorem query_where_allowed_exec_init (env : EvalEnv) (ds : Dataset)
    (hpm : ∀ k, k < 4 → PermMem cx.st k (prb k) (ms k)) (hscan : cx.st.scanTable = none)
    (hds : cx.ds = none) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (htag : ∀ x, sok x → IdPathEval.litTag x = some (!isNotLiteral (dec x)))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (henv : cx.env = env)
    (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) (htagk : ∀ x, ok x → TagKind x (dec x)) (p : QueryPattern)
    (a : Graph)
    (h : ExecHyps (ExecLeaf cid dec sok ok idv (listingsOf gof prb ms)) (NamedRows cx prb ms)
        (∃ ds0, env.dataset = some ds0) cx cid ds gof p a) :
    Ends ((evalGroupM cx p (gof a)).run {}) (WhereOk env ds cid dec ok p a {}) :=
  query_where_allowed_exec cx gof prb ms cid dec idv sok ok env ds hpm hscan hds hid hdec hsok hcid hidv hcid0 htag
    hcidN henv htermOf hloc hcidok htagk p a h {} (inv_empty cid)

end

end main

end L4Factoidal.Storage.Sbm11.GroupTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.query_where_allowed_exec
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.query_where_allowed_exec_init
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.graphVar_ends
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.graphBgp_ends
#print axioms L4Factoidal.Storage.Sbm11.GroupTableTheorems.graphVar_eq
