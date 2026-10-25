/-
L4Factoidal.Storage.Sbm11.HarnessWhereTheorems — the WHERE clause theorem
for the context the SBM11 harness builds
(https://github.com/danbri/factoidal/issues/776; lemma L4z of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`Harness/Sbm11Query.runOne` answers a query whose plan has a nested WHERE
clause by `IdGroup.runNestedM st plan ps (queryEnv q)`; its first step,
`IdGroup.nestedTableM st plan env`, builds the context
`{ st, env, ds := plan.dataset, named := ← namedOf st plan.dataset }` and
runs `evalGroupM` on the default graph from the empty state. `queryEnv q` is
`IdGroup.queryEnvOf clock q.base` (no dataset).

`harness_where_allowed` instantiates
`GroupTableTheorems.query_where_allowed_exec_init` with that context, that
environment, the reference's environment `{ queryEnvOf clock q.base with
dataset := some ds }` (what `evalSelect` builds for a query with no dataset
clause; it differs from the harness's reference environment only in the
NOW value, read by a second clock call) and the default graph of `ds` as the
active graph. `nestedTableM` refuses with a refusal of the query-local
vocabulary, or returns a table whose rows decode, with the decoder of the
final state (the store `st.withLocal` it returns decodes the same way), to
an answer SPARQL 1.1 allows.

The hypotheses that remain are invariants of the store, of the dictionary
and of the dataset the store denotes, to be discharged from the generation
(E0, L3c) and from the `IO` store against `m = Id` (L4e): `hpm`, `hscan`,
`hid`, `hdec`, `hsok`, `hcid`, `hidv`, `hcid0`, `hcidN`, `htermOf`,
`hloc`, `hcidok`, `htagk`, `hnamed`, and the store part of `ExecHyps`
(`ExecLeaf` of each leaf: `StoreGraph` of the active graph over the
listings of its context: the default graph's rows for the default graph, the
rows of the id of a named graph's name for that graph; `NamedRows`; at GRAPH: the store lists its named graphs and the
dictionary ids of the dataset's named graphs). The rest of `ExecHyps` is
syntax of the query (`FilterExOk`, distinct VALUES variables, EXISTS-free
BIND, the sub-SELECT forms), which `IdQuery.translate` checks in part.
`hnest` and `hdsq` are the plan. No hypothesis states the table of a pattern
or the environment of the code beyond its definition.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.GroupTableTheorems
import L4Factoidal.Storage.Sbm11.QueryEnv

namespace L4Factoidal.Storage.Sbm11.HarnessWhereTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt GCtx evalGroupM nestedTableM namedOf queryEnvOf)
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem)
open L4Factoidal.Storage.Sbm11.ExecLeafTheorems (ExecLeaf)
open L4Factoidal.Storage.Sbm11.ExistsTableTheorems (TagKind)
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (ExecHyps NamedRows WhereOk listingsAt query_where_allowed_exec_init)
open L4Factoidal.Storage.Sbm11.LocalVocab

/-- **The WHERE clause as the harness runs it.** For a plan with a nested
    WHERE clause `p` and no dataset clause, run on a store `st` with the
    environment the harness builds (`queryEnvOf clock base`, no dataset):
    `nestedTableM` refuses with a refusal of the query-local vocabulary, or
    returns a table and a store that decodes with the final state's
    vocabulary, whose rows decode to an answer `Allowed` for `p` in the
    default graph of `ds`, under the environment `evalSelect` builds (the
    harness's environment with the dataset `ds`). The hypotheses are listed
    in the module header. The context of each graph is the one of its place
    in the dataset (`.dflt` for the default graph, `.named x` for the named
    graph whose name has the id `x`), so the statement holds for a dataset in
    which two named graphs, or a named graph and the default graph, have the
    same triples. -/
theorem harness_where_allowed (st : Store Id) (clock : EvalEnv) (base : Option String) (plan : Plan)
    (p : QueryPattern) (ds : Dataset) (named : Array UInt64)
    (prb : Nat → ByteArray) (ms : Nat → List Block.BlockMeta)
    (cid : Term → Option UInt64) (dec : UInt64 → Term) (idv : Term → UInt64) (sok ok : UInt64 → Prop)
    (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (hnamed : namedOf st plan.dataset = pure named)
    (hpm : ∀ k, k < 4 → PermMem st k (prb k) (ms k)) (hscan : st.Sequential)
    (hid : ∀ t, st.idOf t = pure (cid t))
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (hsok : ∀ x, sok x → ok x)
    (hcid : ∀ c, CidOk dec ok c (cid c))
    (hidv : ∀ t x, cid t = some x → idv t = x) (hcid0 : ∀ t x, cid t = some x → x ≠ 0)
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (htermOf : ∀ x, ok x → st.termOf x = pure (dec x)) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcidok : ∀ t x, cid t = some x → ok x) (htagk : ∀ x, ok x → TagKind x (dec x))
    (h : ExecHyps (fun g => ExecLeaf cid dec sok ok idv (listingsAt prb ms g))
        (NamedRows { st, env := queryEnvOf clock base, ds := plan.dataset, named } prb ms)
        { st, env := queryEnvOf clock base, ds := plan.dataset, named } cid ds p ds.default .dflt) :
    (∃ e, nestedTableM st plan (queryEnvOf clock base) = throw e ∧ LocalRefusal e) ∨
      ∃ t s lines stats, nestedTableM st plan (queryEnvOf clock base) = pure (t, st.withLocal s.vocab, lines, stats) ∧
        WhereOk { queryEnvOf clock base with dataset := some ds } ds cid dec ok p ds.default {} t s := by
  let cx : NCx Id := { st, env := queryEnvOf clock base, ds := plan.dataset, named }
  have hE := query_where_allowed_exec_init cx prb ms cid dec idv sok ok
    { queryEnvOf clock base with dataset := some ds } ds hpm hscan hdsq hid hdec hsok hcid hidv hcid0 hcidN
    (ExprLocalTheorems.EnvAgree.withDataset _ _) rfl htermOf hloc hcidok htagk p ds.default .dflt h
  have hrun : nestedTableM st plan (queryEnvOf clock base) =
      ((evalGroupM cx p .dflt).run {} >>= fun (r : Table × NSt) =>
        pure (r.1, st.withLocal r.2.vocab,
          r.2.lines.push s!"nested WHERE (issue 959): {r.1.rows} solutions", r.2.stats)) := by
    unfold nestedTableM
    rw [hnest, hnamed]
    rfl
  rw [hrun]
  rcases hE with ⟨e, he, hr⟩ | ⟨t, s, he, hw⟩
  · left
    refine ⟨e, ?_, hr⟩
    rw [he]; rfl
  · right
    refine ⟨t, s, s.lines.push s!"nested WHERE (issue 959): {t.rows} solutions", s.stats, ?_, hw⟩
    rw [he]; rfl

end L4Factoidal.Storage.Sbm11.HarnessWhereTheorems

#print axioms L4Factoidal.Storage.Sbm11.HarnessWhereTheorems.harness_where_allowed
