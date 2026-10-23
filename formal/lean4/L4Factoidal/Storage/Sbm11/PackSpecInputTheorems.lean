/-
L4Factoidal.Storage.Sbm11.PackSpecInputTheorems — the WHERE clause theorem
of the harness for the INPUT dataset of the packer, not only for the dataset
of the generation (https://github.com/danbri/factoidal/issues/776; row L3c
of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`PackSpecTheorems.harness_where_allowed_packed` states the answer of the id
path as an answer `Allowed` for `denote G`, the dataset of the generation:
its triples are those of the input as sets, in SPO row order and without
repeats. `harness_where_allowed_input` states it for a dataset `D` of the
input quads (`DatasetOf qs decl D`: the same triples and graph names as
sets, no repeated triple in a graph, no repeated graph name), under the
environment whose dataset is `D`:

* `graphOf_nodup`: a graph of `denote G` holds each triple once;
* `default_perm`, `namedPerm`: the default graph of `denote G` is a
  permutation of that of `D`, and the named graphs correspond by name
  (`AllowedPerm.NamedPerm`);
* then `AllowedPerm.allowed_perm` moves the answer from `denote G` to `D`.

Conditions on the input: the objects are normalised (`normTriple q.1 =
q.1`: language tags in lower case, which `termFits` already asks of a
term with a key) and are their own join keys (`joinKey`). Condition on the
query: `AllowedPerm.PermOk p` (no EXISTS in a condition or outside the WHERE
clause of a sub-SELECT, no full-text pattern).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PackSpecSomeTheorems
import L4Factoidal.Storage.Sbm11.AllowedPermTheorems

namespace L4Factoidal.Storage.Sbm11.PackSpec

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.AllowedPerm

/-- `D` is the dataset of the quads `qs` and the declared graphs `decl`, as
    sets: the same triples in the default graph and in each named graph, the
    same graph names, each triple once in its graph, each name once. -/
structure DatasetOf (qs : List Quad) (decl : List Subject) (D : Dataset) : Prop where
  dflt : ∀ tr, tr ∈ D.default ↔ ∃ q ∈ qs, q.2 = none ∧ q.1 = tr
  named : ∀ g tr, (∃ ng ∈ D.named, ng.name = g ∧ tr ∈ ng.graph) ↔ ∃ q ∈ qs, q.2 = some g ∧ q.1 = tr
  names : ∀ g, (∃ ng ∈ D.named, ng.name = g) ↔ g ∈ qs.filterMap (·.2) ∨ g ∈ decl
  nodupDefault : D.default.Nodup
  nodupNames : (D.named.map (·.name)).Nodup
  nodupGraphs : ∀ ng ∈ D.named, ng.graph.Nodup

section input
variable (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
  (h : packSpec B qs decl = some (G, F))
include h

/-- A graph of `denote G` holds each triple once. -/
theorem graphOf_nodup (x : UInt64) : (G.graphOf x).Nodup := by
  have hf := packSpec_facts B qs decl G F h
  obtain ⟨spo, hspo, _⟩ := hf.spo
  obtain ⟨hs1, _⟩ := allSome_mem _ qs spo hspo
  unfold MemGen.graphOf ScanTableTheorems.permListing
  rw [List.map_map]
  have hnd : (G.rows 2).Nodup := by
    rw [rows_eq B qs decl G F h spo hspo 2 (by decide)]
    exact sortUniq_nodup strict_rowCmp _
  refine nodup_map_of_inj _ ?_ (hnd.filter _)
  intro r hr r' hr' he
  simp only [List.mem_filter, beq_iff_eq] at hr hr'
  obtain ⟨r0, hr0, rfl⟩ := (mem_rows B qs decl G F h spo hspo 2 (by decide) r).1 hr.1
  obtain ⟨r0', hr0', rfl⟩ := (mem_rows B qs decl G F h spo hspo 2 (by decide) r').1 hr'.1
  simp only [toPermRow_two] at hr hr' he ⊢
  obtain ⟨q, _, hq⟩ := hs1 r0 hr0
  obtain ⟨q', _, hq'⟩ := hs1 r0' hr0'
  simp only [Function.comp_apply] at he
  rw [tripleAt_row B qs decl G F h q r0 hq, tripleAt_row B qs decl G F h q' r0' hq'] at he
  obtain ⟨a0, a1, a2, _⟩ := spoRow_spec G.keys q r0 hq
  obtain ⟨b0, b1, b2, _⟩ := spoRow_spec G.keys q' r0' hq'
  simp only [normTriple, Triple.mk.injEq] at he
  obtain ⟨es, ep, eo⟩ := he
  rw [es] at a0
  rw [ep] at a1
  rw [eo] at a2
  rw [a0] at b0
  rw [a1] at b1
  rw [a2] at b2
  simp only [Option.some.injEq] at b0 b1 b2
  rw [Row.ext']
  exact ⟨b0, b1, b2, by rw [hr.2, hr'.2]⟩

/-- The names of the named graphs of `denote G` are distinct. -/
theorem denote_names_nodup : (G.denote.named.map (·.name)).Nodup := by
  have hG := packSpec_check B qs decl G F h
  unfold MemGen.denote
  rw [List.map_map]
  exact nodup_map_of_inj _ (fun x hx y hy he => named_inj G hG x y hx hy he) (named_nodup G hG)

theorem denote_named_unique (ng ng' : NamedGraph) (hm : ng ∈ G.denote.named) (hm' : ng' ∈ G.denote.named)
    (hn : ng.name = ng'.name) : ng = ng' :=
  eq_of_name (denote_names_nodup B qs decl G F h) hm hm' hn

omit h in
theorem denote_named_graph (ng : NamedGraph) (hm : ng ∈ G.denote.named) :
    ∃ x, ng.graph = G.graphOf x := by
  unfold MemGen.denote at hm
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hm
  exact ⟨x, rfl⟩

variable (D : Dataset) (hD : DatasetOf qs decl D) (hnorm : ∀ q ∈ qs, normTriple q.1 = q.1)
include hD hnorm

/-- The default graph of `denote G` is a permutation of the default graph of
    `D`. -/
theorem default_perm : G.denote.default.Perm D.default := by
  apply (List.perm_ext_iff_of_nodup (graphOf_nodup B qs decl G F h 0) hD.nodupDefault).2
  intro tr
  show tr ∈ G.denote.default ↔ _
  rw [packSpec_default B qs decl G F h, hD.dflt]
  constructor
  · rintro ⟨q, hq, hn, rfl⟩; exact ⟨q, hq, hn, (hnorm q hq).symm⟩
  · rintro ⟨q, hq, hn, rfl⟩; exact ⟨q, hq, hn, hnorm q hq⟩

/-- A triple of a named graph of `denote G` is in the graph of `D` with the
    same name, and back. -/
theorem named_mem_iff (ng : NamedGraph) (hm : ng ∈ G.denote.named) (ng' : NamedGraph) (hm' : ng' ∈ D.named)
    (hn : ng.name = ng'.name) (tr : Triple) : tr ∈ ng.graph ↔ tr ∈ ng'.graph := by
  constructor
  · intro ht
    obtain ⟨q, hq, hqg, e⟩ := (packSpec_named B qs decl G F h ng.name tr).1 ⟨ng, hm, rfl, ht⟩
    rw [hnorm q hq] at e
    obtain ⟨ng'', hm'', hn'', ht''⟩ := (hD.named ng.name tr).2 ⟨q, hq, hqg, e⟩
    rw [eq_of_name hD.nodupNames hm' hm'' (hn.symm.trans hn''.symm)]
    exact ht''
  · intro ht
    obtain ⟨q, hq, hqg, e⟩ := (hD.named ng'.name tr).1 ⟨ng', hm', rfl, ht⟩
    rw [← hnorm q hq] at e
    obtain ⟨ng'', hm'', hn'', ht''⟩ := (packSpec_named B qs decl G F h ng'.name tr).2 ⟨q, hq, hqg, e⟩
    rw [denote_named_unique B qs decl G F h ng ng'' hm hm'' (hn.trans hn''.symm)]
    exact ht''

omit h hD in
theorem objects_fixed (hfix : ∀ q ∈ qs, q.1.o.joinKey = q.1.o) (tr : Triple)
    (ht : ∃ q ∈ qs, normTriple q.1 = tr) : tr.o.joinKey = tr.o := by
  obtain ⟨q, hq, rfl⟩ := ht
  rw [hnorm q hq]
  exact hfix q hq

/-- The named graphs of `denote G` and of `D` correspond by name. -/
theorem namedPerm (hfix : ∀ q ∈ qs, q.1.o.joinKey = q.1.o) : NamedPerm G.denote D where
  names := denote_names_nodup B qs decl G F h
  names' := hD.nodupNames
  same := fun n => by rw [packSpec_names B qs decl G F h, hD.names]
  graphs := fun ng hm ng' hm' hn => by
    obtain ⟨x, hx⟩ := denote_named_graph G ng hm
    apply (List.perm_ext_iff_of_nodup (hx ▸ graphOf_nodup B qs decl G F h x) (hD.nodupGraphs ng' hm')).2
    exact named_mem_iff B qs decl G F h D hD hnorm ng hm ng' hm' hn
  fixed := fun ng hm t ht => by
    obtain ⟨q, hq, _, e⟩ := (packSpec_named B qs decl G F h ng.name t).1 ⟨ng, hm, rfl, ht⟩
    exact objects_fixed qs hnorm hfix t ⟨q, hq, e⟩

omit hD in
theorem default_fixed (hfix : ∀ q ∈ qs, q.1.o.joinKey = q.1.o) : GraphFixed G.denote.default := by
  intro t ht
  obtain ⟨q, hq, _, e⟩ := (packSpec_default B qs decl G F h t).1 ht
  exact objects_fixed qs hnorm hfix t ⟨q, hq, e⟩

end input

open L4Factoidal.Storage.Sbm11.IdQuery in
open L4Factoidal.Storage.Sbm11.IdGroup (nestedTableM queryEnvOf Allowed) in
open L4Factoidal.Storage.Sbm11.GroupTableTheorems (WhereOk) in
open L4Factoidal.Storage.Sbm11.LocalVocab in
/-- **The WHERE clause theorem of the harness for the input dataset.** For
    the store over the files of `packSpec B qs decl`, the id path refuses
    with a `LocalRefusal`, or its table decodes to an answer that SPARQL 1.1
    allows for `p` over `D`, the dataset of the input quads, in its default
    graph, under the environment whose dataset is `D`. Hypotheses: the
    packer's domain gives `packSpec ... = some (G, F)`
    (`PackSpecSomeTheorems.packSpec_some`), `D` is the dataset of the input
    as sets, the input objects are normalised and their own join keys, and
    the query conditions `QHyps` and `PermOk`. -/
theorem harness_where_allowed_input (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen) (F : FileGen)
    (h : packSpec B qs decl = some (G, F)) (D : Dataset) (hD : DatasetOf qs decl D)
    (hnorm : ∀ q ∈ qs, normTriple q.1 = q.1) (hfix : ∀ q ∈ qs, q.1.o.joinKey = q.1.o)
    (clock : EvalEnv) (base : Option String)
    (plan : Plan) (p : QueryPattern) (hnest : plan.nested = some p) (hdsq : plan.dataset = none)
    (hq : QHyps G.cid p) (hp : PermOk p) :
    (∃ e, nestedTableM F.store plan (queryEnvOf clock base) = throw e ∧ LocalRefusal e) ∨
      ∃ t s lines stats, nestedTableM F.store plan (queryEnvOf clock base) =
          pure (t, F.store.withLocal s.vocab, lines, stats) ∧
        WhereOk { queryEnvOf clock base with dataset := some G.denote } G.denote G.cid G.dec G.ok p
          G.denote.default {} t s ∧
        Allowed { queryEnvOf clock base with dataset := some D } D p D.default
          (t.idRows.map (OptJoin.decRow (decV G.dec s.vocab))) := by
  rcases harness_where_allowed_packed B qs decl G F h clock base plan p hnest hdsq hq with hr | ⟨t, s, lines, stats, he, hw⟩
  · exact Or.inl hr
  · refine Or.inr ⟨t, s, lines, stats, he, hw, ?_⟩
    exact allowed_perm (env := { queryEnvOf clock base with dataset := some G.denote })
      (env' := { queryEnvOf clock base with dataset := some D }) ⟨rfl, rfl, rfl⟩
      (namedPerm B qs decl G F h D hD hnorm hfix) hw.2.1
      (default_perm B qs decl G F h D hD hnorm) (default_fixed B qs decl G F h hnorm hfix) hp

end L4Factoidal.Storage.Sbm11.PackSpec
