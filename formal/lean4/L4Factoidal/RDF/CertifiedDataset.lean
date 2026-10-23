/-
L4Factoidal.RDF.CertifiedDataset — a dataset value that carries the proof that
it is a set of quads.

RDF 1.1 Concepts and Abstract Syntax §3: "An RDF graph is a set of RDF
triples." RDF 1.1 Semantics §4 uses that definition (empty graph, subgraph,
union). §4 of Concepts: an RDF dataset has one default graph and zero or more
named graphs, and the graph names are unique in the dataset. `Graph` is
`List Triple`, so the type `Dataset` does not exclude a triple that occurs two
times in one graph. `CertifiedDataset` is a `Dataset` together with a proof of
`Dataset.IsSet` (`RDF/DatasetSet.lean`): no two triples of one graph have the
same `Triple.key` (the key is equal exactly when the triples are `Triple.eqb`
equal, that is, the same RDF term: lexical form, datatype and base direction
exact, language tag without case), and no two named graphs have the same name.
A value of the type cannot be built without that proof.

Admission, in order of cost:

* A dataset already known to be a set takes its proof from a theorem and is
  not walked again: the parse (`parseDocumentOutcomeBy_isSet`) followed by the
  document blank-node scope (`renameDatasetBnodes_isSet`), and the SPARQL
  `insertQuads` / `deleteQuads` steps (`Dataset.insertQuads_isSet`,
  `Dataset.deleteQuads_isSet`).
* Any other dataset goes through `Dataset.certify`, which is `Dataset.toSet`
  (compiled as the hash-indexed `Dataset.toSetFast`, linear in the number of
  quads). `Dataset.memQuad_toSet` and `Dataset.names_toSet` state that it keeps
  every quad and every graph name, empty named graphs included.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetSet
import L4Factoidal.RDF.DatasetMerge
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.RDF

/-- A dataset with a proof that it is a set of quads (module header). -/
abbrev CertifiedDataset := { ds : Dataset // ds.IsSet }

/-- Admit any dataset: its set of quads (`Dataset.toSet`). -/
def Dataset.certify (ds : Dataset) : CertifiedDataset := ⟨ds.toSet, ds.toSet_isSet⟩

theorem Dataset.certify_memQuad (ds : Dataset) (u : Triple) (g : Option Subject) :
    ds.certify.val.memQuad u g ↔ ds.memQuad u g := ds.memQuad_toSet u g

theorem Dataset.certify_names (ds : Dataset) (m : Subject) :
    m ∈ ds.certify.val.names ↔ m ∈ ds.names := ds.names_toSet m

/-! ## The document blank-node scope keeps a set a set -/

theorem renameBnodeLabel_injective (pre : String) :
    Function.Injective (renameBnodeLabel pre) := by
  intro a b h
  unfold renameBnodeLabel at h
  have h' := congrArg String.toList h
  simp only [String.toList_append] at h'
  exact String.toList_inj.mp (List.append_cancel_left h')

theorem renameSubject_injective (pre : String) : Function.Injective (renameSubject pre) := by
  intro a b h
  cases a <;> cases b <;> simp only [renameSubject, reduceCtorEq, Subject.bnode.injEq,
    Subject.iri.injEq] at h ⊢
  · exact h
  · exact renameBnodeLabel_injective pre h

theorem renameTerm_injective (pre : String) : Function.Injective (renameTerm pre) := by
  intro a b h
  cases a <;> cases b <;> simp only [renameTerm, reduceCtorEq] at h ⊢ <;>
    first
    | exact h
    | exact congrArg Term.bnode (renameBnodeLabel_injective pre (Term.bnode.inj h))

theorem renameTriple_injective (pre : String) : Function.Injective (renameTriple pre) := by
  intro a b h
  obtain ⟨s1, p1, o1⟩ := a
  obtain ⟨s2, p2, o2⟩ := b
  simp only [renameTriple, Triple.mk.injEq] at h
  obtain ⟨hs, hp, ho⟩ := h
  rw [renameSubject_injective pre hs, hp, renameTerm_injective pre ho]

/-- The scope prefix commutes with the key: it changes blank-node labels, and
the key changes only literals. -/
theorem key_renameTriple (pre : String) (t : Triple) :
    (renameTriple pre t).key = renameTriple pre t.key := by
  obtain ⟨s, p, o⟩ := t
  cases o <;> simp [renameTriple, Triple.key, renameTerm, Term.joinKey]

theorem Graph.KeyNodup.rename {g : Graph} (pre : String) (h : g.KeyNodup) :
    (renameGraphBnodes pre g).KeyNodup := by
  unfold Graph.KeyNodup renameGraphBnodes
  rw [List.map_map]
  have hk : (Triple.key ∘ renameTriple pre) = (renameTriple pre ∘ Triple.key) :=
    funext (key_renameTriple pre)
  rw [hk, ← List.map_map]
  exact List.pairwise_map.mpr (h.imp fun hne he => hne (renameTriple_injective pre he))

theorem renameDatasetBnodes_isSet (pre : String) {ds : Dataset} (h : ds.IsSet) :
    (renameDatasetBnodes pre ds).IsSet where
  default := h.default.rename pre
  names := by
    have hn : (renameDatasetBnodes pre ds).names = ds.names.map (renameSubject pre) := by
      simp [Dataset.names, renameDatasetBnodes, renameNamedGraph, renameGraphName,
        List.map_map, Function.comp_def]
    rw [hn]
    exact List.pairwise_map.mpr (h.names.imp fun hne he => hne (renameSubject_injective pre he))
  graphs := by
    intro ng hng
    simp only [renameDatasetBnodes, List.mem_map] at hng
    obtain ⟨ng0, h0, rfl⟩ := hng
    exact (h.graphs ng0 h0).rename pre

/-! ## SPARQL quad insertion and deletion keep a set a set -/

theorem Graph.KeyNodup.remove {g : Graph} (t : Triple) (h : g.KeyNodup) :
    (g.remove t).KeyNodup := by
  unfold Graph.KeyNodup Graph.remove at *
  exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h

theorem replaceNamed_names (i : WfIri) (g : Graph) :
    ∀ (l : List NamedGraph) (m : Subject),
      m ∈ (replaceNamed i g l).map (·.name) → m ∈ l.map (·.name) ∨ m = .iri i
  | [], m, hm => by simp [replaceNamed] at hm; exact Or.inr hm
  | ng :: rest, m, hm => by
      unfold replaceNamed at hm
      split at hm
      · next he =>
        simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with hm | hm
        · exact Or.inl (List.mem_cons.mpr (Or.inl hm))
        · exact Or.inl (List.mem_cons_of_mem _ hm)
      · simp only [List.map_cons, List.mem_cons] at hm
        rcases hm with hm | hm
        · exact Or.inl (List.mem_cons.mpr (Or.inl hm))
        · rcases replaceNamed_names i g rest m hm with h1 | h1
          · exact Or.inl (List.mem_cons_of_mem _ h1)
          · exact Or.inr h1

theorem replaceNamed_isSet (i : WfIri) (g : Graph) (hg : g.KeyNodup) :
    ∀ (l : List NamedGraph), (l.map (·.name)).Nodup → (∀ ng ∈ l, ng.graph.KeyNodup) →
      ((replaceNamed i g l).map (·.name)).Nodup ∧ ∀ ng ∈ replaceNamed i g l, ng.graph.KeyNodup
  | [], _, _ => by
      refine ⟨List.pairwise_singleton _ _, ?_⟩
      intro ng hng
      simp only [replaceNamed, List.mem_singleton] at hng
      subst hng; exact hg
  | ng :: rest, hn, hgs => by
      unfold replaceNamed
      split
      · refine ⟨by simpa using hn, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with hx | hx
        · subst hx; exact hg
        · exact hgs x (List.mem_cons_of_mem _ hx)
      · next he =>
        rw [List.map_cons, List.nodup_cons] at hn
        obtain ⟨ih1, ih2⟩ := replaceNamed_isSet i g hg rest hn.2
          (fun x hx => hgs x (List.mem_cons_of_mem _ hx))
        refine ⟨?_, ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih1⟩
          intro hm
          rcases replaceNamed_names i g rest ng.name hm with h1 | h1
          · exact hn.1 h1
          · exact he (by rw [h1]; exact beq_self_eq_true _)
        · intro x hx
          rcases List.mem_cons.mp hx with hx | hx
          · subst hx; exact hgs x List.mem_cons_self
          · exact ih2 x hx

theorem Dataset.graphOf_keyNodup (i : WfIri) {ds : Dataset} (h : ds.IsSet) :
    (ds.graphOf i).KeyNodup := by
  unfold Dataset.graphOf Dataset.lookupNamed
  split
  · next g hg =>
    split at hg
    · next ng hf =>
      cases hg
      exact h.graphs ng (List.mem_of_find?_eq_some hf)
    · cases hg
  · exact Graph.keyNodup_nil

theorem Dataset.setGraph_isSet (i : WfIri) {g : Graph} (hg : g.KeyNodup) {ds : Dataset}
    (h : ds.IsSet) : (ds.setGraph i g).IsSet :=
  let r := replaceNamed_isSet i g hg ds.named h.names h.graphs
  ⟨h.default, r.1, r.2⟩

theorem Dataset.insertQuad_isSet {ds : Dataset} (h : ds.IsSet) (q : Quad) :
    (ds.insertQuad q).IsSet := by
  obtain ⟨g, t⟩ := q
  cases g with
  | none => exact ⟨h.default.add t, h.names, h.graphs⟩
  | some i => exact Dataset.setGraph_isSet i ((ds.graphOf_keyNodup i h).add t) h

theorem Dataset.deleteQuad_isSet {ds : Dataset} (h : ds.IsSet) (q : Quad) :
    (ds.deleteQuad q).IsSet := by
  obtain ⟨g, t⟩ := q
  cases g with
  | none => exact ⟨h.default.remove t, h.names, h.graphs⟩
  | some i =>
    simp only [Dataset.deleteQuad]
    split
    · exact Dataset.setGraph_isSet i ((ds.graphOf_keyNodup i h).remove t) h
    · exact h

theorem Dataset.insertQuads_isSet (qs : List Quad) :
    ∀ {ds : Dataset}, ds.IsSet → (ds.insertQuads qs).IsSet := by
  induction qs with
  | nil => intro ds h; exact h
  | cons q qs ih => intro ds h; exact ih (Dataset.insertQuad_isSet h q)

theorem Dataset.deleteQuads_isSet (qs : List Quad) :
    ∀ {ds : Dataset}, ds.IsSet → (ds.deleteQuads qs).IsSet := by
  induction qs with
  | nil => intro ds h; exact h
  | cons q qs ih => intro ds h; exact ih (Dataset.deleteQuad_isSet h q)

/-! ## Every SPARQL 1.1 Update operation keeps a set a set

So the handle store admits an update result with this proof and does not walk
the dataset again (`applyUpdateIn_isSet`). -/

theorem Graph.KeyNodup.union {g : Graph} (h : g.KeyNodup) :
    ∀ (ts : Graph), (g.union ts).KeyNodup := by
  intro ts
  unfold Graph.union
  induction ts generalizing g with
  | nil => exact h
  | cons t ts ih => exact ih (h.add t)

theorem Dataset.isSet_withDefault {ds : Dataset} (h : ds.IsSet) {g : Graph} (hg : g.KeyNodup) :
    ({ ds with default := g } : Dataset).IsSet := ⟨hg, h.names, h.graphs⟩

theorem Dataset.clearAllNamed_isSet {ds : Dataset} (h : ds.IsSet) : ds.clearAllNamed.IsSet := by
  refine ⟨h.default, ?_, ?_⟩
  · have hn : ds.clearAllNamed.names = ds.names := by
      simp [Dataset.clearAllNamed, Dataset.names, List.map_map, Function.comp_def]
    rw [hn]; exact h.names
  · intro ng hng
    simp only [Dataset.clearAllNamed, List.mem_map] at hng
    obtain ⟨_, _, rfl⟩ := hng
    exact Graph.keyNodup_nil

theorem Dataset.dropGraph_isSet (i : WfIri) {ds : Dataset} (h : ds.IsSet) :
    (ds.dropGraph i).IsSet := by
  refine ⟨h.default, ?_, ?_⟩
  · exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h.names
  · intro ng hng
    exact h.graphs ng (List.mem_filter.mp hng).1

theorem Dataset.ensureGraph_isSet (i : WfIri) {ds : Dataset} (h : ds.IsSet) :
    (ds.ensureGraph i).IsSet := by
  unfold Dataset.ensureGraph
  split
  · exact h
  · next hg =>
    refine ⟨h.default, ?_, ?_⟩
    · show ((ds.named ++ [({ name := .iri i, graph := [] } : NamedGraph)]).map (·.name)).Nodup
      rw [List.map_append, List.nodup_append]
      refine ⟨h.names, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      obtain ⟨ng, hng, hn⟩ := List.mem_map.mp ha
      exact hg (List.any_eq_true.mpr ⟨ng, hng, by simp [hn]⟩)
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact h.graphs x hx
      · rw [List.mem_singleton] at hx; subst hx; exact Graph.keyNodup_nil

open L4Factoidal.SPARQL in
theorem readRef_keyNodup {ds : Dataset} (h : ds.IsSet) : ∀ r : GraphRef, (readRef ds r).KeyNodup
  | .default => h.default
  | .graph i => ds.graphOf_keyNodup i h
  | .named => Graph.keyNodup_nil
  | .all => Graph.keyNodup_nil

open L4Factoidal.SPARQL in
theorem writeRef_isSet {ds : Dataset} (h : ds.IsSet) {g : Graph} (hg : g.KeyNodup) :
    ∀ r : GraphRef, (writeRef ds g r).IsSet
  | .default => Dataset.isSet_withDefault h hg
  | .graph i => Dataset.setGraph_isSet i hg h
  | .named => h
  | .all => h

open L4Factoidal.SPARQL in
theorem applyOp_isSet (env : EvalEnv) (pre : String) (opIx : Nat) {ds ds' : Dataset}
    (h : ds.IsSet) (op : UpdateOp) (hop : applyOp env pre opIx ds op = .ok ds') : ds'.IsSet := by
  cases op with
  | load silent src g =>
    simp only [applyOp] at hop
    split at hop
    · cases hop; exact h
    · cases hop
  | clear silent gr =>
    simp only [applyOp] at hop
    cases gr <;> simp only [applyClear] at hop
    · cases hop; exact Dataset.isSet_withDefault h Graph.keyNodup_nil
    · cases hop; exact Dataset.clearAllNamed_isSet h
    · cases hop
      exact Dataset.isSet_withDefault (Dataset.clearAllNamed_isSet h) Graph.keyNodup_nil
    · split at hop
      · cases hop; exact Dataset.setGraph_isSet _ Graph.keyNodup_nil h
      · split at hop
        · cases hop; exact h
        · cases hop
  | drop silent gr =>
    simp only [applyOp] at hop
    cases gr <;> simp only [applyDrop] at hop
    · cases hop; exact Dataset.isSet_withDefault h Graph.keyNodup_nil
    · cases hop; exact ⟨h.default, List.nodup_nil, fun _ hx => absurd hx List.not_mem_nil⟩
    · cases hop; exact Dataset.isSet_empty
    · split at hop
      · cases hop; exact Dataset.dropGraph_isSet _ h
      · split at hop
        · cases hop; exact h
        · cases hop
  | create silent i =>
    simp only [applyOp, applyCreate] at hop
    split at hop
    · split at hop
      · cases hop; exact h
      · cases hop
    · cases hop; exact Dataset.ensureGraph_isSet i h
  | add silent src dst =>
    simp only [applyOp, applyAdd] at hop
    split at hop
    · cases hop; exact h
    · split at hop
      · cases hop
      · split at hop
        · cases hop; exact h
        · cases hop
          exact writeRef_isSet h ((readRef_keyNodup h dst).union _) dst
  | move silent src dst =>
    simp only [applyOp, applyMove] at hop
    split at hop
    · cases hop; exact h
    · split at hop
      · cases hop
      · split at hop
        · cases hop; exact h
        · have hc := writeRef_isSet h (readRef_keyNodup h src) dst
          split at hop
          · cases hop; exact Dataset.isSet_withDefault hc Graph.keyNodup_nil
          · cases hop; exact Dataset.dropGraph_isSet _ hc
          · cases hop; exact hc
  | copy silent src dst =>
    simp only [applyOp, applyCopy] at hop
    split at hop
    · cases hop; exact h
    · split at hop
      · cases hop
      · split at hop
        · cases hop; exact writeRef_isSet h (readRef_keyNodup h src) dst
        · cases hop; exact h
  | insertData q =>
    simp only [applyOp, applyInsertData] at hop
    cases hop; exact Dataset.insertQuads_isSet _ h
  | deleteData q =>
    simp only [applyOp, applyDeleteData] at hop
    cases hop; exact Dataset.deleteQuads_isSet _ h
  | deleteWhere p =>
    simp only [applyOp] at hop
    split at hop
    · cases hop
    · cases hop; exact Dataset.deleteQuads_isSet _ h
  | modify w d i u p =>
    simp only [applyOp] at hop
    split at hop
    · cases hop
    · cases hop
      unfold applyModify
      dsimp only
      cases i with
      | none => exact Dataset.deleteQuads_isSet _ h
      | some it => exact Dataset.insertQuads_isSet _ (Dataset.deleteQuads_isSet _ h)

open L4Factoidal.SPARQL in
theorem applyOps_isSet (env : EvalEnv) (pre : String) :
    ∀ (ix : Nat) (ds : Dataset) (ops : List UpdateOp) (ds' : Dataset),
      ds.IsSet → applyOps env pre ix ds ops = .ok ds' → ds'.IsSet
  | _, ds, [], ds', h, hop => by simp only [applyOps] at hop; cases hop; exact h
  | ix, ds, op :: rest, ds', h, hop => by
      simp only [applyOps] at hop
      split at hop
      · cases hop
      · next d hd => exact applyOps_isSet env pre (ix + 1) d rest ds' (applyOp_isSet env pre ix h op hd) hop

open L4Factoidal.SPARQL in
/-- A SPARQL 1.1 Update request applied to a set gives a set. -/
theorem applyUpdateIn_isSet (env : EvalEnv) {ds ds' : Dataset} (u : Update) (h : ds.IsSet)
    (hu : applyUpdateIn env ds u = .ok ds') : ds'.IsSet :=
  applyOps_isSet env (requestPrefix ds) 0 ds u.ops ds' h hu

/-! ## Operations on certified datasets -/

def CertifiedDataset.renameBnodes (pre : String) (c : CertifiedDataset) : CertifiedDataset :=
  ⟨renameDatasetBnodes pre c.val, renameDatasetBnodes_isSet pre c.property⟩

def CertifiedDataset.insertQuads (c : CertifiedDataset) (qs : List Quad) : CertifiedDataset :=
  ⟨c.val.insertQuads qs, Dataset.insertQuads_isSet qs c.property⟩

def CertifiedDataset.deleteQuads (c : CertifiedDataset) (qs : List Quad) : CertifiedDataset :=
  ⟨c.val.deleteQuads qs, Dataset.deleteQuads_isSet qs c.property⟩

/-! ## Checks -/

private def px : WfIri := ⟨"urn:p", by decide⟩
private def gx : WfIri := ⟨"urn:g", by decide⟩
private def tx : Triple := ⟨.iri ⟨"urn:s", by decide⟩, px, .literal (Literal.string "x")⟩
private def tb : Triple := ⟨.bnode "b", px, .bnode "c"⟩

-- `certify` removes a repeated triple and keeps an empty named graph.
#guard (Dataset.certify { default := [tx, tx], named := [⟨.iri gx, []⟩] }).val ==
  { default := [tx], named := [⟨.iri gx, []⟩] }
-- Inserting a triple the graph has, or deleting one it lacks, keeps the count.
#guard ((Dataset.certify { default := [tx], named := [] }).insertQuads
  [(none, tx), (none, tx), (some gx, tx), (some gx, tx)]).val ==
  { default := [tx], named := [⟨.iri gx, [tx]⟩] }
#guard ((Dataset.certify { default := [tx, tb], named := [] }).deleteQuads
  [(none, tx)]).val.default == [tb]
-- The scope prefix renames blank nodes only.
#guard ((Dataset.certify { default := [tb, tx], named := [] }).renameBnodes "d0_").val.default ==
  [⟨.bnode "d0_b", px, .bnode "d0_c"⟩, tx]

#print axioms Dataset.certify
#print axioms renameDatasetBnodes_isSet
#print axioms Dataset.insertQuads_isSet
#print axioms Dataset.deleteQuads_isSet
#print axioms applyUpdateIn_isSet

end L4Factoidal.RDF
