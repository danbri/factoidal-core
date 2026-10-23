/-
L4Factoidal.RDF.NormalizeSet — `normalizeDataset` for a dataset that is
already a set of quads, without indexing the triples a second time.

RDF 1.1 Concepts and Abstract Syntax, section 3: "An RDF graph is a set of RDF
triples." Every parser of the source layer returns a set (`Source.parseDocument`
ends in `Dataset.toSet`, `RDF/DatasetSet.lean`). The command line then handed
that dataset to `datasetForOps` (`RDF/DatasetNormalize.lean`), whose
`normalizeDataset` adds every quad to the hash-indexed accumulator once more:
two passes that remove duplicates, the second of which finds none. On QUDT
(6.8 MB of Turtle, 130,404 triples) the second pass was 13 to 14 percent of the
time of `l4factoidal query`.

`normalizeDataset` does two things (section 3.3 and section 3, section 4):

* it lower-cases every language tag ("The value space of language tags is
  always in lower case"), and
* it builds the dataset from the quads, so a named graph with no quad is not
  there, and a triple that `Triple.eqb` equates with an earlier one of its
  graph is not added.

For a dataset that `Dataset.IsSet` holds of, the second part changes nothing but
the empty named graphs: `Triple.key` of a triple does not change when its tags
are lower-cased (`Triple.key_lowerTags`), so no two of the lowered triples of a
graph are `Triple.eqb`-equal, and the names are unique already. So the result is
a map over the lists: `Dataset.normalizeSet`. `normalizeDataset_of_isSet` proves
it equal to `normalizeDataset` for every set, and `datasetForOpsSet_eq` that the
operations get the same dataset from `datasetForOpsSet` as from `datasetForOps`
(`roundTripSafe` and the text round trip are unchanged).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetNormalize
import L4Factoidal.RDF.DatasetSet
import L4Factoidal.Syntax.NQuadsFastTheorems

namespace L4Factoidal.RDF

open L4Factoidal.Syntax
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## The key does not see the case of a language tag -/

private theorem char_toLower_idem (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split
  · next h =>
    rw [dif_neg]
    intro h2
    simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add] at h h2
    simp at h h2
    omega
  · rfl

private theorem string_toLower_idem (s : String) : s.toLower.toLower = s.toLower := by
  apply String.ext
  simp [String.toLower, String.toList_map, char_toLower_idem]

theorem Term.joinKey_lowerTags : ∀ t : Term, t.lowerTags.joinKey = t.joinKey
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal l => by
      simp only [Term.lowerTags, Term.joinKey]
      congr 1
      apply Subtype.ext
      show (l.val.lowerTag).joinKey = l.val.joinKey
      unfold Literal.joinKey Literal.lowerTag
      cases l.val.langTag with
      | none => rfl
      | some a => simp [string_toLower_idem]
  | .tripleTerm s p o => by
      simp only [Term.lowerTags, Term.joinKey]
      rw [Term.joinKey_lowerTags o]

/-- Lower-casing the language tags of a triple does not change its key. -/
theorem Triple.key_lowerTags (t : Triple) : t.lowerTags.key = t.key := by
  simp [Triple.key, Triple.lowerTags, Term.joinKey_lowerTags]

theorem Graph.keyNodup_map_lowerTags (g : Graph) :
    Graph.KeyNodup (g.map Triple.lowerTags) ↔ Graph.KeyNodup g := by
  unfold Graph.KeyNodup
  rw [List.map_map]
  have : (Triple.key ∘ Triple.lowerTags) = Triple.key := funext Triple.key_lowerTags
  rw [this]

/-! ## The result -/

/-- The named graph with the language tags of its triples in lower case. -/
def lowerNG (ng : NamedGraph) : NamedGraph :=
  { name := ng.name, graph := ng.graph.map Triple.lowerTags }

/-- `normalizeDataset` of a dataset that is a set of quads: the language tags in
lower case, the named graphs with no triple left out, the lists otherwise as
they are. -/
def Dataset.normalizeSet (ds : Dataset) : Dataset :=
  { default := ds.default.map Triple.lowerTags
  , named := (ds.named.filter (fun ng => !ng.graph.isEmpty)).map lowerNG }

/-! ## The indexed accumulator is `addQuad` -/

theorem foldFast_toDataset (f : Triple → Triple) (qs : List (Triple × Option Subject)) :
    ∀ acc : FastDataset, acc.Inv →
      (qs.foldl (fun a q => addQuadFast a (f q.1) q.2) acc).Inv ∧
      (qs.foldl (fun a q => addQuadFast a (f q.1) q.2) acc).toDataset =
        qs.foldl (fun d q => addQuad d (f q.1) q.2) acc.toDataset := by
  induction qs with
  | nil => intro acc h; exact ⟨h, rfl⟩
  | cons q qs ih =>
    intro acc h
    obtain ⟨h1, h2⟩ := ih (addQuadFast acc (f q.1) q.2) (FastDataset.add_inv h)
    exact ⟨h1, by rw [List.foldl_cons, List.foldl_cons, h2, addQuadFast_toDataset _ _ h]⟩

/-! ## Adding to a set -/

theorem Graph.add_of_nodup {G rest : Graph} {t : Triple} (h : (G ++ t :: rest).KeyNodup) :
    Graph.add t G = G ++ [t] := by
  unfold Graph.KeyNodup at h
  rw [List.map_append, List.map_cons] at h
  have hn := List.nodup_append.mp h
  have hm : Graph.mem t G = false := by
    cases hmm : Graph.mem t G
    · rfl
    · exact absurd rfl (hn.2.2 t.key ((Graph.mem_iff_keys t G).mp hmm) t.key (List.mem_cons_self ..))
  simp [Graph.add, hm]

/-- The default graph: adding the lowered triples of a graph that is a set. -/
theorem fold_default (g : Graph) : ∀ (d : Dataset),
    (d.default ++ g.map Triple.lowerTags).KeyNodup →
    g.foldl (fun d t => addQuad d (Triple.lowerTags t) none) d =
      { d with default := d.default ++ g.map Triple.lowerTags } := by
  induction g with
  | nil => intro d _; cases d; simp
  | cons t ts ih =>
    intro d h
    have hadd : d.default.add (Triple.lowerTags t) = d.default ++ [Triple.lowerTags t] :=
      Graph.add_of_nodup (by simpa using h)
    rw [List.foldl_cons, addQuad_default, ih]
    · simp [hadd, List.append_assoc]
    · simpa [hadd, List.append_assoc] using h

/-- One named graph that is there: the lowered triples are appended to it. -/
theorem fold_named_graph (n : Subject) : ∀ (l : Graph) (A : List NamedGraph) (g : Graph) (d : Dataset),
    (∀ x ∈ A, x.name ≠ n) → (g ++ l).KeyNodup →
    d.named = A ++ [{ name := n, graph := g }] →
    l.foldl (fun d t => addQuad d t (some n)) d =
      { d with named := A ++ [{ name := n, graph := g ++ l }] } := by
  intro l
  induction l with
  | nil => intro A g d _ _ hd; cases d; simp_all
  | cons t ts ih =>
    intro A g d hne hk hd
    have hadd : g.add t = g ++ [t] := Graph.add_of_nodup (by simpa using hk)
    have hnone : A.find? (fun ng => ng.name == n) = none :=
      List.find?_eq_none.mpr (fun x hx => by simpa using hne x hx)
    have hstep : addQuad d t (some n) = { d with named := A ++ [{ name := n, graph := g ++ [t] }] } := by
      simp only [addQuad, hd, List.find?_append, hnone]
      simp only [List.map_append, List.map_cons, List.map_nil]
      simp
      refine ⟨?_, hadd⟩
      rw [hadd]
      refine (List.map_congr_left (g := id) ?_).trans (List.map_id A)
      intro x hx
      simp [hne x hx]
    rw [List.foldl_cons, hstep, ih A (g ++ [t]) _ hne _ rfl]
    · simp [List.append_assoc]
    · simpa [List.append_assoc] using hk

/-- One named graph that is not there yet: the first lowered triple makes it. -/
theorem fold_named_first (n : Subject) (l : Graph) (A : List NamedGraph) (d : Dataset)
    (hne : ∀ x ∈ A, x.name ≠ n) (hl : l.KeyNodup) (hd : d.named = A) :
    l.foldl (fun d t => addQuad d t (some n)) d =
      (if l.isEmpty then d else { d with named := A ++ [{ name := n, graph := l }] }) := by
  cases l with
  | nil => simp
  | cons t ts =>
    have hnone : A.find? (fun ng => ng.name == n) = none :=
      List.find?_eq_none.mpr (fun x hx => by simpa using hne x hx)
    have hstep : addQuad d t (some n) = { d with named := A ++ [{ name := n, graph := [t] }] } := by
      simp only [addQuad, hd, hnone]
    rw [List.foldl_cons, hstep,
      fold_named_graph n ts A [t] _ hne (by simpa using hl) rfl]
    simp

/-- The named graphs in list order. -/
theorem fold_named_list : ∀ (rest : List NamedGraph) (A : List NamedGraph) (d : Dataset),
    d.named = A → ((A ++ rest).map (·.name)).Nodup → (∀ ng ∈ rest, ng.graph.KeyNodup) →
    (rest.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))).foldl
        (fun d q => addQuad d (Triple.lowerTags q.1) q.2) d =
      { d with named := A ++ (rest.filter (fun ng => !ng.graph.isEmpty)).map lowerNG } := by
  intro rest
  induction rest with
  | nil => intro A d hd _ _; cases d; simp_all
  | cons ng rest ih =>
    intro A d hd hnames hgraphs
    have hnames' : ((A ++ ng :: rest).map (·.name)).Nodup := hnames
    rw [List.map_append, List.nodup_append] at hnames'
    have hne : ∀ x ∈ A, x.name ≠ ng.name := by
      intro x hx
      exact hnames'.2.2 x.name (List.mem_map_of_mem hx) ng.name (by simp)
    have hinner : (ng.graph.map (fun t => (t, some ng.name))).foldl
          (fun d q => addQuad d (Triple.lowerTags q.1) q.2) d =
        (ng.graph.map Triple.lowerTags).foldl (fun d t => addQuad d t (some ng.name)) d := by
      rw [List.foldl_map, List.foldl_map]
    rw [List.flatMap_cons, List.foldl_append, hinner,
      fold_named_first ng.name _ A d hne
        ((Graph.keyNodup_map_lowerTags _).mpr (hgraphs ng (List.mem_cons_self ..))) hd]
    by_cases hemp : ng.graph.isEmpty = true
    · have hemp' : (ng.graph.map Triple.lowerTags).isEmpty = true := by
        simpa using hemp
      rw [if_pos hemp', List.filter_cons, if_neg (by simp [hemp])]
      apply ih A d hd
      · have hsub : ((A ++ rest).map (·.name)).Sublist ((A ++ ng :: rest).map (·.name)) :=
          List.Sublist.map _ ((List.sublist_cons_self ng rest).append_left A)
        exact hsub.nodup hnames
      · exact fun x hx => hgraphs x (List.mem_cons_of_mem _ hx)
    · have hemp' : (ng.graph.map Triple.lowerTags).isEmpty = false := by
        simpa using hemp
      rw [if_neg (by simp [hemp']), List.filter_cons, if_pos (by simpa using hemp)]
      rw [ih (A ++ [lowerNG ng]) _ (by simp [lowerNG]) _ (fun x hx => hgraphs x (List.mem_cons_of_mem _ hx))]
      · simp [List.append_assoc]
      · have : (A ++ [lowerNG ng] ++ rest).map (·.name) = (A ++ ng :: rest).map (·.name) := by
          simp [lowerNG]
        rw [this]; exact hnames

/-- **`normalizeDataset` of a set is the map.** -/
theorem normalizeDataset_of_isSet (ds : Dataset) (h : ds.IsSet) :
    normalizeDataset ds = ds.normalizeSet := by
  unfold normalizeDataset
  rw [(foldFast_toDataset Triple.lowerTags ds.quadList {} FastDataset.inv_empty).2,
    FastDataset.toDataset_empty]
  unfold Dataset.quadList
  rw [List.foldl_append, List.foldl_map]
  have hdef : Graph.KeyNodup (ds.default.map Triple.lowerTags) :=
    (Graph.keyNodup_map_lowerTags _).mpr h.default
  rw [fold_default ds.default Dataset.empty (by simpa [Dataset.empty] using hdef)]
  rw [fold_named_list ds.named [] _ rfl (by simpa [Dataset.names] using h.names)
    (fun ng hng => h.graphs ng hng)]
  simp [Dataset.normalizeSet, Dataset.empty]

/-! ## What the command line calls -/

/-- `datasetForOps` for a dataset that is a set. -/
def datasetForOpsSet (mode : Mode) (ds : Dataset) (_ : ds.IsSet) : Except ParseError Dataset :=
  if roundTripSafe mode ds then .ok ds.normalizeSet
  else parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode

/-- `datasetForOpsSet` gives what `datasetForOps` gives, so the operations answer as before. -/
theorem datasetForOpsSet_eq (mode : Mode) (ds : Dataset) (h : ds.IsSet) :
    datasetForOpsSet mode ds h = datasetForOps mode ds := by
  unfold datasetForOpsSet datasetForOps
  split
  · rw [normalizeDataset_of_isSet ds h]
  · rfl

#print axioms Term.joinKey_lowerTags
#print axioms normalizeDataset_of_isSet
#print axioms datasetForOpsSet_eq

end L4Factoidal.RDF
