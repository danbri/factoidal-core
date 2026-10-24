/-
L4Factoidal.RDFS.Closure — the EXECUTABLE rdfs-core closure.

Port of the extractable part of
`formal/fstar/RDF.Entailment.RDFS.RhoDFClosure.fst`:
`rho_df_closure_step_pre_dedup` (line 98), `rho_df_closure_step`
(line 107) and the fuel/length-test fixpoint `rho_df_closure`
(line 114), together with the six `rdfs_rule_*` bodies those compose,
which live in `formal/fstar/RDFS.Closure.fsti` lines 242-355.

`RdfsCore.lean` is the specification (the rule relation `Derives`); this
file is the implementation; `ClosureTheorems.lean` connects them. The
split is deliberate: a reviewer checks the six inductive constructors
of `Derives` against the RDF 1.1 Semantics §9.2 table by eye, and
trusts this file only through the proved theorems.

## Two faithful-port decisions, and one deliberate deviation

1. **Deduplication is `Graph.add`'s**, i.e. the engine's `Triple.eqb`
   membership — the same set semantics `RDF.Graph`'s `graph_add` has.
   The F* step ends in `graph_dedup_sort`; sorting is a performance
   device (it makes the length test cheap and the index build linear)
   and carries no semantics, so it is not ported. What IS ported is
   that the step emits no duplicate: `addAll` folds `Graph.add`.

2. **The fixpoint test is the F* one**: run a step, compare LENGTHS,
   stop when the length did not move. `addAll_eq_of_length_eq` in
   `ClosureTheorems.lean` proves that test exact for this step
   function — equal length really does imply the step was the
   identity — which the F* module carries as the hypothesis pair
   `no_repeats_p g` / `no_repeats_p (rho_df_closure_step g)` on
   `lemma_len_eq_saturated` rather than discharging.

3. **DEVIATION (documented, semantics-preserving at the fixpoint).**
   The F* step threads its accumulator through the six rows, so a
   triple emitted by rdfs7 inside a step can drive rdfs9 in the SAME
   step (the rows read premises from the snapshot index `ig`, but
   rdfs9/rdfs11/rdfs5 fold over the accumulated graph). This port
   reads EVERY premise from the step's input snapshot `g`. Per step
   this can emit less; at the fixpoint it emits the same set, since a
   conclusion the F* step reaches through an intra-step chain is
   reached here one round later, and the loop runs to saturation.
   The cost is iteration count, not the result. Stated this way the
   step is a plain function of its input, which is what makes the
   soundness and saturation proofs one induction each.
-/
import L4Factoidal.RDFS.RdfsCore
import L4Factoidal.RDF.FastGraph
import Std.Data.HashMap

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## Premise lookup

The F* rows read premises through `build_indexed`'s buckets
(`bucket_lookup ig.ig_pred p`, `find_objects_indexed ig s p`). The
index is performance machinery; the specification-level lookup is a
list scan with the same answer. -/

/-- Every object of a `(s, p, ·)` triple of `g` — the specification
counterpart of `find_objects_indexed ig s p`. -/
def objectsOf (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  (g.filter (fun t => t.s == s && t.p == p)).map (fun t => t.o)

/-- Every triple of `g` with predicate `p` — the specification
counterpart of `bucket_lookup ig.ig_pred p`. -/
def triplesWithPredicate (g : Graph) (p : WfIri) : List Triple :=
  g.filter (fun t => t.p == p)

/-! ## The six rows

Each `rdfsNFor g t` reads `t` as the row's FIRST premise and returns
every conclusion that row licenses from `t` together with a second
premise found in `g`. Rows rdfs7/rdfs2/rdfs3 are driven by the schema
declaration (the join reorder of F* task #36); rows rdfs9/rdfs11/rdfs5
are driven by the data triple, exactly as the F* bodies are. -/

/-- **rdfs7** (`rdfs_rule_subPropertyOf`): from a declaration
`p rdfs:subPropertyOf q`, re-assert every `p`-triple of `g` under
`q`. -/
def rdfs7For (g : Graph) (decl : Triple) : List Triple :=
  match decl.s, decl.o with
  | .iri p, .iri q =>
      if decl.p == rdfsSubPropertyOf then
        (triplesWithPredicate g p).map (fun t => ⟨t.s, q, t.o⟩)
      else []
  | _, _ => []

/-- **rdfs2** (`rdfs_rule_domain`): from `p rdfs:domain C`, type the
subject of every `p`-triple of `g` as a `C`. -/
def rdfs2For (g : Graph) (decl : Triple) : List Triple :=
  match decl.s with
  | .iri p =>
      if decl.p == rdfsDomain then
        (triplesWithPredicate g p).map (fun t => ⟨t.s, rdfType, decl.o⟩)
      else []
  | _ => []

/-- **rdfs3** (`rdfs_rule_range`): from `p rdfs:range C`, type the
object of every `p`-triple of `g` as a `C` — skipping the triples
whose object cannot be a subject (literals, and RDF 1.2 triple
terms). -/
def rdfs3For (g : Graph) (decl : Triple) : List Triple :=
  match decl.s with
  | .iri p =>
      if decl.p == rdfsRange then
        (triplesWithPredicate g p).filterMap (fun t =>
          match t.o.toSubject? with
          | some osub => some ⟨osub, rdfType, decl.o⟩
          | none      => none)
      else []
  | _ => []

/-- **rdfs9** (`rdfs_rule_subClassOf`): from a data triple
`s rdf:type A`, re-type `s` under every super-class of `A` in `g`.
RDF 1.1 Semantics §9.2: "xxx rdfs:subClassOf yyy . zzz rdf:type xxx . |
zzz rdf:type yyy ." `A` is an IRI or a blank node (issue 982); a literal
object has no `rdfs:subClassOf` triple, since a literal cannot be a
subject. -/
def rdfs9For (g : Graph) (t : Triple) : List Triple :=
  match t.o.toSubject? with
  | some a =>
      if t.p == rdfType then
        (objectsOf g a rdfsSubClassOf).map
          (fun b => ⟨t.s, rdfType, b⟩)
      else []
  | none => []

/-- **rdfs11** (`rdfs_rule_subClassOf_trans`): from `A rdfs:subClassOf
B`, compose with every `B rdfs:subClassOf C` of `g`. -/
def rdfs11For (g : Graph) (t : Triple) : List Triple :=
  if t.p == rdfsSubClassOf then
    match t.o.toSubject? with
    | some bsub =>
        (objectsOf g bsub rdfsSubClassOf).map
          (fun c => ⟨t.s, rdfsSubClassOf, c⟩)
    | none => []
  else []

/-- **rdfs5** (`rdfs_rule_subPropertyOf_trans`): the dual of rdfs11
for the property hierarchy. -/
def rdfs5For (g : Graph) (t : Triple) : List Triple :=
  if t.p == rdfsSubPropertyOf then
    match t.o.toSubject? with
    | some bsub =>
        (objectsOf g bsub rdfsSubPropertyOf).map
          (fun c => ⟨t.s, rdfsSubPropertyOf, c⟩)
    | none => []
  else []

/-! ## One step -/

/-- Everything the six rows conclude from `g` in one round, before
deduplication — the counterpart of
`rho_df_closure_step_pre_dedup`, in the same row order (rdfs7,
rdfs2, rdfs3, rdfs9, rdfs11, rdfs5). Unlike the F* function this
returns only the NEW conclusions, not `g` extended by them; `step`
adds them. -/
def stepConclusions (g : Graph) : List Triple :=
  g.flatMap (rdfs7For g) ++
  g.flatMap (rdfs2For g) ++
  g.flatMap (rdfs3For g) ++
  g.flatMap (rdfs9For g) ++
  g.flatMap (rdfs11For g) ++
  g.flatMap (rdfs5For g)

/-- Add a list of triples set-wise (`Graph.add` skips a triple the
graph already holds under `Triple.eqb`). -/
def addAll (g : Graph) : List Triple → Graph
  | []      => g
  | t :: ts => addAll (g.add t) ts

/-- One closure round: `g` plus every conclusion the six rows license
from `g`, deduplicated — port of `rho_df_closure_step`. -/
def step (g : Graph) : Graph :=
  addAll g (stepConclusions g)

/-! ## The fixpoint loop -/

/-- Fuel-bounded fixpoint — port of `rho_df_closure` (line 114),
including its exact stopping rule: run a step, and if the LENGTH did
not change, return the INPUT `g` (not the step's output; at equal
length the two hold the same triples — see
`ClosureTheorems.addAll_eq_of_length_eq`). -/
def closure (g : Graph) (fuel : Nat) : Graph :=
  match fuel with
  | 0     => g
  | n + 1 =>
      let g' := step g
      if g'.length = g.length then g else closure g' n

/-! ## Indexed evaluation of the same rounds (2026-10-10)

`step` reads its premises through list scans: `triplesWithPredicate g p` and
`objectsOf g s p` each traverse all of `g`, once per triple of `g`, and
`addAll` folds `Graph.add`, whose membership test is another traversal. One
round therefore costs O(|g|^2), and the loop runs one round per derivation
depth. Measured 2026-10-10 (`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`):
the RDFS closure of a 160-class `rdfs:subClassOf` chain took 359 s, against
0.66 s in the F\* engine.

This section computes the SAME rounds with hash indexes and proves it:

* `StepIndex.build g` holds, for each predicate, the triples of `g` that carry
  it, and for each (subject, predicate), the objects of the matching triples,
  both in the order of `g` (`StepIndex.byPred_getD`, `StepIndex.objs_getD`).
  The row functions with an `Ix` suffix read those buckets instead of scanning;
  `rdfs7ForIx_eq` .. `rdfs5ForIx_eq` prove each equal to its scanning twin, so
  `stepConclusionsIx g = stepConclusions g` as LISTS (`stepConclusionsIx_eq`):
  same triples, same order, same repetitions.
* `stepFast` adds those conclusions with `FastGraph.addAll`, whose bucketed
  membership test is proved equal to the `Graph.add` scan
  (`FastGraph.addAll_toGraph`), so `stepFast g = step g` as lists
  (`stepFast_eq`).
* `closureFast` is `closure` with `stepFast`; `closureFast_eq` proves it equal
  by induction on the fuel, and `closure_eq_closureFast` is registered
  `@[csimp]`, so the compiler emits `closureFast` for every call of `closure`
  made after this point: `closureFix`, `rhoDfClosure`, and the callers in
  other modules. The definition of `closure`, and therefore every theorem
  stated about it, is unchanged.

The result is identical as a list, not only as a set, so the order of the
printed closure does not change.
-/

/-- The premise index of one round. `byPred p` lists the triples of the graph
with predicate `p`; `objs (s, p)` lists the objects of its `(s, p, ·)` triples.
Both keep the order of the graph. -/
structure StepIndex where
  byPred : Std.HashMap WfIri (List Triple)
  objs   : Std.HashMap (Subject × WfIri) (List Term)

/-- Index a graph. The graph is traversed from its end so that consing
leaves each bucket in graph order. -/
def StepIndex.build (g : Graph) : StepIndex :=
  { byPred := g.reverse.foldl (fun m t => m.insert t.p (t :: m.getD t.p [])) ∅
  , objs := g.reverse.foldl
      (fun m t => m.insert (t.s, t.p) (t.o :: m.getD (t.s, t.p) [])) ∅ }

theorem foldl_byPred_getD (l : List Triple) :
    ∀ (m : Std.HashMap WfIri (List Triple)) (k : WfIri),
      (l.foldl (fun m t => m.insert t.p (t :: m.getD t.p [])) m).getD k []
        = l.reverse.filter (fun t => t.p == k) ++ m.getD k [] := by
  induction l with
  | nil => intro m k; simp
  | cons t ts ih =>
      intro m k
      rw [List.foldl_cons, ih, Std.HashMap.getD_insert, List.reverse_cons,
        List.filter_append, List.append_assoc]
      by_cases h : (t.p == k) = true
      · have h' : t.p = k := eq_of_beq h
        subst h'
        simp only [beq_self_eq_true, if_true, List.filter_cons, List.filter_nil,
          List.singleton_append]
      · have h' : (t.p == k) = false := by simpa using h
        simp only [h', Bool.false_eq_true, if_false, List.filter_cons, List.filter_nil,
          List.nil_append]

theorem StepIndex.byPred_getD (g : Graph) (p : WfIri) :
    (StepIndex.build g).byPred.getD p [] = triplesWithPredicate g p := by
  simp only [StepIndex.build, foldl_byPred_getD, List.reverse_reverse, triplesWithPredicate]
  simp

theorem foldl_objs_getD (l : List Triple) :
    ∀ (m : Std.HashMap (Subject × WfIri) (List Term)) (k : Subject × WfIri),
      (l.foldl (fun m t => m.insert (t.s, t.p) (t.o :: m.getD (t.s, t.p) [])) m).getD k []
        = (l.reverse.filter (fun t => t.s == k.1 && t.p == k.2)).map (fun t => t.o)
            ++ m.getD k [] := by
  induction l with
  | nil => intro m k; simp
  | cons t ts ih =>
      intro m k
      rw [List.foldl_cons, ih, Std.HashMap.getD_insert, List.reverse_cons,
        List.filter_append, List.map_append, List.append_assoc]
      by_cases h : ((t.s, t.p) == k) = true
      · have h' : (t.s, t.p) = k := eq_of_beq h
        subst h'
        simp only [beq_self_eq_true, if_true, Bool.and_self, List.filter_cons, List.map_cons,
          List.filter_nil, List.map_nil, List.singleton_append]
      · have h2 : ((t.s, t.p) == k) = false := by simpa using h
        have h' : (t.s == k.1 && t.p == k.2) = false := by
          cases hh : (t.s == k.1 && t.p == k.2)
          · rfl
          · exfalso
            apply h
            have hs : t.s = k.1 := eq_of_beq (by simpa using (Bool.and_eq_true_iff.mp hh).1)
            have hp : t.p = k.2 := eq_of_beq (by simpa using (Bool.and_eq_true_iff.mp hh).2)
            have : (t.s, t.p) = k := Prod.ext hs hp
            subst this
            exact beq_self_eq_true _
        simp only [h2, h', Bool.false_eq_true, if_false, List.filter_cons, List.map_nil,
          List.filter_nil, List.nil_append]

theorem StepIndex.objs_getD (g : Graph) (s : Subject) (p : WfIri) :
    (StepIndex.build g).objs.getD (s, p) [] = objectsOf g s p := by
  simp only [StepIndex.build, foldl_objs_getD, List.reverse_reverse, objectsOf]
  simp

/-- `rdfs7For`, reading the predicate bucket. -/
def rdfs7ForIx (ix : StepIndex) (decl : Triple) : List Triple :=
  match decl.s, decl.o with
  | .iri p, .iri q =>
      if decl.p == rdfsSubPropertyOf then
        (ix.byPred.getD p []).map (fun t => ⟨t.s, q, t.o⟩)
      else []
  | _, _ => []

/-- `rdfs2For`, reading the predicate bucket. -/
def rdfs2ForIx (ix : StepIndex) (decl : Triple) : List Triple :=
  match decl.s with
  | .iri p =>
      if decl.p == rdfsDomain then
        (ix.byPred.getD p []).map (fun t => ⟨t.s, rdfType, decl.o⟩)
      else []
  | _ => []

/-- `rdfs3For`, reading the predicate bucket. -/
def rdfs3ForIx (ix : StepIndex) (decl : Triple) : List Triple :=
  match decl.s with
  | .iri p =>
      if decl.p == rdfsRange then
        (ix.byPred.getD p []).filterMap (fun t =>
          match t.o.toSubject? with
          | some osub => some ⟨osub, rdfType, decl.o⟩
          | none      => none)
      else []
  | _ => []

/-- `rdfs9For`, reading the (subject, `rdfs:subClassOf`) bucket. -/
def rdfs9ForIx (ix : StepIndex) (t : Triple) : List Triple :=
  match t.o.toSubject? with
  | some a =>
      if t.p == rdfType then
        (ix.objs.getD (a, rdfsSubClassOf) []).map
          (fun b => ⟨t.s, rdfType, b⟩)
      else []
  | none => []

/-- `rdfs11For`, reading the (subject, `rdfs:subClassOf`) bucket. -/
def rdfs11ForIx (ix : StepIndex) (t : Triple) : List Triple :=
  if t.p == rdfsSubClassOf then
    match t.o.toSubject? with
    | some bsub =>
        (ix.objs.getD (bsub, rdfsSubClassOf) []).map
          (fun c => ⟨t.s, rdfsSubClassOf, c⟩)
    | none => []
  else []

/-- `rdfs5For`, reading the (subject, `rdfs:subPropertyOf`) bucket. -/
def rdfs5ForIx (ix : StepIndex) (t : Triple) : List Triple :=
  if t.p == rdfsSubPropertyOf then
    match t.o.toSubject? with
    | some bsub =>
        (ix.objs.getD (bsub, rdfsSubPropertyOf) []).map
          (fun c => ⟨t.s, rdfsSubPropertyOf, c⟩)
    | none => []
  else []

theorem rdfs7ForIx_eq (g : Graph) (decl : Triple) :
    rdfs7ForIx (StepIndex.build g) decl = rdfs7For g decl := by
  unfold rdfs7ForIx rdfs7For
  split <;> simp [StepIndex.byPred_getD]

theorem rdfs2ForIx_eq (g : Graph) (decl : Triple) :
    rdfs2ForIx (StepIndex.build g) decl = rdfs2For g decl := by
  unfold rdfs2ForIx rdfs2For
  split <;> simp [StepIndex.byPred_getD]

theorem rdfs3ForIx_eq (g : Graph) (decl : Triple) :
    rdfs3ForIx (StepIndex.build g) decl = rdfs3For g decl := by
  unfold rdfs3ForIx rdfs3For
  split <;> simp [StepIndex.byPred_getD]

theorem rdfs9ForIx_eq (g : Graph) (t : Triple) :
    rdfs9ForIx (StepIndex.build g) t = rdfs9For g t := by
  unfold rdfs9ForIx rdfs9For
  split <;> simp [StepIndex.objs_getD]

theorem rdfs11ForIx_eq (g : Graph) (t : Triple) :
    rdfs11ForIx (StepIndex.build g) t = rdfs11For g t := by
  unfold rdfs11ForIx rdfs11For
  split
  · split <;> simp [StepIndex.objs_getD]
  · rfl

theorem rdfs5ForIx_eq (g : Graph) (t : Triple) :
    rdfs5ForIx (StepIndex.build g) t = rdfs5For g t := by
  unfold rdfs5ForIx rdfs5For
  split
  · split <;> simp [StepIndex.objs_getD]
  · rfl

/-- `stepConclusions` with every premise read from an index built once. -/
def stepConclusionsIx (g : Graph) : List Triple :=
  let ix := StepIndex.build g
  g.flatMap (rdfs7ForIx ix) ++
  g.flatMap (rdfs2ForIx ix) ++
  g.flatMap (rdfs3ForIx ix) ++
  g.flatMap (rdfs9ForIx ix) ++
  g.flatMap (rdfs11ForIx ix) ++
  g.flatMap (rdfs5ForIx ix)

/-- The indexed conclusions are the scanning conclusions: the same list. -/
theorem stepConclusionsIx_eq (g : Graph) : stepConclusionsIx g = stepConclusions g := by
  have h7 : rdfs7ForIx (StepIndex.build g) = rdfs7For g := funext (rdfs7ForIx_eq g)
  have h2 : rdfs2ForIx (StepIndex.build g) = rdfs2For g := funext (rdfs2ForIx_eq g)
  have h3 : rdfs3ForIx (StepIndex.build g) = rdfs3For g := funext (rdfs3ForIx_eq g)
  have h9 : rdfs9ForIx (StepIndex.build g) = rdfs9For g := funext (rdfs9ForIx_eq g)
  have h11 : rdfs11ForIx (StepIndex.build g) = rdfs11For g := funext (rdfs11ForIx_eq g)
  have h5 : rdfs5ForIx (StepIndex.build g) = rdfs5For g := funext (rdfs5ForIx_eq g)
  simp only [stepConclusionsIx, stepConclusions]
  rw [h7, h2, h3, h9, h11, h5]

/-- `addAll` is the left fold of `Graph.add` that `FastGraph.addAll`
refines. -/
theorem addAll_eq_graphAddAll (ts : List Triple) :
    ∀ g : Graph, addAll g ts = graphAddAll g ts := by
  induction ts with
  | nil => intro g; rfl
  | cons t ts ih => intro g; exact ih (g.add t)

/-- One round with the indexed conclusions and the bucketed duplicate test. -/
def stepFast (g : Graph) : Graph :=
  ((FastGraph.ofGraph g).addAll (stepConclusionsIx g)).toGraph

theorem stepFast_eq (g : Graph) : stepFast g = step g := by
  unfold stepFast step
  rw [FastGraph.addAll_toGraph _ _ (FastGraph.ofGraph_inv g), FastGraph.ofGraph_toGraph,
    stepConclusionsIx_eq, addAll_eq_graphAddAll]

/-- `closure` with `stepFast`. -/
def closureFast (g : Graph) : Nat → Graph
  | 0     => g
  | n + 1 =>
      let g' := stepFast g
      if g'.length = g.length then g else closureFast g' n

theorem closureFast_eq (g : Graph) (n : Nat) : closureFast g n = closure g n := by
  induction n generalizing g with
  | zero => rfl
  | succ n ih =>
      simp only [closureFast, closure, stepFast_eq]
      split
      · rfl
      · exact ih _

/-- The compiler emits `closureFast` for every later call of `closure`. -/
@[csimp] theorem closure_eq_closureFast : @closure = @closureFast := by
  funext g n
  exact (closureFast_eq g n).symm

/-- Repeated stepping with no fixpoint test — port of
`rho_df_closure_iter` (line 124). Used by the theorems, not by
callers. -/
def closureIter (g : Graph) : Nat → Graph
  | 0     => g
  | n + 1 => closureIter (step g) n

/-- The fuel budget `closureFix` spends.

The F* module leaves fuel to the caller, and the F* tree's callers
pass the constant 100 (`bin/w3c-runner/w3c_runner.ml:1276`,
`bin/factoidal-cli/factoidal_cli.ml:2427`) — a resource budget, not a
bound with an argument behind it. The bound here has the counting
argument behind it instead:

* the loop only recurses when the step STRICTLY grew the graph (equal
  length stops it), so at most one iteration per triple ever added;
* every rule conclusion is built from components already present —
  its subject is a subject or object of `g`, its object is an object
  of `g`, and its predicate is a predicate of `g` or `rdf:type` — so
  the closure of an `n`-triple graph holds at most `n * (n + 1) * n`
  triples;

hence `n * (n + 1) * n + 1` rounds cannot be exhausted before the
length test fires. The counting argument is stated, NOT proved:
`ClosureTheorems.closure_saturated_or_underfueled` is what is proved,
and it says precisely that the only alternative to saturation is a
closure that grew by at least one triple per unit of fuel. Formalising
the term-universe bound is the named remaining obligation. -/
def closureFuelBound (g : Graph) : Nat :=
  g.length * (g.length + 1) * g.length + 1

/-- The closure at the fuel bound above. -/
def closureFix (g : Graph) : Graph :=
  closure g (closureFuelBound g)

/-! ## The ρdf model fragment, decided

`RhoDfCompleteness.RhoDfModelFragGraph` is the Prop under which the
completeness theorem holds: every object is an IRI or a blank node,
and the object of `rdfs:subPropertyOf` is an IRI. `isRhoDfFrag` is its
executable twin — the check the npm `rhoDfFragmentCheck` entry serves
(the F\* counterpart is `rho_df_model_frag_check`). -/

/-- One triple of the fragment. -/
def isRhoDfFragTriple (t : Triple) : Bool :=
  (match t.o with
   | .iri _ => true
   | .bnode _ => true
   | _ => false) &&
  (t.p != rdfsSubPropertyOf ||
   (match t.o with | .iri _ => true | _ => false))

/-- The whole graph. -/
def isRhoDfFrag (g : Graph) : Bool := g.all isRhoDfFragTriple

end L4Factoidal.RDFS
