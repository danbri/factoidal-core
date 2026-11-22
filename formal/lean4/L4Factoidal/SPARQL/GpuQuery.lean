import L4Factoidal.SPARQL.IndexedEvalRefinement
import L4Factoidal.SPARQL.PathAlternativeTheorems
import L4Factoidal.Dataflow.Evaluator

/-!
# Resumable SPARQL evaluation through generic UInt64 candidate joins

The ordinary parser and reference algebra remain authoritative. A request
contains hash keys and row indices, never a replacement RDF interpretation.
The decoder applies the existing `tpMatch` or `Binding.compatible` operation
to the original Lean payloads. Hash collisions therefore add work without
adding solutions. A missing device reply runs the existing CPU operation.

The physical device obligation is exact, ordered index pairs for the numeric
request. It is stated by `Job.ReplyValid`; it is not an axiom. `Plan.Sound`
connects that obligation to the reference SPARQL answer, with no CPU replay
on a successful GPU path. The model interpreter is for proofs and tests.
-/

namespace L4Factoidal.SPARQL.GpuQuery

open L4Factoidal.RDF
open L4Factoidal.Dataflow

abbrev Pairs := List (Nat × Nat)

/-- Device-independent request. Keys are hash lanes, not RDF term IDs.
The row order is immutable for the lifetime of the suspended query. -/
structure Job where
  left : Array UInt64
  right : Array UInt64
  label : String
  maxPairs : Nat

/-- Ordered mathematical index pairs, including every matching occurrence.
This specification is never computed to validate a successful readback. -/
def Job.pairs (job : Job) : Pairs :=
  job.left.toList.zipIdx.flatMap fun l =>
    job.right.toList.zipIdx.filterMap fun r =>
      if l.1 == r.1 then some (l.2, r.2) else none

/-- The sole device semantic obligation. `none` means a refused, failed or
unavailable dispatch and is always admissible. -/
def Job.ReplyValid (job : Job) : Option Pairs → Prop
  | none => True
  | some ps => ps = job.pairs

/-- A query retains RDF values, expression closures, active graphs and all
remaining work in Lean while the host executes one numeric request. -/
inductive Plan (α : Type) where
  | done (value : α)
  | dispatch (job : Job) (resume : Option Pairs → Plan α)

namespace Plan

def bind (p : Plan α) (f : α → Plan β) : Plan β :=
  match p with
  | .done a => f a
  | .dispatch job resume => .dispatch job (fun reply => bind (resume reply) f)

def map (f : α → β) (p : Plan α) : Plan β := p.bind (fun a => .done (f a))

/-- Pure interpretation, for tests and semantic statements. Production
advances one constructor at a time and awaits the physical device. -/
def run (device : Job → Option Pairs) : Plan α → α
  | .done a => a
  | .dispatch job resume => run device (resume (device job))

def cpu (p : Plan α) : α := p.run (fun _ => none)
def denote (p : Plan α) : α := p.run (fun job => some job.pairs)

/-- Every sequence of valid device replies and CPU refusals has this exact
answer. This is stronger than testing a particular placement decision. -/
def Sound : Plan α → α → Prop
  | .done a, expected => a = expected
  | .dispatch job resume, expected =>
      ∀ reply, job.ReplyValid reply → Sound (resume reply) expected

/-- Refinement theorem. Says: interpreting a sound plan with a device
satisfying the numeric law returns its reference answer. Does not say:
that a particular driver, shader compiler or device satisfies that law. -/
theorem run_eq (p : Plan α) (expected : α) (hs : p.Sound expected)
    (device : Job → Option Pairs)
    (hd : ∀ job : Job, job.ReplyValid (device job)) : p.run device = expected := by
  induction p with
  | done a => exact hs
  | dispatch job resume ih =>
      exact ih (device job) (hs (device job) (hd job))

/-- Refinement theorem. Says: CPU refusal at every request preserves the
answer of a sound plan. Does not say: that CPU and GPU have equal cost. -/
theorem cpu_eq (p : Plan α) (expected : α) (hs : p.Sound expected) :
    p.cpu = expected := run_eq p expected hs _ (fun _ => trivial)

/-- Refinement theorem. Says: the numeric reference interpretation has the
answer of a sound plan. Does not say: that production recomputes this model. -/
theorem denote_eq (p : Plan α) (expected : α) (hs : p.Sound expected) :
    p.denote = expected := run_eq p expected hs _ (fun _ => rfl)

/-- Says: composing sound continuations preserves their stated result.
Does not say: that an unvalidated device reply is sound. -/
theorem Sound.bind {p : Plan α} {a : α} (hp : p.Sound a)
    {f : α → Plan β} {b : β} (hf : (f a).Sound b) :
    (p.bind f).Sound b := by
  induction p with
  | done value => cases hp; exact hf
  | dispatch job resume ih =>
      intro reply hr
      exact ih reply (hp reply hr)

/-- Says: pure post-processing preserves a sound result. Does not say:
that post-processing may observe or change device placement. -/
theorem Sound.map {p : Plan α} {a : α} (hp : p.Sound a) (f : α → β) :
    (p.map f).Sound (f a) := hp.bind rfl

def collect (xs : List α) (f : α → Plan (List β)) : Plan (List β) :=
  match xs with
  | [] => .done []
  | x :: rest => (f x).bind fun ys => (collect rest f).map (ys ++ ·)

/-- Says: collecting sound subplans preserves concatenation order and
multiplicity. Does not say: that the subplans execute concurrently. -/
theorem collect_sound (xs : List α) (f : α → Plan (List β))
    (g : α → List β) (h : ∀ x ∈ xs, (f x).Sound (g x)) :
    (collect xs f).Sound (xs.flatMap g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      apply Sound.bind (h x (by simp))
      apply Sound.map
      exact ih (fun y hy => h y (by simp [hy]))

end Plan

/-- Cost and resource admission are Lean decisions. The host reports device
availability and may calibrate the row crossover from measured transfers.
There is no Cartesian candidate allocation before this check. -/
structure Config where
  available : Bool := false
  minLeftRows : Nat := 1024
  minRightRows : Nat := 1024
  maxInputRows : Nat := 1000000
  maxOutputPairs : Nat := 1000000

def Config.admits (cfg : Config) (left right : Nat) : Bool :=
  cfg.available && left >= cfg.minLeftRows && right >= cfg.minRightRows &&
    left > 0 && right > 0 && left <= cfg.maxInputRows && right <= cfg.maxInputRows

/-- A planning estimate, never a bound on query semantics. Backend estimates
already account for constant predicates, subjects and objects. Saturating
cardinalities keeps speculative arithmetic bounded without reading solutions. -/
private structure Estimate where
  rows : Nat
  eligible : Bool

private def capEstimate (cfg : Config) (n : Nat) : Nat := min n (cfg.maxInputRows + 1)

private def sharesVars (l r : QueryPattern) : Bool :=
  l.inScopeVars.any (fun v => r.inScopeVars.contains v)

private def estimateBgp (cfg : Config) (gb : StoreBackend.GraphBackend) :
    Bgp → List VarName → Nat → Bool → Estimate
  | [], _, rows, eligible => ⟨rows, eligible⟩
  | tp :: rest, bound, rows, eligible =>
      let count := StorePlan.estimateTpBackend tp gb Binding.empty
      let vars := (QueryPattern.bgp [tp]).inScopeVars
      let shared := vars.any bound.contains
      let constant := (tp.s.resolveKey Binding.empty).isSome ||
        (tp.p.resolveKey Binding.empty).isSome || (tp.o.resolveKey Binding.empty).isSome
      let useGpu := (constant || shared) && cfg.admits rows count
      -- Shared variables make the expected join selective. A product is only
      -- estimated for disconnected patterns, and actual rows are checked again.
      let next := if shared then max rows count else rows * count
      estimateBgp cfg gb rest (bound ++ vars) (capEstimate cfg next) (eligible || useGpu)

private def estimatedDataset (dsb : StoreDataset.DatasetBackend)
    (clauses : List DatasetClause) : StoreDataset.DatasetBackend :=
  if clauses.isEmpty then dsb else
    let defaults := clauses.filterMap fun
      | .default iri => StoreDataset.lookupNamedBackend iri.val dsb.named
      | _ => none
    let named := dsb.named.filter fun ng => clauses.any fun
      | .named iri => StoreDataset.iriNamed ng.name iri.val
      | _ => false
    { default := .union defaults, named }

private def estimatePattern (cfg : Config) (dsb : StoreDataset.DatasetBackend)
    (gb : StoreBackend.GraphBackend) : QueryPattern → Estimate
  | .bgp triples => estimateBgp cfg gb triples [] 1 false
  | .join l r =>
      let le := estimatePattern cfg dsb gb l
      let re := estimatePattern cfg dsb gb r
      let shared := sharesVars l r
      let rows := if shared then max le.rows re.rows else le.rows * re.rows
      ⟨capEstimate cfg rows, le.eligible || re.eligible ||
        (shared && cfg.admits le.rows re.rows)⟩
  | .leftJoin l r _ =>
      let le := estimatePattern cfg dsb gb l
      let re := estimatePattern cfg dsb gb r
      ⟨capEstimate cfg (max le.rows re.rows), le.eligible || re.eligible⟩
  | .union l r =>
      let le := estimatePattern cfg dsb gb l
      let re := estimatePattern cfg dsb gb r
      ⟨capEstimate cfg (le.rows + re.rows), le.eligible || re.eligible⟩
  | .minus l r =>
      let le := estimatePattern cfg dsb gb l
      let re := estimatePattern cfg dsb gb r
      ⟨le.rows, le.eligible || re.eligible⟩
  | .filter _ p | .bind _ _ p => estimatePattern cfg dsb gb p
  | .graph name p =>
      match name with
      | .iri iri => match StoreDataset.lookupNamedBackend iri.val dsb.named with
          | none => ⟨0, false⟩
          | some named => estimatePattern cfg dsb named p
      | .var _ =>
          (dsb.named.map fun ng => estimatePattern cfg dsb ng.backend p).foldl
            (fun a e => ⟨capEstimate cfg (a.rows + e.rows), a.eligible || e.eligible⟩)
            ⟨0, false⟩
      | _ => estimatePattern cfg dsb gb p
  | .subSelect (.mk _ clauses p _ _ modifier _ _) =>
      let dsb' := estimatedDataset dsb clauses
      let e := estimatePattern cfg dsb' dsb'.default p
      { e with rows := min e.rows (modifier.limit.getD e.rows) }
  | .values _ rows => ⟨rows.length, false⟩
  | .empty => ⟨1, false⟩
  | _ => ⟨0, false⟩

/-- Cheap automatic-placement preflight using the shipping backend's cached
selectivity estimates. Small queries retain the existing shipping evaluator
without constructing a continuation. This is a cost heuristic: an estimate
can miss an opportunity, but cannot affect the answer or bypass runtime
input/output limits. No RDF rows are materialised by this function. -/
def worthwhile (cfg : Config) (dsb : StoreDataset.DatasetBackend) (q : Query) : Bool :=
  if !cfg.available then false else
    let usesWhere := match q.form with
      | .describe targets => describeNeedsSolutions targets
      | _ => true
    if !usesWhere then false else
      let selected := estimatedDataset dsb q.dataset
      (estimatePattern cfg selected selected.default q.pattern).eligible

/-- Only original payloads are reconstructed. Out-of-range indices are
rejected by the host's numeric readback validator before this decoder. -/
def decodePairs (left : Array α) (right : Array β) (f : α → β → Option γ)
    (pairs : Pairs) : List γ :=
  pairs.filterMap fun ij => do
    let l ← left[ij.1]?
    let r ← right[ij.2]?
    f l r

/-- Says: equal images on list members give equal flattened lists. Does
not say: that the functions agree outside those members. -/
private theorem flatMap_congr_mem {xs : List α} {f g : α → List β}
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Says: equal optional images on members give equal filtered lists.
Does not say: that filtering removes duplicate successful images. -/
private theorem filterMap_congr_mem {xs : List α} {f g : α → Option β}
    (h : ∀ x ∈ xs, f x = g x) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.filterMap_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- Says: unused occurrence indices do not change flattening. Does not
say: that occurrence indices identify distinct payload values. -/
private theorem zipIdx_flatMap_fst (xs : List α) (f : α → List β) :
    xs.zipIdx.flatMap (fun xi => f xi.1) = xs.flatMap f := by
  simpa only [List.flatMap_map] using
    congrArg (fun ys => ys.flatMap f) (List.zipIdx_map_fst 0 xs)

/-- Says: unused occurrence indices do not change filtering. Does not
say: that occurrence indices can be discarded by the physical join. -/
private theorem zipIdx_filterMap_fst (xs : List α) (f : α → Option β) :
    xs.zipIdx.filterMap (fun xi => f xi.1) = xs.filterMap f := by
  simpa only [List.filterMap_map, Function.comp_def] using
    congrArg (fun ys => ys.filterMap f) (List.zipIdx_map_fst 0 xs)

/-- Refinement theorem. Says: decoding the exact ordered numeric index
pairs is the corresponding key-filtered join of the original payloads.
Does not say: that physical device bytes satisfy the numeric model. -/
theorem decodePairs_pairs (left : List α) (right : List β)
    (leftKey : α → UInt64) (rightKey : β → UInt64)
    (finish : α → β → Option γ) (label : String) (limit : Nat) :
    decodePairs left.toArray right.toArray finish
      ({ left := left.toArray.map leftKey, right := right.toArray.map rightKey,
         label, maxPairs := limit } : Job).pairs =
      left.flatMap (fun l => right.filterMap (fun r =>
        if leftKey l == rightKey r then finish l r else none)) := by
  unfold decodePairs Job.pairs
  simp only [Array.toList_map, List.zipIdx_map,
    List.flatMap_map, List.filterMap_map, List.filterMap_flatMap,
    List.filterMap_filterMap, Function.comp_def, Prod.map, id_eq]
  calc
    _ = left.zipIdx.flatMap (fun li => right.zipIdx.filterMap (fun ri =>
      if leftKey li.1 == rightKey ri.1 then finish li.1 ri.1 else none)) := by
      apply flatMap_congr_mem
      intro li hli
      apply filterMap_congr_mem
      intro ri hri
      have hl := List.mem_zipIdx_iff_getElem?.mp hli
      have hr := List.mem_zipIdx_iff_getElem?.mp hri
      split <;> simp_all
    _ = left.zipIdx.flatMap (fun li => right.filterMap (fun r =>
        if leftKey li.1 == rightKey r then finish li.1 r else none)) := by
      apply flatMap_congr_mem
      intro li _
      exact zipIdx_filterMap_fst right (fun r =>
        if leftKey li.1 == rightKey r then finish li.1 r else none)
    _ = _ := zipIdx_flatMap_fst left (fun l => right.filterMap (fun r =>
        if leftKey l == rightKey r then finish l r else none))

/-- Refinement theorem. Says: hash filtering loses no result when every
accepted payload pair has equal keys. Hash injectivity is unnecessary.
Does not say: that adversarial collisions are inexpensive. -/
theorem candidate_filter_exact (left : List α) (right : List β)
    (leftKey : α → UInt64) (rightKey : β → UInt64)
    (finish : α → β → Option γ)
    (hkey : ∀ l ∈ left, ∀ r ∈ right, ∀ value,
      finish l r = some value → leftKey l = rightKey r) :
    left.flatMap (fun l => right.filterMap (fun r =>
      if leftKey l == rightKey r then finish l r else none)) =
    left.flatMap (fun l => right.filterMap (finish l)) := by
  apply flatMap_congr_mem
  intro l hl
  apply filterMap_congr_mem
  intro r hr
  cases hf : finish l r with
  | none => simp
  | some value => simp [hkey l hl r hr value hf]

def candidateJoin (cfg : Config) (label : String)
    (left : List α) (right : List β) (leftKey : α → UInt64) (rightKey : β → UInt64)
    (finish : α → β → Option Binding) (fallback : Unit → SolutionSeq) : Plan SolutionSeq :=
  if cfg.admits left.length right.length then
    let ls := left.toArray
    let rs := right.toArray
    let job : Job := { left := ls.map leftKey, right := rs.map rightKey, label := label, maxPairs := cfg.maxOutputPairs }
    .dispatch job fun
      | none => .done (fallback ())
      | some pairs => .done (decodePairs ls rs finish pairs)
  else .done (fallback ())

/-- Refinement theorem. Says: both a numeric device reply and CPU fallback
give the same ordered payload join. Does not say: that the device law is
checked by a second CPU join at runtime. -/
theorem candidateJoin_sound (cfg : Config) (label : String)
    (left : List α) (right : List β) (leftKey : α → UInt64) (rightKey : β → UInt64)
    (finish : α → β → Option Binding) (fallback : Unit → SolutionSeq)
    (hkey : ∀ l ∈ left, ∀ r ∈ right, ∀ value,
      finish l r = some value → leftKey l = rightKey r)
    (hf : fallback () = left.flatMap (fun l => right.filterMap (finish l))) :
    (candidateJoin cfg label left right leftKey rightKey finish fallback).Sound
      (fallback ()) := by
  unfold candidateJoin
  split
  · dsimp only
    intro reply hr
    cases reply with
    | none => rfl
    | some pairs =>
        change decodePairs _ _ _ pairs = fallback ()
        change pairs = _ at hr
        rw [hr, decodePairs_pairs, candidate_filter_exact left right leftKey rightKey finish hkey]
        exact hf.symm
  · rfl

def tripleMask (tp : TriplePattern) (mu : Binding) : TpMask :=
  { s := (tp.s.resolveKey mu).isSome,
    p := (tp.p.resolveKey mu).isSome,
    o := (tp.o.resolveKey mu).isSome }

/-- Says: a constant subject probe is binding-independent. Does not say:
that a triple-term subject pattern matches any RDF data subject. -/
private theorem constant_subject_key (ps : PatternSubject) (mu : Binding) :
    maskedKey (ps.resolveKey Binding.empty).isSome (ps.resolveKey mu) =
      maskedKey (ps.resolveKey Binding.empty).isSome (ps.resolveKey Binding.empty) := by
  cases ps <;> simp [PatternSubject.resolveKey, Binding.empty, Binding.lookup, maskedKey]

/-- Says: a constant term probe is binding-independent. Does not say:
that unresolved triple-term patterns can be encoded as constants. -/
private theorem constant_term_key (pt : PatternTerm) (mu : Binding) :
    maskedKey (pt.resolveKey Binding.empty).isSome (pt.resolveKey mu) =
      maskedKey (pt.resolveKey Binding.empty).isSome (pt.resolveKey Binding.empty) := by
  cases pt <;> simp [PatternTerm.resolveKey, Binding.empty, Binding.lookup, maskedKey]

/-- Refinement lemma. Says: the constant-only probe is independent of the
current solution. Does not say: that a variable has an RDF value when unbound. -/
theorem constant_probe_key (tp : TriplePattern) (mu : Binding) :
    probeKey? (tripleMask tp Binding.empty) tp mu =
      probeKey? (tripleMask tp Binding.empty) tp Binding.empty := by
  simp only [probeKey?, tripleMask, constant_subject_key, constant_term_key]

/-- Select constants before encoding device keys. The seven lazy indexes
are shared by all steps of this BGP; each bucket retains graph order.
Variable constraints remain in the full key and the final `tpMatch`. -/
def constantCandidates (ix : ExistsIndex) (tp : TriplePattern) : Graph :=
  let mask := tripleMask tp Binding.empty
  match ix.table.find? (fun entry => entry.1 == mask) with
  | none => ix.graph
  | some entry =>
      match probeKey? mask tp Binding.empty with
      | none => ix.graph
      | some key => bucketOf entry.2.get key

/-- Refinement theorem. Says: constant-index selection retains, in order,
every triple accepted under any solution binding. Does not say: that the
bucket alone checks repeated variables or row-dependent constraints. -/
theorem constantCandidates_exact (g : Graph) (tp : TriplePattern) (mu : Binding) :
    (constantCandidates (ExistsIndex.ofGraph g) tp).filterMap (fun t => tpMatch tp t mu) =
      g.filterMap (fun t => tpMatch tp t mu) := by
  unfold constantCandidates
  dsimp only
  split
  · rfl
  · rename_i entry hentry
    have hmem := List.mem_of_find?_eq_some hentry
    have hpred := List.find?_some hentry
    simp only [ExistsIndex.ofGraph, List.mem_map] at hmem
    obtain ⟨mask, _, hm⟩ := hmem
    subst hm
    have heq : mask = tripleMask tp Binding.empty := by
      simpa only [beq_iff_eq] using hpred
    subst mask
    split
    · rfl
    · rename_i key hkey
      have hprobe : probeKey? (tripleMask tp Binding.empty) tp mu = some key := by
        rw [constant_probe_key]; exact hkey
      simpa only [evalTPIdx, hprobe, evalTP, Thunk.get] using
        evalTPIdx_eq (tripleMask tp Binding.empty) g tp mu

/-- One general triple-pattern extension. Missing probe keys take the CPU
path; every true match has the same canonical key (`tpMatch_key`). -/
def bgpStep (cfg : Config) (ix : ExistsIndex) (tp : TriplePattern)
    (rows : SolutionSeq) : Plan SolutionSeq :=
  match rows with
  | [] => .done []
  | mu :: _ =>
      let mask := tripleMask tp mu
      let g := constantCandidates ix tp
      if (mask.s || mask.p || mask.o) && rows.all (fun row => (probeKey? mask tp row).isSome) then
        candidateJoin cfg "sparql.bgp.extend" rows g
          (fun row => hash ((probeKey? mask tp row).getD []))
          (fun triple => hash (tripleKey mask triple))
          (fun row triple => tpMatch tp triple row)
          (fun _ => evalBgpStepIdx tp g rows)
      else .done (evalBgpStepIdx tp g rows)

/-- Refinement theorem. Says: candidate generation and exact `tpMatch`
preserve one indexed BGP extension, including duplicate occurrences and
binding layout. Does not say: that numeric hash equality is RDF equality. -/
theorem bgpStep_sound (cfg : Config) (g : Graph) (tp : TriplePattern)
    (rows : SolutionSeq) :
    (bgpStep cfg (ExistsIndex.ofGraph g) tp rows).Sound (evalBgpStepIdx tp g rows) := by
  have hf : evalBgpStepIdx tp (constantCandidates (ExistsIndex.ofGraph g) tp) rows =
      evalBgpStepIdx tp g rows := by
    simp only [evalBgpStepIdx_eq]
    apply flatMap_congr_mem
    intro mu _
    exact constantCandidates_exact g tp mu
  rw [← hf]
  cases rows with
  | nil => rfl
  | cons mu rest =>
      simp only [bgpStep]
      split
      · rename_i hadmit
        apply candidateJoin_sound
        · intro row hrow triple _ value hmatch
          have hall : (mu :: rest).all (fun row =>
              (probeKey? (tripleMask tp mu) tp row).isSome) = true :=
            (Bool.and_eq_true_iff.mp hadmit).2
          have hsome := List.all_eq_true.mp hall row hrow
          cases hk : probeKey? (tripleMask tp mu) tp row with
          | none => simp [hk] at hsome
          | some key =>
              have heq := tpMatch_key hmatch hk
              simp only [Option.getD_some]
              exact congrArg hash heq.symm
        · exact evalBgpStepIdx_eq tp (constantCandidates (ExistsIndex.ofGraph g) tp) (mu :: rest)
      · rfl

def bgpRows (cfg : Config) (ix : ExistsIndex) : Bgp → SolutionSeq → Plan SolutionSeq
  | [], rows => .done rows
  | tp :: rest, rows => (bgpStep cfg ix tp rows).bind (bgpRows cfg ix rest)

/-- Refinement theorem. Says: every combination of CPU and GPU BGP steps
has the exact reference solution list. Does not say: that triple-pattern
reordering preserves this order; this evaluator does not reorder them. -/
theorem bgpRows_sound (cfg : Config) (g : Graph) (b : Bgp) (rows : SolutionSeq) :
    (bgpRows cfg (ExistsIndex.ofGraph g) b rows).Sound (rows.flatMap (evalBgpFrom g b)) := by
  induction b generalizing rows with
  | nil => simp only [bgpRows, evalBgpFrom, List.flatMap_singleton', Plan.Sound]
  | cons tp rest ih =>
      apply Plan.Sound.bind (bgpStep_sound cfg g tp rows)
      simpa only [evalBgpStepIdx_eq, List.flatMap_assoc, evalBgpFrom] using
        ih (evalBgpStepIdx tp g rows)

def mergeCompatible (l r : Binding) : Option Binding :=
  if l.compatible r then some (l.merge r) else none

/-- General SPARQL inner join. The common key uses only variables bound in
every row, so OPTIONAL/UNDEF never loses wildcard-compatible solutions. -/
def innerJoin (cfg : Config) (left right : SolutionSeq) : Plan SolutionSeq :=
  let vars := joinKeyVars left right
  if !vars.isEmpty && left.all (fun row => (Binding.hashKey? vars row).isSome) &&
      right.all (fun row => (Binding.hashKey? vars row).isSome) then
    candidateJoin cfg "sparql.join" left right
      (fun row => hash ((Binding.hashKey? vars row).getD []))
      (fun row => hash ((Binding.hashKey? vars row).getD []))
      mergeCompatible (fun _ => hashJoin left right)
  else .done (hashJoin left right)

/-- Refinement theorem. Says: a general candidate join preserves the
existing SPARQL hash join as an ordered list. Does not say: that a missing
variable is equal to a numeric key; it takes the reference fallback. -/
theorem innerJoin_sound (cfg : Config) (left right : SolutionSeq) :
    (innerJoin cfg left right).Sound (hashJoin left right) := by
  simp only [innerJoin]
  split
  · rename_i hadmit
    apply candidateJoin_sound
    · intro l hl r hr value hmerge
      have hlall : left.all (fun row =>
          (Binding.hashKey? (joinKeyVars left right) row).isSome) = true := by
        simp only [Bool.and_eq_true] at hadmit
        exact hadmit.1.2
      have hrall : right.all (fun row =>
          (Binding.hashKey? (joinKeyVars left right) row).isSome) = true := by
        simp only [Bool.and_eq_true] at hadmit
        exact hadmit.2
      have hls := List.all_eq_true.mp hlall l hl
      have hrs := List.all_eq_true.mp hrall r hr
      have hc : l.compatible r = true := by
        unfold mergeCompatible at hmerge
        split at hmerge
        · assumption
        · cases hmerge
      cases hkl : Binding.hashKey? (joinKeyVars left right) l with
      | none => simp [hkl] at hls
      | some kl =>
          cases hkr : Binding.hashKey? (joinKeyVars left right) r with
          | none => simp [hkr] at hrs
          | some kr =>
              have heq := Binding.hashKey?_eq_of_compatible _ hc hkl hkr
              simp [heq]
    · exact hashJoin_eq_join left right
  · rfl

/-- Recursion follows the existing lowered algebra. Correlated SERVICE
joins and LATERAL retain the complete reference operation. -/
def pattern (cfg : Config) (ds : Dataset) (active : Graph) :
    GraphPattern → Plan SolutionSeq
  | .bgp b => bgpRows cfg (ExistsIndex.ofGraph active) b [Binding.empty]
  | .join l r =>
      if l.isServiceVar || r.isServiceVar then
        .done ((GraphPattern.join l r).evalIn ds active)
      else
        (pattern cfg ds active l).bind fun ls =>
          (pattern cfg ds active r).bind fun rs => innerJoin cfg ls rs
  | .leftJoin l r cond _ =>
      (pattern cfg ds active l).bind fun ls =>
        (pattern cfg ds active r).map fun rs => hashLeftJoin ls rs (cond active)
  | .filter cond p _ => (pattern cfg ds active p).map (filterSeq (cond active))
  | .union l r =>
      (pattern cfg ds active l).bind fun ls =>
        (pattern cfg ds active r).map (SPARQL.union ls)
  | .minus l r =>
      (pattern cfg ds active l).bind fun ls =>
        (pattern cfg ds active r).map (hashMinus ls)
  | .graph name p =>
      match name with
      | .iri i => match ds.lookupNamedIri i.val with
          | some g => pattern cfg ds g p
          | none => .done []
      | .var v => Plan.collect ds.named fun ng =>
          (pattern cfg ds ng.graph p).map (fun rows =>
            rows.filterMap (fun mu => mu.bindIfCompatible v ng.name.toTerm))
      | _ => pattern cfg ds active p
  | .bind binder v p _ =>
      (pattern cfg ds active p).map (fun rows => bindRowsFresh binder active v rows 0)
  | .modified post p _ => (pattern cfg ds active p).map (post active)
  | p => .done (p.evalIn ds active)

/-- Refinement theorem. Says: every supported algebra context preserves the
complete reference WHERE sequence under valid numeric replies, including
active named graphs and solution multiplicity. Does not say: that SERVICE
or correlated evaluation is moved across an effect boundary. -/
theorem pattern_sound (cfg : Config) (ds : Dataset) (active : Graph)
    (p : GraphPattern) :
    (pattern cfg ds active p).Sound (p.evalIn ds active) := by
  induction p generalizing active with
  | bgp b =>
      change (bgpRows cfg (ExistsIndex.ofGraph active) b [Binding.empty]).Sound (evalBgpIdx b active)
      rw [evalBgpIdx_eq_evalBgp]
      simpa only [evalBgp, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
        bgpRows_sound cfg active b [Binding.empty]
  | join l r ihl ihr =>
      rw [pattern]
      split
      · rfl
      · rename_i h
        have hplain : (l.isServiceVar || r.isServiceVar) = false := by
          cases hb : (l.isServiceVar || r.isServiceVar) <;> simp_all
        have hlr := Bool.or_eq_false_iff.mp hplain
        rw [evalIn_join_plain hlr.1 hlr.2]
        exact (ihl active).bind ((ihr active).bind (innerJoin_sound cfg _ _))
  | leftJoin l r cond failure ihl ihr =>
      exact (ihl active).bind ((ihr active).map (fun rs => hashLeftJoin _ rs (cond active)))
  | filter cond p failure ih => exact (ih active).map (filterSeq (cond active))
  | union l r ihl ihr => exact (ihl active).bind ((ihr active).map (SPARQL.union _))
  | minus l r ihl ihr => exact (ihl active).bind ((ihr active).map (hashMinus _))
  | graph name p ih =>
      cases name with
      | iri i =>
          cases hn : ds.lookupNamedIri i.val with
          | none => simp only [pattern, hn, GraphPattern.evalIn, Plan.Sound]
          | some g => simpa only [pattern, hn, GraphPattern.evalIn] using ih g
      | var v =>
          apply Plan.collect_sound
          intro ng _
          exact (ih ng.graph).map (fun rows =>
            rows.filterMap (fun mu => mu.bindIfCompatible v ng.name.toTerm))
      | bnode b => exact ih active
      | literal l => exact ih active
      | tripleTerm s p o => exact ih active
  | bind binder v p failure ih =>
      exact (ih active).map (fun rows => bindRowsFresh binder active v rows 0)
  | modified post p failure ih => exact (ih active).map (post active)
  | lateral l r ihl ihr => rfl
  | values vars rows => rfl
  | service endpoint remote silent p ih => rfl
  | serviceVar v resolve silent p ih => rfl
  | propertyPath s path o => rfl
  | empty => rfl

/-- Start from the real query AST, applying FROM and the existing blank-node
rewrite. Every query form uses its existing modifier and rendering semantics.
The caller checks `Query.serviceFailure` before starting, as the shipping op
does, and keeps this environment and dataset immutable until completion. -/
def begin (cfg : Config) (env : EvalEnv) (ds : Dataset) (q : Query) : Plan Answer :=
  let (ds', active) := applyDataset q.dataset ds ds.default
  let env := { env with dataset := some ds' }
  let wherePlan := fun _ : Unit => pattern cfg ds' active (q.pattern.rewriteBnodes.lower env)
  match q.form with
  | .select _ => (wherePlan ()).map (fun rows => .select q.projectedVars (selectPost env active q rows))
  | .ask => (wherePlan ()).map (fun rows => .ask (formHasSolution env active q rows))
  | .construct template => (wherePlan ()).map fun rows =>
      .graph ((instantiateSolutions template (formSolutions env active q rows) 0).foldl
        (fun g t => g.add t) Graph.empty)
  | .describe targets =>
      if describeNeedsSolutions targets then
        (wherePlan ()).map fun rows =>
          .graph (Graph.cbd active (describeRoots targets (formSolutions env active q rows)))
      else .done (.graph (Graph.cbd active (describeRoots targets [])))

/-- End-to-end refinement theorem. Says: every mixture of successful
numeric joins and CPU fallback produces the existing reference SPARQL
answer, with SELECT/ASK/CONSTRUCT/DESCRIBE modifiers unchanged. Does not
say: that the physical backend assumption is discharged by this theorem. -/
theorem begin_sound (cfg : Config) (env : EvalEnv) (ds : Dataset) (q : Query) :
    (begin cfg env ds q).Sound
      (referenceAnswer {env, ds, backend := none, query := q}) := by
  cases hds : applyDataset q.dataset ds ds.default with
  | mk selected active =>
      let frozen := {env with dataset := some selected}
      have hp := pattern_sound cfg selected active (q.pattern.rewriteBnodes.lower frozen)
      cases hform : q.form with
      | select sel =>
          simpa only [begin, referenceAnswer, evalSelect, hds, hform] using
            hp.map (fun rows => Answer.select q.projectedVars (selectPost frozen active q rows))
      | ask =>
          simpa only [begin, referenceAnswer, evalAsk, hds, hform] using
            hp.map (fun rows => Answer.ask (formHasSolution frozen active q rows))
      | construct template =>
          simpa only [begin, referenceAnswer, evalConstruct, hds, hform] using
            hp.map (fun rows => Answer.graph
              ((instantiateSolutions template (formSolutions frozen active q rows) 0).foldl
                (fun g t => g.add t) Graph.empty))
      | describe targets =>
          cases hneed : describeNeedsSolutions targets with
          | false =>
              simp only [begin, referenceAnswer, evalDescribe, hds, hform, hneed,
                Bool.false_eq_true, ↓reduceIte, Plan.Sound]
          | true =>
              simpa only [begin, referenceAnswer, evalDescribe, hds, hform, hneed, ↓reduceIte] using
                hp.map (fun rows => Answer.graph
                  (Graph.cbd active (describeRoots targets (formSolutions frozen active q rows))))

#print axioms decodePairs_pairs
#print axioms candidateJoin_sound
#print axioms bgpStep_sound
#print axioms innerJoin_sound
#print axioms pattern_sound
#print axioms begin_sound

end L4Factoidal.SPARQL.GpuQuery
