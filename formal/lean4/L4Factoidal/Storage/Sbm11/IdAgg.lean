/-
L4Factoidal.Storage.Sbm11.IdAgg — grouped aggregates on term ids
(https://github.com/danbri/factoidal/issues/825; record
docs/designissues/2026-10-12-sbm11-stage4.md section 16).

A SELECT with GROUP BY variables (or none) and items that are variables or
non-DISTINCT COUNT, SUM, MIN, MAX and AVG of a variable (`AggStream.aggPlan?`)
used to run its WHERE clause on ids, decode every variable of every solution
into a `Binding` (326,365 rows for DBpedia d19), and give the bindings to
`selectPost`: 1.9 s of decoding and 1.1 s of grouping and aggregates of 3.2 s
(gdb and perf samples in the record). `aggregateM` instead reads the id table
once:

  * Rows are grouped by the ids of the GROUP BY columns, in the order of first
    appearance. A group column is admitted only when every id in it is a blank
    node, an IRI, an inline integer or an inline boolean (tags 1, 2, 4, 5):
    for those ids, equality of ids is equality of terms, and for the terms
    `erEqual` (the key test of `groupSolutionsFast`) is term identity. Any
    other id, an unbound variable, or a missing column in a group column hands
    the query to the generic path (`decodeRowsM`, `selectPost`).
  * Each distinct id met in an aggregate column or in a representative row is
    decoded once (`terms`, a `Cache`), and the `Summary` of the value of an
    aggregate argument once more (`sums`); `COUNT(?x)` decodes nothing: a bound
    variable is never the type error (`AggStream.varView_ne_error`).
  * The accumulators of `AggStream` are stepped in row order. Their final
    values are `evalAggregate`'s (`AggStream.evalAggregate_stream`,
    `evalAggregate_star`).
  * The representative row of a group is its first row, decoded as
    `decodeRowsM` decodes it (every variable of the WHERE clause; the ids
    already decoded for an aggregate come from `terms`).

`IdQuery.runPostM` then builds the rows of the groups with `groupedRow` and
runs the shared tail `groupedTail`, so ORDER BY, projection, DISTINCT, OFFSET
and LIMIT are the reference's own code. `AggStream.selectPost_aggPlan` is the
specification the result must equal. That the groups, representatives and
streams built here are those of `groupWhere` on the decoded rows (lemma L5k of the end-to-end record) is
NOT proved; `IdAggTests` compares the two on sample tables, and the gate
queries and the W3C census compare them on the store.

The cache is `Cache`: `Cache.getM` returns the value of the function at the
key and a cache that still holds only values of the function (`Cache.Valid`),
proved for the pure instance (`getM_id_fst`, `getM_id_valid`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Qlvr.Bgp
import L4Factoidal.Storage.Sbm11.OptJoin
import L4Factoidal.SPARQL.AggStream
import Std.Data.HashMap

namespace L4Factoidal.Storage.Sbm11.IdAgg

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.AggStream
open L4Factoidal.Qlvr (Table)

/-! ## A cache of a function's values -/

/-- The values of a function at the keys asked so far. -/
structure Cache (α β : Type) [BEq α] [Hashable α] where
  map : Std.HashMap α β := {}

namespace Cache

variable {α β : Type} [BEq α] [Hashable α]

/-- The value at `k`: from the cache, else computed by `f` and kept. -/
def getM {m : Type → Type} [Monad m] (c : Cache α β) (f : α → m β) (k : α) :
    m (β × Cache α β) := do
  match c.map.get? k with
  | some v => pure (v, c)
  | none =>
    let v ← f k
    pure (v, { c with map := c.map.insert k v })

/-- `getM` for a pure function. -/
def getPure (c : Cache α β) (f : α → β) (k : α) : β × Cache α β :=
  match c.map.get? k with
  | some v => (v, c)
  | none => (f k, { c with map := c.map.insert k (f k) })

theorem getM_id (c : Cache α β) (f : α → β) (k : α) :
    c.getM (m := Id) (fun k => (f k : Id β)) k = c.getPure f k := by
  unfold getM getPure
  cases c.map.get? k <;> rfl

/-- Every value held is the function's value at its key. -/
def Valid (f : α → β) (c : Cache α β) : Prop :=
  ∀ k v, c.map.get? k = some v → v = f k

theorem valid_empty (f : α → β) : Valid f ({} : Cache α β) := by
  intro k v h
  simp [Std.HashMap.get?_eq_getElem?] at h

/-- For a pure function the answer is the function's value. -/
theorem getPure_fst (f : α → β) (c : Cache α β) (hv : Valid f c) (k : α) :
    (c.getPure f k).1 = f k := by
  unfold getPure
  cases h : c.map.get? k with
  | some v => exact hv k v h
  | none => rfl

/-- The cache after a lookup still holds only values of the function. -/
theorem getPure_valid [LawfulBEq α] [LawfulHashable α] (f : α → β) (c : Cache α β)
    (hv : Valid f c) (k : α) : Valid f (c.getPure f k).2 := by
  unfold getPure
  cases h : c.map.get? k with
  | some v => exact hv
  | none =>
    intro k' v' h'
    simp only [Std.HashMap.get?_insert] at h'
    split at h'
    · rename_i hk
      obtain rfl := Option.some.inj h'
      have : k = k' := eq_of_beq (by simpa using hk)
      subst this
      rfl
    · exact hv k' v' h'

/-- The pure lookups of a list of keys, threading the cache. -/
def getPureList (f : α → β) : List α → Cache α β → List β × Cache α β
  | [], c => ([], c)
  | k :: ks, c =>
    let r := c.getPure f k
    let rest := getPureList f ks r.2
    (r.1 :: rest.1, rest.2)

/-- Any sequence of lookups returns the values of the function at the keys,
whatever the order and the repeats, and leaves the cache holding only such
values: the cached decode equals the uncached decode. -/
theorem getPure_list [LawfulBEq α] [LawfulHashable α] (f : α → β) :
    ∀ (ks : List α) (c : Cache α β), Valid f c →
      (getPureList f ks c).1 = ks.map f ∧ Valid f (getPureList f ks c).2
  | [], c, hv => ⟨rfl, hv⟩
  | k :: ks, c, hv => by
    have h1 := getPure_fst f c hv k
    have h2 := getPure_valid f c hv k
    obtain ⟨e1, e2⟩ := getPure_list f ks (c.getPure f k).2 h2
    refine ⟨?_, ?_⟩
    · simp [getPureList, h1, e1]
    · simpa [getPureList] using e2

end Cache

/-! ## Group keys and columns -/

/-- The tag of a term id. -/
@[inline] def idTag (x : UInt64) : Nat := (x >>> 60).toNat

/-- A group-key id: a blank node, an IRI, an inline integer or an inline
boolean. For these two ids are equal exactly when the terms are, and
`erEqual` of two such terms is term identity. (A dictionary literal, tag 3,
may be a directional literal, which `literalOrder` does not tell apart from
the same literal in the other direction; a triple term, tag 9, has such a
literal inside it. They take the generic path.) -/
@[inline] def keyIdOk (x : UInt64) : Bool :=
  let g := idTag x
  g == 1 || g == 2 || g == 4 || g == 5

instance : Inhabited AggregateFn := ⟨.count⟩

/-- Where an aggregate reads its argument. -/
inductive ArgCol where
  /-- `COUNT(*)`: every row -/
  | star
  /-- a variable no column holds: unbound in every row -/
  | absent
  | col (c : Nat)

instance : Inhabited ArgCol := ⟨.star⟩

def argColOf (t : Table) : Option VarName → ArgCol
  | none => .star
  | some w => match t.idx w with
    | some c => .col c
    | none => .absent

/-! ## The pass -/

/-- What the pass computes. -/
structure Result where
  /-- the representative row of each group (its first row, decoded) -/
  reps : Array Binding
  /-- the value of each aggregate item of each group, in item order -/
  vals : Array (Array EvalResult)
  /-- the distinct ids decoded, for aggregate arguments and representative rows -/
  decoded : Nat
  /-- the values bound in the representative rows, summed over the groups -/
  repValues : Nat

/-- The row `i` of the table as a solution mapping, as `decodeRowsM` makes it:
the variables in column order, an unbound one left out. Each id is decoded once:
`terms` holds the terms decoded so far. -/
def rowBinding {m : Type → Type} [Monad m] (termOf : UInt64 → ExceptT String m Term)
    (t : Table) (i : Nat) (terms : Cache UInt64 Term) :
    ExceptT String m (Binding × Cache UInt64 Term) := do
  let mut mu : Array (String × Term) := Array.mkEmpty t.vars.size
  let mut terms := terms
  for c in [0:t.vars.size] do
    let x := t.at c i
    if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
      let (tm, terms') ← terms.getM termOf x
      terms := terms'
      mu := mu.push (t.vars[c]!, tm)
  return (mu.toList, terms)

/-- Group the rows of `t` and aggregate; `none` when the plan does not apply to
this table (a group column that is missing, unbound somewhere, or holds an id
that is not a blank node, an IRI, an inline integer or an inline boolean). -/
def aggregateM {m : Type → Type} [Monad m] (termOf : UInt64 → ExceptT String m Term)
    (t : Table) (p : AggPlan) : ExceptT String m (Option Result) := do
  match p.groupVars.mapM (fun v => t.idx v) with
  | none => return none
  | some gl =>
    let gcols := gl.toArray
    for c in gcols do
      for i in [0:t.rows] do
        if !keyIdOk (t.at c i) then return none
    let specs := p.specs.toArray
    let n := specs.size
    let argCols : Array ArgCol := specs.map fun sp => argColOf t sp.2
    let inits : Array AggAcc := specs.map fun sp => AggAcc.init sp.1
    -- groups: the first row of each (`none`: the empty group of an implicit
    -- grouping over no rows), the accumulators, group-major
    let mut first : Array (Option Nat) :=
      if p.implicit then #[if t.rows > 0 then some 0 else none] else #[]
    let mut accs : Array AggAcc := if p.implicit then inits else #[]
    -- the specs that read no value (COUNT star, COUNT of a variable, an absent
    -- variable) and, for the others, the distinct argument columns with the
    -- specs that read each: one summary lookup per row and column
    let mut simple : Array Nat := #[]
    let mut byCol : Array (Nat × Array Nat) := #[]
    for k in [0:n] do
      match argCols[k]! with
      | .star => simple := simple.push k
      | .absent => pure ()
      | .col c =>
        if specs[k]!.1 == .count then simple := simple.push k
        else
          match byCol.findIdx? (fun e => e.1 == c) with
          | some j => byCol := byCol.modify j fun e => (e.1, e.2.push k)
          | none => byCol := byCol.push (c, #[k])
    let mut index1 : Std.HashMap UInt64 Nat := {}
    let mut index : Std.HashMap (List UInt64) Nat := {}
    let mut terms : Cache UInt64 Term := {}
    let mut sums : Cache UInt64 Summary := {}
    for i in [0:t.rows] do
      let mut gi := 0
      if !p.implicit then
        if gcols.size == 1 then
          -- one group column: the id is the key
          let key := t.at gcols[0]! i
          match index1.get? key with
          | some g => gi := g
          | none =>
            gi := first.size
            index1 := index1.insert key gi
            first := first.push (some i)
            accs := accs ++ inits
        else
          let key := gcols.toList.map fun c => t.at c i
          match index.get? key with
          | some g => gi := g
          | none =>
            gi := first.size
            index := index.insert key gi
            first := first.push (some i)
            accs := accs ++ inits
      for k in simple do
        match argCols[k]! with
        | .col c =>
          -- COUNT of a variable: a bound variable is never the type error, no decoding
          if t.at c i != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
            accs := accs.modify (gi * n + k) AggAcc.stepCount
        | _ => accs := accs.modify (gi * n + k) AggAcc.stepCount
      for e in byCol do
        let x := t.at e.1 i
        if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
          let s ← match sums.map.get? x with
            | some s => pure s
            | none => do
              let (tm, terms') ← terms.getM termOf x
              terms := terms'
              let s := Summary.of (varView tm)
              sums := { sums with map := sums.map.insert x s }
              pure s
          for k in e.2 do
            accs := accs.modify (gi * n + k) fun a => AggAcc.step specs[k]!.1 a s
    let mut reps : Array Binding := Array.mkEmpty first.size
    let mut vals : Array (Array EvalResult) := Array.mkEmpty first.size
    let mut repValues := 0
    for g in [0:first.size] do
      let rep ← match first[g]! with
        | some i => do
          let (b, terms') ← rowBinding termOf t i terms
          terms := terms'
          pure b
        | none => pure []
      repValues := repValues + rep.length
      reps := reps.push rep
      let mut row : Array EvalResult := Array.mkEmpty n
      for k in [0:n] do
        row := row.push (AggAcc.finish specs[k]!.1 accs[g * n + k]!)
      vals := vals.push row
    return some { reps, vals, decoded := terms.map.size, repValues }

#print axioms Cache.getM_id
#print axioms Cache.valid_empty
#print axioms Cache.getPure_fst
#print axioms Cache.getPure_valid
#print axioms Cache.getPure_list

end L4Factoidal.Storage.Sbm11.IdAgg
