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
import L4Factoidal.Storage.Sbm11.TermIdTheorems
import L4Factoidal.XSD.IntegerLexTheorems
import Std.Data.HashMap

namespace L4Factoidal.Storage.Sbm11.IdAgg

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.AggStream
open L4Factoidal.Qlvr (Table)

/-! ## A term id as a hash key -/

/-- A term id as a hash-map key. `Std.HashMap` takes the bucket from the low bits
of the hash, and the hash of a `UInt64` is the number itself: the ids of one
dictionary (a tag in the top bits, an index below it) that differ in their middle
bits share buckets. `Id64` hashes the id times a 64-bit odd constant (a
bijection of `UInt64`) with its high half folded onto its low half, so that every
bit of the id reaches the low bits. On d19 the lookups of the group key and of the
argument id were 15 percent of the time before and the change took 15 to 30 ms
off the warm time (interleaved runs, benchmark record, issue 862). Equality is
equality of ids. `Id64` is `UInt64` (no allocation per key); `ofU` and `val` are
the identity. -/
def Id64 : Type := UInt64

namespace Id64

/-- The key of an id (no allocation: `Id64` is `UInt64`). -/
@[inline] def ofU (x : UInt64) : Id64 := x

/-- The id of a key. -/
@[inline] def val (k : Id64) : UInt64 := k

end Id64

instance : BEq Id64 := inferInstanceAs (BEq UInt64)

instance : LawfulBEq Id64 := inferInstanceAs (LawfulBEq UInt64)

instance : Hashable Id64 := ⟨fun k => let h := k.val * 0x9E3779B97F4A7C15; h ^^^ (h >>> 32)⟩

instance : LawfulHashable Id64 where
  hash_eq := by
    intro a b h
    have e : a = b := eq_of_beq h
    subst e
    simp

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

/-- A value of the function stored at its own key keeps the cache valid: the
summary table of pass 2 of `aggregateM` is filled one id at a time by `insert`
of the function's value, in the order the misses occur. -/
theorem insert_valid [LawfulBEq α] [LawfulHashable α] (f : α → β) (c : Cache α β)
    (hv : Valid f c) (k : α) : Valid f { c with map := c.map.insert k (f k) } := by
  intro k' v' h'
  simp only [Std.HashMap.get?_insert] at h'
  split at h'
  · rename_i hk
    obtain rfl := Option.some.inj h'
    have : k = k' := eq_of_beq (by simpa using hk)
    subst this
    rfl
  · exact hv k' v' h'

/-- On a valid cache a hit returns the function's value. Together with
`insert_valid` this is the equality that lets pass 2 of `aggregateM` stop at an
id it has not seen, decode it, and resume at the same row: whichever way an id
is met (hit, or miss then insert) the step reads `f k`, so the steps equal those
of a pass that recomputes `f k` at every row. -/
theorem hit_eq (f : α → β) (c : Cache α β) (hv : Valid f c) (k : α) (v : β)
    (h : c.map.get? k = some v) : v = f k := hv k v h

/-- Filling a cache with the values at a list of keys, in any order and with
repeats, leaves it valid. -/
theorem fill_valid [LawfulBEq α] [LawfulHashable α] (f : α → β) :
    ∀ (ks : List α) (c : Cache α β), Valid f c →
      Valid f (ks.foldl (fun c k => { c with map := c.map.insert k (f k) }) c)
  | [], _, hv => hv
  | k :: ks, c, hv => fill_valid f ks _ (insert_valid f c hv k)

end Cache

/-- The summary of the value of an id, for a pure decoder `termOf`: what the table
of pass 2 holds at that id. -/
def sumOf (termOf : UInt64 → Term) (k : Id64) : Summary := Summary.of (varView (termOf k.val))

/-- The summary table of `aggregateM` over a pure decoder is valid for `sumOf`:
every entry is the summary of the decoded value of its id, so a step with a cached
summary is the step with a recomputed one. -/
theorem sums_fill_valid (termOf : UInt64 → Term) (ks : List Id64) :
    Cache.Valid (sumOf termOf)
      (ks.foldl (fun c k => { c with map := c.map.insert k (sumOf termOf k) })
        ({} : Cache Id64 Summary)) :=
  Cache.fill_valid _ ks _ (Cache.valid_empty _)

/-- The summary of a decoded argument term. A literal's datatype IRI is looked
up once per distinct IRI (`dts`, a `Cache` of `XSD.builtinOfIri?`): on DBpedia
d19 every one of the 47,473 distinct values had the same datatype, and the
lookup (a character walk over the namespace and a search of 50 names) was 7
percent of the warm time (https://github.com/danbri/factoidal/issues/862). -/
def sumCached (dts : Cache String (Option XSD.Builtin)) (tm : Term) :
    Summary × Cache String (Option XSD.Builtin) :=
  match tm with
  | .literal l =>
    let (bo, dts') := dts.getPure XSD.builtinOfIri? l.val.datatype.val
    (Summary.ofLit l bo, dts')
  | _ => (Summary.of (varView tm), dts)

/-- On a valid datatype cache, the cached summary is `Summary.of` of the value. -/
theorem sumCached_fst (dts : Cache String (Option XSD.Builtin)) (hv : Cache.Valid XSD.builtinOfIri? dts)
    (tm : Term) : (sumCached dts tm).1 = Summary.of (varView tm) := by
  cases tm with
  | literal l =>
    simp only [sumCached]
    rw [Cache.getPure_fst _ dts hv]
    exact Summary.ofLit_eq l
  | _ => rfl

/-- The datatype cache stays valid. -/
theorem sumCached_valid (dts : Cache String (Option XSD.Builtin)) (hv : Cache.Valid XSD.builtinOfIri? dts)
    (tm : Term) : Cache.Valid XSD.builtinOfIri? (sumCached dts tm).2 := by
  cases tm with
  | literal l => exact Cache.getPure_valid _ dts hv _
  | _ => exact hv

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

/-! ## Argument columns of inline integers (issue 862)

When every bound id of the one argument column is an inline integer (tag 4),
the value of the id is in its bits: `v = payload - 2^55`, the datatype is
entry `sub` of `intTypesList`. Its readings are then those of
`Summary.of` with no decoding and no parse (`summary_inlineInt`, through
`parseIntegerLex (toString v) = some v`), so SUM and AVG add `v` to an integer
sum and MIN and MAX compare two integers (`IAcc.step_abs`). Only the best id of
each group is decoded, at the end. On DBpedia d19 (326,365 rows,
`xsd:nonNegativeInteger`) this removes the summary table: the per-row hash
probe, the 47,473 decodes and summaries and their frees. -/

/-- The entry of an inline integer type with its built-in datatype, when the
type's literals are well formed (`mkLit` succeeds) and the built-in is an
integer type. -/
structure IntInfo where
  e : IntType
  b : XSD.Builtin

/-- `IntInfo` of each of the 13 inline integer types, by subtype field. -/
def intInfoOf (e : IntType) : Option IntInfo :=
  if (mkLit "0" e.iri.val none none).isSome then
    match XSD.builtinOfIri? e.iri.val with
    | some b => if (XSD.intBounds b).isSome then some ⟨e, b⟩ else none
    | none => none
  else none

def intInfos : Array (Option IntInfo) := intTypesList.toArray.map intInfoOf

/-- The value of an inline integer id whose type is in `infos` and whose value
is in the bounds of that type; `none` for any other id. -/
@[inline] def intVal? (infos : Array (Option IntInfo)) (x : UInt64) : Option Int :=
  let n := x.toNat
  if n / two60 == tagInt then
    match infos[(n / two56) % 16]? with
    | some (some i) =>
      let v : Int := ((n % two56 : Nat) : Int) - two55Int
      if i.e.admits v && XSD.inIntBounds i.b v then some v else none
    | _ => none
  else none

/-- The order of two integers as `sparqlOrder` gives it for their values. -/
@[inline] def ordInt (a b : Int) : Int := if a < b then -1 else if b < a then 1 else 0

/-- The keep test of MIN (`keepMin`) and MAX (`keepMax`). -/
def keepOf : AggregateFn → Int → Bool
  | .min => keepMin
  | _ => keepMax

/-- The state of SUM, AVG, MIN or MAX over an integer column: the integer sum
and the count, or the best value with its id. -/
inductive IAcc where
  | sum (t : Int) (c : Nat)
  | best (o : Option (Int × UInt64))

instance : Inhabited IAcc := ⟨.sum 0 0⟩

def IAcc.init : AggregateFn → IAcc
  | .min | .max => .best none
  | _ => .sum 0 0

/-- One value `v` of id `x`. -/
@[inline] def IAcc.step (fn : AggregateFn) (a : IAcc) (x : UInt64) (v : Int) : IAcc :=
  match a with
  | .sum t c => .sum (v + t) (c + 1)
  | .best none => .best (some (v, x))
  | .best (some (bv, _)) => if keepOf fn (ordInt v bv) then .best (some (v, x)) else a

/-- The accumulator of `AggStream` that an `IAcc` stands for; `dec` decodes an
id (`ofInlineCode?` for the ids met here). -/
def IAcc.abs (dec : UInt64 → Term) : IAcc → AggAcc
  | .sum t c => .num (.num t) c
  | .best none => .best none
  | .best (some (_, x)) => .best (some (Summary.of (varView (dec x))))

/-- The readings of an id: what `Summary.of` of its decoded term gives when it
is the integer `v`. -/
def ReadsInt (dec : UInt64 → Term) (x : UInt64) (v : Int) : Prop :=
  Summary.of (varView (dec x)) = ⟨varView (dec x), some (.dec (XSD.Dec.ofInt v)), true, true⟩

/-- The readings of an inline integer id, from its bits. -/
theorem summary_inlineInt (n : Nat) (h4 : n / two60 = 4) (e : IntType)
    (he : intTypesList[(n / two56) % 16]? = some e)
    (b : XSD.Builtin) (hb : XSD.builtinOfIri? e.iri.val = some b) (hib : (XSD.intBounds b).isSome = true)
    (hin : XSD.inIntBounds b (((n % two56 : Nat) : Int) - two55Int) = true)
    (t : Term) (ht : ofInlineCode? n = some t) :
    Summary.of (varView t) =
      ⟨varView t, some (.dec (XSD.Dec.ofInt (((n % two56 : Nat) : Int) - two55Int))), true, true⟩ := by
  rw [ofInlineCode?_int n h4, he] at ht
  simp only at ht
  split at ht
  · unfold mkLit at ht
    split at ht
    · dsimp only at ht
      split at ht
      · cases ht
        have hty : L4Factoidal.Fn.Numeric.isType b = true := by
          simp [L4Factoidal.Fn.Numeric.isType, hib]
        simp only [Summary.of, varView, EvalResult.numericValue?, EvalResult.isIntegerOperand,
          EvalResult.isNumericOperand, L4Factoidal.Fn.Numeric.literalValue?,
          L4Factoidal.Fn.Numeric.lexicalValue?, L4Factoidal.Fn.Comparison.numericDatatype,
          L4Factoidal.Fn.Numeric.isDatatype, hb, Option.any_some, hty, hib]
        simp only [bind, Option.bind, hty, if_true]
        rw [XSD.IntegerLexTheorems.lexicalFor_int b hib, hin]
        rfl
      · cases ht
    · cases ht
  · cases ht

/-- `mkLit` with no language tag and no direction succeeds or fails by the
datatype alone. -/
theorem mkLit_isSome_lex (a c dt : String) :
    (mkLit a dt none none).isSome = (mkLit c dt none none).isSome := by
  unfold mkLit
  split
  · rename_i h
    by_cases hP : ((⟨dt, h⟩ : WfIri) != rdfLangString && (⟨dt, h⟩ : WfIri) != rdfDirLangString) = true
    · simp [literalWf, hP]
    · simp [literalWf, hP]
  · rfl

/-- An id that `intVal?` reads as `v` decodes, and its readings are those of
the integer `v`. -/
theorem intVal?_reads (x : UInt64) (v : Int) (h : intVal? intInfos x = some v) :
    ∃ t, ofInlineCode? x.toNat = some t ∧ ReadsInt (fun y => (ofInlineCode? y.toNat).getD t) x v := by
  unfold intVal? at h
  simp only at h
  split at h
  · rename_i h4
    split at h
    · rename_i i hi
      split at h
      · rename_i hok
        cases h
        simp only [intInfos, Array.getElem?_map, List.getElem?_toArray] at hi
        cases he : intTypesList[(x.toNat / two56) % 16]? with
        | none => rw [he] at hi; cases hi
        | some e =>
          rw [he] at hi
          simp only [Option.map_some, Option.some.injEq] at hi
          unfold intInfoOf at hi
          split at hi
          · rename_i hmk
            split at hi
            · rename_i b hb
              split at hi
              · rename_i hib
                cases hi
                simp only [Bool.and_eq_true] at hok
                have h4' : x.toNat / two60 = 4 := by simpa [tagInt] using h4
                have hsome : (ofInlineCode? x.toNat).isSome = true := by
                  rw [ofInlineCode?_int _ h4', he]
                  simp only [hok.1, if_true]
                  rw [mkLit_isSome_lex _ "0"]
                  exact hmk
                obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsome
                refine ⟨t, ht, ?_⟩
                unfold ReadsInt
                simp only [ht, Option.getD_some]
                exact summary_inlineInt _ h4' e he b hb hib hok.2 t ht
              · cases hi
            · cases hi
          · cases hi
      · cases h
    · cases h
  · cases h

/-- `Dec.cmp` of two integers is the order of the integers. -/
theorem decCmp_ofInt (a b : Int) :
    XSD.Dec.cmp (XSD.Dec.ofInt a) (XSD.Dec.ofInt b) = compare a b := by
  simp [XSD.Dec.cmp, XSD.Dec.ofInt]

/-- One step of `IAcc` is one step of `AggStream`'s accumulator on the summary
of the decoded value. Premises: the value `x` reads as `v`, and a held best id
reads as its held value. -/
theorem IAcc.step_abs (dec : UInt64 → Term) (fn : AggregateFn)
    (hfn : fn = .sum ∨ fn = .avg ∨ fn = .min ∨ fn = .max) (a : IAcc)
    (ha : ∀ bv bx, a = .best (some (bv, bx)) → ReadsInt dec bx bv)
    (hshape : (∃ t c, a = .sum t c) ↔ (fn = .sum ∨ fn = .avg))
    (x : UInt64) (v : Int) (hx : ReadsInt dec x v) :
    (a.step fn x v).abs dec = AggAcc.step fn (a.abs dec) (Summary.of (varView (dec x))) := by
  unfold ReadsInt at hx ha
  have hxv : (Summary.of (varView (dec x))).v = .term (dec x) := rfl
  have hxn : (Summary.of (varView (dec x))).nv = some (.dec (XSD.Dec.ofInt v)) := by rw [hx]
  have hxi : (Summary.of (varView (dec x))).isInt = true := by rw [hx]
  have hxs : (Summary.of (varView (dec x))).isNum = true := by rw [hx]
  cases a with
  | sum t c =>
    have hs : fn = .sum ∨ fn = .avg := hshape.mp ⟨t, c, rfl⟩
    have hstep : AggAcc.stepNum (.num (.num t) c) (Summary.of (varView (dec x))) =
        .num (.num (v + t)) (c + 1) := by
      unfold AggAcc.stepNum
      rw [hxn, hxi]
      simp [XSD.Dec.ofInt]
    rcases hs with rfl | rfl <;>
      simp only [IAcc.step, IAcc.abs, AggAcc.step, hxv, hstep]
  | best o =>
    have hs : fn = .min ∨ fn = .max := by
      rcases hfn with h | h | h | h
      · exact absurd (hshape.mpr (Or.inl h)) (by rintro ⟨_, _, h'⟩; cases h')
      · exact absurd (hshape.mpr (Or.inr h)) (by rintro ⟨_, _, h'⟩; cases h')
      · exact Or.inl h
      · exact Or.inr h
    cases o with
    | none =>
      rcases hs with rfl | rfl <;>
        simp only [IAcc.step, IAcc.abs, AggAcc.step, AggAcc.stepKeep, AggAcc.stepBest, hxv]
    | some p =>
      obtain ⟨bv, bx⟩ := p
      have hb := ha bv bx rfl
      have hbn : (Summary.of (varView (dec bx))).nv = some (.dec (XSD.Dec.ofInt bv)) := by rw [hb]
      have hbs : (Summary.of (varView (dec bx))).isNum = true := by rw [hb]
      have hord : sparqlOrderReadFast (Summary.of (varView (dec x))).v (Summary.of (varView (dec bx))).v
          (Summary.of (varView (dec x))).isNum (Summary.of (varView (dec bx))).isNum
          (Summary.of (varView (dec x))).nv (Summary.of (varView (dec bx))).nv = ordInt v bv := by
        rw [hxs, hbs, hxn, hbn]
        simp only [sparqlOrderReadFast, decCmp_ofInt, ordInt]
        cases hc : compare v bv <;>
          simp_all [Int.compare_eq_lt, Int.compare_eq_gt] <;> omega
      rcases hs with rfl | rfl <;>
      · simp only [IAcc.step, AggAcc.step, AggAcc.stepKeep, AggAcc.stepBest, hord, keepOf, IAcc.abs]
        simp only [hxv]
        by_cases hk : keepMin (ordInt v bv) = true <;> by_cases hk' : keepMax (ordInt v bv) = true <;>
          simp [hk, hk']

/-- The invariant of an `IAcc` for `fn`: the shape fits the function, and a
held best id reads as its held value. -/
def IAcc.Inv (dec : UInt64 → Term) (fn : AggregateFn) : IAcc → Prop
  | .sum _ _ => fn = .sum ∨ fn = .avg
  | .best none => fn = .min ∨ fn = .max
  | .best (some (bv, bx)) => (fn = .min ∨ fn = .max) ∧ ReadsInt dec bx bv

theorem IAcc.init_inv (dec : UInt64 → Term) (fn : AggregateFn)
    (hfn : fn = .sum ∨ fn = .avg ∨ fn = .min ∨ fn = .max) : (IAcc.init fn).Inv dec fn := by
  rcases hfn with rfl | rfl | rfl | rfl <;> simp [IAcc.init, IAcc.Inv]

theorem IAcc.step_inv (dec : UInt64 → Term) (fn : AggregateFn) (a : IAcc) (ha : a.Inv dec fn)
    (x : UInt64) (v : Int) (hx : ReadsInt dec x v) : (a.step fn x v).Inv dec fn := by
  cases a with
  | sum t c => exact ha
  | best o =>
    cases o with
    | none => exact ⟨ha, hx⟩
    | some p =>
      obtain ⟨bv, bx⟩ := p
      simp only [IAcc.step]
      split
      · exact ⟨ha.1, hx⟩
      · exact ha

/-- `IAcc.step_abs` under the invariant. -/
theorem IAcc.step_abs_inv (dec : UInt64 → Term) (fn : AggregateFn) (a : IAcc) (ha : a.Inv dec fn)
    (x : UInt64) (v : Int) (hx : ReadsInt dec x v) :
    (a.step fn x v).abs dec = AggAcc.step fn (a.abs dec) (Summary.of (varView (dec x))) := by
  have hfn : fn = .sum ∨ fn = .avg ∨ fn = .min ∨ fn = .max := by
    cases a with
    | sum t c => rcases (ha : fn = .sum ∨ fn = .avg) with h | h <;> simp [h]
    | best o =>
      cases o with
      | none => rcases (ha : fn = .min ∨ fn = .max) with h | h <;> simp [h]
      | some p => rcases ha.1 with h | h <;> simp [h]
  apply IAcc.step_abs dec fn hfn a _ _ x v hx
  · intro bv bx h
    subst h
    exact ha.2
  · constructor
    · rintro ⟨t, c, rfl⟩
      exact ha
    · intro h
      cases a with
      | sum t c => exact ⟨t, c, rfl⟩
      | best o =>
        cases o with
        | none =>
          rcases (ha : fn = .min ∨ fn = .max) with h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h
        | some p =>
          rcases ha.1 with h' | h' <;> rcases h with h | h <;> rw [h'] at h <;> cases h

/-- Over a list of ids with their values, each reading as its value, the
`IAcc` fold is the `AggStream` fold on the summaries of the decoded values:
the integer path computes what the summary path computes. -/
theorem IAcc.fold_abs (dec : UInt64 → Term) (fn : AggregateFn) :
    ∀ (xs : List (UInt64 × Int)) (a : IAcc), a.Inv dec fn → (∀ p ∈ xs, ReadsInt dec p.1 p.2) →
      (xs.foldl (fun a p => a.step fn p.1 p.2) a).abs dec =
        (xs.map (fun p => Summary.of (varView (dec p.1)))).foldl (AggAcc.step fn) (a.abs dec)
  | [], _, _, _ => rfl
  | p :: ps, a, ha, hall => by
    have hp := hall p (List.mem_cons_self ..)
    simp only [List.foldl_cons, List.map_cons]
    rw [← IAcc.step_abs_inv dec fn a ha p.1 p.2 hp]
    exact IAcc.fold_abs dec fn ps _ (IAcc.step_inv dec fn a ha p.1 p.2 hp)
      (fun q hq => hall q (List.mem_cons_of_mem _ hq))

/-! ## The pass -/

/-- What the pass computes. -/
structure Result where
  /-- the representative row of each group (its first row, decoded) -/
  reps : Array Binding
  /-- the value of each aggregate item of each group, in item order -/
  vals : Array (Array EvalResult)
  /-- the distinct ids decoded, for aggregate arguments and representative rows,
      plus one for each best id of MIN or MAX that the integer path decodes -/
  decoded : Nat
  /-- the values bound in the representative rows, summed over the groups -/
  repValues : Nat

/-- The row `i` of the table as a solution mapping, as `decodeRowsM` makes it:
the variables in column order, an unbound one left out. Each id is decoded once:
`terms` holds the terms decoded so far. -/
def rowBinding {m : Type → Type} [Monad m] (termOf : UInt64 → ExceptT String m Term)
    (t : Table) (i : Nat) (terms : Cache Id64 Term) :
    ExceptT String m (Binding × Cache Id64 Term) := do
  let mut mu : Array (String × Term) := Array.mkEmpty t.vars.size
  let mut terms := terms
  for c in [0:t.vars.size] do
    let x := t.at c i
    if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
      let (tm, terms') ← terms.getM (fun k => termOf k.val) (Id64.ofU x)
      terms := terms'
      mu := mu.push (t.vars[c]!, tm)
  return (mu.toList, terms)

/-- The group of each row and the first row of each group. -/
structure Groups where
  gids : Array Nat
  first : Array (Option Nat)

/-- Pass 1 of `aggregateM`: rows are numbered by the order of first appearance of
their group key (the id of the one group column, else the list of ids). Pure. -/
def assignGroups (t : Table) (gcols : Array Nat) (gd : ByteArray) : Groups := Id.run do
  let mut first : Array (Option Nat) := #[]
  let mut gids : Array Nat := Array.mkEmpty t.rows
  if gcols.size == 1 then
    let mut index1 : Std.HashMap Id64 Nat := {}
    for i in [0:t.rows] do
      let key := L4Factoidal.Codec.Zstd.word64 gd (8 * i)
      match index1.get? (Id64.ofU key) with
      | some g => gids := gids.push g
      | none =>
        let g := first.size
        index1 := index1.insert (Id64.ofU key) g
        first := first.push (some i)
        gids := gids.push g
  else
    let mut index : Std.HashMap (List UInt64) Nat := {}
    for i in [0:t.rows] do
      let key := gcols.toList.map fun c => t.at c i
      match index.get? key with
      | some g => gids := gids.push g
      | none =>
        let g := first.size
        index := index.insert key g
        first := first.push (some i)
        gids := gids.push g
  return { gids, first }

/-- What a run of pass 2 returns: the row to resume at, the accumulators, and the
id of an aggregate argument that is not yet in the summary table (row `i` is then
not stepped at all). -/
structure StepOut where
  i : Nat
  accs : Array AggAcc
  miss : Option UInt64

/-- The steps of the specs `ks` of the group `gi` on one value. -/
@[inline] def stepKs (fns : Array AggregateFn) (n gi : Nat) (ks : Array Nat) (s : Summary)
    (accs : Array AggAcc) : Array AggAcc :=
  ks.foldl (init := accs) fun accs k => accs.modify (gi * n + k) fun a => AggAcc.step fns[k]! a s

/-- The steps of the specs that read no value, on row `i` of group `gi`. -/
@[inline] def stepSimple (t : Table) (n : Nat) (argCols : Array ArgCol) (simple : Array Nat)
    (i gi : Nat) (accs : Array AggAcc) : Array AggAcc :=
  simple.foldl (init := accs) fun accs k =>
    match argCols[k]! with
    | .col c =>
      -- COUNT of a variable: a bound variable is never the type error, no decoding
      if t.at c i != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
        accs.modify (gi * n + k) AggAcc.stepCount
      else accs
    | _ => accs.modify (gi * n + k) AggAcc.stepCount

/-- The first aggregate argument of row `i` that is bound and absent from `sums`. -/
@[inline] def firstMiss (t : Table) (byCol : Array (Nat × Array Nat))
    (sums : Std.HashMap Id64 Summary) (i : Nat) : Option UInt64 :=
  byCol.findSome? fun e =>
    let x := t.at e.1 i
    if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound && !(sums.contains (Id64.ofU x)) then some x
    else none

/-- Pass 2 of `aggregateM` from row `i`: the steps of every accumulator, in row
order, with no decoding and no monad (a tail call with fuel). Stops at the first
row whose argument id is bound and absent from `sums`, before it changes any
accumulator. -/
def stepRows (t : Table) (n : Nat) (fns : Array AggregateFn) (argCols : Array ArgCol)
    (simple : Array Nat) (byCol : Array (Nat × Array Nat)) (ad : ByteArray)
    (gids : Array Nat) (implicit : Bool) (sums : Std.HashMap Id64 Summary) :
    Nat → Nat → Array AggAcc → StepOut
  | 0, i, accs => { i, accs, miss := none }
  | f + 1, i, accs =>
    if i < t.rows then
      let gi := if implicit then 0 else gids[i]!
      if byCol.size == 1 then
        let x := L4Factoidal.Codec.Zstd.word64 ad (8 * i)
        if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
          match sums.get? (Id64.ofU x) with
          | none => { i, accs, miss := some x }
          | some s =>
            stepRows t n fns argCols simple byCol ad gids implicit sums f (i + 1)
              (stepSimple t n argCols simple i gi (stepKs fns n gi byCol[0]!.2 s accs))
        else
          stepRows t n fns argCols simple byCol ad gids implicit sums f (i + 1)
            (stepSimple t n argCols simple i gi accs)
      else
        match firstMiss t byCol sums i with
        | some x => { i, accs, miss := some x }
        | none =>
          let accs := byCol.foldl (init := accs) fun accs e =>
            let x := t.at e.1 i
            if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
              stepKs fns n gi e.2 (sums.getD (Id64.ofU x) default) accs
            else accs
          stepRows t n fns argCols simple byCol ad gids implicit sums f (i + 1)
            (stepSimple t n argCols simple i gi accs)
    else { i, accs, miss := none }

/-- The functions the integer path takes. -/
def intFn : AggregateFn → Bool
  | .sum | .avg | .min | .max => true
  | _ => false

/-- The integer path from row `i` (a tail call with fuel): the specs `ks` read
the one argument column `ad`, the others are the specs that read no value.
`none` at the first bound id that `intVal?` does not read (the caller then runs
the summary path from the start). -/
def intRows (t : Table) (n : Nat) (fns : Array AggregateFn) (argCols : Array ArgCol)
    (simple : Array Nat) (ks : Array Nat) (ad : ByteArray) (gids : Array Nat) (implicit : Bool)
    (infos : Array (Option IntInfo)) :
    Nat → Nat → Array AggAcc → Array IAcc → Option (Array AggAcc × Array IAcc)
  | 0, _, accs, iaccs => some (accs, iaccs)
  | f + 1, i, accs, iaccs =>
    if i < t.rows then
      let gi := if implicit then 0 else gids[i]!
      let accs := stepSimple t n argCols simple i gi accs
      let x := L4Factoidal.Codec.Zstd.word64 ad (8 * i)
      if x != L4Factoidal.Storage.Sbm11.OptJoin.unbound then
        match intVal? infos x with
        | none => none
        | some v =>
          intRows t n fns argCols simple ks ad gids implicit infos f (i + 1) accs
            (ks.foldl (init := iaccs) fun ia k => ia.modify (gi * n + k) fun a => a.step fns[k]! x v)
      else intRows t n fns argCols simple ks ad gids implicit infos f (i + 1) accs iaccs
    else some (accs, iaccs)

/-- The accumulator an `IAcc` stands for (`IAcc.abs` with `ofInlineCode?`):
the best id of MIN or MAX is decoded here, once per group. -/
def IAcc.absM {m : Type → Type} [Monad m] : IAcc → ExceptT String m AggAcc
  | .sum t c => pure (.num (.num t) c)
  | .best none => pure (.best none)
  | .best (some (_, x)) =>
    match ofInlineCode? x.toNat with
    | some tm => pure (.best (some (Summary.of (varView tm))))
    | none => throw s!"inline id {x} does not decode"

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
    -- pass 1 (pure): the group of each row, and the first row of each group
    -- (`none`: the empty group of an implicit grouping over no rows)
    let gd : ByteArray := if gcols.size == 1 then t.cols[gcols[0]!]! else ByteArray.empty
    let grp : Groups :=
      if p.implicit then
        { gids := #[], first := #[if t.rows > 0 then some 0 else none] }
      else assignGroups t gcols gd
    let first := grp.first
    let mut accs : Array AggAcc := Array.mkEmpty (first.size * n)
    for _ in [0:first.size] do
      accs := accs ++ inits
    -- pass 2 (pure, resumed after each id to decode): the accumulator steps
    let ad : ByteArray := if byCol.size == 1 then t.cols[byCol[0]!.1]! else ByteArray.empty
    let mut terms : Cache Id64 Term := {}
    let mut sums : Cache Id64 Summary := {}
    let mut dts : Cache String (Option XSD.Builtin) := {}
    let mut start := 0
    let mut bestDecoded := 0
    -- the integer path (issue 862): one argument column of inline integers
    let fns := specs.map (·.1)
    let intRes : Option (Array AggAcc × Array IAcc) :=
      if byCol.size == 1 && byCol[0]!.2.all (fun k => intFn fns[k]!) then
        let ks := byCol[0]!.2
        let iinit : Array IAcc := Id.run do
          let mut a : Array IAcc := Array.mkEmpty (first.size * n)
          for _ in [0:first.size] do
            for k in [0:n] do
              a := a.push (IAcc.init fns[k]!)
          return a
        intRows t n fns argCols simple ks ad grp.gids p.implicit intInfos (t.rows + 1) 0 accs iinit
      else none
    match intRes with
    | some (accs', iaccs) =>
      accs := accs'
      for g in [0:first.size] do
        for k in byCol[0]!.2 do
          let ia := iaccs[g * n + k]!
          match ia with
          | .best (some _) => bestDecoded := bestDecoded + 1
          | _ => pure ()
          accs := accs.set! (g * n + k) (← ia.absM)
      start := t.rows + 1
    | none => pure ()
    for _ in [0:t.rows + 1] do
      if start > t.rows then break
      let o := stepRows t n (specs.map (·.1)) argCols simple byCol ad grp.gids p.implicit sums.map (t.rows - start + 1) start accs
      accs := o.accs
      start := o.i
      match o.miss with
      | none => break
      | some x =>
        -- an argument id is decoded here once and kept as its summary only
        let tm ← termOf x
        let (sm, dts') := sumCached dts tm
        dts := dts'
        sums := { sums with map := sums.map.insert (Id64.ofU x) sm }
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
    -- the distinct ids decoded: the argument ids, and the ids of the representative
    -- rows that are not argument ids
    let decoded := terms.map.fold (fun c k _ => if sums.map.contains k then c else c + 1) sums.map.size + bestDecoded
    return some { reps, vals, decoded, repValues }

#print axioms Cache.getM_id
#print axioms Cache.valid_empty
#print axioms Cache.getPure_fst
#print axioms Cache.getPure_valid
#print axioms Cache.getPure_list
#print axioms Cache.insert_valid
#print axioms Cache.hit_eq
#print axioms Cache.fill_valid
#print axioms sums_fill_valid
#print axioms sumCached_fst
#print axioms sumCached_valid

end L4Factoidal.Storage.Sbm11.IdAgg
