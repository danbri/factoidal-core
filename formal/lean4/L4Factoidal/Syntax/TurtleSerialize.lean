/-
L4Factoidal.Syntax.TurtleSerialize — the Turtle pretty-printer.

Port of `formal/fstar/RDF.Turtle.Serialize.fst` (502 lines).

The wire-correct serialisers exist for round-trip and hashing fidelity;
this one targets a HUMAN-FACING rendering of the same graph — a
`@prefix` header, `;`-joined predicate lists, `,`-joined object lists,
one block per subject. The owner's brief for it was "ensure serializers
are not gratuitously ugly".

## The correctness anchor, and what it forbids

`parseTurtle (turtleOfGraph table g)` must give back `g`. So an
abbreviation may be emitted only when the parser would accept it, which
is why `tsAbbreviateIri` calls the SAME `Syntax.validatePnLocal` the
parser uses rather than approximating the Turtle grammar a second time.
An IRI whose remainder is not `PN_LOCAL`-safe falls back to `<iri>`.

Two abbreviations are used, both round-trip safe: a prefixed name when
the local part validates, and the `a` keyword for `rdf:type`, which
Turtle defines as its shorthand and the parser accepts unconditionally.

Numeric and boolean literals are printed in their bare Turtle form (`42`,
`1.5`, `1e3`, `true`) when the option `literalShorthand` is on, which is the
default, AND the lexical form matches the grammar terminal of the literal's
datatype (`literalShorthand` below: INTEGER, DECIMAL, DOUBLE and
BooleanLiteral of Turtle §6.5). A lexical form that does not match, such as
`"5."^^xsd:decimal` or one with a leading space, keeps the quoted form, so the
printed text always reads back to the same (lexical form, datatype) pair. The
datatype IRI in the quoted form is abbreviated, since that is pure compaction
with no ambiguity.

This follows `RDF.Turtle.Serialize.fst` as changed by
https://github.com/danbri/factoidal/issues/681, which superseded the earlier
quoted-only decision ("correctness over sugar") both trees carried. The Lean
tree changed with it so that the two engines print the same text
(https://github.com/danbri/factoidal/issues/685).

## Options

`TurtleRenderOptions.prefixes` is a caller-supplied table of (namespace IRI,
`label:`) pairs that WINS over the derived one: a pair is emitted only when some
IRI of the graph lies under its namespace, in the caller's order, the first
occurrence of a namespace winning, and a derived label is never one a caller
pair already took. `turtleOfGraphOpts` is the entry point; `turtleOfGraphAuto`
is `turtleOfGraphOpts` with the defaults.

## Auto prefix derivation

Split each IRI at its last `#` or `/`, count the namespaces whose
remainder is `PN_LOCAL`-safe, prefer the eight well-known prefixes when
they occur, and fill the rest with `ns1:`…`ns8:`. A namespace whose
IRIs never compact cleanly earns no header line, because the per-term
fallback already covers it.

## Stack use

The writer takes no native stack frame for each triple, subject, predicate, object
or IRI occurrence of the graph
(https://github.com/danbri/factoidal/issues/863), for each prefix of the caller's table
or for each level of triple-term nesting
(https://github.com/danbri/factoidal/issues/864). `walkTriples` and `joinWithAcc` are
tail calls. `List.mergeSort` runs as the core library's `mergeSortTR₂` (tail-recursive
merges, recursion depth logarithmic in the length), and `map`, `filter`, `filterMap`,
`flatMap` and `zipIdx` run as their tail-recursive forms (`csimp` theorems of the core
library). Four functions of this module are the specification of a loop that the compiler
runs in their place, each by a `csimp` theorem of this module: `countRuns`, which counts
the runs of the sorted namespaces (`countRuns_eq_countRunsFast`); `tsUserUsed`, which keeps
the caller's prefixes that some IRI uses (`tsUserUsed_eq_fast`); `tsTermToTurtle`, which
takes a frame for each level of RDF 1.2 triple-term nesting in one object
(`tsTermToTurtle_eq_fast`); and `insertStr`, through `sortStrs` (`sortStrsSpec_eq_sortStrs`).
The rows `turtle-write-one-node`, `turtle-write-subjects` and `turtle-write-cli-*` of
`tests/stack/run.sh` write 100,000 triples in two shapes under a 512 KB stack; the rows
`turtle-write-prefixes*` write a table of 100,000 prefixes, every one used, through the
three ops that take one; and the row `turtle-triple-term` writes a triple term nested
300,000 deep. One recursion of this module still takes a frame for each step of
something other than the triples: `assignLabelsAvoiding` for each numbered prefix (at
most nine).

## Time

The time of the writer is linear in the graph and in the prefix table, with the sorts at
n log n. Four scans were quadratic
(https://github.com/danbri/factoidal/issues/864), each now a specification with a proved
fast form that the compiler runs:

  * `tsFindPrefix` scanned the table for each IRI of the document. A table of more than
    `prefixIndexRatio` rows for each distinct length of a namespace is answered by
    `PrefixIndex`, one hash lookup for each distinct length (`PrefixIndex.find_eq`,
    `turtleOfGraph_eq_fast`).
  * `tsUserUsed` scanned the list of namespaces seen, and the IRIs of the graph, for each
    pair of the caller's table (`tsUserUsed_eq_fast`).
  * `freshTopSpec` compared each namespace of the graph with each covered row, also when no
    numbered prefix was wanted (`freshTopSpec_eq_fast`).
  * `tsTermToTurtle` built the text of each level of a nested triple term from the text of
    the level below it, which copies the text so far at each level
    (`tsTermToTurtle_eq_fast`).

`declarationOrderPrefixes` in `Wasm/Ops/Parse.lean`, which `datasetOpen` runs on the
prefixes of the document, had the same list scan and has the same repair. The rows
`turtle-prefixes`, `turtle-prefixes-open` and `turtle-nest-time` of
`tests/stack/lean_scaling.py` measure the times at n, 2n and 4n.

## What the F\* module proves, and what it does not

It carries `lemma_ts_abbreviate_iri_pname_safe`, a structural fact
about the abbreviator, and its banner is explicit that the term-level
round trip is out of reach there: the literal path goes through byte
primitives that stay opaque to the solver, so even
`nq_escape_literal "a" == "a"` fails to reduce. Wire correctness of the
literal path is pinned at the CLI level instead.

Lean has the opposite situation. `Syntax.escapeLiteral` is an ordinary
computable function, so the round trip is CHECKABLE by `#guard` on
concrete graphs, through the real `parseTurtle` — which is what the
checks at the end do. That is evidence at the checked shapes, not a
theorem for all graphs, and this note says which it is.
-/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDFS.Vocabulary
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Joins

One reverse-accumulate then one concat, so a graph whose triples all
share a subject and predicate stays linear rather than quadratic. -/

def joinWithAcc (sep : String) : List String → List String → List String
  | [], acc => acc
  | [x], acc => x :: acc
  | x :: rest, acc => joinWithAcc sep rest (sep :: x :: acc)

def joinWith (sep : String) (xs : List String) : String :=
  String.join (joinWithAcc sep xs []).reverse

/-! ## The prefix table

`(namespace IRI, "label:")` pairs — the label already carries its
colon. -/

abbrev PrefixTable := List (String × String)

def tsStartsWithStrict (s pfx : String) : Bool :=
  s.length > pfx.length && s.startsWith pfx

def tsFindPrefix (table : PrefixTable) (iri : String) : Option (String × String) :=
  table.find? (fun p => tsStartsWithStrict iri p.1)

/-- `PN_LOCAL` may legally be empty (a bare `ex:`); anything non-empty
    must satisfy the parser's own validator. -/
def tsLocalOk (loc : String) : Bool :=
  loc.isEmpty || validatePnLocal loc.toList true

/-- Compact to a prefixed name only when the parser would read it back;
    otherwise emit the full `<iri>`. `find iri` is the row of the prefix table
    that names the namespace of `iri`: `tsFindPrefix table`, or the indexed lookup
    that the writer runs for a large table (`PrefixIndex.find_eq`). -/
def tsAbbreviateIriBy (find : String → Option (String × String)) (iri : String) : String :=
  match find iri with
  | some (ns, abbr) =>
      let loc := String.ofList (iri.toList.drop ns.length)
      if tsLocalOk loc then abbr ++ loc else "<" ++ iri ++ ">"
  | none => "<" ++ iri ++ ">"

def tsAbbreviateIri (table : PrefixTable) (iri : String) : String :=
  tsAbbreviateIriBy (tsFindPrefix table) iri

/-! ## The prefix index

`tsFindPrefix` scans the table for each IRI of the document: a table of `P` rows and a
graph of `n` IRI occurrences take `P * n` comparisons, which is 3 * 10^10 for 100,000
prefixes and 100,000 triples (https://github.com/danbri/factoidal/issues/864). The index
answers the same question with one hash lookup for each distinct LENGTH of a namespace
in the table. The namespaces that are proper prefixes of an IRI of `L` characters are
among the strings `take l iri` with `l < L`, and the table holds a namespace of length
`l` only when `l` is one of the lengths of its namespaces (`mem_lengths`). Among the
rows found, the writer takes the one of least rank, which is what `List.find?` takes.

The rank of a row is its position in the table. A namespace that occurs in several
rows keeps its first row, because a later row can never be the first row that matches. -/

/-- For each namespace of a table, its first row and the rank of that row. -/
abbrev PrefixRows := Std.HashMap String (Nat × (String × String))

/-- Add the rows of the table to `m`, the head with rank `k`. A namespace keeps the
row it had first. -/
def prefixRowsLoop : List (String × String) → Nat → PrefixRows → PrefixRows
  | [], _, m => m
  | e :: rest, k, m => prefixRowsLoop rest (k + 1) (m.insertIfNew e.1 (k, e))

/-- Add the lengths, in characters, of the namespaces of the table to `s`. -/
def prefixLengthsLoop : List (String × String) → Std.HashSet Nat → Std.HashSet Nat
  | [], s => s
  | e :: rest, s => prefixLengthsLoop rest (s.insert e.1.length)

/-- An index of a prefix table: the first row of each namespace, and the lengths of the
namespaces. -/
structure PrefixIndex where
  rows : PrefixRows
  /-- The lengths of the namespaces of the table, each once. -/
  lengths : List Nat

def PrefixIndex.ofTable (table : PrefixTable) : PrefixIndex :=
  { rows := prefixRowsLoop table 0 ∅, lengths := (prefixLengthsLoop table ∅).toList }

/-- The first row of namespace `s` in a list whose head has rank `k`: the specification
of the entries of `PrefixIndex.rows`. -/
def firstRow (s : String) : List (String × String) → Nat → Option (Nat × (String × String))
  | [], _ => none
  | e :: rest, k => if e.1 == s then some (k, e) else firstRow s rest (k + 1)

theorem prefixRowsLoop_get (s : String) :
    ∀ (l : List (String × String)) (k : Nat) (m : PrefixRows),
      (prefixRowsLoop l k m)[s]? = (match m[s]? with | some v => some v | none => firstRow s l k)
  | [], k, m => by
      cases h : m[s]? <;> simp [prefixRowsLoop, firstRow, h]
  | e :: rest, k, m => by
      rw [prefixRowsLoop, prefixRowsLoop_get s rest (k + 1) (m.insertIfNew e.1 (k, e)),
        Std.HashMap.getElem?_insertIfNew]
      by_cases h1 : (e.1 == s) = true
      · have hs : e.1 = s := eq_of_beq h1
        subst hs
        cases h : m[e.1]? with
        | some v =>
            have hmem : e.1 ∈ m := Std.HashMap.isSome_getElem?_iff_mem.mp (by simp [h])
            simp [hmem]
        | none =>
            have hmem : e.1 ∉ m := fun hm => by
              have := Std.HashMap.isSome_getElem?_iff_mem.mpr hm
              simp [h] at this
            simp [hmem, firstRow]
      · simp [h1, firstRow]

/-- A first row is a row of the list, at the rank it is reported at, with no earlier row
of the same namespace. -/
theorem firstRow_some (s : String) :
    ∀ (l : List (String × String)) (k r : Nat) (e : String × String),
      firstRow s l k = some (r, e) →
      ∃ i, k + i = r ∧ l[i]? = some e ∧ e.1 = s ∧ ∀ j, j < i → ∀ x, l[j]? = some x → x.1 ≠ s
  | [], k, r, e, h => by simp [firstRow] at h
  | x :: rest, k, r, e, h => by
      unfold firstRow at h
      by_cases hx : (x.1 == s) = true
      · rw [if_pos hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hr, he⟩ := h
        subst hr; subst he
        refine ⟨0, by omega, by simp, eq_of_beq hx, ?_⟩
        intro j hj; omega
      · rw [if_neg hx] at h
        obtain ⟨i, hi1, hi2, hi3, hi4⟩ := firstRow_some s rest (k + 1) r e h
        refine ⟨i + 1, by omega, by simpa using hi2, hi3, ?_⟩
        intro j hj y hy
        cases j with
        | zero =>
            simp at hy; subst hy
            intro hs; exact hx (by simp [hs])
        | succ j' => exact hi4 j' (by omega) y (by simpa using hy)

/-- If some row of the list has the namespace `s`, the list has a first row of `s`. -/
theorem firstRow_exists (s : String) :
    ∀ (l : List (String × String)) (k : Nat) (x : String × String), x ∈ l → x.1 = s →
      ∃ p, firstRow s l k = some p
  | [], _, _, h, _ => by simp at h
  | y :: rest, k, x, hx, hs => by
      unfold firstRow
      by_cases hy : (y.1 == s) = true
      · exact ⟨(k, y), by rw [if_pos hy]⟩
      · rw [if_neg hy]
        have hxr : x ∈ rest := by
          rcases List.mem_cons.mp hx with h | h
          · subst h; exact absurd (by simp [hs]) hy
          · exact h
        exact firstRow_exists s rest (k + 1) x hxr hs

theorem prefixLengthsLoop_contains (n : Nat) :
    ∀ (l : List (String × String)) (s : Std.HashSet Nat),
      (prefixLengthsLoop l s).contains n = true ↔ s.contains n = true ∨ ∃ e ∈ l, e.1.length = n
  | [], s => by simp [prefixLengthsLoop]
  | e :: rest, s => by
      rw [prefixLengthsLoop, prefixLengthsLoop_contains n rest]
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨x, hx, hn⟩)
        · exact Or.inr ⟨e, Or.inl rfl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨x, Or.inr hx, hn⟩
      · rintro (h | ⟨x, hx | hx, hn⟩)
        · exact Or.inl (Or.inr h)
        · subst hx; exact Or.inl (Or.inl hn)
        · exact Or.inr ⟨x, hx, hn⟩

theorem mem_lengths {T : PrefixTable} {n : Nat} :
    n ∈ (PrefixIndex.ofTable T).lengths ↔ ∃ e ∈ T, e.1.length = n := by
  unfold PrefixIndex.ofTable
  simp only
  rw [Std.HashSet.mem_toList, Std.HashSet.mem_iff_contains, prefixLengthsLoop_contains]
  simp [Std.HashSet.contains_empty]

theorem startsWithStrict_iff (s pfx : String) :
    tsStartsWithStrict s pfx = true ↔ pfx.length < s.length ∧ pfx.toList <+: s.toList := by
  unfold tsStartsWithStrict
  rw [Bool.and_eq_true, decide_eq_true_eq, String.startsWith_string_iff]

theorem take_copy_length (iri : String) (l : Nat) (h : l < iri.length) :
    ((iri.take l).copy).length = l := by
  rw [← String.length_toList, String.toList_copy_take, List.length_take, String.length_toList]
  omega

theorem startsWithStrict_take (iri : String) (l : Nat) (h : l < iri.length) :
    tsStartsWithStrict iri (iri.take l).copy = true := by
  rw [startsWithStrict_iff, take_copy_length iri l h, String.toList_copy_take]
  exact ⟨h, List.take_prefix _ _⟩

theorem take_copy_eq {iri ns : String} (h : tsStartsWithStrict iri ns = true) :
    (iri.take ns.length).copy = ns := by
  rw [startsWithStrict_iff] at h
  apply String.toList_inj.mp
  rw [String.toList_copy_take]
  have h2 := List.prefix_iff_eq_take.mp h.2
  rw [String.length_toList] at h2
  exact h2.symm

/-- The first rows, with their ranks, of the namespaces of the table that are proper
prefixes of `iri`: one lookup for each length of a namespace shorter than `iri`. -/
def PrefixIndex.candidates (ix : PrefixIndex) (iri : String) : List (Nat × (String × String)) :=
  let len := iri.length
  ix.lengths.filterMap fun l => if l < len then ix.rows[(iri.take l).copy]? else none

/-- Every candidate is a row of the table at its rank, its namespace is a proper prefix
of the IRI, and no earlier row has that namespace. -/
theorem mem_candidates {T : PrefixTable} {iri : String} {c : Nat × (String × String)}
    (h : c ∈ (PrefixIndex.ofTable T).candidates iri) :
    T[c.1]? = some c.2 ∧ tsStartsWithStrict iri c.2.1 = true ∧
      ∀ j, j < c.1 → ∀ x, T[j]? = some x → x.1 ≠ c.2.1 := by
  unfold PrefixIndex.candidates at h
  simp only [List.mem_filterMap] at h
  obtain ⟨l, _, hl⟩ := h
  by_cases hlt : l < iri.length
  · rw [if_pos hlt] at hl
    have hrows : (PrefixIndex.ofTable T).rows = prefixRowsLoop T 0 ∅ := rfl
    rw [hrows, prefixRowsLoop_get, Std.HashMap.getElem?_empty] at hl
    have hl' : firstRow (iri.take l).copy T 0 = some (c.1, c.2) := hl
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := firstRow_some _ T 0 c.1 c.2 hl'
    have hr : c.1 = i := by omega
    rw [hr]
    refine ⟨hi2, ?_, ?_⟩
    · rw [hi3]
      exact startsWithStrict_take iri l hlt
    · intro j hj x hx
      rw [hi3]
      exact hi4 j hj x hx
  · rw [if_neg hlt] at hl
    simp at hl

/-- A row whose namespace is a proper prefix of the IRI has a candidate of its
namespace, at its rank or an earlier one. -/
theorem candidate_of_row {T : PrefixTable} {iri : String} {j : Nat} {e : String × String}
    (hj : T[j]? = some e) (hp : tsStartsWithStrict iri e.1 = true) :
    ∃ c ∈ (PrefixIndex.ofTable T).candidates iri, c.2.1 = e.1 ∧ c.1 ≤ j := by
  have hmem : e ∈ T := List.mem_of_getElem? hj
  have hlen : e.1.length ∈ (PrefixIndex.ofTable T).lengths := mem_lengths.mpr ⟨e, hmem, rfl⟩
  have hlt : e.1.length < iri.length := ((startsWithStrict_iff _ _).mp hp).1
  have hkey := take_copy_eq hp
  obtain ⟨p, hp1⟩ := firstRow_exists e.1 T 0 e hmem rfl
  obtain ⟨r, e1⟩ := p
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ := firstRow_some _ T 0 r e1 hp1
  have hr : r = i := by omega
  subst hr
  have hle : r ≤ j := Nat.le_of_not_lt (fun hgt => hi4 j hgt e hj rfl)
  refine ⟨(r, e1), ?_, hi3, hle⟩
  unfold PrefixIndex.candidates
  simp only [List.mem_filterMap]
  refine ⟨e.1.length, hlen, ?_⟩
  rw [if_pos hlt, hkey]
  have hrows : (PrefixIndex.ofTable T).rows = prefixRowsLoop T 0 ∅ := rfl
  rw [hrows, prefixRowsLoop_get, Std.HashMap.getElem?_empty]
  simp [hp1]

/-- Of two rows, the one of lower rank; the first when the ranks are equal. -/
def lowerRank (best : Option (Nat × (String × String))) (c : Nat × (String × String)) :
    Option (Nat × (String × String)) :=
  match best with
  | none => some c
  | some b => if c.1 < b.1 then some c else some b

/-- The row `tsFindPrefix` finds: the candidate of least rank. -/
def PrefixIndex.find (ix : PrefixIndex) (iri : String) : Option (String × String) :=
  ((ix.candidates iri).foldl lowerRank none).map (·.2)

theorem foldl_lowerRank_some : ∀ (cs : List (Nat × (String × String))) (b : Nat × (String × String)),
    ∃ r, cs.foldl lowerRank (some b) = some r
  | [], b => ⟨b, rfl⟩
  | c :: rest, b => by
      simp only [List.foldl_cons]
      by_cases h : c.1 < b.1
      · have h1 : lowerRank (some b) c = some c := by simp [lowerRank, h]
        rw [h1]; exact foldl_lowerRank_some rest c
      · have h1 : lowerRank (some b) c = some b := by simp [lowerRank, h]
        rw [h1]; exact foldl_lowerRank_some rest b

theorem foldl_lowerRank_min : ∀ (cs : List (Nat × (String × String))) (b r : Nat × (String × String)),
    cs.foldl lowerRank (some b) = some r →
      (r = b ∨ r ∈ cs) ∧ r.1 ≤ b.1 ∧ ∀ c ∈ cs, r.1 ≤ c.1
  | [], b, r, h => by
      simp only [List.foldl_nil, Option.some.injEq] at h
      subst h; exact ⟨Or.inl rfl, Nat.le_refl _, by simp⟩
  | c :: rest, b, r, h => by
      simp only [List.foldl_cons] at h
      by_cases hc : c.1 < b.1
      · have h1 : lowerRank (some b) c = some c := by simp [lowerRank, hc]
        rw [h1] at h
        obtain ⟨hA, hB, hC⟩ := foldl_lowerRank_min rest c r h
        refine ⟨?_, by omega, ?_⟩
        · rcases hA with h | h
          · exact Or.inr (List.mem_cons.mpr (Or.inl h))
          · exact Or.inr (List.mem_cons.mpr (Or.inr h))
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; exact hB
          · exact hC x h
      · have h1 : lowerRank (some b) c = some b := by simp [lowerRank, hc]
        rw [h1] at h
        obtain ⟨hA, hB, hC⟩ := foldl_lowerRank_min rest b r h
        refine ⟨?_, hB, ?_⟩
        · rcases hA with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons.mpr (Or.inr h))
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · subst h; omega
          · exact hC x h

/-- The indexed lookup finds the row that `tsFindPrefix` finds, for every table and
every IRI. -/
theorem PrefixIndex.find_eq (T : PrefixTable) (iri : String) :
    (PrefixIndex.ofTable T).find iri = tsFindPrefix T iri := by
  unfold PrefixIndex.find tsFindPrefix
  generalize hcs : (PrefixIndex.ofTable T).candidates iri = cs
  have hmem : ∀ c ∈ cs, T[c.1]? = some c.2 ∧ tsStartsWithStrict iri c.2.1 = true ∧
      ∀ j, j < c.1 → ∀ x, T[j]? = some x → x.1 ≠ c.2.1 :=
    fun c hc => mem_candidates (hcs ▸ hc)
  have hcomp : ∀ j e, T[j]? = some e → tsStartsWithStrict iri e.1 = true →
      ∃ c ∈ cs, c.2.1 = e.1 ∧ c.1 ≤ j :=
    fun j e hj hp => hcs ▸ candidate_of_row hj hp
  cases hf : T.find? (fun p => tsStartsWithStrict iri p.1) with
  | none =>
      have hnone : ∀ x ∈ T, ¬ tsStartsWithStrict iri x.1 = true := List.find?_eq_none.mp hf
      cases cs with
      | nil => rfl
      | cons c rest =>
          exfalso
          have h := hmem c (List.mem_cons_self ..)
          exact hnone c.2 (List.mem_of_getElem? h.1) h.2.1
  | some e0 =>
      obtain ⟨hp0, j0, hj0, hT, hmin⟩ := List.find?_eq_some_iff_getElem.mp hf
      have hj0' : T[j0]? = some e0 := by rw [List.getElem?_eq_getElem hj0, hT]
      obtain ⟨c, hc, hc1, hc2⟩ := hcomp j0 e0 hj0' hp0
      cases cs with
      | nil => exact absurd hc (by simp)
      | cons c0 rest =>
          obtain ⟨r, hr⟩ := foldl_lowerRank_some rest c0
          have h0 : lowerRank none c0 = some c0 := rfl
          simp only [List.foldl_cons, h0, hr]
          obtain ⟨hA, hB, hC⟩ := foldl_lowerRank_min rest c0 r hr
          have hrmem : r ∈ c0 :: rest := by
            rcases hA with h | h
            · rw [h]; exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ h
          have hrmin : ∀ x ∈ c0 :: rest, r.1 ≤ x.1 := by
            intro x hx
            rcases List.mem_cons.mp hx with h | h
            · rw [h]; exact hB
            · exact hC x h
          have hrc : r.1 ≤ j0 := Nat.le_trans (hrmin c hc) hc2
          obtain ⟨hr1, hr2, _⟩ := hmem r hrmem
          have hge : j0 ≤ r.1 := by
            refine Nat.le_of_not_lt (fun hlt => ?_)
            have h := hmin r.1 hlt
            have hx : (T[r.1]'(by
                exact (List.getElem?_eq_some_iff.mp hr1).1)) = r.2 := by
              have := List.getElem?_eq_getElem (l := T) (i := r.1) (by
                exact (List.getElem?_eq_some_iff.mp hr1).1)
              rw [this] at hr1
              exact Option.some.inj hr1
            rw [hx] at h
            simp [hr2] at h
          have heq : r.1 = j0 := Nat.le_antisymm hrc hge
          rw [heq] at hr1
          rw [hj0'] at hr1
          have : r.2 = e0 := (Option.some.inj hr1).symm
          show some r.2 = some e0
          rw [this]

/-- A table is scanned when it has at most this many rows for each distinct length of a
namespace, and indexed above it. A lookup in the index costs one hash lookup for each
distinct length (about 170 ns, with 500 ns of fixed cost); a scan costs about 4 ns for each
row (500 ns of fixed cost). Measured on 2026-10-15 with `Abbreviator.run` on 300,000 IRIs,
half of them under a namespace of the table and half under none (the timer noise was
30 percent): the index wins from about 64 rows when the namespaces have one length, from
128 rows for 4 lengths and from 400 rows for 8. -/
def prefixIndexRatio : Nat := 64

/-- How a document abbreviates the IRIs against its prefix table: the scan for a small
table, the index for a large one. This is DATA and not a function that returns a
function. A definition `def f (table) : String → String := let ix := ...; fun iri => ...`
is compiled with the arity 2, so each call of the result would build the index again:
the first version of this section took 16 s for 1,000 rows and 63 s for 2,000. -/
inductive Abbreviator where
  | scan (table : PrefixTable)
  | indexed (ix : PrefixIndex)

/-- The abbreviator of a table; the index is built once, here. -/
def Abbreviator.ofTable (table : PrefixTable) : Abbreviator :=
  let ix := PrefixIndex.ofTable table
  if table.length ≤ prefixIndexRatio * ix.lengths.length then .scan table else .indexed ix

def Abbreviator.run : Abbreviator → String → String
  | .scan table, iri => tsAbbreviateIri table iri
  | .indexed ix, iri => tsAbbreviateIriBy ix.find iri

def Abbreviator.isIndexed : Abbreviator → Bool
  | .scan _ => false
  | .indexed _ => true

theorem Abbreviator.run_ofTable (table : PrefixTable) :
    (Abbreviator.ofTable table).run = tsAbbreviateIri table := by
  unfold Abbreviator.ofTable
  dsimp only
  split
  · rfl
  · funext iri
    have h : (PrefixIndex.ofTable table).find = tsFindPrefix table :=
      funext (PrefixIndex.find_eq table)
    show tsAbbreviateIriBy (PrefixIndex.ofTable table).find iri = tsAbbreviateIri table iri
    rw [h]; rfl

#print axioms PrefixIndex.find_eq
#print axioms Abbreviator.run_ofTable

/-! ## Bare literals — Turtle §6.5 terminals

```
INTEGER        ::= [+-]? [0-9]+
DECIMAL        ::= [+-]? [0-9]* '.' [0-9]+
DOUBLE         ::= [+-]? ( [0-9]+ '.' [0-9]* EXPONENT | '.' [0-9]+ EXPONENT | [0-9]+ EXPONENT )
EXPONENT       ::= [eE] [+-]? [0-9]+
BooleanLiteral ::= 'true' | 'false'
```

Each checker accepts a lexical form only when the terminal consumes the WHOLE
string. Port of `is_turtle_integer_lexical` and its siblings. -/

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `[+-]?` at the front. -/
def dropSign : List Char → List Char
  | '+' :: r => r
  | '-' :: r => r
  | cs => cs

/-- `[0-9]*`: how many digits there are at the front, and what follows them. -/
def scanDigits (cs : List Char) : Nat × List Char :=
  ((cs.takeWhile isAsciiDigit).length, cs.dropWhile isAsciiDigit)

/-- `[0-9]+` and nothing else. -/
def allDigitsNonEmpty (cs : List Char) : Bool := !cs.isEmpty && cs.all isAsciiDigit

/-- `EXPONENT`, consuming the whole remainder. -/
def isExponentSuffix : List Char → Bool
  | e :: r => (e == 'e' || e == 'E') && allDigitsNonEmpty (dropSign r)
  | [] => false

def isTurtleIntegerLexical (s : String) : Bool := allDigitsNonEmpty (dropSign s.toList)

def isTurtleDecimalLexical (s : String) : Bool :=
  match (scanDigits (dropSign s.toList)).2 with
  | '.' :: frac => allDigitsNonEmpty frac
  | _ => false

def isTurtleDoubleLexical (s : String) : Bool :=
  let r := dropSign s.toList
  match r with
  | '.' :: rest =>
      let (n, after) := scanDigits rest
      n > 0 && isExponentSuffix after
  | c :: _ =>
      if isAsciiDigit c then
        let (_, afterInt) := scanDigits r
        match afterInt with
        | '.' :: rest => isExponentSuffix (scanDigits rest).2
        | _ => isExponentSuffix afterInt
      else false
  | [] => false

def isTurtleBooleanLexical (s : String) : Bool := s == "true" || s == "false"

/-- The bare text of a literal whose datatype is `xsd:integer`, `xsd:decimal`,
`xsd:double` or `xsd:boolean` AND whose lexical form matches that datatype's
terminal; `none` otherwise, and the caller prints the quoted form. Port of
`literal_shorthand`. -/
def literalShorthand (l : Literal) : Option String :=
  if l.datatype == xsdInteger && isTurtleIntegerLexical l.lexicalForm then some l.lexicalForm
  else if l.datatype == xsdDecimal && isTurtleDecimalLexical l.lexicalForm then some l.lexicalForm
  else if l.datatype == xsdDouble && isTurtleDoubleLexical l.lexicalForm then some l.lexicalForm
  else if l.datatype == xsdBoolean && isTurtleBooleanLexical l.lexicalForm then some l.lexicalForm
  else none

/-! ## Terms -/

/-- The text of a term. This is the SPECIFICATION: it takes one stack frame for each
level of triple-term nesting, and at each level it copies the text of the levels below
(`tsTripleOpen ++ below ++ closer`), so the time is quadratic in the nesting depth. A
triple term nested 300,000 deep overflowed a 512 KB stack
(https://github.com/danbri/factoidal/issues/864). The compiler runs
`tsTermToTurtleFast` in its place (`tsTermToTurtle_eq_fast`, a `csimp` theorem). -/
def tsTermToTurtle (table : PrefixTable) (shorthand : Bool) : Term → String
  | .iri i => tsAbbreviateIri table i.val
  | .bnode b => "_:" ++ b
  | .literal l =>
      let esc := escapeLiteral l.val.lexicalForm
      match l.val.langTag with
      | some tag =>
          let ds := match l.val.direction with
                    | some .ltr => "--ltr"
                    | some .rtl => "--rtl"
                    | none => ""
          "\"" ++ esc ++ "\"@" ++ tag ++ ds
      | none =>
          if l.val.datatype == xsdString then "\"" ++ esc ++ "\""
          else
            match (if shorthand then literalShorthand l.val else none) with
            | some bare => bare
            | none => "\"" ++ esc ++ "\"^^" ++ tsAbbreviateIri table l.val.datatype.val
  | .tripleTerm s p o =>
      let subjStr := match s with
                     | .iri i => tsAbbreviateIri table i.val
                     | .bnode b => "_:" ++ b
      let predStr := if p == rdfType then "a" else tsAbbreviateIri table p.val
      "<<( " ++ subjStr ++ " " ++ predStr ++ " " ++ tsTermToTurtle table shorthand o ++ " )>>"

/-- The text of a triple term up to its object. -/
def tsTripleOpen (abbr : String → String) (s : Subject) (p : WfIri) : String :=
  let subjStr := match s with
                 | .iri i => abbr i.val
                 | .bnode b => "_:" ++ b
  let predStr := if p == rdfType then "a" else abbr p.val
  "<<( " ++ subjStr ++ " " ++ predStr ++ " "

/-- The text of a literal: the `.literal` case of `tsTermToTurtle`, with the
abbreviation of an IRI as a parameter. -/
def tsLiteralToTurtleBy (abbr : String → String) (shorthand : Bool) (l : WfLiteral) : String :=
  let esc := escapeLiteral l.val.lexicalForm
  match l.val.langTag with
  | some tag =>
      let ds := match l.val.direction with
                | some .ltr => "--ltr"
                | some .rtl => "--rtl"
                | none => ""
      "\"" ++ esc ++ "\"@" ++ tag ++ ds
  | none =>
      if l.val.datatype == xsdString then "\"" ++ esc ++ "\""
      else
        match (if shorthand then literalShorthand l.val else none) with
        | some bare => bare
        | none => "\"" ++ esc ++ "\"^^" ++ abbr l.val.datatype.val

/-- `" )>>"` written `k` times: the end of `k` open triple terms. -/
def closersStr (k : Nat) : String := String.join (List.replicate k " )>>")

theorem closersStr_zero : closersStr 0 = "" := rfl

theorem closersStr_succ (k : Nat) : closersStr (k + 1) = " )>>" ++ closersStr k := by
  simp [closersStr, List.replicate_succ, String.join_cons]

/-- `acc` followed by the `k` closers, one tail call for each. -/
def appendClosers (acc : String) : Nat → String
  | 0 => acc
  | k + 1 => appendClosers (acc ++ " )>>") k

theorem appendClosers_eq : ∀ (k : Nat) (acc : String), appendClosers acc k = acc ++ closersStr k
  | 0, acc => by simp [appendClosers, closersStr_zero]
  | k + 1, acc => by
      rw [appendClosers, appendClosers_eq k, closersStr_succ, String.append_assoc]

/-- The loop of `tsTermToTurtleFast`. `acc` is the text so far and `k` the number of
triple terms open in it: a triple term appends its opening and continues with its
object, a term that is not a triple term appends its text and the `k` closers. Every
call of the loop on itself is a tail call, and `acc` is appended to in place, so the
loop takes no stack frame for a nesting level and time linear in the text. -/
def tsTermToTurtleLoop (abbr : String → String) (shorthand : Bool) :
    Term → String → Nat → String
  | .tripleTerm s p o, acc, k =>
      tsTermToTurtleLoop abbr shorthand o (acc ++ tsTripleOpen abbr s p) (k + 1)
  | .iri i, acc, k => appendClosers (acc ++ abbr i.val) k
  | .bnode b, acc, k => appendClosers (acc ++ ("_:" ++ b)) k
  | .literal l, acc, k => appendClosers (acc ++ tsLiteralToTurtleBy abbr shorthand l) k

/-- `tsTermToTurtle` for any abbreviation of IRIs. -/
def tsTermToTurtleBy (abbr : String → String) (shorthand : Bool) (t : Term) : String :=
  tsTermToTurtleLoop abbr shorthand t "" 0

/-- The loop, for every state it can be in: the text so far, the specification on the
term, and the closers of the open triple terms. -/
theorem tsTermToTurtleLoop_eq (table : PrefixTable) (shorthand : Bool) :
    ∀ (t : Term) (acc : String) (k : Nat),
      tsTermToTurtleLoop (tsAbbreviateIri table) shorthand t acc k =
        acc ++ tsTermToTurtle table shorthand t ++ closersStr k
  | .tripleTerm s p o, acc, k => by
      rw [tsTermToTurtleLoop, tsTermToTurtleLoop_eq table shorthand o, closersStr_succ]
      have : tsTermToTurtle table shorthand (.tripleTerm s p o) =
          tsTripleOpen (tsAbbreviateIri table) s p ++ tsTermToTurtle table shorthand o ++ " )>>" := rfl
      rw [this]
      simp only [String.append_assoc]
  | .iri i, acc, k => by
      rw [tsTermToTurtleLoop, appendClosers_eq]
      rfl
  | .bnode b, acc, k => by
      rw [tsTermToTurtleLoop, appendClosers_eq]
      rfl
  | .literal l, acc, k => by
      rw [tsTermToTurtleLoop, appendClosers_eq]
      rfl

/-- `tsTermToTurtle` as a loop. -/
def tsTermToTurtleFast (table : PrefixTable) (shorthand : Bool) (t : Term) : String :=
  tsTermToTurtleBy (tsAbbreviateIri table) shorthand t

theorem tsTermToTurtleFast_eq (table : PrefixTable) (shorthand : Bool) (t : Term) :
    tsTermToTurtleFast table shorthand t = tsTermToTurtle table shorthand t := by
  unfold tsTermToTurtleFast tsTermToTurtleBy
  rw [tsTermToTurtleLoop_eq, closersStr_zero]
  simp

/-- Any call of the specification runs the loop. The calls in the stream writer
(`Sink.bodyPush`) and in `walkTriples` are compiled after this line, so the Turtle
writer takes no frame for a nesting level of a triple term. -/
@[csimp] theorem tsTermToTurtle_eq_fast : @tsTermToTurtle = @tsTermToTurtleFast := by
  funext table shorthand t; exact (tsTermToTurtleFast_eq table shorthand t).symm

#print axioms tsTermToTurtleLoop_eq
#print axioms tsTermToTurtleFast_eq
#print axioms tsTermToTurtle_eq_fast

def tsSubjectToTurtleBy (abbr : String → String) : Subject → String
  | .iri i => abbr i.val
  | .bnode b => "_:" ++ b

def tsSubjectToTurtle (table : PrefixTable) : Subject → String :=
  tsSubjectToTurtleBy (tsAbbreviateIri table)

/-- `a` is Turtle's own shorthand for `rdf:type`, accepted back by the
    parser, and needs no prefix-table entry. -/
def tsPredicateToTurtleBy (abbr : String → String) (p : WfIri) : String :=
  if p == rdfType then "a" else abbr p.val

def tsPredicateToTurtle (table : PrefixTable) (p : WfIri) : String :=
  tsPredicateToTurtleBy (tsAbbreviateIri table) p

/-! ## Sorting and subject grouping

The sort key is subject, separator, predicate, separator, object — the
same discipline the closure path's dedup uses. The separator is U+001F,
which the F\* source documents as forbidden inside an IRI, so the join
is unambiguous. -/

def unitSep : String := String.singleton (Char.ofNat 31)

def tsTermKey : Term → String
  | .iri i => "1" ++ i.val
  | .bnode b => "0" ++ b
  | .literal l => "2" ++ l.val.lexicalForm ++ unitSep ++ l.val.datatype.val ++
      unitSep ++ l.val.langTag.getD ""
  | .tripleTerm _ _ _ => "3"

def tsSubjKey : Subject → String
  | .iri i => "1" ++ i.val
  | .bnode b => "0" ++ b

def tsTripleKey (t : Triple) : String :=
  tsSubjKey t.s ++ unitSep ++ t.p.val ++ unitSep ++ tsTermKey t.o

/-- Lean's own merge sort, keyed by `tsTripleKey`. The F\* module uses
    `List.Tot.sortWith triple_cmp`; this is the same O(n log n) sort
    with the comparator expressed as a `≤` on the key string. -/
def sortTriples (g : List Triple) : List Triple :=
  g.mergeSort (fun a b => tsTripleKey a ≤ tsTripleKey b)

structure SubjState where
  subj        : Subject
  subjText    : String
  curPred     : WfIri
  curPredText : String
  curObjs     : List String
  predChunks  : List String

def finishPred (st : SubjState) : List String :=
  (st.curPredText ++ " " ++ joinWith " , " st.curObjs.reverse) :: st.predChunks

def finishSubj (st : SubjState) : String :=
  st.subjText ++ " " ++ joinWith " ;\n    " (finishPred st).reverse ++ " .\n\n"

/-- The statements of a sorted list of triples, newest first. `abbr` abbreviates an IRI. -/
def walkTriplesBy (abbr : String → String) (shorthand : Bool) : List Triple → Option SubjState →
    List String → List String
  | [], none, acc => acc
  | [], some s, acc => finishSubj s :: acc
  | t :: rest, none, acc =>
      walkTriplesBy abbr shorthand rest (some
        { subj := t.s, subjText := tsSubjectToTurtleBy abbr t.s,
          curPred := t.p, curPredText := tsPredicateToTurtleBy abbr t.p,
          curObjs := [tsTermToTurtleBy abbr shorthand t.o], predChunks := [] }) acc
  | t :: rest, some s, acc =>
      let objText := tsTermToTurtleBy abbr shorthand t.o
      if s.subj == t.s then
        if s.curPred == t.p then
          walkTriplesBy abbr shorthand rest (some { s with curObjs := objText :: s.curObjs }) acc
        else
          walkTriplesBy abbr shorthand rest (some
            { s with curPred := t.p, curPredText := tsPredicateToTurtleBy abbr t.p,
                     curObjs := [objText], predChunks := finishPred s }) acc
      else
        walkTriplesBy abbr shorthand rest (some
          { subj := t.s, subjText := tsSubjectToTurtleBy abbr t.s,
            curPred := t.p, curPredText := tsPredicateToTurtleBy abbr t.p,
            curObjs := [objText], predChunks := [] }) (finishSubj s :: acc)

def walkTriples (table : PrefixTable) (shorthand : Bool) : List Triple → Option SubjState →
    List String → List String :=
  walkTriplesBy (tsAbbreviateIri table) shorthand

def renderTriplesBy (abbr : String → String) (shorthand : Bool) (g : Graph) : String :=
  String.join (walkTriplesBy abbr shorthand (sortTriples g) none []).reverse

def renderTriples (table : PrefixTable) (shorthand : Bool) (g : Graph) : String :=
  renderTriplesBy (tsAbbreviateIri table) shorthand g

/-! ## The header and the entry point -/

def renderPrefixHeader (table : PrefixTable) : List String :=
  table.map (fun (ns, abbr) => "@prefix " ++ abbr ++ " <" ++ ns ++ "> .\n")

/-- The document for a prefix table: the SPECIFICATION. It looks every IRI up with a
scan of the table (`tsFindPrefix`), so a table of `P` rows and a graph of `n` IRI
occurrences take `P * n` comparisons. The compiler runs `turtleOfGraphFast` in its
place (`turtleOfGraph_eq_fast`, a `csimp` theorem). -/
def turtleOfGraph (table : PrefixTable) (shorthand : Bool) (g : Graph) : String :=
  let headerLines := renderPrefixHeader table
  String.join headerLines ++ (if headerLines.isEmpty then "" else "\n") ++
    renderTriples table shorthand g

/-- `turtleOfGraph` with the lookups of a large table indexed (`Abbreviator`). -/
def turtleOfGraphFast (table : PrefixTable) (shorthand : Bool) (g : Graph) : String :=
  let headerLines := renderPrefixHeader table
  let ab := Abbreviator.ofTable table
  String.join headerLines ++ (if headerLines.isEmpty then "" else "\n") ++
    renderTriplesBy ab.run shorthand g

theorem turtleOfGraphFast_eq (table : PrefixTable) (shorthand : Bool) (g : Graph) :
    turtleOfGraphFast table shorthand g = turtleOfGraph table shorthand g := by
  unfold turtleOfGraphFast turtleOfGraph renderTriples
  simp only [Abbreviator.run_ofTable]

/-- Any call of the specification runs the indexed writer. `turtleOfGraphOpts` is compiled
after this line. -/
@[csimp] theorem turtleOfGraph_eq_fast : @turtleOfGraph = @turtleOfGraphFast := by
  funext table shorthand g; exact (turtleOfGraphFast_eq table shorthand g).symm

#print axioms turtleOfGraphFast_eq
#print axioms turtleOfGraph_eq_fast

/-! ## Auto prefix derivation -/

/-- The last `#` or `/`, as a split into `(namespace-with-delimiter,
    local)`. `none` when the IRI has neither and so cannot be
    compacted. -/
def nsSplit (iri : String) : Option (String × String) :=
  let cs := iri.toList
  let idx := cs.zipIdx.foldl (fun best (ci : Char × Nat) =>
    if ci.1 == '#' || ci.1 == '/' then some ci.2 else best) none
  match idx with
  | none => none
  | some i => some (String.ofList (cs.take (i + 1)), String.ofList (cs.drop (i + 1)))

/-- Every IRI in the graph: subjects, predicates, object IRIs, and
    literal datatypes other than the implicit `xsd:string` and language
    cases, which never print with a suffix. The IRIs nested inside a
    triple term are skipped, as in F\* — they print un-abbreviated,
    which is correct if less pretty. -/
def collectIris (g : Graph) : List String :=
  g.flatMap (fun t =>
    [t.p.val] ++
    (match t.s with | .iri i => [i.val] | _ => []) ++
    (match t.o with
     | .iri i => [i.val]
     | .literal l => match l.val.langTag with
                     | some _ => []
                     | none => if l.val.datatype == xsdString then []
                               else [l.val.datatype.val]
     | _ => []))

def candidateNamespaces (iris : List String) : List String :=
  iris.filterMap (fun i =>
    match nsSplit i with
    | none => none
    | some (ns, loc) =>
        if !loc.isEmpty && validatePnLocal loc.toList true then some ns else none)

/-- The runs of equal neighbours of a list, in order, each with its length: the
run-length encoding. `turtleOfGraphOpts` applies it to the sorted namespaces of the
graph, one string for each IRI occurrence, so `n` is the size of the graph.

This is the SPECIFICATION. It takes one stack frame for each element of the list,
because it continues with the result of the recursive call (`(y2, n + 1) :: more` or
`(x, 1) :: ...`). A graph of 2,711 triples overflowed a 512 KB stack
(https://github.com/danbri/factoidal/issues/863). The compiler runs `countRunsFast`
in its place (`countRuns_eq_countRunsFast`, a `csimp` theorem). -/
def countRuns : List String → List (String × Nat)
  | [] => []
  | [x] => [(x, 1)]
  | x :: y :: rest =>
      if x == y then
        match countRuns (y :: rest) with
        | (y2, n) :: more => (y2, n + 1) :: more
        | [] => [(x, 1)]
      else (x, 1) :: countRuns (y :: rest)

/-- The loop of `countRunsFast`. `cur` is the string of the run in progress and `k`
the number of equal strings that followed its first one, so the run has length
`k + 1`; `acc` holds the finished runs, newest first. Every call of the loop on
itself is a tail call, and the list is reversed once, at the end. -/
def countRunsLoop : List String → String → Nat → List (String × Nat) → List (String × Nat)
  | [], cur, k, acc => ((cur, k + 1) :: acc).reverse
  | y :: rest, cur, k, acc =>
      if cur == y then countRunsLoop rest cur (k + 1) acc
      else countRunsLoop rest y 0 ((cur, k + 1) :: acc)

/-- `countRuns` as a loop over the list: no stack frame for each element. -/
def countRunsFast (xs : List String) : List (String × Nat) :=
  match xs with
  | [] => []
  | x :: rest => countRunsLoop rest x 0 []

/-- Add `k` to the length of the first run. -/
def bumpFirstRun (k : Nat) : List (String × Nat) → List (String × Nat)
  | [] => []
  | (a, m) :: more => (a, k + m) :: more

theorem bumpFirstRun_zero : ∀ r : List (String × Nat), bumpFirstRun 0 r = r
  | [] => rfl
  | (a, m) :: more => by simp [bumpFirstRun]

/-- A list with a first element has a first run. -/
theorem countRuns_ne_nil : ∀ (x : String) (l : List String), countRuns (x :: l) ≠ []
  | x, [] => by simp [countRuns]
  | x, y :: rest => by
      rw [countRuns]
      split
      · split <;> simp
      · simp

/-- The loop, for every state it can be in: the finished runs, then the specification
on the string in progress and the rest, with the `k` strings already counted added to
the first run. -/
theorem countRunsLoop_eq : ∀ (l : List String) (cur : String) (k : Nat)
    (acc : List (String × Nat)),
    countRunsLoop l cur k acc = acc.reverse ++ bumpFirstRun k (countRuns (cur :: l))
  | [], cur, k, acc => by
      simp [countRunsLoop, countRuns, bumpFirstRun]
  | y :: rest, cur, k, acc => by
      unfold countRunsLoop
      by_cases h : (cur == y) = true
      · have hcy : cur = y := eq_of_beq h
        subst hcy
        rw [if_pos h, countRunsLoop_eq rest cur (k + 1) acc, countRuns, if_pos h]
        cases hr : countRuns (cur :: rest) with
        | nil => exact absurd hr (countRuns_ne_nil cur rest)
        | cons p more =>
            obtain ⟨a, m⟩ := p
            simp only [bumpFirstRun]
            have : k + 1 + m = k + (m + 1) := by omega
            rw [this]
      · rw [if_neg h, countRunsLoop_eq rest y 0 ((cur, k + 1) :: acc), bumpFirstRun_zero,
          countRuns, if_neg h]
        simp [bumpFirstRun]

theorem countRunsFast_eq (xs : List String) : countRunsFast xs = countRuns xs := by
  cases xs with
  | nil => rfl
  | cons x rest =>
      simp only [countRunsFast]
      rw [countRunsLoop_eq]
      simp [bumpFirstRun_zero]

/-- Any call of the specification runs the loop. The call in `turtleOfGraphOpts`
is compiled after this line, so the Turtle writer takes no frame for each IRI
occurrence of the graph. -/
@[csimp] theorem countRuns_eq_countRunsFast : @countRuns = @countRunsFast := by
  funext xs; exact (countRunsFast_eq xs).symm

#print axioms countRunsLoop_eq
#print axioms countRunsFast_eq
#print axioms countRuns_eq_countRunsFast

#guard countRuns [] == []
#guard countRuns ["a"] == [("a", 1)]
#guard countRuns ["a", "a", "b", "a", "a", "a", "c"] ==
  [("a", 2), ("b", 1), ("a", 3), ("c", 1)]
#guard countRunsFast ["a", "a", "b", "a", "a", "a", "c"] ==
  countRuns ["a", "a", "b", "a", "a", "a", "c"]
#guard countRunsFast (List.replicate 100000 "x") == [("x", 100000)]

/-- Descending by count, STABLE: namespaces of equal count keep the order they
had, which is what F\*'s `List.Tot.sortWith count_desc_compare` gives. (An
insertion sort that places each element after its equals reverses the ties, and
with them the order in which `ns1:`, `ns2:` … are handed out.) -/
def sortByCountDesc (xs : List (String × Nat)) : List (String × Nat) :=
  xs.mergeSort (fun a b => decide (b.2 ≤ a.2))

/-- Insertion sort: the specification of `sortStrs`. Quadratic; kept as the
meaning of the sort and as the right-hand side of `sortStrs_eq`. -/
def insertStr (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertStr x ys

def sortStrsSpec : List String → List String
  | [] => []
  | x :: xs => insertStr x (sortStrsSpec xs)

/-- The sort `turtleOfGraphAuto` runs: merge sort, O(n log n). The input is one
namespace string per IRI occurrence in the graph, so n is the size of the
graph; the insertion sort it replaces took 18 s on 22,000 triples. -/
def sortStrs (xs : List String) : List String :=
  xs.mergeSort (fun a b => a ≤ b)

/-- Inserting keeps the elements. -/
theorem insertStr_perm (x : String) : ∀ ys : List String, List.Perm (insertStr x ys) (x :: ys)
  | [] => List.Perm.refl _
  | y :: ys => by
      unfold insertStr
      split
      · exact List.Perm.refl _
      · exact ((insertStr_perm x ys).cons y).trans (List.Perm.swap x y ys)

/-- Inserting into a sorted list gives a sorted list. -/
theorem insertStr_pairwise (x : String) :
    ∀ ys : List String, ys.Pairwise (fun a b => decide (a ≤ b) = true) →
      (insertStr x ys).Pairwise (fun a b => decide (a ≤ b) = true)
  | [], _ => by simp [insertStr]
  | y :: ys, h => by
      unfold insertStr
      split
      · rename_i hxy
        have h0 := h
        rw [List.pairwise_cons] at h ⊢
        refine ⟨?_, h0⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · simpa using hxy
        · have := h.1 b hb
          have hyb : y ≤ b := by simpa using this
          simpa using Std.le_trans hxy hyb
      · rename_i hxy
        rw [List.pairwise_cons] at h ⊢
        refine ⟨?_, insertStr_pairwise x ys h.2⟩
        intro b hb
        have hb' : b ∈ x :: ys := (insertStr_perm x ys).mem_iff.mp hb
        rcases List.mem_cons.mp hb' with rfl | hb'
        · have : y ≤ b := by
            rcases (Std.le_total : y ≤ b ∨ b ≤ y) with h1 | h1
            · exact h1
            · exact absurd h1 hxy
          simpa using this
        · simpa using h.1 b hb'

/-- The insertion sort returns a permutation of its input. -/
theorem sortStrsSpec_perm : ∀ xs : List String, List.Perm (sortStrsSpec xs) xs
  | [] => List.Perm.refl _
  | x :: xs => by
      unfold sortStrsSpec
      exact (insertStr_perm x _).trans ((sortStrsSpec_perm xs).cons x)

/-- The insertion sort returns a list sorted by `≤`. -/
theorem sortStrsSpec_pairwise : ∀ xs : List String,
    (sortStrsSpec xs).Pairwise (fun a b => decide (a ≤ b) = true)
  | [] => by simp [sortStrsSpec]
  | x :: xs => by
      unfold sortStrsSpec
      exact insertStr_pairwise x _ (sortStrsSpec_pairwise xs)

/-- The merge sort returns exactly what the insertion sort returns: both are
sorted permutations of the input, and `≤` on strings is antisymmetric. So the
prefix table `turtleOfGraphAuto` derives is the one it derived before. -/
theorem sortStrs_eq (xs : List String) : sortStrs xs = sortStrsSpec xs := by
  unfold sortStrs
  have hp : (xs.mergeSort (fun a b => a ≤ b)).Pairwise (fun a b => decide (a ≤ b) = true) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact Std.le_trans hab hbc)
      (fun a b => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact (Std.le_total : a ≤ b ∨ b ≤ a)) xs
  refine List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true) ?_ hp
    (sortStrsSpec_pairwise xs) ?_
  · intro a b _ _ hab hba
    simp only [decide_eq_true_eq] at hab hba
    exact Std.le_antisymm hab hba
  · exact (List.mergeSort_perm xs _).trans (sortStrsSpec_perm xs).symm

/-- Any call of the specification runs the merge sort: the insertion sort
takes one stack frame per string as well as quadratic time (https://github.com/danbri/factoidal/issues/746). -/
@[csimp] theorem sortStrsSpec_eq_sortStrs : @sortStrsSpec = @sortStrs := by
  funext xs; exact (sortStrs_eq xs).symm

def assignLabels : Nat → List (String × Nat) → List (String × String)
  | _, [] => []
  | idx, (ns, _) :: rest =>
      if idx < 9 then (ns, "ns" ++ toString idx ++ ":") :: assignLabels (idx + 1) rest
      else []

/-- Preferred over auto-numbered labels when the graph uses them: real
    graphs are dominated by `rdf:type` and `xsd:` datatypes, and a
    numbered prefix for those would be needless ugliness. -/
def wellKnownPrefixes : PrefixTable :=
  [ ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:")
  , ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:")
  , ("http://www.w3.org/2001/XMLSchema#",           "xsd:")
  , ("http://www.w3.org/2002/07/owl#",              "owl:")
  , ("http://xmlns.com/foaf/0.1/",                  "foaf:")
  , ("http://purl.org/dc/terms/",                   "dcterms:")
  , ("http://purl.org/dc/elements/1.1/",            "dc:")
  , ("http://schema.org/",                          "schema:") ]

/-- Render options. -/
structure TurtleRenderOptions where
  /-- Caller-supplied (namespace IRI, `label:`) pairs; they win over the derived
  table. -/
  prefixes : PrefixTable := []
  /-- Bare INTEGER, DECIMAL, DOUBLE and BooleanLiteral when the lexical form
  qualifies. -/
  literalShorthand : Bool := true

/-- Does some IRI of the graph lie strictly under namespace `ns`? -/
def tsAnyIriUsesNs (iris : List String) (ns : String) : Bool :=
  iris.any (fun i => tsStartsWithStrict i ns)

/-- The caller's pairs whose namespace some IRI of the graph uses, in the
caller's order. The first occurrence of a namespace wins: a repeat is dropped
even when the first occurrence went unused, and a namespace no IRI uses is not
emitted. Port of `ts_user_used`.

This is the SPECIFICATION. It takes one stack frame for each pair it keeps, because it
continues with `(ns, label) :: tsUserUsed ...`, and it takes time quadratic in the
table: a scan of `seenNs` and a scan of the IRIs for each pair. A table of 8,128 used
pairs overflowed a 512 KB stack, and 32,000 pairs took 50.7 s
(https://github.com/danbri/factoidal/issues/864). The compiler runs `tsUserUsedFast` in
its place (`tsUserUsed_eq_fast`, a `csimp` theorem). -/
def tsUserUsed (iris : List String) : PrefixTable → List String → PrefixTable
  | [], _ => []
  | (ns, label) :: rest, seenNs =>
      if seenNs.contains ns then tsUserUsed iris rest seenNs
      else if tsAnyIriUsesNs iris ns then (ns, label) :: tsUserUsed iris rest (ns :: seenNs)
      else tsUserUsed iris rest (ns :: seenNs)

/-- The namespaces of the index that some IRI of the list lies strictly under: for each
IRI, the namespaces of its candidates. -/
def usedNsLoop (ix : PrefixIndex) : List String → Std.HashSet String → Std.HashSet String
  | [], s => s
  | iri :: rest, s =>
      usedNsLoop ix rest ((ix.candidates iri).foldl (fun s c => s.insert c.2.1) s)

theorem candidatesFold_contains (x : String) :
    ∀ (cs : List (Nat × (String × String))) (s : Std.HashSet String),
      (cs.foldl (fun s c => s.insert c.2.1) s).contains x = true ↔
        s.contains x = true ∨ ∃ c ∈ cs, c.2.1 = x
  | [], s => by simp
  | c :: rest, s => by
      rw [List.foldl_cons, candidatesFold_contains x rest]
      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨y, hy, hx⟩)
        · exact Or.inr ⟨c, Or.inl rfl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨y, Or.inr hy, hx⟩
      · rintro (h | ⟨y, hy | hy, hx⟩)
        · exact Or.inl (Or.inr h)
        · subst hy; exact Or.inl (Or.inl hx)
        · exact Or.inr ⟨y, hy, hx⟩

theorem usedNsLoop_contains (ix : PrefixIndex) (x : String) :
    ∀ (iris : List String) (s : Std.HashSet String),
      (usedNsLoop ix iris s).contains x = true ↔
        s.contains x = true ∨ ∃ iri ∈ iris, ∃ c ∈ ix.candidates iri, c.2.1 = x
  | [], s => by simp [usedNsLoop]
  | iri :: rest, s => by
      rw [usedNsLoop, usedNsLoop_contains ix x rest, candidatesFold_contains]
      simp only [List.mem_cons]
      constructor
      · rintro ((h | ⟨c, hc, hx⟩) | ⟨i, hi, hx⟩)
        · exact Or.inl h
        · exact Or.inr ⟨iri, Or.inl rfl, c, hc, hx⟩
        · obtain ⟨c, hc, hx⟩ := hx
          exact Or.inr ⟨i, Or.inr hi, c, hc, hx⟩
      · rintro (h | ⟨i, hi | hi, c, hc, hx⟩)
        · exact Or.inl (Or.inl h)
        · subst hi; exact Or.inl (Or.inr ⟨c, hc, hx⟩)
        · exact Or.inr ⟨i, hi, c, hc, hx⟩

/-- For a namespace of the table, the set holds it exactly when some IRI lies strictly
under it. -/
theorem usedNs_eq_any (T : PrefixTable) (iris : List String) (e : String × String)
    (he : e ∈ T) :
    (usedNsLoop (PrefixIndex.ofTable T) iris ∅).contains e.1 = tsAnyIriUsesNs iris e.1 := by
  rw [Bool.eq_iff_iff, usedNsLoop_contains]
  simp only [Std.HashSet.contains_empty, Bool.false_eq_true, false_or, tsAnyIriUsesNs,
    List.any_eq_true]
  constructor
  · rintro ⟨iri, hi, c, hc, hx⟩
    exact ⟨iri, hi, hx ▸ (mem_candidates hc).2.1⟩
  · rintro ⟨iri, hi, hp⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    obtain ⟨c, hc, hc1, _⟩ := candidate_of_row hj hp
    exact ⟨iri, hi, c, hc, hc1⟩

/-- The loop of `tsUserUsedFast`. `used` holds the namespaces that some IRI lies under,
`seen` the namespaces met so far, and `acc` the pairs kept, newest first. Every call of
the loop on itself is a tail call. -/
def tsUserUsedLoop (used : Std.HashSet String) :
    PrefixTable → Std.HashSet String → PrefixTable → PrefixTable
  | [], _, acc => acc.reverse
  | (ns, label) :: rest, seen, acc =>
      if seen.contains ns then tsUserUsedLoop used rest seen acc
      else if used.contains ns then tsUserUsedLoop used rest (seen.insert ns) ((ns, label) :: acc)
      else tsUserUsedLoop used rest (seen.insert ns) acc

/-- The loop, for every state it can be in: the pairs kept so far, then the
specification on the rest of the table, when the hash set `seenS` holds the strings of
the list `seenL` and `used` agrees with `tsAnyIriUsesNs` on the table. -/
theorem tsUserUsedLoop_eq (iris : List String) (used : Std.HashSet String) :
    ∀ (l : PrefixTable) (seenS : Std.HashSet String) (seenL : List String) (acc : PrefixTable),
      (∀ x, seenS.contains x = seenL.contains x) →
      (∀ e ∈ l, used.contains e.1 = tsAnyIriUsesNs iris e.1) →
      tsUserUsedLoop used l seenS acc = acc.reverse ++ tsUserUsed iris l seenL
  | [], seenS, seenL, acc, _, _ => by simp [tsUserUsedLoop, tsUserUsed]
  | (ns, label) :: rest, seenS, seenL, acc, hseen, hused => by
      have hu : used.contains ns = tsAnyIriUsesNs iris ns :=
        hused (ns, label) (List.mem_cons_self ..)
      have hrest : ∀ e ∈ rest, used.contains e.1 = tsAnyIriUsesNs iris e.1 :=
        fun e he => hused e (List.mem_cons_of_mem _ he)
      have hins : ∀ x, (seenS.insert ns).contains x = (ns :: seenL).contains x := by
        intro x
        have hc : (ns == x) = (x == ns) := by
          rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
          exact ⟨Eq.symm, Eq.symm⟩
        rw [Std.HashSet.contains_insert, hseen x, List.contains_cons, hc]
      unfold tsUserUsedLoop tsUserUsed
      by_cases h1 : seenL.contains ns = true
      · have h1' : seenS.contains ns = true := by rw [hseen]; exact h1
        rw [if_pos h1', if_pos h1]
        exact tsUserUsedLoop_eq iris used rest seenS seenL acc hseen hrest
      · have h1' : ¬ seenS.contains ns = true := by rw [hseen]; exact h1
        rw [if_neg h1', if_neg h1]
        by_cases h2 : tsAnyIriUsesNs iris ns = true
        · have h2' : used.contains ns = true := by rw [hu]; exact h2
          rw [if_pos h2', if_pos h2,
            tsUserUsedLoop_eq iris used rest _ _ ((ns, label) :: acc) hins hrest]
          simp
        · have h2' : ¬ used.contains ns = true := by rw [hu]; exact h2
          rw [if_neg h2', if_neg h2, tsUserUsedLoop_eq iris used rest _ _ acc hins hrest]

/-- `tsUserUsed` as a loop over the table, with the namespaces that some IRI uses found
by the index and the namespaces seen held in a hash set. -/
def tsUserUsedFast (iris : List String) (table : PrefixTable) (seen : List String) :
    PrefixTable :=
  tsUserUsedLoop (usedNsLoop (PrefixIndex.ofTable table) iris ∅) table (Std.HashSet.ofList seen) []

theorem tsUserUsedFast_eq (iris : List String) (table : PrefixTable) (seen : List String) :
    tsUserUsedFast iris table seen = tsUserUsed iris table seen := by
  unfold tsUserUsedFast
  have := tsUserUsedLoop_eq iris (usedNsLoop (PrefixIndex.ofTable table) iris ∅) table
    (Std.HashSet.ofList seen) seen []
    (fun x => Std.HashSet.contains_ofList)
    (fun e he => usedNs_eq_any table iris e he)
  simpa using this

/-- Any call of the specification runs the loop. `turtleOfGraphOpts` is compiled after
this line, so the Turtle writer takes no frame for a prefix of the caller's table and
no time quadratic in it. -/
@[csimp] theorem tsUserUsed_eq_fast : @tsUserUsed = @tsUserUsedFast := by
  funext iris table seen; exact (tsUserUsedFast_eq iris table seen).symm

#print axioms usedNs_eq_any
#print axioms tsUserUsedLoop_eq
#print axioms tsUserUsedFast_eq
#print axioms tsUserUsed_eq_fast

/-- `ns1:` … `ns8:`, skipping any label already taken by the caller's table or
the well-known table, so a caller label `ns1:` is never given to another
namespace. `idx` only grows, which is the termination measure. Port of
`assign_labels_avoiding`. -/
def assignLabelsAvoiding (reserved : List String) :
    (fuel : Nat) → (idx : Nat) → List (String × Nat) → List (String × String)
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, idx, (ns, n) :: rest =>
      if idx ≥ 9 then []
      else
        let label := "ns" ++ toString idx ++ ":"
        if reserved.contains label then assignLabelsAvoiding reserved fuel (idx + 1) ((ns, n) :: rest)
        else (ns, label) :: assignLabelsAvoiding reserved fuel (idx + 1) rest

/-- The numbered namespaces: the `budget` most frequent namespaces of the graph that no
earlier row of the table covers.

This is the SPECIFICATION. It filters every namespace of the graph, also when `budget` is
0, which is the case once the caller's rows and the well-known rows are 8 or more: the
filter takes `C * |coveredNs|` comparisons for `C` namespaces, which is 10^10 for 100,000
namespaces of the caller's table (https://github.com/danbri/factoidal/issues/864). The
compiler runs `freshTopFast` in its place (`freshTopSpec_eq_fast`, a `csimp` theorem). -/
def freshTopSpec (counted : List (String × Nat)) (coveredNs : List String) (budget : Nat) :
    List (String × Nat) :=
  ((sortByCountDesc counted).filter (fun p => !coveredNs.contains p.1)).take budget

/-- `freshTopSpec`, which takes no namespace when the budget is 0 and so need not look at
any. With a budget above 0 the rows covered number fewer than 8. -/
def freshTopFast (counted : List (String × Nat)) (coveredNs : List String) (budget : Nat) :
    List (String × Nat) :=
  if budget = 0 then [] else freshTopSpec counted coveredNs budget

theorem freshTopFast_eq (counted : List (String × Nat)) (coveredNs : List String)
    (budget : Nat) : freshTopFast counted coveredNs budget = freshTopSpec counted coveredNs budget := by
  unfold freshTopFast
  by_cases h : budget = 0
  · subst h; simp [freshTopSpec]
  · simp [h]

@[csimp] theorem freshTopSpec_eq_fast : @freshTopSpec = @freshTopFast := by
  funext counted coveredNs budget; exact (freshTopFast_eq counted coveredNs budget).symm

#print axioms freshTopSpec_eq_fast

/-- The prefix table for a graph and its options, then the document. Caller
pairs first, then the well-known labels the graph uses, then at most
`8 - (those)` numbered ones for the most frequent remaining namespaces. Port of
`turtle_of_graph_opts`. -/
def turtleOfGraphOpts (opts : TurtleRenderOptions) (g : Graph) : String :=
  let iris := collectIris g
  let counted := countRuns (sortStrs (candidateNamespaces iris))
  let presentNs := counted.map (·.1)
  let userUsed := tsUserUsed iris opts.prefixes []
  let userNs := userUsed.map (·.1)
  let userLabels := userUsed.map (·.2)
  let known := (wellKnownPrefixes.filter (fun p => presentNs.contains p.1)).filter
    (fun p => !userNs.contains p.1 && !userLabels.contains p.2)
  let knownNs := known.map (·.1)
  let knownLabels := known.map (·.2)
  let coveredNs := userNs ++ knownNs
  let coveredLen := userUsed.length + known.length
  let budget := if coveredLen ≥ 8 then 0 else 8 - coveredLen
  let freshTop := freshTopSpec counted coveredNs budget
  let auto := assignLabelsAvoiding (userLabels ++ knownLabels) 10 1 freshTop
  turtleOfGraph (userUsed ++ known ++ auto) opts.literalShorthand g

/-- The default rendering: no caller prefixes, bare literals on. -/
def turtleOfGraphAuto (g : Graph) : String := turtleOfGraphOpts {} g

/-! ## Build-time checks

### Abbreviation happens only when the parser would read it back -/

private def wi (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩

private def exTable : PrefixTable := [("http://example.org/", "ex:")]

#guard tsAbbreviateIri exTable "http://example.org/a" == "ex:a"
#guard tsAbbreviateIri exTable "http://other.org/a" == "<http://other.org/a>"

/-! A local part the parser would reject is NOT compacted: a space
    cannot appear in `PN_LOCAL`, so the full form is emitted. -/

#guard tsAbbreviateIri exTable "http://example.org/a b"
       == "<http://example.org/a b>"

/-! The strict prefix test needs the IRI to be LONGER than the
    namespace, so an IRI equal to it does not compact. -/

#guard tsAbbreviateIri exTable "http://example.org/" == "<http://example.org/>"

/-! ### `rdf:type` renders as `a`, in PREDICATE position only -/

#guard tsPredicateToTurtle [] rdfType == "a"
#guard tsPredicateToTurtle exTable (wi "http://example.org/p") == "ex:p"
#guard tsTermToTurtle [] true (.iri rdfType) ==
       "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"

/-! ### Literals -/

private def litT (lex : String) (dt : String) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := wi dt,
                       langTag := none, direction := none }
  if h : literalWf l then .literal ⟨l, h⟩ else .bnode "bad"

#guard tsTermToTurtle [] true (litT "x" "http://www.w3.org/2001/XMLSchema#string")
       == "\"x\""
-- With shorthand OFF the quoted form is the only one (the pre-681 behaviour).
#guard tsTermToTurtle [("http://www.w3.org/2001/XMLSchema#", "xsd:")] false
         (litT "1" "http://www.w3.org/2001/XMLSchema#integer") == "\"1\"^^xsd:integer"
#guard tsTermToTurtle [] true (litT "a\"b" "http://www.w3.org/2001/XMLSchema#string")
       == "\"a\\\"b\""

/-! ### Bare literals: the grammar terminals, in both directions

A bare form is printed only when the lexical form is exactly an INTEGER,
DECIMAL, DOUBLE or BooleanLiteral of the literal's own datatype. -/

private def xsd (n : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ n
private def bare (lex dt : String) : String := tsTermToTurtle [] true (litT lex (xsd dt))
private def quoted (lex dt : String) : String := tsTermToTurtle [] false (litT lex (xsd dt))

#guard bare "42" "integer" == "42"
#guard bare "-7" "integer" == "-7"
#guard bare "+7" "integer" == "+7"
#guard bare "0" "integer" == "0"
#guard bare "1.5" "decimal" == "1.5"
#guard bare ".5" "decimal" == ".5"
#guard bare "-0.50" "decimal" == "-0.50"
#guard bare "1e3" "double" == "1e3"
#guard bare "1.5E-3" "double" == "1.5E-3"
#guard bare "1.e3" "double" == "1.e3"
#guard bare ".5e+2" "double" == ".5e+2"
#guard bare "true" "boolean" == "true"
#guard bare "false" "boolean" == "false"
-- Not a terminal of the datatype's own production: stays quoted.
#guard bare "" "integer" == "\"\"^^<" ++ xsd "integer" ++ ">"
#guard bare "+" "integer" == "\"+\"^^<" ++ xsd "integer" ++ ">"
#guard bare "1.0" "integer" == "\"1.0\"^^<" ++ xsd "integer" ++ ">"
#guard bare " 1" "integer" == "\" 1\"^^<" ++ xsd "integer" ++ ">"
#guard bare "5." "decimal" == "\"5.\"^^<" ++ xsd "decimal" ++ ">"
#guard bare "5" "decimal" == "\"5\"^^<" ++ xsd "decimal" ++ ">"
#guard bare "." "decimal" == "\".\"^^<" ++ xsd "decimal" ++ ">"
#guard bare "1.5" "double" == "\"1.5\"^^<" ++ xsd "double" ++ ">"
#guard bare "1e" "double" == "\"1e\"^^<" ++ xsd "double" ++ ">"
#guard bare "e5" "double" == "\"e5\"^^<" ++ xsd "double" ++ ">"
#guard bare "INF" "double" == "\"INF\"^^<" ++ xsd "double" ++ ">"
#guard bare "1" "boolean" == "\"1\"^^<" ++ xsd "boolean" ++ ">"
#guard bare "True" "boolean" == "\"True\"^^<" ++ xsd "boolean" ++ ">"
-- The datatype decides: a digit string typed as a string or a date is quoted.
#guard bare "42" "string" == "\"42\""
#guard bare "42" "long" == "\"42\"^^<" ++ xsd "long" ++ ">"
-- Turned off, every one of them is quoted.
#guard quoted "42" "integer" == "\"42\"^^<" ++ xsd "integer" ++ ">"
#guard quoted "true" "boolean" == "\"true\"^^<" ++ xsd "boolean" ++ ">"

-- Whole-graph output: the bare form reads back to the same graph, the quoted
-- form too, and the two differ.
private def numGraph : Graph :=
  [ ⟨.iri (wi "http://x/a"), wi "http://x/n", litT "42" (xsd "integer")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/d", litT "1.5" (xsd "decimal")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/e", litT "1e3" (xsd "double")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/b", litT "true" (xsd "boolean")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/q", litT "5." (xsd "decimal")⟩ ]

#guard ((turtleOfGraphOpts {} numGraph).splitOn "^^").length == 2
#guard ((turtleOfGraphOpts { literalShorthand := false } numGraph).splitOn "^^").length == 6
#guard (match parseTurtle (turtleOfGraphOpts {} numGraph) none .rdf12 with
        | .ok g2 => sortTriples g2 == sortTriples numGraph
        | .error _ => false)
#guard (match parseTurtle (turtleOfGraphOpts { literalShorthand := false } numGraph) none .rdf12 with
        | .ok g2 => sortTriples g2 == sortTriples numGraph
        | .error _ => false)

/-! ### Caller prefixes win, and are emitted only when used -/

private def exOpts : TurtleRenderOptions :=
  { prefixes := [("http://x/", "ex:"), ("http://unused.example/", "un:")] }

#guard ((turtleOfGraphOpts exOpts numGraph).splitOn "@prefix ex: <http://x/> .").length == 2
-- A namespace no IRI uses gets no header line.
#guard ((turtleOfGraphOpts exOpts numGraph).splitOn "un:").length == 1
-- The caller's label is the one used in the body.
#guard ((turtleOfGraphOpts exOpts numGraph).splitOn "ex:a ex:").length == 2
-- Without a caller table the derived one names the same namespace `ns1:`.
#guard ((turtleOfGraphOpts {} numGraph).splitOn "@prefix ns1: <http://x/> .").length == 2
-- A derived label never takes one the caller used: `ns1:` is reserved here.
private def ns1Taken : TurtleRenderOptions := { prefixes := [("http://y/", "ns1:")] }
private def twoNs : Graph :=
  [ ⟨.iri (wi "http://y/a"), wi "http://x/p", .iri (wi "http://x/b")⟩ ]
#guard ((turtleOfGraphOpts ns1Taken twoNs).splitOn "@prefix ns1: <http://y/> .").length == 2
#guard ((turtleOfGraphOpts ns1Taken twoNs).splitOn "@prefix ns2: <http://x/> .").length == 2
-- The first occurrence of a namespace wins over a later repeat.
private def dup : TurtleRenderOptions :=
  { prefixes := [("http://x/", "ex:"), ("http://x/", "other:")] }
#guard ((turtleOfGraphOpts dup numGraph).splitOn "other:").length == 1
-- Ties in count keep their order: `ns1:` goes to the namespace that sorts first.
private def tie : Graph :=
  [ ⟨.iri (wi "http://b.example/a"), wi "http://a.example/p", .iri (wi "http://c.example/c")⟩ ]
#guard ((turtleOfGraphOpts {} tie).splitOn "@prefix ns1: <http://a.example/> .").length == 2

/-! ### The round trip, through the real parser

The F\* banner records that this could not be proved OR
`assert_norm`-witnessed there, because the literal path goes through
byte primitives that stay opaque to the solver. In Lean these are
ordinary computable functions, so the round trip is checkable — at
these shapes, which is evidence and not a theorem. -/

private def g1 : Graph :=
  [ ⟨.iri (wi "http://example.org/a"), rdfType, .iri (wi "http://example.org/C")⟩
  , ⟨.iri (wi "http://example.org/a"), wi "http://example.org/p",
     .iri (wi "http://example.org/b")⟩
  , ⟨.iri (wi "http://example.org/a"), wi "http://example.org/p",
     litT "hello" "http://www.w3.org/2001/XMLSchema#string"⟩
  , ⟨.bnode "b0", wi "http://example.org/q",
     litT "a\"b\\c" "http://www.w3.org/2001/XMLSchema#string"⟩ ]

private def roundTrips (g : Graph) : Bool :=
  match parseTurtle (turtleOfGraphAuto g) none .rdf12 with
  | .error _ => false
  | .ok g2 => sortTriples g2 == sortTriples g

#guard roundTrips g1
#guard roundTrips []
#guard roundTrips [⟨.iri (wi "http://x/y"), wi "http://x/p", .iri (wi "http://x/z")⟩]

/-! An IRI that cannot be compacted round-trips through the `<…>`
    fallback. -/

#guard roundTrips [⟨.iri (wi "http://x/a"), wi "http://x/p",
                    litT "1" "http://www.w3.org/2001/XMLSchema#integer"⟩]

/-! ### Grouping: `;` between predicates, `,` between objects -/

#guard ((turtleOfGraphAuto g1).splitOn " ;\n    ").length == 2
#guard ((turtleOfGraphAuto g1).splitOn " , ").length == 2

/-! ### The auto table prefers a well-known label over a numbered one -/

#guard ((turtleOfGraphAuto
  [⟨.iri (wi "http://example.org/a"), rdfType,
    .iri (wi "http://www.w3.org/2000/01/rdf-schema#Class")⟩]).splitOn
  "@prefix rdfs:").length == 2

/-! ### Issue 864: the index, the loop for terms and the fast user-prefix filter

The call of `tsTermToTurtle`, `tsUserUsed` or `turtleOfGraph` below runs the loop or the
index, because the `csimp` theorems come first in this file; their equalities with the
specifications are theorems (`tsTermToTurtle_eq_fast`, `tsUserUsed_eq_fast`,
`turtleOfGraph_eq_fast`). These checks pin the text of concrete cases, among them the
first-row rule (the FIRST row of the table whose namespace is a proper prefix of the IRI,
not the longest) in both the scan and the index. -/

private def nested3 : Term :=
  .tripleTerm (.iri (wi "http://x/s")) (wi "http://x/p")
    (.tripleTerm (.bnode "b") rdfType
      (.tripleTerm (.iri (wi "http://x/s")) (wi "http://x/q")
        (litT "v" "http://www.w3.org/2001/XMLSchema#string")))

#guard tsTermToTurtle [("http://x/", "x:")] true nested3 ==
  "<<( x:s x:p <<( _:b a <<( x:s x:q \"v\" )>> )>> )>>"
#guard tsTermToTurtleFast [("http://x/", "x:")] true nested3 ==
  "<<( x:s x:p <<( _:b a <<( x:s x:q \"v\" )>> )>> )>>"
#guard tsTermToTurtleBy (tsAbbreviateIri []) true nested3 ==
  "<<( <http://x/s> <http://x/p> <<( _:b a <<( <http://x/s> <http://x/q> \"v\" )>> )>> )>>"

private def nestN (s : Subject) (p : WfIri) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => nestN s p n (.tripleTerm s p t)

-- 100,000 levels: 30 characters to open a level, 4 to close it, 3 for the literal
#guard (tsTermToTurtle [] true (nestN (.iri (wi "http://x/s")) (wi "http://x/p") 100000
  (litT "v" "http://www.w3.org/2001/XMLSchema#string"))).length == 3400003

-- 300 rows with 3 lengths of a namespace: more than `prefixIndexRatio` rows for each
-- length, so the writer indexes it
private def wideTable : PrefixTable :=
  (List.range 300).map fun i => (s!"http://e/n{i}/", s!"n{i}:")

private def padded (head : PrefixTable) : PrefixTable := head ++ wideTable

#guard (Abbreviator.ofTable wideTable).isIndexed
#guard !(Abbreviator.ofTable [("http://e/", "e:")]).isIndexed
#guard !(Abbreviator.ofTable (wideTable.take 100)).isIndexed
#guard (Abbreviator.ofTable wideTable).run "http://e/n7/x" == "n7:x"
#guard (Abbreviator.ofTable wideTable).run "http://e/n7/" == "<http://e/n7/>"
#guard (Abbreviator.ofTable wideTable).run "http://e/n300/x" == "<http://e/n300/x>"
#guard (Abbreviator.ofTable [("http://e/", "a:")]).run "http://e/x" == "a:x"
#guard (Abbreviator.ofTable (padded [("http://e/n7/", "b:"), ("http://e/", "a:")])).run "http://e/n7/x" == "b:x"
#guard (Abbreviator.ofTable (padded [("http://e/", "a:"), ("http://e/n7/", "b:")])).run "http://e/n7/x" ==
  "<http://e/n7/x>"
#guard tsAbbreviateIri (padded [("http://e/", "a:"), ("http://e/n7/", "b:")]) "http://e/n7/x" ==
  "<http://e/n7/x>"
-- the first row of a namespace wins, and an empty namespace is a proper prefix of every IRI
#guard (Abbreviator.ofTable (padded [("http://e/n7/", "b:"), ("http://e/n7/", "c:")])).run "http://e/n7/x" == "b:x"
#guard (Abbreviator.ofTable (padded [("", "z:")])).run "abc" == "z:abc"
#guard (Abbreviator.ofTable (padded [("é/", "u:")])).run "é/x" == "u:x"

#guard tsUserUsed ["http://e/a", "http://f/b"]
  [("http://e/", "e:"), ("http://g/", "g:"), ("http://e/", "e2:"), ("http://f/", "f:")] [] ==
  [("http://e/", "e:"), ("http://f/", "f:")]
#guard tsUserUsed ["http://e/a"] [("http://e/", "e:"), ("http://f/", "f:")] ["http://e/"] == []
#guard tsUserUsed ["http://e/"] [("http://e/", "e:")] [] == []

private def manyNs (n : Nat) : PrefixTable :=
  (List.range n).map fun i => (s!"http://e/n{i}/", s!"n{i}:")

private def manyIris (n : Nat) : List String :=
  (List.range n).map fun i => s!"http://e/n{i}/s"

-- 20,000 used prefixes, and the same table in the writer
#guard (tsUserUsed (manyIris 20000) (manyNs 20000) []).length == 20000
#guard ((turtleOfGraphOpts { prefixes := manyNs 3000 }
  ((List.range 3000).map fun i =>
    (⟨.iri (wi s!"http://e/n{i}/s"), wi "http://e/p", .iri (wi s!"http://e/n{i}/o")⟩ : Triple))
  ).splitOn "@prefix ").length == 3001

end L4Factoidal.Syntax
