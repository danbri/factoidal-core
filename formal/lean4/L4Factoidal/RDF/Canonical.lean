/-
L4Factoidal.RDF.Canonical — RDF Dataset Canonicalization 1.0 (RDFC-1.0).

Spec: https://www.w3.org/TR/rdf-canon/ (W3C Recommendation, 2024).
Port of `formal/fstar/RDF.Canonical.fst` (the F* module that passes the
W3C `rdf-canon` suite; it is the spec of record for every edge case
where the prose leaves a choice open).

What this module implements, with the spec sections each step cites:

  * §3  — canonical N-Quads form: the serialisation of one quad, the
          literal escaping table, and "sort the serialised quads in
          code point order".
  * §4.5 (Hash First Degree Quads) — per blank node, render its
          incident quads with the node itself as `_:a` and every other
          blank node as `_:z`, sort, concatenate, hash.
  * §4.6 (Hash Related Blank Node) — position tag + predicate +
          identifier, hashed.
  * §4.7 (Hash N-Degree Quads) — the bucket map over related blank
          nodes and the permutation loop, run through a cloned
          ("temporary") issuer.
  * §4.8 (Issue Identifier) — sequential `c14n0`, `c14n1`, … for the
          canonical issuer; `b0`, `b1`, … for each temporary one.
  * §4.4 (canonicalization algorithm) — two passes over the
          hash-to-blank-nodes map: unique hashes first, then the
          collision groups.

ASSUMPTION REPORT (the point of the port). The F* module has exactly
two `assume val`s — `hash_sha256` and `hash_sha384`, realised outside
F* by hand-written OCaml. Both are REPLACED here by the pure Lean
SHA-2 of `L4Factoidal.Crypto.SHA2`, reached only through the
`HashAlgorithm` parameter (`Crypto.hashHex`), per the hash-agility
rule: no function in this file names `sha256`/`sha384` directly.
Nothing else in the F* module was assumed, and nothing else is assumed
here: no `sorry`, no `axiom`, no `native_decide`, no `partial`.

DIFFERENCES FROM THE F* SOURCE, all deliberate and all listed:

  1. Termination. F* bounds the Hash-N-Degree-Quads recursion with a
     lexicographic `decreases %[fuel; phase; list]` over a six-function
     mutual block. Here the same shape is obtained without any mutual
     recursion: `hndqRun` is structurally recursive on its fuel and
     hands the "recurse one level down" closure (`HndqRec`) to the
     bucket/permutation walkers, each of which is structurally
     recursive on its own list. Consequence: one fuel unit is spent
     per HNDQ level instead of the F* source's two. Fuel is seeded at
     `bnodes + 1` in both, and in both it is a totality device that no
     real input reaches (each level issues at least one fresh blank
     node), so this is strictly more generous, never less.
  2. Permutation cap. Mirrored from F*, NOT silently: each bucket's
     related-blank-node list is truncated to `permutationCap = 6`
     members before permuting (`720` permutations per bucket). A
     dataset with a symmetric collision bucket wider than 6 therefore
     gets a RESULT VARIANT, not the spec's answer. See
     `permutationCap` for the full statement.
  3. Work budget. Mirrored from F*: `hndqBudget` counts calls to Hash
     N-Degree Quads and makes the §4.4 "excessive calls" abort
     explicit (`canonicalizeExceedsBudget`), so a poison input is a
     reported abort rather than a wrong answer.
  4. Sorting. F* uses a merge sort (its inputs reach 100k+ lines).
     `sortBy` here is a STABLE INSERTION SORT: the same total preorder,
     the same stable tie-breaking, and short enough to prove sorted
     (`RDF/CanonicalTheorems.lean`). It is the specification of the
     sort and costs O(n^2): 4,000 quads took 25 s (2026-10-10). The
     algorithm runs `sortByFast`, `List.mergeSort`, at the five places
     where the input grows with the dataset, and
     `CanonicalTheorems.sortBy_eq_mergeSort` proves the two return the
     same list for every total preorder, ties included. The whole W3C
     corpus is under 50 lines per file, so the suites cannot see the
     difference; `tests/stack/lean_scaling.sh` can.
  5. Not ported: the F* module's Section 6b/6c "bounded neighbour
     hash" ladder (`compute_all_nbr1`/`nbr2`/`nbr3`, `bn_full_key`,
     `sort_full_keys`). Those are dead code in the F* tree — an
     earlier phase's approximation of HNDQ, no longer reachable from
     `build_canonical_mapping_alg_budgeted`. Grep-confirmed before
     omitting them.
  6. Not ported: the F* performance machinery whose only purpose is
     the OCaml extraction's cost model (byte-level `fs_byte_at`
     scanning, the accumulator/`rev` rewrites of every list build).
     Where a plain definition was measured to cost time or stack, a
     fast twin sits beside it with a proved `csimp` equality, and the
     definition stays as written: the merge sort (item 4), the
     accumulator forms of `dedupAdj` and `collapseKeyedQQuads`, the
     §4.4 step 2 blank node to quads map (`bnodeQuadIndex`, replacing a
     filter over every quad per blank node) and a search tree for
     relabelling (`labelTree`, the role of F*'s `bn_lookup_tree`);
     https://github.com/danbri/factoidal/issues/745. The Hash N-Degree
     Quads path still filters every quad per call:
     https://github.com/danbri/factoidal/issues/751.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.Crypto.SHA2
import Std.Data.TreeMap

namespace L4Factoidal.RDF.Canonical

open L4Factoidal.Crypto

/-! ## Code-point ordering

RDFC-1.0 §3 requires the serialised quads to be sorted "in code point
order". The F* source compares UTF-8 BYTES (and documents why that is
the same relative order: byte-wise comparison of valid UTF-8 agrees
with code-point comparison). Lean strings are already code-point
sequences, so the comparison is direct. -/

/-- Lexicographic ≤ over code-point lists — the total preorder every
sort in this module uses. -/
def charsLe : List Char → List Char → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs =>
      if a.val < b.val then true
      else if b.val < a.val then false
      else charsLe as bs

/-- Code-point ≤ over strings (RDFC-1.0 §3, "code point order"). -/
def strLe (a b : String) : Bool := charsLe a.toList b.toList

/-! ### The comparison the compiler emits

`strLe` builds two character lists for every comparison. On a graph of 2,000
IRIs without blank nodes that conversion (`lean_string_data`) and the list walk
are 57 percent of the instructions of `canonicalize`, after the sorts were
changed to merge sorts (survey of 2026-10-10,
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`). Lean's order on
`String` is the same lexicographic order on code points, and its decision
procedure is native code. `strLe_eq_not_lt` proves the equality; the `csimp`
theorem makes every function compiled after this point call `strLeFast`. The
definition of `strLe` and every theorem about it do not change. -/

private theorem char_lt_iff (x y : Char) : x < y ↔ x.val.toNat < y.val.toNat :=
  UInt32.lt_iff_toNat_lt

private theorem char_eq_of_not_lt {x y : Char} (h1 : ¬ x.val < y.val)
    (h2 : ¬ y.val < x.val) : x = y := by
  apply Char.ext
  exact UInt32.le_antisymm (UInt32.not_lt.1 h2) (UInt32.not_lt.1 h1)

/-- `charsLe` is the negation of Lean's list order read backwards. -/
theorem charsLe_eq_not_lt : ∀ (as bs : List Char), charsLe as bs = !decide (bs < as)
  | [], bs => by
      cases bs with
      | nil => simp [charsLe]
      | cons b bs => simp [charsLe, List.not_lt_nil]
  | a :: as, [] => by simp [charsLe, List.nil_lt_cons]
  | a :: as, b :: bs => by
      have ih := charsLe_eq_not_lt as bs
      have key : (b :: bs < a :: as) ↔ (b < a ∨ b = a ∧ bs < as) := List.cons_lt_cons_iff
      simp only [charsLe]
      by_cases h1 : a.val < b.val
      · have h1' := (UInt32.lt_iff_toNat_lt).1 h1
        have hn : ¬ (b :: bs < a :: as) := by
          rw [key]
          rintro (h | ⟨h, _⟩)
          · have := (char_lt_iff b a).1 h; omega
          · subst h; omega
        simp [h1, hn]
      · by_cases h2 : b.val < a.val
        · have hp : (b :: bs < a :: as) := key.2 (Or.inl h2)
          simp [h1, h2, hp]
        · have heq : b = a := (char_eq_of_not_lt h2 h1)
          have hiff : (b :: bs < a :: as) ↔ bs < as := by
            rw [key]
            constructor
            · rintro (h | ⟨_, h⟩)
              · exact absurd h h2
              · exact h
            · intro h; exact Or.inr ⟨heq, h⟩
          simp [h1, h2, ih, hiff]

theorem strLe_eq_not_lt (a b : String) : strLe a b = !decide (b < a) := by
  unfold strLe
  rw [charsLe_eq_not_lt]
  rfl

/-- `strLe` through Lean's native string order. -/
def strLeFast (a b : String) : Bool := !decide (b < a)

/-- The compiler calls `strLeFast` wherever the source says `strLe`. -/
@[csimp] theorem strLe_eq_strLeFast : @strLe = @strLeFast :=
  funext fun a => funext fun b => strLe_eq_not_lt a b

/-! ## Stable insertion sort

Stability matters: RDFC-1.0 §4.4 step 5.3 orders exploration results
"by hash" but leaves ties undefined, and the F* source resolves them
first-explored-wins. Inserting each element after every element it
compares ≥ to, folding left, reproduces exactly that. -/

/-- Insert `x` after every element `y` of the (already sorted) list
with `le y x`. -/
def insertSortedBy (le : α → α → Bool) (x : α) : List α → List α
  | []      => [x]
  | y :: ys => if le y x then y :: insertSortedBy le x ys else x :: y :: ys

/-- `insertSortedBy` with the passed prefix on a reverse accumulator: a tail
call per element. `sortBy` runs on the blank nodes left unissued after a
budget is exhausted, as many as the dataset has (https://github.com/danbri/factoidal/issues/746). -/
def insertSortedByTR (le : α → α → Bool) (x : α) (ys : List α) : List α := go ys []
where
  go : List α → List α → List α
    | [], acc => (x :: acc).reverse
    | y :: ys, acc => if le y x then go ys (y :: acc) else acc.reverse ++ x :: y :: ys

theorem insertSortedByTR_go_eq (le : α → α → Bool) (x : α) :
    ∀ (ys acc : List α), insertSortedByTR.go le x ys acc = acc.reverse ++ insertSortedBy le x ys
  | [], acc => by simp [insertSortedByTR.go, insertSortedBy]
  | y :: ys, acc => by
      simp only [insertSortedByTR.go, insertSortedBy]
      split <;> rename_i h <;> simp [h, insertSortedByTR_go_eq le x ys]

@[csimp] theorem insertSortedBy_eq_TR : @insertSortedBy = @insertSortedByTR := by
  funext α le x ys; simp [insertSortedByTR, insertSortedByTR_go_eq]

/-- Stable insertion sort under the total preorder `le`. -/
def sortBy (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldl (fun acc x => insertSortedBy le x acc) []

/-- The sort the algorithm runs: `List.mergeSort`, O(n log n) and stable.
`CanonicalTheorems.sortBy_eq_mergeSort` proves it returns exactly what
`sortBy` returns whenever `le` is transitive and total, and every
comparator passed to it below is `strLe` on a projection. -/
def sortByFast (le : α → α → Bool) (xs : List α) : List α := xs.mergeSort le

/-- Sort strings into code-point order (RDFC-1.0 §3). -/
def sortStrings (xs : List String) : List String := sortByFast strLe xs

/-- Drop adjacent duplicates from a sorted list — RDF set semantics
(RDF 1.1 Concepts §4: a dataset's quads form a set). The F* source
does this both before hashing (so a repeated quad cannot double a
blank node's first-degree contribution) and on the output lines. -/
def dedupAdj : List String → List String
  | []           => []
  | [x]          => [x]
  | x :: y :: rest =>
      if x == y then dedupAdj (y :: rest) else x :: dedupAdj (y :: rest)

/-- `dedupAdj` with an accumulator. `dedupAdj` conses after its recursive
call: one stack frame per line. In the wasm module under Node's default
stack, `canonicalize` of 24,000 quads ran out of stack here after
`collapseKeyedQQuads` was repaired
(https://github.com/danbri/factoidal/issues/713 stage 5). The `csimp`
theorem below makes the compiler emit this form for every call. -/
def dedupAdjTR : List String → List String
  | []        => []
  | x :: rest => go x rest []
where
  /-- `x` is the last survivor so far; `acc` holds the earlier ones, newest
  first. -/
  go (x : String) : List String → List String → List String
    | [],        acc => (x :: acc).reverse
    | y :: rest, acc => if x == y then go y rest acc else go y rest (x :: acc)

theorem dedupAdjTR_go_eq :
    ∀ (rest : List String) (x : String) (acc : List String),
      dedupAdjTR.go x rest acc = acc.reverse ++ dedupAdj (x :: rest)
  | [], x, acc => by simp [dedupAdjTR.go, dedupAdj]
  | y :: rest, x, acc => by
      by_cases h : (x == y) = true
      · simp [dedupAdjTR.go, dedupAdj, h, dedupAdjTR_go_eq rest y acc]
      · simp [dedupAdjTR.go, dedupAdj, h, dedupAdjTR_go_eq rest y (x :: acc)]

@[csimp] theorem dedupAdj_eq_dedupAdjTR : @dedupAdj = @dedupAdjTR := by
  funext xs
  cases xs with
  | nil => rfl
  | cons x rest => simp [dedupAdjTR, dedupAdjTR_go_eq]

/-- Concatenate a list of strings. -/
def joinStrings (xs : List String) : String := xs.foldl (· ++ ·) ""

/-! ## §3 — canonical N-Quads serialisation

Deliberately NOT reusing `Syntax.NTriples.Term.toNTriples`: that is the
EMIT-MINIMAL wire form (its own module header says so), which escapes
only `\ " \n \r \t`. The canonical form additionally escapes every
remaining C0 control character and DEL as an uppercase-hex `\u00XX`,
and passes non-ASCII through as raw UTF-8. -/

/-- One uppercase hex digit. Out-of-range maps to `'0'` to stay total;
`escapeChar` only ever passes values below 16. -/
def hexDigitUC (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n)
  else if n < 16 then Char.ofNat (0x41 + (n - 10))
  else '0'

/-- The canonical N-Quads escape of one character inside a literal's
lexical form (RDFC-1.0 §3 → N-Triples canonical literal form): the five
short mnemonics plus `\"` and `\\`, every other C0 control character
and DEL as `\u00XX` with UPPERCASE hex, everything else raw. -/
def escapeChar (c : Char) : String :=
  if c == '\\' then "\\\\"
  else if c == '"' then "\\\""
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.val == 0x08 then "\\b"
  else if c.val == 0x0C then "\\f"
  else if c.val < 0x20 || c.val == 0x7F then
    let b := c.val.toNat
    String.ofList ['\\', 'u', '0', '0', hexDigitUC ((b / 16) % 16), hexDigitUC (b % 16)]
  else String.singleton c

/-- Escape a literal's lexical form for canonical N-Quads. -/
def escapeLit (s : String) : String :=
  joinStrings (s.toList.map escapeChar)

/-- Canonical N-Quads form of a subject (RDFC-1.0 §3). -/
def canonSubject : Subject → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b

/-- Canonical N-Quads form of a term (RDFC-1.0 §3; RDF 1.2 triple
terms use the `<<( s p o )>>` form, directional literals the
`--ltr`/`--rtl` suffix). -/
def canonTerm : Term → String
  | .iri i   => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal wl =>
      let l := wl.val
      let lex := escapeLit l.lexicalForm
      match l.langTag with
      | some tag =>
          let dirSuffix := match l.direction with
            | some .ltr => "--ltr"
            | some .rtl => "--rtl"
            | none      => ""
          "\"" ++ lex ++ "\"@" ++ tag ++ dirSuffix
      | none =>
          if l.datatype == xsdString then "\"" ++ lex ++ "\""
          else "\"" ++ lex ++ "\"^^<" ++ l.datatype.val ++ ">"
  | .tripleTerm s p o =>
      "<<( " ++ canonSubject s ++ " <" ++ p.val ++ "> " ++ canonTerm o ++ " )>>"

/-! ### Blank-node graph names

RDF 1.1 Concepts §4 lets a graph name be an IRI or a blank node, and
RDFC-1.0 treats a blank-node graph name as a blank node in every step
that reasons over blank nodes (§4.5's placeholder rewrite, §4.7's
related-component walk, §4.4's label issuing). `RDF.NamedGraph.name` is
a `Subject`, so the graph slot needs no encoding of its own: its
canonical N-Quads form is `canonSubject`, the very function the subject
slot uses. -/

/-- Canonical N-Quads form of a graph name (RDFC-1.0 §3): `<iri>` or
`_:label`. -/
def canonGraphName (g : Subject) : String := canonSubject g

/-! ## Quads with graph names

RDFC-1.0 reasons over quads; the default graph is the `none` graph
name. -/

/-- A quad: an optional graph name (IRI or blank node) plus a triple. -/
abbrev QQuad := Option Subject × Triple

/-- Canonical N-Quads line for one quad, `" .\n"`-terminated
(RDFC-1.0 §3). -/
def canonQuad (q : QQuad) : String :=
  let (g, t) := q
  let gs := match g with
    | some gi => " " ++ canonGraphName gi
    | none    => ""
  canonSubject t.s ++ " <" ++ t.p.val ++ "> " ++ canonTerm t.o ++ gs ++ " .\n"

/-- Flatten a dataset into quads: default graph first, then each named
graph in order. -/
def datasetQuads (ds : Dataset) : List QQuad :=
  ds.default.map (fun t => (none, t)) ++
  ds.named.flatMap (fun ng => ng.graph.map (fun t => (some ng.name, t)))

/-- Sort quads by their canonical rendering and drop duplicates (RDF
set semantics). The F* source does this before hashing so a quad
repeated in the input syntax cannot double a blank node's first-degree
contribution (W3C tests test076 / test077). Ordering the survivors by
rendering also fixes the order in which HNDQ buckets are filled, so
mirroring it exactly matters for tie-breaks. -/
def collapseKeyedQQuads : List (String × QQuad) → List QQuad
  | []            => []
  | [(_, q)]      => [q]
  | (k1, q1) :: (k2, q2) :: rest =>
      if k1 == k2 then collapseKeyedQQuads ((k2, q2) :: rest)
      else q1 :: collapseKeyedQQuads ((k2, q2) :: rest)

/-- `collapseKeyedQQuads` with an accumulator. `collapseKeyedQQuads` conses
after its recursive call: one stack frame per quad. In the wasm module under
Node's default stack, `canonicalize` of 24,000 quads ran out of stack here
("Maximum call stack size exceeded";
https://github.com/danbri/factoidal/issues/713 stage 5). The `csimp` theorem
below makes the compiler emit this form for every call. -/
def collapseKeyedQQuadsTR : List (String × QQuad) → List QQuad
  | []             => []
  | (k, q) :: rest => go k q rest []
where
  /-- `q`, keyed `k`, is the last survivor so far; `acc` holds the earlier
  survivors, newest first. -/
  go (k : String) (q : QQuad) : List (String × QQuad) → List QQuad → List QQuad
    | [],                acc => (q :: acc).reverse
    | (k2, q2) :: rest,  acc =>
        if k == k2 then go k2 q2 rest acc else go k2 q2 rest (q :: acc)

theorem collapseKeyedQQuadsTR_go_eq :
    ∀ (rest : List (String × QQuad)) (k : String) (q : QQuad) (acc : List QQuad),
      collapseKeyedQQuadsTR.go k q rest acc =
        acc.reverse ++ collapseKeyedQQuads ((k, q) :: rest)
  | [], k, q, acc => by simp [collapseKeyedQQuadsTR.go, collapseKeyedQQuads]
  | (k2, q2) :: rest, k, q, acc => by
      by_cases h : (k == k2) = true
      · simp [collapseKeyedQQuadsTR.go, collapseKeyedQQuads, h,
          collapseKeyedQQuadsTR_go_eq rest k2 q2 acc]
      · simp [collapseKeyedQQuadsTR.go, collapseKeyedQQuads, h,
          collapseKeyedQQuadsTR_go_eq rest k2 q2 (q :: acc)]

@[csimp] theorem collapseKeyedQQuads_eq_TR : @collapseKeyedQQuads = @collapseKeyedQQuadsTR := by
  funext xs
  cases xs with
  | nil => rfl
  | cons p rest =>
      obtain ⟨k, q⟩ := p
      simp [collapseKeyedQQuadsTR, collapseKeyedQQuadsTR_go_eq]

def dedupQQuads (qs : List QQuad) : List QQuad :=
  collapseKeyedQQuads (sortByFast (fun a b => strLe a.1 b.1) (qs.map (fun q => (canonQuad q, q))))

/-! ## Blank-node enumeration -/

/-- Blank nodes occurring in a term, including inside RDF 1.2 triple
terms (they must be issued canonical identifiers too). -/
def bnodesInTerm : Term → List BNodeId
  | .bnode b          => [b]
  | .tripleTerm s _ o =>
      (match s with | .bnode b => [b] | _ => []) ++ bnodesInTerm o
  | _                 => []

/-- Blank nodes occurring anywhere in a quad: subject, object (
recursively), and the graph-name slot. -/
def bnodesInQuad (q : QQuad) : List BNodeId :=
  let (g, t) := q
  (match t.s with | .bnode b => [b] | _ => []) ++
  bnodesInTerm t.o ++
  (match g with
   | some (.bnode b) => [b]
   | _               => [])

/-- Sort and deduplicate a list of labels. -/
def dedupStrings (xs : List String) : List String := dedupAdj (sortStrings xs)

/-- Every blank node of the dataset, ascending, without duplicates. -/
def datasetBnodes (ds : Dataset) : List BNodeId :=
  dedupStrings ((datasetQuads ds).flatMap bnodesInQuad)

/-! ## §4.5 — Hash First Degree Quads

"For each quad in which the blank node occurs, serialise it with the
node itself replaced by `_:a` and every other blank node replaced by
`_:z`; sort those serialisations in code point order; concatenate;
hash." The `_:a` / `_:z` placeholders are what makes the result
independent of the input labels. -/

def rewriteSubjectForHfdq (target : BNodeId) : Subject → Subject
  | .bnode b => .bnode (if b == target then "a" else "z")
  | s        => s

def rewriteTermForHfdq (target : BNodeId) : Term → Term
  | .bnode b => .bnode (if b == target then "a" else "z")
  | .tripleTerm s p o =>
      .tripleTerm (rewriteSubjectForHfdq target s) p (rewriteTermForHfdq target o)
  | t        => t

def rewriteTripleForHfdq (target : BNodeId) (t : Triple) : Triple :=
  { s := rewriteSubjectForHfdq target t.s, p := t.p,
    o := rewriteTermForHfdq target t.o }

/-- Graph-name slot under the §4.5 rewrite: own label → `_:a`, another
blank node → `_:z`, IRI graph and default graph unchanged. -/
def rewriteGraphForHfdq (target : BNodeId) : Option Subject → Option Subject
  | none              => none
  | some (.bnode b)   => some (.bnode (if b == target then "a" else "z"))
  | some (.iri i)     => some (.iri i)

/-- Does this quad mention `target` in any slot? -/
def quadMentionsBnode (target : BNodeId) (q : QQuad) : Bool :=
  let (g, t) := q
  (match t.s with | .bnode b => b == target | _ => false) ||
  (bnodesInTerm t.o).contains target ||
  (match g with
   | some (.bnode b) => b == target
   | _               => false)

/-- The quads a blank node occurs in, input order preserved. -/
def quadsForBnode (target : BNodeId) (qs : List QQuad) : List QQuad :=
  qs.filter (quadMentionsBnode target)

/-- One quad rendered under the §4.5 placeholder rewrite. -/
def renderForHfdq (target : BNodeId) (q : QQuad) : String :=
  let (g, t) := q
  canonQuad (rewriteGraphForHfdq target g, rewriteTripleForHfdq target t)

/-- RDFC-1.0 §4.5 — Hash First Degree Quads. Parameterised by the hash
algorithm (§4.4 note: SHA-256 is the default; the test manifests select
SHA-384 with `rdfc:hashAlgorithm`). -/
def hashFirstDegreeQuads (alg : HashAlgorithm) (target : BNodeId)
    (qs : List QQuad) : String :=
  hashHex alg (joinStrings (sortStrings ((quadsForBnode target qs).map (renderForHfdq target))))

/-! ## §4.8 — Issue Identifier

An issuer holds a label prefix, a counter, and the identifiers issued
so far. The canonical issuer's prefix is `c14n` (§4.4 step 1: "an
identifier issuer initialized with the prefix `c14n`"); each temporary
issuer cloned during §4.7 uses the prefix `b` (§4.4 step 5.2). The
temporary prefix is spec-visible, not cosmetic: those labels are
embedded in the §4.7 path strings, so using `c14n` for them would
change every N-degree hash. -/

/-- One decimal digit. Written as an explicit ten-way match (rather
than `Char.ofNat (0x30 + d)`) so `CanonicalTheorems` can invert it by
`rfl` on each case — that inversion is what makes the issued labels
provably distinct. Out-of-range maps to `'0'` to stay total. -/
def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | 9 => '9'
  | _ => '0'

/-- Decimal digits of a natural number, most significant first. -/
def natToDigits (n : Nat) : List Char :=
  if n < 10 then [digitChar n]
  else natToDigits (n / 10) ++ [digitChar (n % 10)]
decreasing_by omega

/-- Decimal rendering of a natural number. -/
def natToString (n : Nat) : String := String.ofList (natToDigits n)

/-- The label an issuer with prefix `pfx` mints for counter value `n` —
`c14n0`, `c14n1`, … or `b0`, `b1`, …. Built on the character list so
that `CanonicalTheorems` can reason about it without unfolding
`String.append`. -/
def mkLabel (pfx : String) (n : Nat) : String := String.ofList (pfx.toList ++ natToDigits n)

/-- RDFC-1.0 §4.8 identifier issuer state. -/
structure IssuerState where
  labelPrefix : String
  counter : Nat
  issued  : List (BNodeId × String)
  deriving Repr

/-- The canonical issuer (§4.4 step 1). -/
def emptyIssuer : IssuerState := { labelPrefix := "c14n", counter := 0, issued := [] }

/-- A temporary issuer for one §4.7 exploration (§4.4 step 5.2). -/
def emptyTempIssuer : IssuerState := { labelPrefix := "b", counter := 0, issued := [] }

def lookupIssued (b : BNodeId) : List (BNodeId × String) → Option String
  | []            => none
  | (k, v) :: rest => if k == b then some v else lookupIssued b rest

/-- RDFC-1.0 §4.8: return the existing identifier if this blank node
already has one, otherwise mint the next one and record it. -/
def issueIdentifier (st : IssuerState) (b : BNodeId) : IssuerState × String :=
  match lookupIssued b st.issued with
  | some v => (st, v)
  | none   =>
      let label := mkLabel st.labelPrefix st.counter
      ({ st with counter := st.counter + 1, issued := st.issued ++ [(b, label)] }, label)

/-- Issue without the already-issued check — only used where the
caller has partitioned the blank nodes so that `b` is provably fresh
(`assignSingletons` below: each hash group is disjoint and every
singleton member is visited once). -/
def issueFresh (st : IssuerState) (b : BNodeId) : IssuerState :=
  { st with counter := st.counter + 1, issued := (b, mkLabel st.labelPrefix st.counter) :: st.issued }

/-! ## §4.6 — Hash Related Blank Node -/

/-- RDFC-1.0 §4.6: input is the position tag, then `<predicate>` unless
the position is `g`, then the related node's identifier; hash it. -/
def hashRelatedBlankNode (alg : HashAlgorithm) (pos pred identifier : String) : String :=
  hashHex alg (pos ++ (if pos != "g" then "<" ++ pred ++ ">" else "") ++ identifier)

/-! ## §4.7 — Hash N-Degree Quads -/

/-- One entry of the §4.7 "hash to related blank nodes" map: the §4.6
hash, and the related blank nodes that produced it. -/
abbrev Bucket := String × List BNodeId

/-- Insert `b` under key `k`, keeping the bucket list sorted by key and
each bucket's members in insertion order (§4.7 step 3.1). -/
def bucketInsert (k : String) (b : BNodeId) : List Bucket → List Bucket
  | [] => [(k, [b])]
  | (k', members) :: rest =>
      if k == k' then (k', members ++ [b]) :: rest
      else if strLe k k' then (k, [b]) :: (k', members) :: rest
      else (k', members) :: bucketInsert k b rest

/-- RDFC-1.0 §4.7 step 3.1: every blank-node COMPONENT of an incident
quad other than `target`, tagged with the slot it occupies. One quad
can contribute up to three entries (`_:s <p> _:o _:g` seen from `_:s`
yields an `o` entry and a `g` entry); a quad whose only blank node is
`target` contributes none — it was fully accounted for by §4.5. -/
def graphBnodeOf (q : QQuad) : Option BNodeId :=
  match q.1 with
  | some (.bnode b) => some b
  | _               => none

def relatedComponents (target : BNodeId) (q : QQuad) : List (String × BNodeId) :=
  let (_, t) := q
  (match t.s with | .bnode b => if b != target then [("s", b)] else [] | _ => []) ++
  (match t.o with | .bnode b => if b != target then [("o", b)] else [] | _ => []) ++
  (match graphBnodeOf q with | some b => if b != target then [("g", b)] else [] | none => [])

/-- §4.6 step 3: the identifier of a related node is its canonical
label if it already has one, else this exploration's temporary label,
else its first-degree hash. -/
def lookupIssued2 (b : BNodeId) (canonSt localSt : IssuerState) : Option String :=
  match lookupIssued b canonSt.issued with
  | some lbl => some lbl
  | none     => lookupIssued b localSt.issued

def lookupHfdq (b : BNodeId) : List (BNodeId × String) → String
  | []            => ""
  | (k, h) :: rest => if k == b then h else lookupHfdq b rest

def insertRelatedEntries (alg : HashAlgorithm) (pred : String)
    (hfdqTable : List (BNodeId × String)) (canonSt localSt : IssuerState) :
    List (String × BNodeId) → List Bucket → List Bucket
  | [],              acc => acc
  | (pos, rb) :: rest, acc =>
      let identifier := match lookupIssued2 rb canonSt localSt with
        | some lbl => "_:" ++ lbl
        | none     => lookupHfdq rb hfdqTable
      insertRelatedEntries alg pred hfdqTable canonSt localSt rest
        (bucketInsert (hashRelatedBlankNode alg pos pred identifier) rb acc)

/-- Build the §4.7 "hash to related blank nodes" map for `target`. -/
def buildBucketsFor (alg : HashAlgorithm) (target : BNodeId)
    (hfdqTable : List (BNodeId × String)) (canonSt localSt : IssuerState) :
    List QQuad → List Bucket → List Bucket
  | [],       acc => acc
  | q :: rest, acc =>
      if !quadMentionsBnode target q then
        buildBucketsFor alg target hfdqTable canonSt localSt rest acc
      else
        buildBucketsFor alg target hfdqTable canonSt localSt rest
          (insertRelatedEntries alg q.2.p.val hfdqTable canonSt localSt
            (relatedComponents target q) acc)

/-! ### The permutation loop (§4.7 step 5)

`permutationCap` is a RESULT VARIANT, stated here rather than buried:
RDFC-1.0 §4.7 enumerates EVERY permutation of a bucket's related blank
nodes. Both the F* source and this port truncate the bucket to its
first `permutationCap` members first, so at most `permutationCap!`
permutations are explored. For every dataset in the W3C `rdf-canon`
suite no bucket exceeds this width, so the enumerated set is the
complete one and the result is the spec's. For a symmetric graph with a
wider bucket the output is deterministic and self-consistent but NOT
guaranteed to be the spec's canonical form. Removing the cap requires
either the §4.4 "excessive calls" abort (which `hndqBudget` below
already provides) or a real automorphism search. -/
def permutationCap : Nat := 6

/-- Every way to insert `x` into `ys`, in the F* source's order (front
first) — the order matters because §4.7 step 5.4.5 keeps the FIRST
permutation attaining the lowest hash. -/
def insertAtAll (x : BNodeId) : List BNodeId → List (List BNodeId)
  | []      => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAtAll x ys).map (fun zs => y :: zs)

/-- All permutations of a list, in the F* source's enumeration order.
Structurally recursive, so the "permutations of a list are finite"
bound is the list's own structure — no fuel needed here. -/
def permutationsOf : List BNodeId → List (List BNodeId)
  | []       => [[]]
  | hd :: tl => (permutationsOf tl).foldl (fun acc p => acc ++ insertAtAll hd p) []

/-! ### The §4.4 "excessive calls" budget

RDFC-1.0 §4.4 requires an implementation to be able to abort on inputs
that provoke excessive calls to Hash N-Degree Quads (the W3C suite's
`RDFC10NegativeEvalTest`, e.g. its poison-clique fixture). The budget
counts `hndqRun` invocations and latches once spent, so exploration
unwinds in depth-proportional time instead of continuing a
combinatorial blow-up. -/
structure HndqBudget where
  remaining : Nat
  exceeded  : Bool
  deriving Repr

def hbInit (n : Nat) : HndqBudget := { remaining := n, exceeded := false }

def hbConsume (b : HndqBudget) : HndqBudget :=
  if b.exceeded then b
  else if b.remaining == 0 then { b with exceeded := true }
  else { b with remaining := b.remaining - 1 }

/-- The result triple every step of the §4.7 walk threads: the hash (or
path string) built so far, the temporary issuer, and the budget. -/
abbrev HndqOut := String × IssuerState × HndqBudget

/-- "Run Hash N-Degree Quads one level down", as a closure: takes the
temporary issuer, the target node, and the budget. Passing this
explicitly is what removes the F* source's mutual recursion. -/
abbrev HndqRec := IssuerState → BNodeId → HndqBudget → HndqOut

/-- RDFC-1.0 §4.7 step 5.4.4, first pass over a permutation: every
member contributes its `_:label` — already issued (canonically or
locally) or freshly issued here — concatenated with NO separator.
Members freshly issued here are returned, in order, as the list the
second pass recurses into. -/
def buildPathLabels (canonSt : IssuerState) : IssuerState → List BNodeId → String →
    List BNodeId → String × IssuerState × List BNodeId
  | localSt, [],        path, recursion => (path, localSt, recursion)
  | localSt, b :: rest, path, recursion =>
      match lookupIssued2 b canonSt localSt with
      | some lbl => buildPathLabels canonSt localSt rest (path ++ "_:" ++ lbl) recursion
      | none     =>
          let (local1, lbl) := issueIdentifier localSt b
          buildPathLabels canonSt local1 rest (path ++ "_:" ++ lbl) (recursion ++ [b])

/-- RDFC-1.0 §4.7 step 5.4.5, second pass: recurse into each freshly
issued member, appending `_:<label><recursive hash>`. -/
def walkRecursion (rec : HndqRec) : IssuerState → List BNodeId → String → HndqBudget → HndqOut
  | localSt, [],        path, hb => (path, localSt, hb)
  | localSt, b :: rest, path, hb =>
      if hb.exceeded then (path, localSt, hb)
      else
        -- `b` was issued by `buildPathLabels`; `issueIdentifier` is
        -- idempotent, so this recovers the same label.
        let (local1, lbl) := issueIdentifier localSt b
        let (subHash, local2, hb1) := rec local1 b hb
        walkRecursion rec local2 rest (path ++ "_:" ++ lbl ++ "<" ++ subHash ++ ">") hb1

/-- One permutation: label pass, then recursion pass (§4.7 step 5.4). -/
def walkPerm (rec : HndqRec) (canonSt localSt : IssuerState) (perm : List BNodeId)
    (path : String) (hb : HndqBudget) : HndqOut :=
  let (path1, local1, recursion) := buildPathLabels canonSt localSt perm path []
  walkRecursion rec local1 recursion path1 hb

/-- Keep the lowest path hash, first one wins on a tie (§4.7 step
5.4.6 orders by hash; the tie is left open by the spec and settled
first-explored-wins, matching the F* source). -/
def pickBest (rec : HndqRec) (canonSt localStInitial : IssuerState) :
    List (List BNodeId) → String → IssuerState → HndqBudget → HndqOut
  | [],       bestHash, bestSt, hb => (bestHash, bestSt, hb)
  | p :: rest, bestHash, bestSt, hb =>
      if hb.exceeded then (bestHash, bestSt, hb)
      else
        let (h, st', hb1) := walkPerm rec canonSt localStInitial p "" hb
        let (bestHash', bestSt') :=
          if strLe h bestHash && h != bestHash then (h, st') else (bestHash, bestSt)
        pickBest rec canonSt localStInitial rest bestHash' bestSt' hb1

/-- §4.7 step 5.4: explore every permutation of one bucket. -/
def bestPermutation (rec : HndqRec) (canonSt localSt : IssuerState)
    (perms : List (List BNodeId)) (hb : HndqBudget) : HndqOut :=
  match perms with
  | []       => ("", localSt, hb)
  | p :: rest =>
      if hb.exceeded then ("", localSt, hb)
      else
        let (h, st', hb1) := walkPerm rec canonSt localSt p "" hb
        pickBest rec canonSt localSt rest h st' hb1

/-- §4.7 step 5: walk the buckets in key order, appending each key and
its winning permutation hash to the data-to-hash string; hash the
result (§4.7 step 6). -/
def walkBuckets (alg : HashAlgorithm) (rec : HndqRec) (canonSt : IssuerState) :
    IssuerState → List Bucket → String → HndqBudget → HndqOut
  | localSt, [],                 data, hb => (hashHex alg data, localSt, hb)
  | localSt, (k, members) :: rest, data, hb =>
      if hb.exceeded then (hashHex alg data, localSt, hb)
      else
        let perms := permutationsOf (members.take permutationCap)
        let (bestHash, bestSt, hb1) := bestPermutation rec canonSt localSt perms hb
        walkBuckets alg rec canonSt bestSt rest (data ++ k ++ bestHash) hb1

/-- RDFC-1.0 §4.7 — Hash N-Degree Quads.

Totality: structural recursion on `fuel`. `fuel` is seeded at
`|blank nodes| + 1`; each level issues at least one previously
unissued blank node, so no real input reaches the `0` case (it returns
the empty hash, the same defensive answer the F* source gives). The
permutation enumeration inside a level is bounded by the structure of
the (capped) bucket list, not by fuel. -/
def hndqRun (alg : HashAlgorithm) (qs : List QQuad) (hfdqTable : List (BNodeId × String))
    (canonSt : IssuerState) : Nat → IssuerState → BNodeId → HndqBudget → HndqOut
  | 0,        localSt, _,      hb => ("", localSt, hbConsume hb)
  | fuel + 1, localSt, target, hb =>
      let hb1 := hbConsume hb
      if hb1.exceeded then ("", localSt, hb1)
      else
        let buckets := buildBucketsFor alg target hfdqTable canonSt localSt qs []
        walkBuckets alg (hndqRun alg qs hfdqTable canonSt fuel) canonSt localSt buckets "" hb1

/-! ## §4.4 — the canonicalization algorithm -/

/-- The §4.4 "hash to blank nodes" map: blank nodes grouped by their
first-degree hash, groups in code-point order of the hash, members in
ascending label order (which is `datasetBnodes`' order — a stable sort
keeps it). -/
def groupSortedHfdq : List (BNodeId × String) → String → List BNodeId → List Bucket →
    List Bucket
  | [],             curH, curMembers, acc => ((curH, curMembers.reverse) :: acc).reverse
  | (b, h) :: rest, curH, curMembers, acc =>
      if h == curH then groupSortedHfdq rest curH (b :: curMembers) acc
      else groupSortedHfdq rest h [b] ((curH, curMembers.reverse) :: acc)

def groupByHfdq (table : List (BNodeId × String)) : List Bucket :=
  match sortByFast (fun a b => strLe a.2 b.2) table with
  | []               => []
  | (b0, h0) :: rest => groupSortedHfdq rest h0 [b0] []

/-- §4.4 step 4: every blank node whose first-degree hash is unique
gets its canonical identifier now, in hash order. This whole pass runs
BEFORE step 5 — interleaving the two would hand out different absolute
`c14nN` numbers whenever a unique hash sorts between two colliding
ones. -/
def assignSingletons (st : IssuerState) : List Bucket → IssuerState
  | []                => st
  | (_, [b]) :: rest  => assignSingletons (issueFresh st b) rest
  | (_, _) :: rest    => assignSingletons st rest

def filterUnissued (st : IssuerState) (xs : List BNodeId) : List BNodeId :=
  xs.filter (fun b => (lookupIssued b st.issued).isNone)

/-- §4.4 step 5.2: explore EVERY not-yet-issued member of a collision
group, each with its own fresh temporary issuer (only the canonical
issuer is shared, and only read). -/
def exploreMembers (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) (canonSt : IssuerState) :
    List BNodeId → HndqBudget → List (String × List (BNodeId × String)) × HndqBudget
  | [],       hb => ([], hb)
  | m :: rest, hb =>
      if hb.exceeded then ([], hb)
      else match lookupIssued m canonSt.issued with
        | some _ => exploreMembers alg fuel qs hfdqTable canonSt rest hb
        | none   =>
            let (local1, _) := issueIdentifier emptyTempIssuer m
            let (h, local2, hb1) := hndqRun alg qs hfdqTable canonSt fuel local1 m hb
            let (restResults, hb2) := exploreMembers alg fuel qs hfdqTable canonSt rest hb1
            ((h, local2.issued) :: restResults, hb2)

/-- §4.4 step 5.3: in ascending-hash order, replay every identifier the
winning exploration touched into the canonical issuer. -/
def replayOne (canonSt : IssuerState) : List (BNodeId × String) → IssuerState
  | []            => canonSt
  | (b, _) :: rest => replayOne (issueIdentifier canonSt b).1 rest

def replayAll (canonSt : IssuerState) :
    List (String × List (BNodeId × String)) → IssuerState
  | []                  => canonSt
  | (_, tempIssued) :: rest => replayAll (replayOne canonSt tempIssued) rest

def processCollisionMembers (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) (st : IssuerState) (members : List BNodeId)
    (hb : HndqBudget) : IssuerState × HndqBudget :=
  let (results, hb1) := exploreMembers alg fuel qs hfdqTable st members hb
  (replayAll st (sortByFast (fun a b => strLe a.1 b.1) results), hb1)

/-- §4.4 step 5: the collision groups, in hash order. -/
def processCollisionGroups (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) :
    IssuerState → List Bucket → HndqBudget → IssuerState × HndqBudget
  | st, [],                   hb => (st, hb)
  | st, (_, [_]) :: rest,     hb => processCollisionGroups alg fuel qs hfdqTable st rest hb
  | st, (_, members) :: rest, hb =>
      if hb.exceeded then (st, hb)
      else
        let (st', hb1) :=
          processCollisionMembers alg fuel qs hfdqTable st (filterUnissued st members) hb
        processCollisionGroups alg fuel qs hfdqTable st' rest hb1

/-- §4.4 steps 4 and 5, in that order. -/
def walkGroups (alg : HashAlgorithm) (fuel : Nat) (qs : List QQuad)
    (hfdqTable : List (BNodeId × String)) (st : IssuerState) (groups : List Bucket)
    (hb : HndqBudget) : IssuerState × HndqBudget :=
  processCollisionGroups alg fuel qs hfdqTable (assignSingletons st groups) groups hb

/-! ## Public entry points -/

/-- Practically unbounded budget for ordinary use. The whole W3C
`rdf-canon` corpus is orders of magnitude below it; only deliberately
pathological inputs reach it. -/
def defaultHndqBudget : Nat := 1000000

/-- The first-degree hash of every blank node, in ascending label
order (§4.4 step 3). -/
def hfdqTableOf (alg : HashAlgorithm) (ds : Dataset) (qs : List QQuad) :
    List (BNodeId × String) :=
  (datasetBnodes ds).map (fun b => (b, hashFirstDegreeQuads alg b qs))

/-! ### The blank node to quads map (§4.4 step 2)

`hashFirstDegreeQuads` finds the quads of its blank node with
`quadsForBnode`, a filter over EVERY quad of the dataset, and `hfdqTableOf`
calls it once per blank node: B blank nodes and Q quads cost B times Q
calls of `quadMentionsBnode`. On 8,000 blank nodes in 24,000 quads that was
192 million calls, and 61 to 70 percent of the instructions of
`l4factoidal canonicalize` at 2,000 blank nodes
(https://github.com/danbri/factoidal/issues/745). RDFC-1.0 §4.4 step 2 builds
the "blank node to quads map" once, with one pass over the quads.
`bnodeQuadIndex` is that map: a `Std.TreeMap` from a blank node to the quads
it occurs in, newest first. `quadsForBnodeIx_bnodeQuadIndex` proves that the
map returns, for every blank node, the list `quadsForBnode` returns, in the
same order, so `hfdqTableOf_eq_hfdqTableOfIx` holds for every dataset and the
`csimp` theorem makes the compiler emit the indexed form. -/

/-- The blank node to quads map, each list newest first. -/
abbrev QuadIndex := Std.TreeMap BNodeId (List QQuad) compare

/-- Add one quad to the map, under every blank node it mentions. Each new
list is built from `m`, the map BEFORE this quad, so a blank node that
occurs twice in the quad gets the quad once. -/
def indexQuad (m : QuadIndex) (q : QQuad) : QuadIndex :=
  (bnodesInQuad q).foldl (fun acc b => acc.insert b (q :: m.getD b [])) m

/-- RDFC-1.0 §4.4 step 2: the blank node to quads map of `qs`. -/
def bnodeQuadIndex (qs : List QQuad) : QuadIndex := qs.foldl indexQuad ∅

/-- The quads of `target`, in input order, read from the map. -/
def quadsForBnodeIx (ix : QuadIndex) (target : BNodeId) : List QQuad :=
  (ix.getD target []).reverse

private theorem quadIndex_getD_insert (t : QuadIndex) (a k : BNodeId) (v : List QQuad) :
    (t.insert k v).getD a [] = if k = a then v else t.getD a [] := by
  have := @Std.TreeMap.getD_insert _ _ _ t _ k a [] v
  simpa [Std.compare_eq_iff_eq] using this

private theorem foldl_insert_getD (m : QuadIndex) (q : QQuad) (a : BNodeId) :
    ∀ (L : List BNodeId) (acc : QuadIndex),
      (L.foldl (fun acc b => acc.insert b (q :: m.getD b [])) acc).getD a [] =
        if a ∈ L then q :: m.getD a [] else acc.getD a []
  | [], acc => by simp
  | c :: L, acc => by
      rw [List.foldl_cons, foldl_insert_getD m q a L, quadIndex_getD_insert]
      by_cases hL : a ∈ L
      · simp [hL]
      · by_cases hc : c = a
        · subst hc; simp
        · have hac : a ≠ c := fun h => hc h.symm
          simp [hL, hc, hac]

/-- A blank node is in `bnodesInQuad q` exactly when `quadMentionsBnode`
says the quad mentions it. -/
theorem mem_bnodesInQuad_iff (a : BNodeId) (q : QQuad) :
    a ∈ bnodesInQuad q ↔ quadMentionsBnode a q = true := by
  obtain ⟨g, t⟩ := q
  obtain ⟨s, p, o⟩ := t
  unfold bnodesInQuad quadMentionsBnode
  cases s <;> rcases g with _ | (_ | _) <;> simp <;> (try simp only [@eq_comm _ a]) <;> (try simp only [or_assoc])

theorem indexQuad_getD (m : QuadIndex) (q : QQuad) (a : BNodeId) :
    (indexQuad m q).getD a [] =
      if quadMentionsBnode a q then q :: m.getD a [] else m.getD a [] := by
  unfold indexQuad
  rw [foldl_insert_getD]
  by_cases h : quadMentionsBnode a q = true
  · simp [h, (mem_bnodesInQuad_iff a q).2 h]
  · have h' : a ∉ bnodesInQuad q := fun hm => h ((mem_bnodesInQuad_iff a q).1 hm)
    simp [h, h']

theorem foldl_indexQuad_getD (a : BNodeId) :
    ∀ (qs : List QQuad) (m : QuadIndex),
      (qs.foldl indexQuad m).getD a [] =
        (qs.filter (quadMentionsBnode a)).reverse ++ m.getD a []
  | [], m => by simp
  | q :: qs, m => by
      rw [List.foldl_cons, foldl_indexQuad_getD a qs, indexQuad_getD]
      by_cases h : quadMentionsBnode a q = true
      · simp [h]
      · simp [h]

/-- The map answers what the filter answers, for every blank node. -/
theorem quadsForBnodeIx_bnodeQuadIndex (qs : List QQuad) (a : BNodeId) :
    quadsForBnodeIx (bnodeQuadIndex qs) a = quadsForBnode a qs := by
  unfold quadsForBnodeIx bnodeQuadIndex quadsForBnode
  rw [foldl_indexQuad_getD]
  simp

/-- `hashFirstDegreeQuads` over the quads the map holds for `target`. -/
def hashFirstDegreeQuadsIx (alg : HashAlgorithm) (ix : QuadIndex) (target : BNodeId) :
    String :=
  hashHex alg (joinStrings (sortStrings ((quadsForBnodeIx ix target).map (renderForHfdq target))))

theorem hashFirstDegreeQuadsIx_eq (alg : HashAlgorithm) (qs : List QQuad) (b : BNodeId) :
    hashFirstDegreeQuadsIx alg (bnodeQuadIndex qs) b = hashFirstDegreeQuads alg b qs := by
  unfold hashFirstDegreeQuadsIx hashFirstDegreeQuads
  rw [quadsForBnodeIx_bnodeQuadIndex]

/-- `hfdqTableOf` with the map built once (§4.4 step 2) and read once per
blank node (§4.4 step 3). -/
def hfdqTableOfIx (alg : HashAlgorithm) (ds : Dataset) (qs : List QQuad) :
    List (BNodeId × String) :=
  let ix := bnodeQuadIndex qs
  (datasetBnodes ds).map (fun b => (b, hashFirstDegreeQuadsIx alg ix b))

theorem hfdqTableOf_eq_hfdqTableOfIx (alg : HashAlgorithm) (ds : Dataset) (qs : List QQuad) :
    hfdqTableOf alg ds qs = hfdqTableOfIx alg ds qs := by
  unfold hfdqTableOf hfdqTableOfIx
  simp only [hashFirstDegreeQuadsIx_eq]

/-- The compiler calls `hfdqTableOfIx` wherever the source says `hfdqTableOf`. -/
@[csimp] theorem hfdqTableOf_eq_Ix : @hfdqTableOf = @hfdqTableOfIx := by
  funext alg ds qs; exact hfdqTableOf_eq_hfdqTableOfIx alg ds qs

/-- The full §4.4 run under an explicit Hash-N-Degree-Quads budget.
`none` means the budget was spent before every blank node had a
canonical identifier — the §4.4 "excessive calls to Hash N-Degree
Quads" abort. -/
def buildCanonicalMappingBudgeted (alg : HashAlgorithm) (budget : Nat) (ds : Dataset) :
    Option (List (BNodeId × String)) :=
  let qs := dedupQQuads (datasetQuads ds)
  let bs := datasetBnodes ds
  let hfdqTable := hfdqTableOf alg ds qs
  let groups := groupByHfdq hfdqTable
  let (st, hb) := walkGroups alg (bs.length + 1) qs hfdqTable emptyIssuer groups (hbInit budget)
  if hb.exceeded then none
  else
    -- Defensive: any blank node still unissued (only reachable through
    -- fuel exhaustion) gets an identifier in (hash, label) order.
    let leftover := if st.issued.length == bs.length then [] else filterUnissued st bs
    let leftoverSorted :=
      sortBy (fun a b => if a.2 == b.2 then strLe a.1 b.1 else strLe a.2 b.2)
        (leftover.map (fun b => (b, lookupHfdq b hfdqTable)))
    some (leftoverSorted.foldl (fun s p => (issueIdentifier s p.1).1) st).issued

/-! ### Applying the map -/

def lookupMap (b : BNodeId) : List (BNodeId × String) → Option String
  | []             => none
  | (k, v) :: rest => if k == b then some v else lookupMap b rest

def relabelSubject (m : List (BNodeId × String)) : Subject → Subject
  | .bnode b => match lookupMap b m with | some l => .bnode l | none => .bnode b
  | s        => s

def relabelTerm (m : List (BNodeId × String)) : Term → Term
  | .bnode b => match lookupMap b m with | some l => .bnode l | none => .bnode b
  | .tripleTerm s p o => .tripleTerm (relabelSubject m s) p (relabelTerm m o)
  | t => t

def relabelTriple (m : List (BNodeId × String)) (t : Triple) : Triple :=
  { s := relabelSubject m t.s, p := t.p, o := relabelTerm m t.o }

/-- A blank-node graph name takes its canonical label like any other
blank node (RDF 1.1 Concepts §4 + RDFC-1.0 §4.4); an IRI name is
untouched. Same function as the subject slot, which is the point of
typing the name as a `Subject`. -/
def relabelGraphName (m : List (BNodeId × String)) (g : Subject) : Subject :=
  relabelSubject m g

def relabelDataset (m : List (BNodeId × String)) (ds : Dataset) : Dataset :=
  { default := ds.default.map (relabelTriple m),
    named := ds.named.map (fun ng =>
      { name := relabelGraphName m ng.name, graph := ng.graph.map (relabelTriple m) }) }

/-! ### Relabelling through a search tree

`relabelDataset` finds each blank node's canonical label with `lookupMap`, a
scan of the issued list, which has one entry per blank node: B blank nodes in
Q quads cost about Q times B comparisons (6.4 percent of the instructions of
`l4factoidal canonicalize` at 4,000 blank nodes, growing 4.7 times from 2,000;
https://github.com/danbri/factoidal/issues/745). `relabelDatasetBy` is the
same walk over any lookup function; `labelTree` holds the issued list in a
`Std.TreeMap` whose answer is the FIRST entry of each label, as `lookupMap`'s
is (`labelTree_get?`). The `csimp` theorem makes the compiler build the tree
once per dataset. -/

def relabelSubjectBy (look : BNodeId → Option String) : Subject → Subject
  | .bnode b => match look b with | some l => .bnode l | none => .bnode b
  | s        => s

def relabelTermBy (look : BNodeId → Option String) : Term → Term
  | .bnode b => match look b with | some l => .bnode l | none => .bnode b
  | .tripleTerm s p o => .tripleTerm (relabelSubjectBy look s) p (relabelTermBy look o)
  | t => t

def relabelTripleBy (look : BNodeId → Option String) (t : Triple) : Triple :=
  { s := relabelSubjectBy look t.s, p := t.p, o := relabelTermBy look t.o }

def relabelDatasetBy (look : BNodeId → Option String) (ds : Dataset) : Dataset :=
  { default := ds.default.map (relabelTripleBy look),
    named := ds.named.map (fun ng =>
      { name := relabelSubjectBy look ng.name, graph := ng.graph.map (relabelTripleBy look) }) }

theorem relabelSubject_eq_by (m : List (BNodeId × String)) (s : Subject) :
    relabelSubject m s = relabelSubjectBy (fun b => lookupMap b m) s := by
  cases s <;> rfl

theorem relabelTerm_eq_by (m : List (BNodeId × String)) :
    ∀ (t : Term), relabelTerm m t = relabelTermBy (fun b => lookupMap b m) t
  | .iri _ => rfl
  | .bnode _ => rfl
  | .literal _ => rfl
  | .tripleTerm s p o => by
      simp only [relabelTerm, relabelTermBy, relabelSubject_eq_by, relabelTerm_eq_by m o]

theorem relabelDataset_eq_by (m : List (BNodeId × String)) (ds : Dataset) :
    relabelDataset m ds = relabelDatasetBy (fun b => lookupMap b m) ds := by
  have ht : relabelTriple m = relabelTripleBy (fun b => lookupMap b m) := by
    funext t
    simp only [relabelTriple, relabelTripleBy, relabelSubject_eq_by, relabelTerm_eq_by]
  simp only [relabelDataset, relabelDatasetBy, relabelGraphName, ht, relabelSubject_eq_by]

/-- The issued list as a search tree. Inserting from the LAST entry to the
first leaves the first entry of each blank node in the tree. -/
def labelTree (m : List (BNodeId × String)) : Std.TreeMap BNodeId String compare :=
  m.reverse.foldl (fun t p => t.insert p.1 p.2) ∅

private theorem labelTree_foldr_get? (b : BNodeId) :
    ∀ (m : List (BNodeId × String)),
      (m.foldr (fun p t => t.insert p.1 p.2) (∅ : Std.TreeMap BNodeId String compare)).get? b =
        lookupMap b m
  | [] => by simp [lookupMap]
  | (k, v) :: rest => by
      have h := @Std.TreeMap.getElem?_insert _ _ _
        (rest.foldr (fun p t => t.insert p.1 p.2) (∅ : Std.TreeMap BNodeId String compare)) _ b k v
      simp only [Std.compare_eq_iff_eq] at h
      simp only [List.foldr_cons, Std.TreeMap.get?_eq_getElem?, h, lookupMap]
      rw [← Std.TreeMap.get?_eq_getElem?, labelTree_foldr_get? b rest]
      by_cases hk : k = b
      · simp [hk]
      · simp [hk]

/-- The tree answers what `lookupMap` answers, for every blank node. -/
theorem labelTree_get? (m : List (BNodeId × String)) (b : BNodeId) :
    (labelTree m).get? b = lookupMap b m := by
  unfold labelTree
  rw [List.foldl_reverse]
  exact labelTree_foldr_get? b m

/-- `relabelDataset` with the label map built once as a search tree. -/
def relabelDatasetFast (m : List (BNodeId × String)) (ds : Dataset) : Dataset :=
  let t := labelTree m
  relabelDatasetBy (fun b => t.get? b) ds

/-- The compiler calls `relabelDatasetFast` wherever the source says
`relabelDataset`. -/
@[csimp] theorem relabelDataset_eq_fast : @relabelDataset = @relabelDatasetFast := by
  funext m ds
  rw [relabelDataset_eq_by]
  unfold relabelDatasetFast
  simp only [labelTree_get?]

/-! ### Hash N-Degree Quads through the map, with an indexed issuer

When k blank nodes share one first-degree hash, §4.4 step 5 runs Hash
N-Degree Quads (§4.7) once for each of them. Two costs then grew with k
squared (https://github.com/danbri/factoidal/issues/751; callgrind, 4,000 blank
nodes: 3,139 of 5,168 million instructions in `buildBucketsFor`, 482 million in
the replay):

  1. `hndqRun` gave `buildBucketsFor` every quad of the dataset, and
     `buildBucketsFor` tested each one with `quadMentionsBnode`, once per call.
     A `csimp` theorem on `buildBucketsFor` alone would build the §4.4 step 2
     map once per call, so the map is built once, in
     `buildCanonicalMappingBudgetedFast`, and passed down.
  2. `IssuerState.issued` is a list: `issueIdentifier` scans it
     (`lookupIssued`) and appends at its end, and `filterUnissued`,
     `exploreMembers` and `lookupIssued2` scan it once per blank node.

The twins below run the same steps with `FIssuer`: the issued list held as
`front ++ backRev.reverse` (`issueFresh` adds to the front, `issueIdentifier`
to the back, each in constant time) and a search tree that answers
`lookupIssued` on that list (the field `tree_get`, carried by every value).
`FIssuer.toSpec` gives the `IssuerState` a value stands for. Every twin is
proved to give the definition's result through `toSpec` (`*_toSpec` and
`*_eq` below), and `buildCanonicalMappingBudgeted_eq_fast` makes the compiler
emit the twin for every caller: the issued identifiers, in the order the
definition gives them, are unchanged. -/

/-- A search tree from a blank node to a label (or a hash). -/
abbrev LabelTree := Std.TreeMap BNodeId String compare

theorem lookupIssued_eq_lookupMap (b : BNodeId) :
    ∀ (l : List (BNodeId × String)), lookupIssued b l = lookupMap b l
  | [] => rfl
  | (k, v) :: rest => by simp only [lookupIssued, lookupMap, lookupIssued_eq_lookupMap b rest]

theorem lookupHfdq_eq_lookupMap (b : BNodeId) :
    ∀ (l : List (BNodeId × String)), lookupHfdq b l = (lookupMap b l).getD ""
  | [] => rfl
  | (k, v) :: rest => by
      simp only [lookupHfdq, lookupMap, lookupHfdq_eq_lookupMap b rest]
      split <;> rfl

theorem labelTree_get?_insert (t : LabelTree) (k a : BNodeId) (v : String) :
    (t.insert k v).get? a = if k = a then some v else t.get? a := by
  have h := @Std.TreeMap.getElem?_insert _ _ _ t _ a k v
  simp only [Std.compare_eq_iff_eq] at h
  simp only [Std.TreeMap.get?_eq_getElem?, h]

/-- Adding a blank node that is not yet in the list at its end: a lookup of
any blank node answers as before, except for the new one. -/
theorem lookupIssued_append_fresh {b0 : BNodeId} (l : String) (b : BNodeId) :
    ∀ {L : List (BNodeId × String)}, lookupIssued b0 L = none →
      lookupIssued b (L ++ [(b0, l)]) = if b0 = b then some l else lookupIssued b L
  | [], _ => by
      by_cases h : b0 = b
      · simp [lookupIssued, h]
      · simp [lookupIssued, h]
  | (k, v) :: rest, h0 => by
      have hk : k ≠ b0 := by
        intro hk; subst hk; simp [lookupIssued] at h0
      have hrest : lookupIssued b0 rest = none := by
        simp only [lookupIssued] at h0
        split at h0
        · cases h0
        · exact h0
      simp only [List.cons_append, lookupIssued, lookupIssued_append_fresh l b hrest]
      by_cases hkb : k = b
      · subst hkb
        have hb0 : b0 ≠ k := fun h => hk h.symm
        simp [hb0]
      · by_cases hb : b0 = b
        · simp [hkb, hb]
        · simp [hkb, hb]

/-- An identifier issuer (§4.8) whose issued list is `front ++ backRev.reverse`
and whose `tree` answers `lookupIssued` on that list. -/
structure FIssuer where
  labelPrefix : String
  counter : Nat
  front : List (BNodeId × String)
  backRev : List (BNodeId × String)
  tree : LabelTree
  tree_get : ∀ b, tree.get? b = lookupIssued b (front ++ backRev.reverse)

/-- The issuer state a fast issuer stands for. -/
def FIssuer.toSpec (st : FIssuer) : IssuerState :=
  { labelPrefix := st.labelPrefix, counter := st.counter, issued := st.front ++ st.backRev.reverse }

/-- A fresh issuer with the label prefix `pfx`. -/
def FIssuer.empty (pfx : String) : FIssuer :=
  { labelPrefix := pfx, counter := 0, front := [], backRev := [], tree := ∅,
    tree_get := fun b => by simp [lookupIssued] }

theorem FIssuer.empty_toSpec_c14n : (FIssuer.empty "c14n").toSpec = emptyIssuer := rfl

theorem FIssuer.empty_toSpec_b : (FIssuer.empty "b").toSpec = emptyTempIssuer := rfl

theorem FIssuer.get?_eq (st : FIssuer) (b : BNodeId) :
    st.tree.get? b = lookupIssued b st.toSpec.issued := st.tree_get b

/-- Issue a label to a blank node the issuer has not seen. -/
def FIssuer.issueNew (st : FIssuer) (b : BNodeId) (h : st.tree.get? b = none) : FIssuer :=
  { labelPrefix := st.labelPrefix, counter := st.counter + 1, front := st.front,
    backRev := (b, mkLabel st.labelPrefix st.counter) :: st.backRev,
    tree := st.tree.insert b (mkLabel st.labelPrefix st.counter),
    tree_get := fun a => by
      rw [labelTree_get?_insert, List.reverse_cons, ← List.append_assoc,
        lookupIssued_append_fresh _ _ (by rw [← st.tree_get]; exact h), st.tree_get] }

/-- `issueIdentifier` (§4.8) on a fast issuer. -/
def FIssuer.issue (st : FIssuer) (b : BNodeId) : FIssuer × String :=
  match h : st.tree.get? b with
  | some v => (st, v)
  | none => (st.issueNew b h, mkLabel st.labelPrefix st.counter)

theorem FIssuer.issue_of_some {st : FIssuer} {b : BNodeId} {v : String}
    (h : st.tree.get? b = some v) : st.issue b = (st, v) := by
  unfold FIssuer.issue
  split
  · rename_i v' h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i h'
    rw [h] at h'
    cases h'

theorem FIssuer.issue_of_none {st : FIssuer} {b : BNodeId} (h : st.tree.get? b = none) :
    st.issue b = (st.issueNew b h, mkLabel st.labelPrefix st.counter) := by
  unfold FIssuer.issue
  split
  · rename_i v' h'
    rw [h] at h'
    cases h'
  · rfl

theorem FIssuer.issue_toSpec (st : FIssuer) (b : BNodeId) :
    issueIdentifier st.toSpec b = ((st.issue b).1.toSpec, (st.issue b).2) := by
  unfold issueIdentifier
  rw [← FIssuer.get?_eq]
  cases hc : st.tree.get? b with
  | some v => rw [FIssuer.issue_of_some hc]
  | none =>
      rw [FIssuer.issue_of_none hc]
      simp [FIssuer.toSpec, FIssuer.issueNew]

/-- `issueFresh` on a fast issuer: the new pair goes to the FRONT, as in
`issueFresh`. -/
def FIssuer.issueFresh (st : FIssuer) (b : BNodeId) : FIssuer :=
  { labelPrefix := st.labelPrefix, counter := st.counter + 1,
    front := (b, mkLabel st.labelPrefix st.counter) :: st.front, backRev := st.backRev,
    tree := st.tree.insert b (mkLabel st.labelPrefix st.counter),
    tree_get := fun a => by
      rw [labelTree_get?_insert, st.tree_get]
      by_cases h : b = a
      · simp [lookupIssued, h]
      · simp [lookupIssued, h] }

theorem FIssuer.issueFresh_toSpec (st : FIssuer) (b : BNodeId) :
    (st.issueFresh b).toSpec = L4Factoidal.RDF.Canonical.issueFresh st.toSpec b := rfl

/-- `lookupIssued2` (§4.6 step 3) on fast issuers. -/
def lookupIssued2F (b : BNodeId) (canonF localF : FIssuer) : Option String :=
  match canonF.tree.get? b with
  | some lbl => some lbl
  | none     => localF.tree.get? b

theorem lookupIssued2F_eq (b : BNodeId) (canonF localF : FIssuer) :
    lookupIssued2F b canonF localF = lookupIssued2 b canonF.toSpec localF.toSpec := by
  unfold lookupIssued2F lookupIssued2
  rw [FIssuer.get?_eq, FIssuer.get?_eq]

/-- `insertRelatedEntries` with fast issuers and the first-degree hashes in a
search tree. -/
def insertRelatedEntriesF (alg : HashAlgorithm) (pred : String) (hT : LabelTree)
    (canonF localF : FIssuer) : List (String × BNodeId) → List Bucket → List Bucket
  | [],                acc => acc
  | (pos, rb) :: rest, acc =>
      let identifier := match lookupIssued2F rb canonF localF with
        | some lbl => "_:" ++ lbl
        | none     => (hT.get? rb).getD ""
      insertRelatedEntriesF alg pred hT canonF localF rest
        (bucketInsert (hashRelatedBlankNode alg pos pred identifier) rb acc)

theorem insertRelatedEntriesF_eq (alg : HashAlgorithm) (pred : String) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl)
    (canonF localF : FIssuer) :
    ∀ (xs : List (String × BNodeId)) (acc : List Bucket),
      insertRelatedEntriesF alg pred hT canonF localF xs acc =
        insertRelatedEntries alg pred tbl canonF.toSpec localF.toSpec xs acc
  | [], acc => rfl
  | (pos, rb) :: rest, acc => by
      simp only [insertRelatedEntriesF, insertRelatedEntries, lookupIssued2F_eq, hhT]
      exact insertRelatedEntriesF_eq alg pred hhT canonF localF rest _

/-- `buildBucketsFor` with fast issuers, run over the quads of `target` only. -/
def buildBucketsForF (alg : HashAlgorithm) (target : BNodeId) (hT : LabelTree)
    (canonF localF : FIssuer) : List QQuad → List Bucket → List Bucket
  | [],       acc => acc
  | q :: rest, acc =>
      if !quadMentionsBnode target q then
        buildBucketsForF alg target hT canonF localF rest acc
      else
        buildBucketsForF alg target hT canonF localF rest
          (insertRelatedEntriesF alg q.2.p.val hT canonF localF (relatedComponents target q) acc)

theorem buildBucketsForF_eq (alg : HashAlgorithm) (target : BNodeId) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl)
    (canonF localF : FIssuer) :
    ∀ (qs : List QQuad) (acc : List Bucket),
      buildBucketsForF alg target hT canonF localF qs acc =
        buildBucketsFor alg target tbl canonF.toSpec localF.toSpec qs acc
  | [], acc => rfl
  | q :: rest, acc => by
      simp only [buildBucketsForF, buildBucketsFor,
        insertRelatedEntriesF_eq alg _ hhT canonF localF]
      split
      · exact buildBucketsForF_eq alg target hhT canonF localF rest _
      · exact buildBucketsForF_eq alg target hhT canonF localF rest _

/-- `buildBucketsFor` skips every quad that does not mention `target`, so it
gives the same buckets over the quads of `target` alone. -/
theorem buildBucketsFor_filter (alg : HashAlgorithm) (target : BNodeId)
    (tbl : List (BNodeId × String)) (canonSt localSt : IssuerState) :
    ∀ (qs : List QQuad) (acc : List Bucket),
      buildBucketsFor alg target tbl canonSt localSt (qs.filter (quadMentionsBnode target)) acc =
        buildBucketsFor alg target tbl canonSt localSt qs acc
  | [], acc => rfl
  | q :: rest, acc => by
      by_cases h : quadMentionsBnode target q = true
      · simp only [List.filter_cons, h, if_true, buildBucketsFor, Bool.not_true]
        exact buildBucketsFor_filter alg target tbl canonSt localSt rest _
      · simp only [List.filter_cons, h, buildBucketsFor]
        simp only [Bool.not_eq_true] at h
        simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
        exact buildBucketsFor_filter alg target tbl canonSt localSt rest _

/-- The result of one step of the fast §4.7 walk. -/
abbrev HndqOutF := String × FIssuer × HndqBudget

/-- "Run Hash N-Degree Quads one level down" with a fast issuer. -/
abbrev HndqRecF := FIssuer → BNodeId → HndqBudget → HndqOutF

/-- The `HndqOut` a fast result stands for. -/
def HndqOutF.toSpec (o : HndqOutF) : HndqOut := (o.1, o.2.1.toSpec, o.2.2)

/-- `buildPathLabels` (§4.7 step 5.4.4) with fast issuers. -/
def buildPathLabelsF (canonF : FIssuer) : FIssuer → List BNodeId → String →
    List BNodeId → String × FIssuer × List BNodeId
  | localF, [],        path, recursion => (path, localF, recursion)
  | localF, b :: rest, path, recursion =>
      match lookupIssued2F b canonF localF with
      | some lbl => buildPathLabelsF canonF localF rest (path ++ "_:" ++ lbl) recursion
      | none     =>
          let r := localF.issue b
          buildPathLabelsF canonF r.1 rest (path ++ "_:" ++ r.2) (recursion ++ [b])

theorem buildPathLabelsF_eq (canonF : FIssuer) :
    ∀ (localF : FIssuer) (bs : List BNodeId) (path : String) (recursion : List BNodeId),
      (fun r => (r.1, r.2.1.toSpec, r.2.2)) (buildPathLabelsF canonF localF bs path recursion) =
        buildPathLabels canonF.toSpec localF.toSpec bs path recursion
  | localF, [], path, recursion => rfl
  | localF, b :: rest, path, recursion => by
      simp only [buildPathLabelsF, buildPathLabels, lookupIssued2F_eq]
      split
      · exact buildPathLabelsF_eq canonF localF rest _ _
      · rw [FIssuer.issue_toSpec]
        exact buildPathLabelsF_eq canonF _ rest _ _

/-- `walkRecursion` (§4.7 step 5.4.5) with fast issuers. -/
def walkRecursionF (rec : HndqRecF) : FIssuer → List BNodeId → String → HndqBudget → HndqOutF
  | localF, [],        path, hb => (path, localF, hb)
  | localF, b :: rest, path, hb =>
      if hb.exceeded then (path, localF, hb)
      else
        let r1 := localF.issue b
        let r2 := rec r1.1 b hb
        walkRecursionF rec r2.2.1 rest (path ++ "_:" ++ r1.2 ++ "<" ++ r2.1 ++ ">") r2.2.2

theorem walkRecursionF_eq {recF : HndqRecF} {rec : HndqRec}
    (hrec : ∀ st b hb, (recF st b hb).toSpec = rec st.toSpec b hb) :
    ∀ (localF : FIssuer) (bs : List BNodeId) (path : String) (hb : HndqBudget),
      (walkRecursionF recF localF bs path hb).toSpec = walkRecursion rec localF.toSpec bs path hb
  | localF, [], path, hb => rfl
  | localF, b :: rest, path, hb => by
      simp only [walkRecursionF, walkRecursion]
      split
      · rfl
      · rw [FIssuer.issue_toSpec, ← hrec]
        exact walkRecursionF_eq hrec _ rest _ _

/-- `walkPerm` with fast issuers. -/
def walkPermF (rec : HndqRecF) (canonF localF : FIssuer) (perm : List BNodeId)
    (path : String) (hb : HndqBudget) : HndqOutF :=
  let r := buildPathLabelsF canonF localF perm path []
  walkRecursionF rec r.2.1 r.2.2 r.1 hb

theorem walkPermF_eq {recF : HndqRecF} {rec : HndqRec}
    (hrec : ∀ st b hb, (recF st b hb).toSpec = rec st.toSpec b hb)
    (canonF localF : FIssuer) (perm : List BNodeId) (path : String) (hb : HndqBudget) :
    (walkPermF recF canonF localF perm path hb).toSpec =
      walkPerm rec canonF.toSpec localF.toSpec perm path hb := by
  unfold walkPermF walkPerm
  rw [← buildPathLabelsF_eq]
  exact walkRecursionF_eq hrec _ _ _ _

/-- `pickBest` with fast issuers. -/
def pickBestF (rec : HndqRecF) (canonF localStInitial : FIssuer) :
    List (List BNodeId) → String → FIssuer → HndqBudget → HndqOutF
  | [],       bestHash, bestSt, hb => (bestHash, bestSt, hb)
  | p :: rest, bestHash, bestSt, hb =>
      if hb.exceeded then (bestHash, bestSt, hb)
      else
        let r := walkPermF rec canonF localStInitial p "" hb
        if strLe r.1 bestHash && r.1 != bestHash then
          pickBestF rec canonF localStInitial rest r.1 r.2.1 r.2.2
        else
          pickBestF rec canonF localStInitial rest bestHash bestSt r.2.2

theorem pickBestF_eq {recF : HndqRecF} {rec : HndqRec}
    (hrec : ∀ st b hb, (recF st b hb).toSpec = rec st.toSpec b hb)
    (canonF localStInitial : FIssuer) :
    ∀ (perms : List (List BNodeId)) (bestHash : String) (bestSt : FIssuer) (hb : HndqBudget),
      (pickBestF recF canonF localStInitial perms bestHash bestSt hb).toSpec =
        pickBest rec canonF.toSpec localStInitial.toSpec perms bestHash bestSt.toSpec hb
  | [], bestHash, bestSt, hb => rfl
  | p :: rest, bestHash, bestSt, hb => by
      simp only [pickBestF, pickBest]
      split
      · rfl
      · rw [← walkPermF_eq hrec]
        simp only [HndqOutF.toSpec]
        split
        · rename_i hc
          simp only [hc, if_true]
          exact pickBestF_eq hrec canonF localStInitial rest _ _ _
        · rename_i hc
          simp only [hc, if_false, Bool.false_eq_true]
          exact pickBestF_eq hrec canonF localStInitial rest _ _ _

/-- `bestPermutation` with fast issuers. -/
def bestPermutationF (rec : HndqRecF) (canonF localF : FIssuer)
    (perms : List (List BNodeId)) (hb : HndqBudget) : HndqOutF :=
  match perms with
  | []       => ("", localF, hb)
  | p :: rest =>
      if hb.exceeded then ("", localF, hb)
      else
        let r := walkPermF rec canonF localF p "" hb
        pickBestF rec canonF localF rest r.1 r.2.1 r.2.2

theorem bestPermutationF_eq {recF : HndqRecF} {rec : HndqRec}
    (hrec : ∀ st b hb, (recF st b hb).toSpec = rec st.toSpec b hb)
    (canonF localF : FIssuer) (perms : List (List BNodeId)) (hb : HndqBudget) :
    (bestPermutationF recF canonF localF perms hb).toSpec =
      bestPermutation rec canonF.toSpec localF.toSpec perms hb := by
  unfold bestPermutationF bestPermutation
  cases perms with
  | nil => rfl
  | cons p rest =>
      simp only
      split
      · rfl
      · rw [← walkPermF_eq hrec]
        exact pickBestF_eq hrec canonF localF rest _ _ _

/-- `walkBuckets` with fast issuers. -/
def walkBucketsF (alg : HashAlgorithm) (rec : HndqRecF) (canonF : FIssuer) :
    FIssuer → List Bucket → String → HndqBudget → HndqOutF
  | localF, [],                 data, hb => (hashHex alg data, localF, hb)
  | localF, (k, members) :: rest, data, hb =>
      if hb.exceeded then (hashHex alg data, localF, hb)
      else
        let perms := permutationsOf (members.take permutationCap)
        let r := bestPermutationF rec canonF localF perms hb
        walkBucketsF alg rec canonF r.2.1 rest (data ++ k ++ r.1) r.2.2

theorem walkBucketsF_eq (alg : HashAlgorithm) {recF : HndqRecF} {rec : HndqRec}
    (hrec : ∀ st b hb, (recF st b hb).toSpec = rec st.toSpec b hb) (canonF : FIssuer) :
    ∀ (localF : FIssuer) (bs : List Bucket) (data : String) (hb : HndqBudget),
      (walkBucketsF alg recF canonF localF bs data hb).toSpec =
        walkBuckets alg rec canonF.toSpec localF.toSpec bs data hb
  | localF, [], data, hb => rfl
  | localF, (k, members) :: rest, data, hb => by
      simp only [walkBucketsF, walkBuckets]
      split
      · rfl
      · rw [← bestPermutationF_eq hrec]
        exact walkBucketsF_eq alg hrec canonF _ rest _ _

/-- RDFC-1.0 §4.7 with the blank node to quads map `ix` (§4.4 step 2), the
first-degree hashes in the search tree `hT`, and fast issuers. -/
def hndqRunF (alg : HashAlgorithm) (ix : QuadIndex) (hT : LabelTree) (canonF : FIssuer) :
    Nat → FIssuer → BNodeId → HndqBudget → HndqOutF
  | 0,        localF, _,      hb => ("", localF, hbConsume hb)
  | fuel + 1, localF, target, hb =>
      let hb1 := hbConsume hb
      if hb1.exceeded then ("", localF, hb1)
      else
        let buckets := buildBucketsForF alg target hT canonF localF (quadsForBnodeIx ix target) []
        walkBucketsF alg (hndqRunF alg ix hT canonF fuel) canonF localF buckets "" hb1

theorem hndqRunF_eq (alg : HashAlgorithm) {ix : QuadIndex} {qs : List QQuad}
    (hix : ∀ t, quadsForBnodeIx ix t = quadsForBnode t qs) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl)
    (canonF : FIssuer) :
    ∀ (fuel : Nat) (localF : FIssuer) (target : BNodeId) (hb : HndqBudget),
      (hndqRunF alg ix hT canonF fuel localF target hb).toSpec =
        hndqRun alg qs tbl canonF.toSpec fuel localF.toSpec target hb
  | 0, localF, target, hb => rfl
  | fuel + 1, localF, target, hb => by
      simp only [hndqRunF, hndqRun]
      split
      · rfl
      · rw [hix, buildBucketsForF_eq alg target hhT, quadsForBnode, buildBucketsFor_filter]
        exact walkBucketsF_eq alg (hndqRunF_eq alg hix hhT canonF fuel) canonF _ _ _ _

/-! The §4.4 steps 4 and 5 with fast issuers. -/

def assignSingletonsF (st : FIssuer) : List Bucket → FIssuer
  | []                => st
  | (_, [b]) :: rest  => assignSingletonsF (st.issueFresh b) rest
  | (_, _) :: rest    => assignSingletonsF st rest

theorem assignSingletonsF_toSpec :
    ∀ (st : FIssuer) (groups : List Bucket),
      (assignSingletonsF st groups).toSpec = assignSingletons st.toSpec groups
  | st, [] => rfl
  | st, (_, []) :: rest => by
      simp only [assignSingletonsF, assignSingletons]
      exact assignSingletonsF_toSpec st rest
  | st, (_, [b]) :: rest => by
      simp only [assignSingletonsF, assignSingletons]
      rw [← FIssuer.issueFresh_toSpec]
      exact assignSingletonsF_toSpec _ rest
  | st, (_, b :: c :: more) :: rest => by
      simp only [assignSingletonsF, assignSingletons]
      exact assignSingletonsF_toSpec st rest

def filterUnissuedF (st : FIssuer) (xs : List BNodeId) : List BNodeId :=
  xs.filter (fun b => (st.tree.get? b).isNone)

theorem filterUnissuedF_eq (st : FIssuer) (xs : List BNodeId) :
    filterUnissuedF st xs = filterUnissued st.toSpec xs := by
  unfold filterUnissuedF filterUnissued
  simp only [FIssuer.get?_eq]

/-- `exploreMembers` with fast issuers and the map, the results on a reverse
accumulator (one loop instead of one stack frame per member). -/
def exploreMembersF (alg : HashAlgorithm) (fuel : Nat) (ix : QuadIndex) (hT : LabelTree)
    (canonF : FIssuer) : List BNodeId → HndqBudget → List (String × List (BNodeId × String)) →
    List (String × List (BNodeId × String)) × HndqBudget
  | [],       hb, acc => (acc.reverse, hb)
  | m :: rest, hb, acc =>
      if hb.exceeded then (acc.reverse, hb)
      else match canonF.tree.get? m with
        | some _ => exploreMembersF alg fuel ix hT canonF rest hb acc
        | none   =>
            let r := hndqRunF alg ix hT canonF fuel ((FIssuer.empty "b").issue m).1 m hb
            exploreMembersF alg fuel ix hT canonF rest r.2.2 ((r.1, r.2.1.toSpec.issued) :: acc)

theorem exploreMembersF_eq (alg : HashAlgorithm) (fuel : Nat) {ix : QuadIndex}
    {qs : List QQuad} (hix : ∀ t, quadsForBnodeIx ix t = quadsForBnode t qs) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl)
    (canonF : FIssuer) :
    ∀ (ms : List BNodeId) (hb : HndqBudget) (acc : List (String × List (BNodeId × String))),
      exploreMembersF alg fuel ix hT canonF ms hb acc =
        (acc.reverse ++ (exploreMembers alg fuel qs tbl canonF.toSpec ms hb).1,
         (exploreMembers alg fuel qs tbl canonF.toSpec ms hb).2)
  | [], hb, acc => by simp [exploreMembersF, exploreMembers]
  | m :: rest, hb, acc => by
      simp only [exploreMembersF, exploreMembers]
      split
      · simp
      · rw [← FIssuer.get?_eq]
        split
        · exact exploreMembersF_eq alg fuel hix hhT canonF rest hb acc
        · rw [← FIssuer.empty_toSpec_b, FIssuer.issue_toSpec,
            ← hndqRunF_eq alg hix hhT canonF fuel]
          rw [exploreMembersF_eq alg fuel hix hhT canonF rest]
          simp [HndqOutF.toSpec]

def replayOneF (canonF : FIssuer) : List (BNodeId × String) → FIssuer
  | []             => canonF
  | (b, _) :: rest => replayOneF (canonF.issue b).1 rest

theorem replayOneF_toSpec :
    ∀ (canonF : FIssuer) (l : List (BNodeId × String)),
      (replayOneF canonF l).toSpec = replayOne canonF.toSpec l
  | canonF, [] => rfl
  | canonF, (b, _) :: rest => by
      simp only [replayOneF, replayOne, FIssuer.issue_toSpec]
      exact replayOneF_toSpec _ rest

def replayAllF (canonF : FIssuer) : List (String × List (BNodeId × String)) → FIssuer
  | []                      => canonF
  | (_, tempIssued) :: rest => replayAllF (replayOneF canonF tempIssued) rest

theorem replayAllF_toSpec :
    ∀ (canonF : FIssuer) (l : List (String × List (BNodeId × String))),
      (replayAllF canonF l).toSpec = replayAll canonF.toSpec l
  | canonF, [] => rfl
  | canonF, (_, tempIssued) :: rest => by
      simp only [replayAllF, replayAll, ← replayOneF_toSpec]
      exact replayAllF_toSpec _ rest

def processCollisionMembersF (alg : HashAlgorithm) (fuel : Nat) (ix : QuadIndex)
    (hT : LabelTree) (st : FIssuer) (members : List BNodeId) (hb : HndqBudget) :
    FIssuer × HndqBudget :=
  let r := exploreMembersF alg fuel ix hT st members hb []
  (replayAllF st (sortByFast (fun a b => strLe a.1 b.1) r.1), r.2)

theorem processCollisionMembersF_eq (alg : HashAlgorithm) (fuel : Nat) {ix : QuadIndex}
    {qs : List QQuad} (hix : ∀ t, quadsForBnodeIx ix t = quadsForBnode t qs) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl)
    (st : FIssuer) (members : List BNodeId) (hb : HndqBudget) :
    (fun r => (r.1.toSpec, r.2)) (processCollisionMembersF alg fuel ix hT st members hb) =
      processCollisionMembers alg fuel qs tbl st.toSpec members hb := by
  simp only [processCollisionMembersF, processCollisionMembers,
    exploreMembersF_eq alg fuel hix hhT st members hb [], replayAllF_toSpec]
  simp

def processCollisionGroupsF (alg : HashAlgorithm) (fuel : Nat) (ix : QuadIndex)
    (hT : LabelTree) : FIssuer → List Bucket → HndqBudget → FIssuer × HndqBudget
  | st, [],                   hb => (st, hb)
  | st, (_, [_]) :: rest,     hb => processCollisionGroupsF alg fuel ix hT st rest hb
  | st, (_, members) :: rest, hb =>
      if hb.exceeded then (st, hb)
      else
        let r := processCollisionMembersF alg fuel ix hT st (filterUnissuedF st members) hb
        processCollisionGroupsF alg fuel ix hT r.1 rest r.2

theorem processCollisionGroupsF_eq (alg : HashAlgorithm) (fuel : Nat) {ix : QuadIndex}
    {qs : List QQuad} (hix : ∀ t, quadsForBnodeIx ix t = quadsForBnode t qs) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl) :
    ∀ (st : FIssuer) (groups : List Bucket) (hb : HndqBudget),
      (fun r => (r.1.toSpec, r.2)) (processCollisionGroupsF alg fuel ix hT st groups hb) =
        processCollisionGroups alg fuel qs tbl st.toSpec groups hb
  | st, [], hb => rfl
  | st, (_, [_]) :: rest, hb => by
      simp only [processCollisionGroupsF, processCollisionGroups]
      exact processCollisionGroupsF_eq alg fuel hix hhT st rest hb
  | st, (h, []) :: rest, hb => by
      simp only [processCollisionGroupsF, processCollisionGroups]
      split
      · rfl
      · rw [filterUnissuedF_eq, ← processCollisionMembersF_eq alg fuel hix hhT]
        exact processCollisionGroupsF_eq alg fuel hix hhT _ rest _
  | st, (h, b :: c :: more) :: rest, hb => by
      simp only [processCollisionGroupsF, processCollisionGroups]
      split
      · rfl
      · rw [filterUnissuedF_eq, ← processCollisionMembersF_eq alg fuel hix hhT]
        exact processCollisionGroupsF_eq alg fuel hix hhT _ rest _

def walkGroupsF (alg : HashAlgorithm) (fuel : Nat) (ix : QuadIndex) (hT : LabelTree)
    (st : FIssuer) (groups : List Bucket) (hb : HndqBudget) : FIssuer × HndqBudget :=
  processCollisionGroupsF alg fuel ix hT (assignSingletonsF st groups) groups hb

theorem walkGroupsF_eq (alg : HashAlgorithm) (fuel : Nat) {ix : QuadIndex}
    {qs : List QQuad} (hix : ∀ t, quadsForBnodeIx ix t = quadsForBnode t qs) {hT : LabelTree}
    {tbl : List (BNodeId × String)} (hhT : ∀ b, (hT.get? b).getD "" = lookupHfdq b tbl)
    (st : FIssuer) (groups : List Bucket) (hb : HndqBudget) :
    (fun r => (r.1.toSpec, r.2)) (walkGroupsF alg fuel ix hT st groups hb) =
      walkGroups alg fuel qs tbl st.toSpec groups hb := by
  unfold walkGroupsF walkGroups
  rw [← assignSingletonsF_toSpec]
  exact processCollisionGroupsF_eq alg fuel hix hhT _ _ _

theorem foldl_issue_toSpec (l : List (BNodeId × String)) :
    ∀ (st : FIssuer),
      (l.foldl (fun s p => (s.issue p.1).1) st).toSpec =
        l.foldl (fun s p => (issueIdentifier s p.1).1) st.toSpec := by
  induction l with
  | nil => intro st; rfl
  | cons p rest ih =>
      intro st
      simp only [List.foldl_cons, FIssuer.issue_toSpec]
      exact ih _

/-- `buildCanonicalMappingBudgeted` with the §4.4 step 2 map built once and
shared by §4.4 step 3 and every Hash N-Degree Quads call, the first-degree
hashes in a search tree, and fast issuers. -/
def buildCanonicalMappingBudgetedFast (alg : HashAlgorithm) (budget : Nat) (ds : Dataset) :
    Option (List (BNodeId × String)) :=
  let qs := dedupQQuads (datasetQuads ds)
  let bs := datasetBnodes ds
  let ix := bnodeQuadIndex qs
  let hfdqTable := bs.map (fun b => (b, hashFirstDegreeQuadsIx alg ix b))
  let hT := labelTree hfdqTable
  let groups := groupByHfdq hfdqTable
  let r := walkGroupsF alg (bs.length + 1) ix hT (FIssuer.empty "c14n") groups (hbInit budget)
  if r.2.exceeded then none
  else
    let st := r.1
    let leftover := if st.toSpec.issued.length == bs.length then [] else filterUnissuedF st bs
    let leftoverSorted :=
      sortBy (fun a b => if a.2 == b.2 then strLe a.1 b.1 else strLe a.2 b.2)
        (leftover.map (fun b => (b, (hT.get? b).getD "")))
    some (leftoverSorted.foldl (fun s p => (s.issue p.1).1) st).toSpec.issued

theorem buildCanonicalMappingBudgeted_eq_fast_apply (alg : HashAlgorithm) (budget : Nat)
    (ds : Dataset) :
    buildCanonicalMappingBudgeted alg budget ds = buildCanonicalMappingBudgetedFast alg budget ds := by
  have htbl : hfdqTableOf alg ds (dedupQQuads (datasetQuads ds)) =
      (datasetBnodes ds).map (fun b =>
        (b, hashFirstDegreeQuadsIx alg (bnodeQuadIndex (dedupQQuads (datasetQuads ds))) b)) := by
    unfold hfdqTableOf
    simp only [hashFirstDegreeQuadsIx_eq]
  have hix := quadsForBnodeIx_bnodeQuadIndex (dedupQQuads (datasetQuads ds))
  have hhT : ∀ b, ((labelTree ((datasetBnodes ds).map (fun b =>
        (b, hashFirstDegreeQuadsIx alg (bnodeQuadIndex (dedupQQuads (datasetQuads ds))) b)))).get?
          b).getD "" =
      lookupHfdq b ((datasetBnodes ds).map (fun b =>
        (b, hashFirstDegreeQuadsIx alg (bnodeQuadIndex (dedupQQuads (datasetQuads ds))) b))) := by
    intro b
    rw [labelTree_get?, lookupHfdq_eq_lookupMap]
  unfold buildCanonicalMappingBudgeted buildCanonicalMappingBudgetedFast
  dsimp only
  rw [htbl, ← FIssuer.empty_toSpec_c14n, ← walkGroupsF_eq alg _ hix hhT]
  dsimp only
  split
  · rfl
  · simp only [filterUnissuedF_eq, hhT, foldl_issue_toSpec]

/-- The compiler calls `buildCanonicalMappingBudgetedFast` wherever the source
says `buildCanonicalMappingBudgeted`. -/
@[csimp] theorem buildCanonicalMappingBudgeted_eq_fast :
    @buildCanonicalMappingBudgeted = @buildCanonicalMappingBudgetedFast := by
  funext alg budget ds
  exact buildCanonicalMappingBudgeted_eq_fast_apply alg budget ds

/-- The blank-node label map: original label → `c14nN`. -/
def buildCanonicalMapping (alg : HashAlgorithm := .sha256) (ds : Dataset) :
    List (BNodeId × String) :=
  (buildCanonicalMappingBudgeted alg defaultHndqBudget ds).getD []

/-- True when canonicalization under `budget` aborted for excessive
calls to Hash N-Degree Quads — the W3C suite's `RDFC10NegativeEvalTest`
criterion. Use a budget well below `defaultHndqBudget` so a
pathological input aborts promptly. -/
def canonicalizeExceedsBudget (alg : HashAlgorithm) (budget : Nat) (ds : Dataset) : Bool :=
  (buildCanonicalMappingBudgeted alg budget ds).isNone

/-! ### Canonical N-Quads output -/

/-- The canonical N-Quads LINES of an already-relabelled dataset:
render every quad, sort in code point order (RDFC-1.0 §3), drop
duplicates (RDF set semantics). -/
def canonicalLinesOf (ds : Dataset) : List String :=
  dedupAdj (sortStrings ((datasetQuads ds).map canonQuad))

/-- What `canonicalize` returns: the canonical N-Quads text and the
issued label map. -/
structure CanonResult where
  /-- The canonical N-Quads document (RDFC-1.0 §3 sorted form). -/
  nquads : String
  /-- The `rdfc10map` relation: original blank-node label → canonical
  identifier, WITHOUT the `_:` prefix, in ascending original-label
  order. -/
  issued : List (BNodeId × String)
  /-- True when the run hit the §4.4 excessive-calls abort; `nquads`
  and `issued` are then the un-canonicalised fallback. -/
  aborted : Bool
  deriving Repr

/-- RDFC-1.0 §4.4 — canonicalize a dataset. Default algorithm SHA-256
(§4.4 note 2); the W3C manifests select SHA-384 for some entries via
`rdfc:hashAlgorithm`. -/
def canonicalize (ds : Dataset) (alg : HashAlgorithm := .sha256) : CanonResult :=
  match buildCanonicalMappingBudgeted alg defaultHndqBudget ds with
  | none => { nquads := joinStrings (canonicalLinesOf ds), issued := [], aborted := true }
  | some m =>
      { nquads  := joinStrings (canonicalLinesOf (relabelDataset m ds)),
        issued  := sortByFast (fun a b => strLe a.1 b.1) m,
        aborted := false }

/-- The canonical N-Quads document of a dataset. -/
def _root_.L4Factoidal.RDF.Dataset.canonicalNQuads
    (ds : Dataset) (alg : HashAlgorithm := .sha256) : String :=
  (canonicalize ds alg).nquads

/-- The canonical N-Quads LINES of a dataset — the sorted list the
`nquads` field concatenates. Exposed so the sortedness theorem in
`RDF/CanonicalTheorems.lean` has something to talk about. -/
def _root_.L4Factoidal.RDF.Dataset.canonicalLines
    (ds : Dataset) (alg : HashAlgorithm := .sha256) : List String :=
  match buildCanonicalMappingBudgeted alg defaultHndqBudget ds with
  | none   => canonicalLinesOf ds
  | some m => canonicalLinesOf (relabelDataset m ds)

/-- The hash of the canonical N-Quads document — the `canonicalHash`
API of the rdf-canonize implementations. -/
def _root_.L4Factoidal.RDF.Dataset.canonicalHash
    (ds : Dataset) (alg : HashAlgorithm := .sha256) : String :=
  hashHex alg (ds.canonicalNQuads alg)

end L4Factoidal.RDF.Canonical
