/-
L4Factoidal.RDF.ConciseBoundedDescription — the Concise Bounded
Description (CBD) of a set of nodes in a graph.

Specification: "CBD - Concise Bounded Description", W3C Member
Submission, https://www.w3.org/Submission/CBD/ , section 2:

  Given a particular node (the starting node) in a particular RDF
  graph (the source graph), a subgraph of that particular graph, taken
  to comprise a concise bounded description of the resource denoted by
  the starting node, can be identified as follows:
    1. Include in the subgraph all statements in the source graph where
       the subject of the statement is the starting node;
    2. Recursively, for all statements identified in the subgraph thus
       far where the object is a blank node, include in the subgraph all
       statements in the source graph where the subject of the statement
       is the blank node in question and which are not already included
       in the subgraph.
    3. Recursively, for all statements included in the subgraph thus
       far, for all reifications of each statement in the source graph,
       include the concise bounded description beginning from the
       rdf:Statement node of each reification.

This is the description SPARQL 1.1 Query section 16.4 leaves to the
query service: "The DESCRIBE form returns a single result RDF graph
containing RDF data about resources ... The query service determines
the description" (https://www.w3.org/TR/sparql11-query/#describe).
`SPARQL/Query.lean` `evalDescribe` chooses this one.

RDF 1.2 has no rdf:Statement reification. A reification is a triple
`r rdf:reifies <<( s p o )>>` whose object is a triple term
(https://www.w3.org/TR/rdf12-concepts/#section-triple-terms-reifiers).
Clause 3 is therefore read this way: for every statement `s p o` in the
subgraph, every reifier `r` with a triple `r rdf:reifies <<( s p o )>>`
in the source graph is a further starting node. The triple term is
compared with the statement by `Subject.eqb`, IRI equality and
`Term.eqb`, the engine equality the rest of the tree uses. A blank node
inside a triple term is not an object of clause 2; clause 2 reads the
object position of a statement only.

Shape of the definition. The subgraph is `g.filter (fun t => t.s ∈ N)`,
where `N` is the set of starting nodes closed under clause 2 and
clause 3. Every triple of the result is a triple of the source graph
(`cbd_subset`), a triple of the source graph with a starting node as its
subject is in the result (`cbd_root_triples`), and the result is the
union of the descriptions of the starting nodes one by one, because the
closure of a union of starting sets is the union of the closures.
`ConciseBoundedDescriptionTheorems.lean` proves that `N` IS that closure:
it is closed under both clauses (`cbd_closed_bnode`, `cbd_closed_reifier`)
and inside every set that holds the starting nodes and is closed under
them (`cbd_least`).

`N` is computed by a worklist over a subject index and a reifier index,
both built once in one pass over `g`. A node enters `N` when it is first
found, and only then is it queued, so each node is expanded once. The
fuel is `roots.length + g.length`: a queued node other than a starting
node is the blank-node object of some statement or the reifier of some
`rdf:reifies` statement, so at most one node per statement of `g` is
queued after the starting nodes. The theorems file proves that this fuel
is enough. Total by structural recursion on the fuel; no `partial`.

No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.Graph
import L4Factoidal.RDFS.Vocabulary
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.RDF

/-! ## Indexes -/

/-- The two lookups the walk needs, built in one pass over the graph.

`bySubject` maps a node to the triples of the graph that have it as
subject (clause 1 and clause 2). `reifiers` maps the SUBJECT of a triple
term to the `(reifier, predicate, object)` entries of the `rdf:reifies`
triples whose object is a triple term with that subject (clause 3). The
key is the subject only, so that a lookup is one hash probe and the
predicate and object are then compared with the engine equality. -/
structure CbdIndex where
  bySubject : Std.HashMap Subject (List Triple)
  reifiers  : Std.HashMap Subject (List (Subject × WfIri × Term))

/-- Add one statement to the by-subject index. -/
def cbdSubjectStep (m : Std.HashMap Subject (List Triple)) (t : Triple) :
    Std.HashMap Subject (List Triple) :=
  m.insert t.s (t :: m.getD t.s [])

/-- Add one statement to the reifier index when it is an `rdf:reifies`
statement whose object is a triple term. -/
def cbdReifierStep (m : Std.HashMap Subject (List (Subject × WfIri × Term))) (t : Triple) :
    Std.HashMap Subject (List (Subject × WfIri × Term)) :=
  if t.p == L4Factoidal.RDFS.rdfReifies then
    match t.o with
    | .tripleTerm s p o => m.insert s ((t.s, p, o) :: m.getD s [])
    | _                 => m
  else m

/-- Index a graph. -/
def Graph.cbdIndex (g : Graph) : CbdIndex :=
  { bySubject := g.foldl cbdSubjectStep ∅
  , reifiers  := g.foldl cbdReifierStep ∅ }

/-- The reifiers of a statement: the subjects `r` of the triples
`r rdf:reifies <<( s p o )>>` in the indexed graph whose triple term is
the statement `t` (clause 3). -/
def CbdIndex.reifiersOf (idx : CbdIndex) (t : Triple) : List Subject :=
  (idx.reifiers.getD t.s []).filterMap fun (r, p, o) =>
    if p == t.p && o.eqb t.o then some r else none

/-- The blank node an object names, if it is one. A triple term, an IRI
and a literal name none. -/
def cbdBnodeObject? : Term → Option Subject
  | .bnode b => some (.bnode b)
  | _        => none

/-- The nodes one expansion of `s` makes further starting nodes: the
blank-node objects of the statements with subject `s` (clause 2), and the
reifiers of those statements (clause 3). -/
def CbdIndex.candidates (idx : CbdIndex) (s : Subject) : List Subject :=
  (idx.bySubject.getD s []).flatMap fun t =>
    (cbdBnodeObject? t.o).toList ++ idx.reifiersOf t

/-! ## The walk -/

/-- Queue each candidate that is not yet in `seen`, marking it seen at
the moment it is queued. -/
def cbdQueue (cands : List Subject) (work : List Subject)
    (seen : Std.HashSet Subject) : List Subject × Std.HashSet Subject :=
  cands.foldl (fun acc c =>
    if acc.2.contains c then acc else (c :: acc.1, acc.2.insert c)) (work, seen)

/-- Expand queued nodes until the queue is empty or the fuel is spent,
and answer the set of nodes seen. One unit of fuel is one expansion. -/
def cbdWalk (idx : CbdIndex) : Nat → List Subject → Std.HashSet Subject →
    Std.HashSet Subject
  | 0,        _,         seen => seen
  | _ + 1,    [],        seen => seen
  | fuel + 1, s :: work, seen =>
      let queued := cbdQueue (idx.candidates s) work seen
      cbdWalk idx fuel queued.1 queued.2

/-- The starting nodes, each once, as a queue and as a seen set. -/
def cbdStart (roots : List Subject) : List Subject × Std.HashSet Subject :=
  cbdQueue roots [] ∅

/-- The set of nodes whose statements make up the concise bounded
description of `roots` in `g`: the starting nodes, closed under clause 2
and clause 3. -/
def Graph.cbdNodes (g : Graph) (roots : List Subject) : Std.HashSet Subject :=
  let start := cbdStart roots
  cbdWalk g.cbdIndex (roots.length + g.length) start.1 start.2

/-- The concise bounded description of `roots` in `g`: every statement of
`g` whose subject is a starting node or a node the two recursive clauses
reach. The statements keep the order they have in `g`. A root that is not
the subject of any statement of `g` contributes nothing. -/
def Graph.cbd (g : Graph) (roots : List Subject) : Graph :=
  let nodes := g.cbdNodes roots
  g.filter fun t => nodes.contains t.s

/-! ## Theorems -/

/-- Every statement of the description is a statement of the source
graph: the description is a subgraph. -/
theorem cbd_subset (g : Graph) (roots : List Subject) :
    ∀ t ∈ g.cbd roots, t ∈ g := by
  intro t ht
  unfold Graph.cbd at ht
  exact (List.mem_filter.mp ht).1

/-- A node found stays found: `cbdQueue` never removes a node from the
seen set. -/
theorem cbdQueue_seen_mono (cands work : List Subject) (seen : Std.HashSet Subject)
    (x : Subject) (hx : seen.contains x = true) :
    (cbdQueue cands work seen).2.contains x = true := by
  unfold cbdQueue
  suffices h : ∀ (cs : List Subject) (acc : List Subject × Std.HashSet Subject),
      acc.2.contains x = true →
      (cs.foldl (fun acc c =>
        if acc.2.contains c then acc else (c :: acc.1, acc.2.insert c)) acc).2.contains x
        = true from h cands (work, seen) hx
  intro cs
  induction cs with
  | nil => intro acc hacc; simpa using hacc
  | cons c cs ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      by_cases hc : acc.2.contains c = true
      · simp [hc, hacc]
      · simp [hc, Std.HashSet.contains_insert, hacc]

/-- The walk never loses a node it has seen. -/
theorem cbdWalk_seen_mono (idx : CbdIndex) :
    ∀ (fuel : Nat) (work : List Subject) (seen : Std.HashSet Subject) (x : Subject),
      seen.contains x = true → (cbdWalk idx fuel work seen).contains x = true := by
  intro fuel
  induction fuel with
  | zero => intro work seen x hx; simpa [cbdWalk] using hx
  | succ n ih =>
      intro work seen x hx
      cases work with
      | nil => simpa [cbdWalk] using hx
      | cons s work =>
          simp only [cbdWalk]
          exact ih _ _ x (cbdQueue_seen_mono _ _ _ x hx)

/-- Every starting node is among the nodes seen. -/
theorem cbdStart_contains (roots : List Subject) (x : Subject) (hx : x ∈ roots) :
    (cbdStart roots).2.contains x = true := by
  unfold cbdStart cbdQueue
  suffices h : ∀ (cs : List Subject) (acc : List Subject × Std.HashSet Subject),
      (x ∈ cs ∨ acc.2.contains x = true) →
      (cs.foldl (fun acc c =>
        if acc.2.contains c then acc else (c :: acc.1, acc.2.insert c)) acc).2.contains x
        = true from h roots ([], ∅) (Or.inl hx)
  intro cs
  induction cs with
  | nil =>
      intro acc hacc
      rcases hacc with h | h
      · simp at h
      · simpa using h
  | cons c cs ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      apply ih
      by_cases hc : acc.2.contains c = true
      · rcases hacc with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inr (by simp [hc])
          · exact Or.inl h'
        · exact Or.inr (by simp [hc, h])
      · rcases hacc with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inr (by simp [hc, Std.HashSet.contains_insert])
          · exact Or.inl h'
        · exact Or.inr (by simp [hc, Std.HashSet.contains_insert, h])

/-- Clause 1: a statement of the source graph whose subject is a starting
node is in the description. -/
theorem cbd_root_triples (g : Graph) (roots : List Subject) :
    ∀ t ∈ g, t.s ∈ roots → t ∈ g.cbd roots := by
  intro t ht hs
  unfold Graph.cbd
  apply List.mem_filter.mpr
  refine ⟨ht, ?_⟩
  unfold Graph.cbdNodes
  exact cbdWalk_seen_mono _ _ _ _ _ (cbdStart_contains roots _ hs)

/-- No starting node, no description. -/
theorem cbd_nil (g : Graph) : g.cbd [] = [] := by
  unfold Graph.cbd Graph.cbdNodes cbdStart cbdQueue
  simp only [List.foldl_nil, List.length_nil, Nat.zero_add]
  have hseen : ∀ (fuel : Nat) (idx : CbdIndex),
      cbdWalk idx fuel [] (∅ : Std.HashSet Subject) = ∅ := by
    intro fuel idx
    cases fuel <;> simp [cbdWalk]
  rw [hseen]
  apply List.filter_eq_nil_iff.mpr
  intro t _
  simp

/-! ## Checks

Fixtures: a chain of blank nodes, a cycle, an IRI object that must NOT be
followed, an unrelated subject, and the RDF 1.2 reifier clause with a
matching and a non-matching triple term. Each negative case fails the
build for an implementation that follows every object, or that returns
the whole graph. -/

namespace CbdChecks

private def iri (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def a    : WfIri := iri "http://example.org/a"
private def c    : WfIri := iri "http://example.org/c"
private def src  : WfIri := iri "http://example.org/src"
private def other : WfIri := iri "http://example.org/other"
private def p    : WfIri := iri "http://example.org/p"
private def q    : WfIri := iri "http://example.org/q"
private def r    : WfIri := iri "http://example.org/r"
private def name : WfIri := iri "http://example.org/name"
private def source : WfIri := iri "http://example.org/source"

private def str (s : String) : Term := .literal (Literal.string s)
private def tr (s : Subject) (p : WfIri) (o : Term) : Triple := { s := s, p := p, o := o }
/-- Only so that `g[i]!` can name a fixture triple in a guard. -/
private instance : Inhabited Triple := ⟨tr (.bnode "none") a (str "none")⟩
private def sa : Subject := .iri a
private def sb (n : String) : Subject := .bnode n

-- :a :p _:b1 . _:b1 :q _:b2 . _:b2 :r "deep" . :other :p "unrelated"
private def chain : Graph :=
  [ tr sa p (.bnode "b1"), tr (sb "b1") q (.bnode "b2"), tr (sb "b2") r (str "deep"),
    tr (.iri other) p (str "unrelated") ]

-- Clause 1 and clause 2: the chain is followed to its end, the unrelated subject is not.
#guard (chain.cbd [sa]) == [chain[0]!, chain[1]!, chain[2]!]
#guard !((chain.cbd [sa]).contains (tr (.iri other) p (str "unrelated")))
-- Starting in the middle of the chain does not reach upwards.
#guard (chain.cbd [sb "b1"]) == [chain[1]!, chain[2]!]
-- Two starting nodes: the union of both descriptions, in graph order.
#guard (chain.cbd [.iri other, sa]) == chain
-- A repeated starting node changes nothing.
#guard (chain.cbd [sa, sa]) == chain.cbd [sa]
-- A node that is the subject of no statement has an empty description.
#guard (chain.cbd [.iri c]) == []
#guard (chain.cbd []) == []

-- An IRI object is not followed (clause 2 reads blank-node objects only).
private def knows : Graph :=
  [ tr sa p (.iri c), tr (.iri c) name (str "C") ]
#guard (knows.cbd [sa]) == [knows[0]!]

-- A cycle of blank nodes terminates and is returned whole.
private def cycle : Graph :=
  [ tr sa p (.bnode "x"), tr (sb "x") q (.bnode "y"), tr (sb "y") q (.bnode "x") ]
#guard (cycle.cbd [sa]) == cycle

-- A chain of 300 blank nodes is followed to its end.
private def longChain (n : Nat) : Graph :=
  tr sa p (.bnode "n0") ::
    (List.range n).map fun i => tr (sb s!"n{i}") q (.bnode s!"n{i + 1}")
#guard ((longChain 300).cbd [sa]).length == 301
#guard ((longChain 300).cbd [sb "n150"]).length == 150

-- Clause 3 in its RDF 1.2 reading. `_:rf` reifies :a :p :o; it has a
-- blank-node child; it also names :src by IRI, which is not followed.
private def o1 : Term := .iri (iri "http://example.org/o1")
private def o2 : Term := .iri (iri "http://example.org/o2")
private def reified : Graph :=
  [ tr sa p o1                                                          -- 0
  , tr (sb "rf") L4Factoidal.RDFS.rdfReifies (.tripleTerm sa p o1)       -- 1
  , tr (sb "rf") source (.iri src)                                       -- 2
  , tr (sb "rf") q (.bnode "n")                                          -- 3
  , tr (sb "n") name (str "child")                                       -- 4
  , tr (.iri src) name (str "S")                                         -- 5
  , tr sa p o2                                                           -- 6
  , tr (sb "rg") L4Factoidal.RDFS.rdfReifies (.tripleTerm sa p o2)       -- 7
  , tr (sb "rg") q (str "only with o2") ]                                -- 8
-- Both statements of :a are selected, so both reifiers are further
-- starting nodes. The IRI :src is not followed.
#guard (reified.cbd [sa]) == [reified[0]!, reified[1]!, reified[2]!, reified[3]!,
  reified[4]!, reified[6]!, reified[7]!, reified[8]!]
-- A reifier of a triple that is not selected is not a starting node.
#guard !((reified.cbd [sb "rf"]).contains reified[0]!)
#guard (reified.cbd [sb "rf"]) == [reified[1]!, reified[2]!, reified[3]!, reified[4]!]
-- A reifies triple whose triple term differs from the statement in one
-- position is not a reification of it.
private def mismatch : Graph :=
  [ tr sa p o1, tr (sb "rf") L4Factoidal.RDFS.rdfReifies (.tripleTerm sa p o2),
    tr (sb "rf") q (str "other statement") ]
#guard (mismatch.cbd [sa]) == [mismatch[0]!]
-- A reifier of a reifier: clause 3 applies to the reifies statement too.
private def nested : Graph :=
  [ tr sa p o1
  , tr (sb "r1") L4Factoidal.RDFS.rdfReifies (.tripleTerm sa p o1)
  , tr (sb "r2") L4Factoidal.RDFS.rdfReifies
      (.tripleTerm (sb "r1") L4Factoidal.RDFS.rdfReifies (.tripleTerm sa p o1))
  , tr (sb "r2") q (str "annotation of the reification") ]
#guard (nested.cbd [sa]) == nested

end CbdChecks

#print axioms cbd_subset
#print axioms cbd_root_triples
#print axioms cbd_nil

end L4Factoidal.RDF
