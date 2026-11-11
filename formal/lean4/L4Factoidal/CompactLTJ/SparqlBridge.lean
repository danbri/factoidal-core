import L4Factoidal.CompactLTJ.Model
import L4Factoidal.SPARQL.Algebra

/-
Copyright 2026 Factoidal contributors. SPDX-License-Identifier: Apache-2.0

Restricted SPARQL-to-integer-domain bridge for the experimental multiway
solver. This deliberately DOES NOT replace the public SPARQL evaluator.

Scope: ordinary RDF triple patterns with IRIs, blank nodes, typed literals
and variables. RDF 1.2 nested triple-term *patterns* are rejected (none).
The independent result is available for differential checks against the
existing Lean SPARQL reference. SPARQL multiset and solution ordering
refinement is not yet proved: do not dispatch production Leana queries here.
-/

namespace L4Factoidal.CompactLTJ.SparqlBridge

open L4Factoidal.RDF

/-- Dictionary identities use the same canonical term representatives
as Factoidal's existing hash-join keys, not xsd:value comparisons. -/
def dictionary (g : RDF.Graph) : List RDF.Term :=
  ((g.flatMap (fun t => [t.s.toTerm, .iri t.p, t.o]))
    |>.map RDF.Term.joinKey).eraseDups

/-- A finite dictionary's first matching position; length if missing.
Deliberately pure and simple before optimising term lookup. -/
def idOf : List RDF.Term → RDF.Term → Nat
  | [], _ => 0
  | x :: xs, t =>
      if x = t.joinKey then 0 else 1 + idOf xs t

theorem idOf_cons_self (t : RDF.Term) (xs : List RDF.Term)
    (h : t = t.joinKey) : idOf (t :: xs) t = 0 := by
  simp [idOf, h]

def variableNames (b : SPARQL.Bgp) : List SPARQL.VarName :=
  (b.flatMap (fun a =>
    (match a.s with
      | .var v => [v]
      | _ => []) ++
    (match a.p with
      | .var v => [v]
      | _ => []) ++
    (match a.o with
      | .var v => [v]
      | _ => []))).eraseDups

def variableId : List SPARQL.VarName → SPARQL.VarName → Nat
  | [], _ => 0
  | x :: xs, v => if x == v then 0 else 1 + variableId xs v

theorem variableId_head (v : SPARQL.VarName)
    (xs : List SPARQL.VarName) : variableId (v :: xs) v = 0 := by
  simp [variableId]

def encodeGraph (dict : List RDF.Term) (g : RDF.Graph) :
    List CompactLTJ.Triple :=
  g.map (fun t =>
    ⟨idOf dict t.s.toTerm,
     idOf dict (.iri t.p),
     idOf dict t.o⟩)

def subjectSlot (dict : List RDF.Term)
    (variables : List SPARQL.VarName) :
    SPARQL.PatternSubject → Option CompactLTJ.Slot
  | .var v => some (.variable (variableId variables v))
  | .iri i => some (.fixed (idOf dict (.iri i)))
  | .bnode b => some (.fixed (idOf dict (.bnode b)))
  | .tripleTerm _ _ _ => none

def termSlot (dict : List RDF.Term)
    (variables : List SPARQL.VarName) :
    SPARQL.PatternTerm → Option CompactLTJ.Slot
  | .var v => some (.variable (variableId variables v))
  | .iri i => some (.fixed (idOf dict (.iri i)))
  | .bnode b => some (.fixed (idOf dict (.bnode b)))
  | .literal l => some (.fixed (idOf dict (.literal l)))
  | .tripleTerm _ _ _ => none

def encodeAtom (dict : List RDF.Term)
    (variables : List SPARQL.VarName)
    (a : SPARQL.TriplePattern) : Option CompactLTJ.Atom := do
  let s ← subjectSlot dict variables a.s
  let p ← termSlot dict variables a.p
  let o ← termSlot dict variables a.o
  return ⟨s, p, o⟩

/-- Lookup is partial to make unsupported dictionary values explicit. -/
def decodeBinding (dict : List RDF.Term)
    (variables : List SPARQL.VarName)
    (b : CompactLTJ.Binding) : SPARQL.Binding :=
  b.filterMap (fun (v, id) =>
    match variables[v]?, dict[id]? with
    | some var, some term => some (var, term)
    | _, _ => none)

/-- Experimental execution path. Returns none for unsupported nested
RDF-star pattern terms. This function is NOT called by production Leana. -/
def evaluate (g : RDF.Graph) (bgp : SPARQL.Bgp) :
    Option SPARQL.SolutionSeq := do
  let dict := dictionary g
  let variables := variableNames bgp
  let atoms ← bgp.mapM (encodeAtom dict variables)
  let solutions := CompactLTJ.solve (encodeGraph dict g) atoms
    (List.range variables.length) []
  return solutions.map (decodeBinding dict variables)

/-- A comparison hook for conformance probes: exposes the experimental
results and the reference evaluator together without asserting equality. -/
def compareWithReference (g : RDF.Graph) (bgp : SPARQL.Bgp) :
    Option (SPARQL.SolutionSeq × SPARQL.SolutionSeq) := do
  let experimental ← evaluate g bgp
  return (SPARQL.evalBgp bgp g, experimental)

end L4Factoidal.CompactLTJ.SparqlBridge
