/-
L4Factoidal.Syntax.RdfXmlWrite — an RDF graph as RDF/XML.

Spec: RDF 1.1 XML Syntax, https://www.w3.org/TR/rdf-syntax-grammar/ ,
the striped form of section 2: one `rdf:Description` per subject, one
property element per triple.

    <rdf:RDF xmlns:rdf="..." xmlns:ns1="...">
      <rdf:Description rdf:about="http://ex/s">
        <ns1:p>text</ns1:p>
        <ns1:q rdf:resource="http://ex/o"/>
      </rdf:Description>
    </rdf:RDF>

The reader is `Syntax.RdfXml.parseRdfXml`, and the correctness
statement is the round trip through it, pinned by `#guard`s below.

## What it refuses

RDF/XML names a property by a qualified name, so a predicate IRI must
split into a namespace and an XML `NCName`. One that does not (its
last segment starts with a digit, or the IRI has no `/` or `#`) has no
RDF/XML form, and the serialiser says so instead of inventing a
namespace (RDF/XML 1.1 section 7.2.2; the note on serialising URIs as
property elements). A triple term object has no RDF/XML 1.1 form and is
refused. Characters XML 1.0 cannot carry are refused.

## Cost

One `rdf:Description` per subject, in the order of the subject's first triple, with
the subject's triples in graph order (`subjectGroups`). The run-time form groups the
triples in one pass with a hash map (`subjectGroupsFast`, `subjectGroups_eq_fast`),
so the writer's time is linear in the number of triples
(https://github.com/danbri/factoidal/issues/845: 64,000 triples took 10.5 s before,
0.44 s after; `tests/stack/lean_scaling.py`, rows `rdfxml-write` and
`rdfxml-write-stack`).
-/
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.XSD.Datatypes
import L4Factoidal.RDF.Isomorphism
import Std.Data.HashMap

namespace L4Factoidal.Syntax.RdfXmlWrite

open L4Factoidal.RDF

private def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
private def xsdString : String := "http://www.w3.org/2001/XMLSchema#string"

private def subjectKey : Subject → String
  | .iri i => i.val
  | .bnode b => "_:" ++ b

/-- XML 1.0 character data escaping. -/
private def esc (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    if c == '&' then "&amp;".toList
    else if c == '<' then "&lt;".toList
    else if c == '>' then "&gt;".toList
    else [c]))

private def escAttr (s : String) : String :=
  String.ofList (s.toList.flatMap (fun c =>
    if c == '&' then "&amp;".toList
    else if c == '<' then "&lt;".toList
    else if c == '"' then "&quot;".toList
    else if c == '\n' then "&#xA;".toList
    else if c == '\t' then "&#x9;".toList
    else if c == '\r' then "&#xD;".toList
    else [c]))

/-- Is every character one XML 1.0 can carry? -/
private def xmlSafe (s : String) : Bool := s.toList.all L4Factoidal.XML.isXmlChar

/-- The namespaces of a graph's predicates, each with a prefix. `rdf`
    is always bound; others are `ns1`, `ns2`, in first-use order. -/
private def predicateNamespaces (g : Graph) : List (String × String) :=
  let nss := g.foldl (fun acc t =>
    match nsSplit t.p.val with
    | some (ns, _) => if ns == rdfNs || acc.contains ns then acc else acc ++ [ns]
    | none => acc) ([] : List String)
  (rdfNs, "rdf") :: nss.zipIdx.map (fun (ns, i) => (ns, "ns" ++ toString (i + 1)))

private def propertyName (nss : List (String × String)) (p : WfIri) : Except String String :=
  match nsSplit p.val with
  | none => .error s!"the predicate <{p.val}> has no namespace to write it in"
  | some (ns, local') =>
      if !L4Factoidal.XSD.isNCName local' then
        .error s!"the predicate <{p.val}> does not end in an XML name"
      else
        match nss.find? (fun e => e.1 == ns) with
        | some (_, pfx) => .ok (pfx ++ ":" ++ local')
        | none => .error "internal: predicate namespace not collected"

private def renderObject (name : String) (o : Term) : Except String String :=
  match o with
  | .iri i => .ok s!"    <{name} rdf:resource=\"{escAttr i.val}\"/>\n"
  | .bnode b => .ok s!"    <{name} rdf:nodeID=\"{escAttr b}\"/>\n"
  | .tripleTerm .. => .error "RDF/XML 1.1 has no form for a triple term"
  | .literal l =>
      let l := l.val
      if !xmlSafe l.lexicalForm then .error "a literal holds a character XML 1.0 cannot carry"
      else
        match l.langTag with
        | some tag => .ok s!"    <{name} xml:lang=\"{escAttr tag}\">{esc l.lexicalForm}</{name}>\n"
        | none =>
            if l.datatype.val == xsdString then
              .ok s!"    <{name}>{esc l.lexicalForm}</{name}>\n"
            else
              .ok s!"    <{name} rdf:datatype=\"{escAttr l.datatype.val}\">{esc l.lexicalForm}</{name}>\n"

/-! ## Grouping the triples by subject

`subjectGroups` is the specification: the subjects in the order of their first
triple, each with its triples in graph order. It reads the graph once for each
subject and keeps the subjects found so far in a list, so it costs time in the
product of the triples and the subjects
(https://github.com/danbri/factoidal/issues/845: 64,000 triples took 11.6 s).
`subjectGroupsFast` reads the graph once. It keeps a hash map from a subject key
to that subject's triples in reverse order, and the subject keys in reverse
order of first use; it reverses each list once at the end.
`subjectGroups_eq_fast` proves the two equal, and the compiler emits the fast
form for every call (`csimp`). -/

/-- One step of the subject list of the specification. -/
def subjectStep (acc : List String) (t : Triple) : List String :=
  let k := subjectKey t.s
  if acc.contains k then acc else acc ++ [k]

/-- The subject keys of a graph, in the order of their first triple. -/
def subjectOrder (g : Graph) : List String := g.foldl subjectStep []

/-- The triples of the subject `k`, in graph order. -/
def triplesOf (g : Graph) (k : String) : List Triple :=
  g.filter (fun t => subjectKey t.s == k)

/-- The specification: every subject with its triples. -/
def subjectGroups (g : Graph) : List (String × List Triple) :=
  (subjectOrder g).map (fun k => (k, triplesOf g k))

/-- The state of the one-pass form. -/
structure GroupAcc where
  /-- The subject keys, the last one first. -/
  orderRev : List String
  /-- Each subject key to its triples, the last one first. -/
  buckets : Std.HashMap String (List Triple)

def groupStep (a : GroupAcc) (t : Triple) : GroupAcc :=
  let k := subjectKey t.s
  match a.buckets[k]? with
  | some b => { a with buckets := a.buckets.insert k (t :: b) }
  | none => { orderRev := k :: a.orderRev, buckets := a.buckets.insert k [t] }

def subjectGroupsFast (g : Graph) : List (String × List Triple) :=
  let a := g.foldl groupStep { orderRev := [], buckets := ∅ }
  a.orderRev.reverse.map (fun k => (k, (a.buckets[k]?.getD []).reverse))

/-- What the one-pass state holds after a prefix `l` of the graph. -/
def GroupInv (l : Graph) (a : GroupAcc) : Prop :=
  (∀ k, (a.buckets[k]?.getD []) = (triplesOf l k).reverse) ∧
  (∀ k, a.buckets[k]?.isSome = (triplesOf l k != [])) ∧
  a.orderRev.reverse = subjectOrder l

theorem subjectOrder_concat (l : Graph) (t : Triple) :
    subjectOrder (l ++ [t]) = subjectStep (subjectOrder l) t := by
  simp [subjectOrder, List.foldl_append]

theorem mem_subjectStep (acc : List String) (t : Triple) (k : String) :
    k ∈ subjectStep acc t ↔ k ∈ acc ∨ subjectKey t.s = k := by
  unfold subjectStep
  by_cases hc : acc.contains (subjectKey t.s) = true
  · simp only [hc, if_true]
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · subst h; simpa using hc
  · simp only [hc, Bool.false_eq_true, if_false, List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm

theorem mem_foldl_subjectStep (k : String) :
    ∀ (l : Graph) (acc : List String),
      k ∈ l.foldl subjectStep acc ↔ k ∈ acc ∨ triplesOf l k ≠ []
  | [], acc => by simp [triplesOf]
  | t :: l, acc => by
    rw [List.foldl_cons, mem_foldl_subjectStep k l, mem_subjectStep]
    by_cases hk : subjectKey t.s = k
    · have : triplesOf (t :: l) k ≠ [] := by simp [triplesOf, hk]
      simp only [this, hk, ne_eq, not_false_eq_true, or_true, true_or]
    · have : triplesOf (t :: l) k = triplesOf l k := by
        simp [triplesOf, hk]
      rw [this]
      simp only [hk, or_false]

theorem mem_subjectOrder (l : Graph) (k : String) :
    k ∈ subjectOrder l ↔ triplesOf l k ≠ [] := by
  simp [subjectOrder, mem_foldl_subjectStep]

theorem triplesOf_concat (l : Graph) (t : Triple) (k : String) :
    triplesOf (l ++ [t]) k = triplesOf l k ++ (if subjectKey t.s = k then [t] else []) := by
  by_cases hk : subjectKey t.s = k <;> simp [triplesOf, List.filter_append, hk]

theorem groupInv_nil : GroupInv [] { orderRev := [], buckets := ∅ } := by
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp [triplesOf, subjectOrder]

theorem groupInv_step (l : Graph) (a : GroupAcc) (t : Triple) (h : GroupInv l a) :
    GroupInv (l ++ [t]) (groupStep a t) := by
  obtain ⟨hb, hs, ho⟩ := h
  have hmem : ∀ k, (a.buckets[k]?.isSome = true) ↔ k ∈ subjectOrder l := by
    intro k; rw [hs k, mem_subjectOrder]; simp
  rcases hget : a.buckets[subjectKey t.s]? with _ | b
  · simp only [groupStep, hget]
    have hnin : subjectKey t.s ∉ subjectOrder l := fun hin => by
      have := (hmem _).mpr hin; rw [hget] at this; simp at this
    have hnil : triplesOf l (subjectKey t.s) = [] := by
      rw [mem_subjectOrder] at hnin; simpa using hnin
    refine ⟨?_, ?_, ?_⟩
    · intro k
      simp only [Std.HashMap.getElem?_insert, triplesOf_concat]
      by_cases hk : subjectKey t.s = k
      · subst hk; simp [hnil]
      · have hk' : (subjectKey t.s == k) = false := by simp [hk]
        simp [hk', hk, hb k]
    · intro k
      simp only [Std.HashMap.getElem?_insert, triplesOf_concat]
      by_cases hk : subjectKey t.s = k
      · subst hk; simp
      · have hk' : (subjectKey t.s == k) = false := by simp [hk]
        simp [hk', hk, hs k]
    · rw [subjectOrder_concat]
      simp only [subjectStep]
      rw [if_neg (by simpa using hnin), List.reverse_cons, ho]
  · simp only [groupStep, hget]
    have hin : subjectKey t.s ∈ subjectOrder l := (hmem _).mp (by simp [hget])
    have hbk : b = (triplesOf l (subjectKey t.s)).reverse := by
      have := hb (subjectKey t.s); rw [hget] at this; simpa using this
    refine ⟨?_, ?_, ?_⟩
    · intro k
      simp only [Std.HashMap.getElem?_insert, triplesOf_concat]
      by_cases hk : subjectKey t.s = k
      · subst hk; simp [hbk]
      · have hk' : (subjectKey t.s == k) = false := by simp [hk]
        simp [hk', hk, hb k]
    · intro k
      simp only [Std.HashMap.getElem?_insert, triplesOf_concat]
      by_cases hk : subjectKey t.s = k
      · subst hk; simp
      · have hk' : (subjectKey t.s == k) = false := by simp [hk]
        simp [hk', hk, hs k]
    · rw [subjectOrder_concat, ← ho]
      simp only [subjectStep]
      have : (subjectOrder l).contains (subjectKey t.s) = true := by simpa using hin
      rw [ho, if_pos this]

theorem groupInv_foldl :
    ∀ (g l : Graph) (a : GroupAcc), GroupInv l a → GroupInv (l ++ g) (g.foldl groupStep a)
  | [], l, a, h => by simpa using h
  | t :: g, l, a, h => by
    rw [List.foldl_cons]
    have := groupInv_foldl g (l ++ [t]) (groupStep a t) (groupInv_step l a t h)
    simpa using this

theorem subjectGroupsFast_eq (g : Graph) : subjectGroupsFast g = subjectGroups g := by
  obtain ⟨hb, -, ho⟩ := groupInv_foldl g [] _ groupInv_nil
  simp only [List.nil_append] at hb ho
  simp only [subjectGroupsFast, subjectGroups, ho]
  apply List.map_congr_left
  intro k _
  rw [hb k, List.reverse_reverse]

@[csimp] theorem subjectGroups_eq_fast : @subjectGroups = @subjectGroupsFast := by
  funext g; exact (subjectGroupsFast_eq g).symm

/-- Serialise a graph as RDF/XML. -/
def graphToRdfXml (g : Graph) : Except String String := do
  let nss := predicateNamespaces g
  let decls := String.join (nss.map (fun (ns, p) => s!"\n  xmlns:{p}=\"{escAttr ns}\""))
  let mut body := ""
  for (s, ts) in subjectGroups g do
    let head :=
      if s.startsWith "_:" then s!"  <rdf:Description rdf:nodeID=\"{escAttr (s.drop 2).toString}\">\n"
      else s!"  <rdf:Description rdf:about=\"{escAttr s}\">\n"
    let mut props := ""
    for t in ts do
      let name ← propertyName nss t.p
      props := props ++ (← renderObject name t.o)
    body := body ++ head ++ props ++ "  </rdf:Description>\n"
  return s!"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<rdf:RDF{decls}>\n{body}</rdf:RDF>\n"

/-! ## Build-time checks -/

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def sample : Graph :=
  [ { s := .iri (iri! "http://ex/s"), p := iri! "http://xmlns.com/foaf/0.1/name",
      o := .literal (Literal.string "A & B <c>") }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://xmlns.com/foaf/0.1/title",
      o := .literal (Literal.langString "hi" "en") }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://xmlns.com/foaf/0.1/age",
      o := .literal ⟨{ lexicalForm := "33", datatype := ⟨"http://www.w3.org/2001/XMLSchema#integer", rfl⟩,
                       langTag := none, direction := none }, rfl⟩ }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p/knows", o := .iri (iri! "http://ex/o") }
  , { s := .bnode "b1", p := iri! "http://ex/p/knows", o := .bnode "b2" }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
      o := .iri (iri! "http://ex/C") } ]

-- Written and read back through the RDF/XML parser, the graph is the same
-- up to blank node labels (the parser renames them), including an escaped literal, a language tag, a datatype, a
-- resource, blank nodes and `rdf:type`.
#guard match graphToRdfXml sample with
       | .ok t => (match RdfXml.parseRdfXml t with
                   | .ok g => g.isomorphic? sample
                   | .error _ => false)
       | .error _ => false
-- The refusals: a predicate with no XML name, a triple term, a control character.
#guard (graphToRdfXml [{ s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p/1x", o := .iri (iri! "http://ex/o") }]).toOption.isNone
#guard (graphToRdfXml [{ s := .iri (iri! "http://ex/s"), p := iri! "urn:nopath", o := .iri (iri! "http://ex/o") }]).toOption.isNone
private def ctrlGraph : Graph :=
  [{ s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p/q", o := .literal (Literal.string (String.singleton (Char.ofNat 1))) }]
#guard (graphToRdfXml ctrlGraph).toOption.isNone
#guard (graphToRdfXml []).toOption.isSome

-- Grouping: a subject whose triples are not adjacent gets one group, in the
-- place of its first triple, with its triples in graph order; the one-pass form
-- answers the same on this graph and on `sample`.
private def interleaved : Graph :=
  [ { s := .iri (iri! "http://ex/a"), p := iri! "http://ex/p/x", o := .iri (iri! "http://ex/o1") }
  , { s := .bnode "b", p := iri! "http://ex/p/x", o := .iri (iri! "http://ex/o2") }
  , { s := .iri (iri! "http://ex/a"), p := iri! "http://ex/p/y", o := .iri (iri! "http://ex/o3") } ]
#guard (subjectGroups interleaved).map (fun e => (e.1, e.2.length)) == [("http://ex/a", 2), ("_:b", 1)]
#guard (subjectGroups interleaved).map (fun e => (e.2.map (·.p.val))) ==
  [["http://ex/p/x", "http://ex/p/y"], ["http://ex/p/x"]]
#guard (subjectGroups interleaved).length != 3
#guard (subjectGroupsFast interleaved).map (fun e => (e.1, e.2.length)) == [("http://ex/a", 2), ("_:b", 1)]
#guard (subjectGroupsFast sample).map (fun e => (e.1, e.2.length)) ==
  (subjectGroups sample).map (fun e => (e.1, e.2.length))
#guard subjectGroups [] |>.isEmpty

end L4Factoidal.Syntax.RdfXmlWrite
