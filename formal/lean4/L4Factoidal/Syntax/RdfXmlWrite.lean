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
refused. A directional language string (RDF 1.2) is written with `its:dir`
and `rdf:version="1.2"` on its property element (RDF 1.2 XML Syntax). Characters XML 1.0 cannot carry are refused.

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
import L4Factoidal.RDF.Runs

namespace L4Factoidal.Syntax.RdfXmlWrite

open L4Factoidal.RDF

private def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
private def xsdString : String := "http://www.w3.org/2001/XMLSchema#string"

/-- The key of a subject: its IRI, or `_:` and its blank node label. -/
def subjectKey : Subject → String
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

/-- One step of the namespace list: the namespace of predicate `p`, when it has one,
    is not `rdf` and is not in the list yet, goes at the end. -/
def nsStep (acc : List String) (p : WfIri) : List String :=
  match nsSplit p.val with
  | some (ns, _) => if ns == rdfNs || acc.contains ns then acc else acc ++ [ns]
  | none => acc

/-- The namespaces of a list of predicates, each with a prefix. `rdf` is always
    bound; others are `ns1`, `ns2`, in first-use order. The list depends only on
    the order in which the predicates first appear, so a caller that knows the
    predicates of a graph in that order (`l4sbm11 export` reads them from the
    store before it writes) gets the table of the whole graph. -/
def namespacesOf (ps : List WfIri) : List (String × String) :=
  let nss := ps.foldl nsStep []
  (rdfNs, "rdf") :: nss.zipIdx.map (fun (ns, i) => (ns, "ns" ++ toString (i + 1)))

/-- The namespaces of a graph's predicates (`namespacesOf`). -/
def predicateNamespaces (g : Graph) : List (String × String) := namespacesOf (g.map (·.p))

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
        | some tag =>
            match l.direction with
            | none => .ok s!"    <{name} xml:lang=\"{escAttr tag}\">{esc l.lexicalForm}</{name}>\n"
            | some d =>
                -- RDF 1.2 XML Syntax: `its:dir` gives the base direction when
                -- `rdf:version="1.2"` is in scope (W3C test rdf12-xml-dir-05).
                let dir := match d with | .ltr => "ltr" | .rtl => "rtl"
                .ok s!"    <{name} xml:lang=\"{escAttr tag}\" rdf:version=\"1.2\" xmlns:its=\"http://www.w3.org/2005/11/its\" its:version=\"2.0\" its:dir=\"{dir}\">{esc l.lexicalForm}</{name}>\n"
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

/-! ## The document

`graphToRdfXmlWith nss g` writes the graph with the namespace table `nss`: the
header (`headerOf`), one `rdf:Description` for each subject group
(`descriptionText`), and the end tag. `graphToRdfXml` takes the table of the
graph's own predicates. -/

/-- The XML declaration and the start tag of `rdf:RDF` with the namespace
    declarations. -/
def headerOf (nss : List (String × String)) : String :=
  let decls := String.join (nss.map (fun (ns, p) => s!"\n  xmlns:{p}=\"{escAttr ns}\""))
  s!"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<rdf:RDF{decls}>\n"

/-- The end tag of `rdf:RDF`. -/
def footer : String := "</rdf:RDF>\n"

/-- The property elements of the triples, after `acc`. -/
def propsText (nss : List (String × String)) (acc : String) : List Triple → Except String String
  | [] => .ok acc
  | t :: ts =>
      match propertyName nss t.p with
      | .error e => .error e
      | .ok name =>
          match renderObject name t.o with
          | .error e => .error e
          | .ok x => propsText nss (acc ++ x) ts

/-- The `rdf:Description` of the subject with key `s` and its triples `ts`. -/
def descriptionText (nss : List (String × String)) (s : String) (ts : List Triple) :
    Except String String :=
  let head :=
    if s.startsWith "_:" then s!"  <rdf:Description rdf:nodeID=\"{escAttr (s.drop 2).toString}\">\n"
    else s!"  <rdf:Description rdf:about=\"{escAttr s}\">\n"
  match propsText nss "" ts with
  | .error e => .error e
  | .ok props => .ok (head ++ props ++ "  </rdf:Description>\n")

/-- The descriptions of the groups, after `acc`. -/
def groupsText (nss : List (String × String)) (acc : String) :
    List (String × List Triple) → Except String String
  | [] => .ok acc
  | (s, ts) :: gs =>
      match descriptionText nss s ts with
      | .error e => .error e
      | .ok d => groupsText nss (acc ++ d) gs

/-- The text with the end tag added, or the error. -/
def withFooter : Except String String → Except String String
  | .ok b => .ok (b ++ footer)
  | .error e => .error e

/-- Serialise a graph as RDF/XML with the namespace table `nss`: one
    `rdf:Description` for each subject (`subjectGroups`). -/
def graphToRdfXmlWith (nss : List (String × String)) (g : Graph) : Except String String :=
  withFooter (groupsText nss (headerOf nss) (subjectGroups g))

/-- Serialise a graph as RDF/XML. -/
def graphToRdfXml (g : Graph) : Except String String :=
  graphToRdfXmlWith (predicateNamespaces g) g

/-! ## The stream form

A writer that gets the triples one at a time keeps the key of the current subject
and its triples (`Open`), and writes the subject's `rdf:Description` when a triple
of another subject arrives (`rxPush`) or at the end (`rxFinish`). It holds one
subject's triples and the namespace table, which the caller gives at the start
(https://github.com/danbri/factoidal/issues/846). `rxRun` runs it over a list.

`rxRun_eq` says what it writes: the descriptions of the runs of the list
(`Runs.runsFrom`). When each subject's triples are consecutive (`Contiguous`, which
the SPO order of a store gives), the runs are the subject groups
(`subjectGroups_eq_runs`), and the stream writes the text of the whole-graph writer
(`streamRdfXml_eq`, `streamRdfXml_eq_graphToRdfXml`). When they are not, the stream
writes a second `rdf:Description` for a subject that comes back, which is the same
graph. -/

/-- The open subject group: the subject key and its triples, the newest first. -/
abbrev Open := Option (String × List Triple)

def tripleKey (t : Triple) : String := subjectKey t.s

/-- Give the stream one triple: the text it completes and the new open group. -/
def rxPush (nss : List (String × String)) : Open → Triple → Except String (Open × String)
  | none, t => .ok (some (tripleKey t, [t]), "")
  | some (k, ts), t =>
      if k == tripleKey t then .ok (some (k, t :: ts), "")
      else
        match descriptionText nss k ts.reverse with
        | .error e => .error e
        | .ok d => .ok (some (tripleKey t, [t]), d)

/-- The end of the stream: the open group's description and the end tag. -/
def rxFinish (nss : List (String × String)) : Open → Except String String
  | none => .ok footer
  | some (k, ts) =>
      match descriptionText nss k ts.reverse with
      | .error e => .error e
      | .ok d => .ok (d ++ footer)

/-- The stream over a list, after the text `acc`. -/
def rxRun (nss : List (String × String)) : Open → String → List Triple → Except String String
  | cur, acc, [] =>
      match rxFinish nss cur with
      | .error e => .error e
      | .ok e => .ok (acc ++ e)
  | cur, acc, t :: l =>
      match rxPush nss cur t with
      | .error e => .error e
      | .ok (c, s) => rxRun nss c (acc ++ s) l

/-- The document the stream writes for the triples `l`. -/
def streamRdfXml (nss : List (String × String)) (l : List Triple) : Except String String :=
  rxRun nss none (headerOf nss) l

/-- Each subject's triples are consecutive in `l`: no two runs have the same subject. -/
def Contiguous (l : List Triple) : Prop := ((Runs.runs tripleKey l).map (·.1)).Nodup

theorem groupsText_singleton (nss : List (String × String)) (acc s : String) (ts : List Triple) :
    withFooter (groupsText nss acc [(s, ts)]) =
      match descriptionText nss s ts with
      | .error e => .error e
      | .ok d => .ok (acc ++ (d ++ footer)) := by
  unfold groupsText
  cases descriptionText nss s ts <;> simp [groupsText, withFooter, String.append_assoc]

/-- The stream writes the descriptions of the runs. -/
theorem rxRun_eq (nss : List (String × String)) :
    ∀ (l : List Triple) (cur : Open) (acc : String),
      rxRun nss cur acc l = withFooter (groupsText nss acc (Runs.runsFrom tripleKey cur l))
  | [], none, acc => by simp [rxRun, rxFinish, Runs.runsFrom, groupsText, withFooter]
  | [], some (k, ts), acc => by
      rw [rxRun, Runs.runsFrom, groupsText_singleton]
      simp only [rxFinish]
      cases descriptionText nss k ts.reverse <;> rfl
  | t :: l, none, acc => by
      have : rxRun nss none acc (t :: l) = rxRun nss (some (tripleKey t, [t])) acc l := by
        simp [rxRun, rxPush]
      rw [this, rxRun_eq nss l _ acc]
      simp [Runs.runsFrom]
  | t :: l, some (k, ts), acc => by
      by_cases hk : (k == tripleKey t) = true
      · have : rxRun nss (some (k, ts)) acc (t :: l) = rxRun nss (some (k, t :: ts)) acc l := by
          simp [rxRun, rxPush, hk]
        rw [this, rxRun_eq nss l _ acc]
        simp [Runs.runsFrom, hk]
      · cases hd : descriptionText nss k ts.reverse with
        | error e => simp [rxRun, rxPush, hk, hd, Runs.runsFrom, groupsText, withFooter]
        | ok d =>
            have : rxRun nss (some (k, ts)) acc (t :: l) =
                rxRun nss (some (tripleKey t, [t])) (acc ++ d) l := by
              simp [rxRun, rxPush, hk, hd]
            rw [this, rxRun_eq nss l _ (acc ++ d)]
            simp [Runs.runsFrom, hk, groupsText, hd]

/-! ### The runs of a contiguous graph are its subject groups -/

theorem foldl_subjectStep_mem (k : String) :
    ∀ (ts : List Triple) (acc : List String), (∀ y ∈ ts, tripleKey y = k) → k ∈ acc →
      ts.foldl subjectStep acc = acc
  | [], _, _, _ => rfl
  | t :: ts, acc, hk, hm => by
      have ht : subjectKey t.s = k := hk t (by simp)
      simp only [List.foldl_cons, subjectStep, ht, List.contains_iff_mem, hm, if_true]
      exact foldl_subjectStep_mem k ts acc (fun y hy => hk y (by simp [hy])) hm

theorem foldl_subjectStep_run (k : String) (ts : List Triple) (acc : List String)
    (hne : ts ≠ []) (hk : ∀ y ∈ ts, tripleKey y = k) (hm : k ∉ acc) :
    ts.foldl subjectStep acc = acc ++ [k] := by
  cases ts with
  | nil => exact absurd rfl hne
  | cons t ts =>
      have ht : subjectKey t.s = k := hk t (by simp)
      have hm' : (acc.contains k) = false := by simpa [List.contains_iff_mem] using hm
      simp only [List.foldl_cons, subjectStep, ht, hm', Bool.false_eq_true, if_false]
      exact foldl_subjectStep_mem k ts _ (fun y hy => hk y (by simp [hy])) (by simp)

/-- The run properties `Runs.mem_runs` gives, for groups of triples by subject key. -/
def GoodGroups (gs : List (String × List Triple)) : Prop :=
  ∀ r ∈ gs, r.2 ≠ [] ∧ ∀ y ∈ r.2, tripleKey y = r.1

theorem foldl_subjectStep_groups :
    ∀ (gs : List (String × List Triple)) (acc : List String), GoodGroups gs →
      (gs.map (·.1)).Nodup → (∀ r ∈ gs, r.1 ∉ acc) →
      (gs.flatMap (·.2)).foldl subjectStep acc = acc ++ gs.map (·.1)
  | [], acc, _, _, _ => by simp
  | r :: gs, acc, hg, hnd, hout => by
      simp only [List.flatMap_cons, List.foldl_append, List.map_cons]
      obtain ⟨hne, hk⟩ := hg r (by simp)
      rw [foldl_subjectStep_run r.1 r.2 acc hne hk (hout r (by simp))]
      have hnd' := List.nodup_cons.mp hnd
      rw [foldl_subjectStep_groups gs (acc ++ [r.1]) (fun x hx => hg x (by simp [hx])) hnd'.2]
      · simp
      · intro x hx hmem
        rcases List.mem_append.mp hmem with h | h
        · exact hout x (by simp [hx]) h
        · have : x.1 = r.1 := by simpa using h
          exact hnd'.1 (List.mem_map.mpr ⟨x, hx, this⟩)

theorem filter_groups :
    ∀ (gs : List (String × List Triple)), GoodGroups gs → (gs.map (·.1)).Nodup →
      ∀ r ∈ gs, (gs.flatMap (·.2)).filter (fun t => subjectKey t.s == r.1) = r.2
  | [], _, _, r, hr => by simp at hr
  | r0 :: gs, hg, hnd, r, hr => by
      have hnd' := List.nodup_cons.mp hnd
      have hg' : GoodGroups gs := fun x hx => hg x (by simp [hx])
      obtain ⟨_, hk0⟩ := hg r0 (by simp)
      simp only [List.flatMap_cons, List.filter_append]
      rcases List.mem_cons.mp hr with rfl | hr
      · have h1 : r.2.filter (fun t => subjectKey t.s == r.1) = r.2 := by
          apply List.filter_eq_self.mpr
          intro t ht; simpa [tripleKey] using hk0 t ht
        have h2 : (gs.flatMap (·.2)).filter (fun t => subjectKey t.s == r.1) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro t ht
          obtain ⟨x, hx, htx⟩ := List.mem_flatMap.mp ht
          have hkx : subjectKey t.s = x.1 := (hg' x hx).2 t htx
          intro heq
          have : x.1 = r.1 := by rw [← hkx]; simpa using heq
          exact hnd'.1 (List.mem_map.mpr ⟨x, hx, this⟩)
        rw [h1, h2, List.append_nil]
      · have h1 : r0.2.filter (fun t => subjectKey t.s == r.1) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro t ht heq
          have hk : subjectKey t.s = r0.1 := hk0 t ht
          have : r.1 = r0.1 := by rw [← hk]; exact (beq_iff_eq.mp heq).symm
          exact hnd'.1 (List.mem_map.mpr ⟨r, hr, this⟩)
        rw [h1, List.nil_append]
        exact filter_groups gs hg' hnd'.2 r hr

theorem subjectGroups_of_groups (gs : List (String × List Triple)) (hg : GoodGroups gs)
    (hnd : (gs.map (·.1)).Nodup) : subjectGroups (gs.flatMap (·.2)) = gs := by
  unfold subjectGroups subjectOrder
  rw [foldl_subjectStep_groups gs [] hg hnd (by simp), List.nil_append, List.map_map]
  conv => rhs; rw [← List.map_id gs]
  apply List.map_congr_left
  intro r hr
  simp only [Function.comp, triplesOf, id]
  rw [filter_groups gs hg hnd r hr]

/-- The subject groups of a contiguous graph are its runs. -/
theorem subjectGroups_eq_runs (l : List Triple) (h : Contiguous l) :
    subjectGroups l = Runs.runs tripleKey l := by
  have := subjectGroups_of_groups (Runs.runs tripleKey l) (Runs.mem_runs tripleKey l) h
  rwa [Runs.runs_flatten] at this

/-- The stream writes the text of the whole-graph writer with the same namespace
    table, for a graph whose subjects' triples are consecutive. -/
theorem streamRdfXml_eq (nss : List (String × String)) (l : List Triple) (h : Contiguous l) :
    streamRdfXml nss l = graphToRdfXmlWith nss l := by
  unfold streamRdfXml graphToRdfXmlWith
  rw [rxRun_eq, subjectGroups_eq_runs l h]
  rfl

/-- With the namespace table of the graph's predicates, the stream writes the text of
    `graphToRdfXml`. -/
theorem streamRdfXml_eq_graphToRdfXml (l : List Triple) (h : Contiguous l) :
    streamRdfXml (predicateNamespaces l) l = graphToRdfXml l :=
  streamRdfXml_eq _ l h

#print axioms rxRun_eq
#print axioms subjectGroups_eq_runs
#print axioms streamRdfXml_eq
#print axioms streamRdfXml_eq_graphToRdfXml

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
-- RDF 1.2: a directional language string keeps its base direction
-- (`its:dir` with `rdf:version="1.2"` on the property element, the form of the
-- W3C test rdf12-xml-dir-05). Before 2026-10-24 the writer wrote `xml:lang` only
-- and the direction was lost (https://github.com/danbri/factoidal/issues/975, phase C).
private def dirGraph : Graph :=
  [ { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p/q", o := .literal (Literal.dirLangString "y" "ar" .rtl) }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p/r", o := .literal (Literal.dirLangString "x" "en" .ltr) }
  , { s := .iri (iri! "http://ex/s"), p := iri! "http://ex/p/t", o := .literal (Literal.langString "z" "fr") } ]
#guard match graphToRdfXml dirGraph with
       | .ok t => (match RdfXml.parseRdfXml t with
                   | .ok g => g.isomorphic? dirGraph
                   | .error _ => false)
       | .error _ => false
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

-- The text of the whole-graph writer, pinned as it was before the stream form was added
-- (2026-10-22): three triples of two subjects, the first subject's triples not adjacent.
private def pinned : Graph :=
  [ { s := .iri (iri! "http://ex/a"), p := iri! "http://ex/p/x", o := .iri (iri! "http://ex/o1") }
  , { s := .bnode "b", p := iri! "http://xmlns.com/foaf/0.1/name", o := .literal (Literal.string "A & B <c>") }
  , { s := .iri (iri! "http://ex/a"), p := iri! "http://ex/p/y", o := .literal (Literal.langString "hi" "en") } ]
#guard (graphToRdfXml pinned).toOption == some "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<rdf:RDF\n  xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n  xmlns:ns1=\"http://ex/p/\"\n  xmlns:ns2=\"http://xmlns.com/foaf/0.1/\">\n  <rdf:Description rdf:about=\"http://ex/a\">\n    <ns1:x rdf:resource=\"http://ex/o1\"/>\n    <ns1:y xml:lang=\"en\">hi</ns1:y>\n  </rdf:Description>\n  <rdf:Description rdf:nodeID=\"b\">\n    <ns2:name>A &amp; B &lt;c&gt;</ns2:name>\n  </rdf:Description>\n</rdf:RDF>\n"
-- The stream over the same triples with the subject `a` contiguous writes the same text.
#guard (match pinned with
        | [a, b, c] => (streamRdfXml (predicateNamespaces pinned) [a, c, b]).toOption == (graphToRdfXml pinned).toOption
        | _ => false)
-- Not contiguous: a second description of `a`, and the same graph read back.
#guard match streamRdfXml (predicateNamespaces pinned) pinned with
       | .ok t => (t.splitOn "rdf:about=\"http://ex/a\"").length == 3 &&
                  (match RdfXml.parseRdfXml t with
                   | .ok g => g.isomorphic? pinned
                   | .error _ => false)
       | .error _ => false
#guard match streamRdfXml (predicateNamespaces sample) sample with
       | .ok t => (match RdfXml.parseRdfXml t with
                   | .ok g => g.isomorphic? sample
                   | .error _ => false)
       | .error _ => false
-- The stream refuses what the whole-graph writer refuses.
#guard (streamRdfXml (predicateNamespaces ctrlGraph) ctrlGraph).toOption.isNone

end L4Factoidal.Syntax.RdfXmlWrite
