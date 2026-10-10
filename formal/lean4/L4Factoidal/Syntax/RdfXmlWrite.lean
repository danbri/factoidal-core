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
-/
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.XSD.Datatypes
import L4Factoidal.RDF.Isomorphism

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

/-- Serialise a graph as RDF/XML. -/
def graphToRdfXml (g : Graph) : Except String String := do
  let nss := predicateNamespaces g
  let decls := String.join (nss.map (fun (ns, p) => s!"\n  xmlns:{p}=\"{escAttr ns}\""))
  let subjects : List String := g.foldl (fun acc t =>
    let k := subjectKey t.s
    if acc.contains k then acc else acc ++ [k]) []
  let mut body := ""
  for s in subjects do
    let ts := g.filter (fun t => subjectKey t.s == s)
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

end L4Factoidal.Syntax.RdfXmlWrite
