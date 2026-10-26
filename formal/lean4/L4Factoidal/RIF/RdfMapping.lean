/- Shared RDF/RIF term and triple conversion for saturation and the native
   conformance runner (RIF-RDF/OWL Compatibility §3). PlainLiteral decoding
   delegates to the datatype-value adapter; empty tags denote strings. -/
import L4Factoidal.RIF.Engine
import L4Factoidal.RDF.Graph
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.RIF.RdfMapping
open L4Factoidal.RDF

def rdfTypeStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfsSubClassStr : String := "http://www.w3.org/2000/01/rdf-schema#subClassOf"

/-- An RDF term as a RIF constant (RIF-RDF Compatibility §3). -/
def gOfTerm : Term → Option GTerm
  | .iri i     => some (gIri i.val)
  | .literal l =>
      if l.val.direction.isSome then none
      else (match l.val.langTag with
       | some tag => some (.const (l.val.lexicalForm ++ "@" ++ tag)
                                  (rdfNs ++ "PlainLiteral"))
       | none     => some (.const l.val.lexicalForm l.val.datatype.val))
  | .bnode b   => some (.const b localSpace)
  | _          => none

/-- Reject inputs that the RIF representation cannot preserve, including RDF
    1.2 direction and triple terms. Callers must not silently drop these facts. -/
def graphMappingSupported (g : Graph) : Bool :=
  g.all (fun t => (gOfTerm t.o).isSome)

def gOfSubject : Subject → GTerm
  | .iri i   => gIri i.val
  | .bnode b => .const b localSpace

/-- A triple as RIF facts. -/
def factsOfTriple (t : Triple) : List GAtom :=
  match gOfTerm t.o with
  | none => []
  | some o =>
      let s := gOfSubject t.s
      let base := [GAtom.frame s (gIri t.p.val) o]
      if t.p.val == rdfTypeStr then base ++ [GAtom.member s o]
      else if t.p.val == rdfsSubClassStr then base ++ [GAtom.sub s o]
      else base

/-- A RIF constant as an RDF term — the reverse reading. `none` when
the constant has no well-formed RDF form. -/
def termOfG : GTerm → Option Term
  | .const l sp =>
      if sp == iriSpace then
        if h : isIri l then some (.iri ⟨l, h⟩) else none
      else if sp == localSpace then some (.bnode l)
      else if sp == rdfNs ++ "PlainLiteral" then
        match literalValue? (.const l sp) with
        | some (.xsd (.str .string text)) => some (.literal (Literal.string text))
        | some (.tagged text tag) => some (.literal (Literal.langString text tag))
        | _ => none
      else
        if h : isIri sp then
          let lit : Literal := { lexicalForm := l, datatype := ⟨sp, h⟩,
                                 langTag := none, direction := none }
          if h2 : literalWf lit then some (.literal ⟨lit, h2⟩) else none
        else none
  | _ => none

def subjectOfG : GTerm → Option Subject
  | .const l sp =>
      if sp == iriSpace then
        if h : isIri l then some (.iri ⟨l, h⟩) else none
      else if sp == localSpace then some (.bnode l)
      else none
  | _ => none

def predOfG : GTerm → Option WfIri
  | .const l sp =>
      if sp == iriSpace then
        if h : isIri l then some ⟨l, h⟩ else none
      else none
  | _ => none

def mkTriple (s p o : GTerm) : Option Triple := do
  let s ← subjectOfG s
  let p ← predOfG p
  let o ← termOfG o
  pure ⟨s, p, o⟩

/-- A derived fact as a triple. -/
def tripleOfGAtom : GAtom → Option Triple
  | .frame o p v => mkTriple o p v
  | .member o c  => do
      let s ← subjectOfG o
      let t ← termOfG c
      pure ⟨s, L4Factoidal.RDFS.rdfType, t⟩
  | .sub c d => do
      let s ← subjectOfG c
      let t ← termOfG d
      pure ⟨s, L4Factoidal.RDFS.rdfsSubClassOf, t⟩
  | .pos _ _ _ => none

end L4Factoidal.RIF.RdfMapping
