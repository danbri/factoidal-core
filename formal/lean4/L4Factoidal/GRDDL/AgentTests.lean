/-
L4Factoidal.GRDDL.AgentTests — positive and negative `#guard` cases for
`GRDDL.Agent`, over a pure document table (no I/O).

Each rule has a case that must find a transformation and a case built
so that a looser rule (an element scan, a list append, the requested IRI
as base) would answer wrongly.
-/
import L4Factoidal.GRDDL.Agent

namespace L4Factoidal.GRDDL.AgentTests

open L4Factoidal.RDF
open L4Factoidal.GRDDL

/-- A stylesheet whose output is `<rdf:RDF>body</rdf:RDF>` whatever the
    source. -/
def rdfStyle (body : String) : String :=
  "<xsl:stylesheet version='1.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'" ++
  " xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'" ++
  " xmlns:g='http://www.w3.org/2003/g/data-view#'>" ++
  "<xsl:template match='/'><rdf:RDF>" ++ body ++ "</rdf:RDF></xsl:template></xsl:stylesheet>"

def rdfDoc (body : String) : String :=
  "<rdf:RDF xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'" ++
  " xmlns:g='http://www.w3.org/2003/g/data-view#'>" ++ body ++ "</rdf:RDF>"

/-- A fetch over a table of `(iri, text)`; the retrieval IRI is the
    requested one unless the table names a redirection `(iri, "->" ++ target)`. -/
def tableFetch (tbl : List (String × String)) (iri : String) : Id (Option Representation) :=
  match tbl.find? (·.1 == iri) with
  | some (_, t) =>
      if t.startsWith "->" then
        let target := String.ofList (t.toList.drop 2)
        (tbl.find? (·.1 == target)).map (fun (_, t2) => { retrievedFrom := target, text := t2 })
      else some { retrievedFrom := iri, text := t }
  | none => none

def styles : List (String × String) :=
  [ ("http://ex/A", rdfStyle "<rdf:Description rdf:about='http://ex/a'><rdf:value>A</rdf:value></rdf:Description>"),
    ("http://ex/B", rdfStyle "<rdf:Description><rdf:value>B</rdf:value></rdf:Description>"),
    ("http://ex/C", rdfStyle "<rdf:Description><rdf:value>C</rdf:value></rdf:Description>"),
    ("http://ex/Self", rdfStyle "<rdf:Description rdf:about=''><rdf:value>self</rdf:value></rdf:Description>"),
    ("http://ex/N", rdfStyle "<rdf:Description rdf:about='http://ex/ns2'><g:namespaceTransformation rdf:resource='http://ex/A'/></rdf:Description>"),
    ("http://ex/E", rdfStyle "<rdf:Description rdf:about='http://ex/loop'><g:namespaceTransformation rdf:resource='http://ex/A'/></rdf:Description>") ]

def run (docs : List (String × String)) (iri : String) : Except String Gleaned :=
  Id.run (glean (tableFetch (docs ++ styles)) iri)

def txs (r : Except String Gleaned) : List String :=
  match r with | .ok g => g.transformations | .error _ => []

def graphOf (r : Except String Gleaned) : Graph :=
  match r with | .ok g => g.graph | .error _ => []

def subjectsOf (g : Graph) : List Subject := (g.map (·.s)).eraseDups

/-! ## §2 merge: blank nodes of two transforms stay apart -/

def twoBnodeSrc : List (String × String) :=
  [("http://ex/src", "<doc xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/B http://ex/C'/>")]

-- Both outputs use the parser's first label; the merge keeps them two nodes.
#guard (graphOf (run twoBnodeSrc "http://ex/src")).length == 2
#guard (subjectsOf (graphOf (run twoBnodeSrc "http://ex/src"))).length == 2
-- Negative: the same ground triple from two contributions is one triple.
#guard (mergeApart [graphOf (run [("http://ex/s", "<d xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/A'/>")] "http://ex/s"),
                    graphOf (run [("http://ex/s", "<d xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/A'/>")] "http://ex/s")]).length == 1

/-! ## §3 namespace transformations, read from the namespace document's GRDDL result -/

def nsRdf (subj : String) : List (String × String) :=
  [("http://ex/src", "<doc xmlns='http://ex/ns'/>"),
   ("http://ex/ns", rdfDoc ("<rdf:Description rdf:about='" ++ subj ++
      "'><g:namespaceTransformation rdf:resource='http://ex/A'/></rdf:Description>"))]

#guard txs (run (nsRdf "http://ex/ns") "http://ex/src") == ["http://ex/A"]
#guard (graphOf (run (nsRdf "http://ex/ns") "http://ex/src")).length == 1
-- Negative: the triple is about another resource, so it names nothing.
#guard txs (run (nsRdf "http://ex/other") "http://ex/src") == []

-- The namespace document is not RDF/XML; its own transformation yields
-- the namespaceTransformation triple (GRDDL §3, XML Schema example).
def nsByTransform : List (String × String) :=
  [("http://ex/src", "<doc xmlns='http://ex/ns2'/>"),
   ("http://ex/ns2", "<schema xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/N'/>")]
#guard txs (run nsByTransform "http://ex/src") == ["http://ex/A"]

-- Negative: an element NAMED namespaceTransformation in a namespace
-- document that has no GRDDL result is not an assertion.
def nsElementOnly : List (String × String) :=
  [("http://ex/src", "<doc xmlns='http://ex/ns3'/>"),
   ("http://ex/ns3", "<schema xmlns:g='http://www.w3.org/2003/g/data-view#' xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'><g:namespaceTransformation rdf:resource='http://ex/A'/></schema>")]
#guard txs (run nsElementOnly "http://ex/src") == []

/-! ## §5 profile transformations, read from the profile document's GRDDL result -/

def profileCase (pred : String) : List (String × String) :=
  [("http://ex/src", "<html xmlns='http://www.w3.org/1999/xhtml'><head profile='http://ex/prof'><title>t</title></head><body/></html>"),
   ("http://ex/prof", rdfDoc ("<rdf:Description rdf:about='http://ex/prof'><g:" ++ pred ++
      " rdf:resource='http://ex/A'/></rdf:Description>"))]

#guard txs (run (profileCase "profileTransformation") "http://ex/src") == ["http://ex/A"]
-- Negative: a namespaceTransformation assertion in a profile document
-- does not make a profile transformation.
#guard txs (run (profileCase "namespaceTransformation") "http://ex/src") == []

/-! ## A document that is its own namespace document (the `loop` tests) -/

def loopCase : List (String × String) :=
  [("http://ex/loop", "<loop xmlns='http://ex/loop' xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/E'/>")]

-- E names A as a namespace transformation of the document's own
-- namespace, so the fixpoint applies both, and stops.
#guard txs (run loopCase "http://ex/loop") == ["http://ex/E", "http://ex/A"]
#guard (match run loopCase "http://ex/loop" with | .ok g => g.converged | .error _ => false)
-- Negative: with one round only, the second-order transformation is not yet found.
#guard (match Id.run (glean (tableFetch (loopCase ++ styles)) "http://ex/loop" 1) with
        | .ok g => !g.converged && g.transformations == ["http://ex/E"]
        | .error _ => false)

/-! ## Base IRI after a redirection (RFC 3986 §5.1.3) -/

def redirectCase : List (String × String) :=
  [("http://ex/old", "->http://ex/new/doc"),
   ("http://ex/new/doc", "<d xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/Self'/>")]

#guard (subjectsOf (graphOf (run redirectCase "http://ex/old"))).map (fun
          | .iri i => i.val | .bnode b => b) == ["http://ex/new/doc"]
-- Negative: the requested IRI is not the subject.
#guard !((subjectsOf (graphOf (run redirectCase "http://ex/old"))).map (fun
          | .iri i => i.val | .bnode b => b)).contains "http://ex/old"

/-! ## Retrieval is a parameter, so a language-negotiated resource needs no library support

`fetch` may answer differently for an agent that asks for another
language (RFC 9110 section 12.5.4). The GRDDL Test Cases cases
`langconneg1` to `langconneg3` rest on this: an agent that retrieves the
English representation, one that retrieves the German one, and one that
retrieves both and merges the results (GRDDL section 2). -/

def titleStyle : String :=
  "<xsl:stylesheet version='1.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'" ++
  " xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'>" ++
  "<xsl:template match='/'><rdf:RDF><rdf:Description rdf:about='http://ex/album'>" ++
  "<rdf:value><xsl:value-of select='/doc/title'/></rdf:value></rdf:Description></rdf:RDF>" ++
  "</xsl:template></xsl:stylesheet>"

/-- The one resource has an English and a German representation. -/
def negotiated (lang : String) : List (String × String) :=
  [("http://ex/conneg",
    "<doc xmlns:g='http://www.w3.org/2003/g/data-view#' g:transformation='http://ex/Title'><title>" ++
    (if lang == "de" then "Hast Du Erfahrung?" else "Are You Experienced?") ++ "</title></doc>"),
   ("http://ex/Title", titleStyle)]

def runAs (lang : String) : Graph :=
  match Id.run (glean (tableFetch (negotiated lang)) "http://ex/conneg") with
  | .ok g => g.graph
  | .error _ => []

-- Each representation has its own GRDDL result, of one triple.
#guard (runAs "en").length == 1
#guard (runAs "de").length == 1
-- Negative: the two results are different graphs (an agent that ignored
-- the language would give the same graph twice).
#guard runAs "en" != runAs "de"
-- The agent that retrieves both: the merge has both titles, and no
-- more than the two (the same representation twice adds nothing).
#guard (mergeApart [runAs "en", runAs "de"]).length == 2
#guard (mergeApart [runAs "en", runAs "en"]).length == 1

/-! ## A source that cannot be retrieved is an error, never an empty result -/

#guard (match run [] "http://ex/absent" with | .error _ => true | .ok _ => false)

end L4Factoidal.GRDDL.AgentTests
