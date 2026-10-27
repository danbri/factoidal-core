/-
L4Factoidal.RDF.IriSplit — an IRI as a namespace and an XML local name.

https://github.com/danbri/factoidal/issues/1051 item 4 (IRI split; Jena
`SplitIRI.splitXML`, RDFLib `compute_qname`).

## The rule

`splitIriXml iri` gives `(namespace, localName)` with `namespace ++ localName =
iri` (`splitIriXml_append`). The local name is the longest suffix of the IRI
that is an XML `NCName` (Namespaces in XML 1.0, section 3, production `[4]
NCName`; the characters are those of `L4Factoidal.XML.isNCNameStartChar` and
`isNCNameChar`). That is the name a qualified name of RDF/XML can carry
(RDF 1.1 XML Syntax, section 2.2: a property element is a QName). When no
suffix is an NCName (the IRI ends in `/`, `#`, `:` or a digit run after one
of these), the local name is empty and the namespace is the whole IRI.

Examples (`#guard`s below): `http://e/ns#name` gives `http://e/ns#` and
`name`; `http://e/123abc` gives `http://e/123` and `abc` (an NCName does not
start with a digit); `http://e/a/` gives the whole IRI and `""`;
`urn:isbn:0451` gives the whole IRI and `""`.

The check of a prefix label (Jena `PrefixMapping.setNsPrefix`, RDFLib
`NamespaceManager.bind`) is `isNCNameOrEmpty`: the empty string (the default
prefix) or an NCName.
-/
import L4Factoidal.XML.Wellformedness

namespace L4Factoidal.RDF

open L4Factoidal.XML

/-- The index of the first character of the local name in `cs`: the start of
the longest NCName suffix, or `cs.length` when there is none. The run of NCName
characters at the end is cut before its first NCName start character. -/
def xmlSplitIndex (cs : List Char) : Nat :=
  let run := (cs.reverse.takeWhile isNCNameChar).reverse
  let skip := (run.takeWhile (fun c => !isNCNameStartChar c)).length
  cs.length - run.length + skip

/-- `(namespace, localName)` of an IRI (see the module header). -/
def splitIriXml (iri : String) : String × String :=
  let cs := iri.toList
  let i := xmlSplitIndex cs
  (String.ofList (cs.take i), String.ofList (cs.drop i))

/-- The two parts are the IRI. -/
theorem splitIriXml_append (iri : String) :
    (splitIriXml iri).1 ++ (splitIriXml iri).2 = iri := by
  simp only [splitIriXml]
  rw [← String.ofList_append, List.take_append_drop, String.ofList_toList]

/-- The empty string or an XML NCName: a prefix label. -/
def isNCNameOrEmpty (s : String) : Bool := s.isEmpty || isValidNCName s

#guard splitIriXml "http://e/ns#name" == ("http://e/ns#", "name")
#guard splitIriXml "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" ==
  ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "type")
#guard splitIriXml "http://e/a/b" == ("http://e/a/", "b")
#guard splitIriXml "http://e/123abc" == ("http://e/123", "abc")
#guard splitIriXml "http://e/a/" == ("http://e/a/", "")
#guard splitIriXml "http://e/ns#" == ("http://e/ns#", "")
#guard splitIriXml "urn:isbn:0451" == ("urn:isbn:0451", "")
#guard splitIriXml "http://e/a.b-c_d" == ("http://e/", "a.b-c_d")
#guard splitIriXml "http://e/x%20y" == ("http://e/x%20", "y")
#guard splitIriXml "http://e/café" == ("http://e/", "café")
#guard splitIriXml "http://e/_a" == ("http://e/", "_a")
#guard splitIriXml "" == ("", "")
#guard [ "http://e/ns#name", "http://e/123abc", "urn:x:9", "http://e/a.b" ].all fun i =>
  let (_, l) := splitIriXml i; l.isEmpty || isValidNCName l
#guard isNCNameOrEmpty "" && isNCNameOrEmpty "ex" && isNCNameOrEmpty "a.b-c"
#guard !isNCNameOrEmpty "1a" && !isNCNameOrEmpty "a:b" && !isNCNameOrEmpty "a b"

end L4Factoidal.RDF
