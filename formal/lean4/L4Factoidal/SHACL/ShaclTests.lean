/-
L4Factoidal.SHACL.ShaclTests — build-time `#guard`s for the SHACL Core
validator on small shapes + data graphs written in Turtle and parsed
by the Lean Turtle parser at elaboration time.

Each guard names the Recommendation clause it pins. The real W3C
suite is run by `Harness/ShaclProbe.lean` (`lake exe l4shacl`); these
are the unit-level checks that fail the BUILD when a clause regresses
(the sabotage discipline of `skills/factoidal-lean-basics`).
-/
import L4Factoidal.SHACL.Report
import L4Factoidal.SHACL.Sparql
import L4Factoidal.SHACL.NodeExpr
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.SHACL.Tests

open L4Factoidal.RDF L4Factoidal.SHACL L4Factoidal.Syntax

def prefixes : String :=
  "@prefix ex: <http://example.org/> . @prefix sh: <http://www.w3.org/ns/shacl#> . " ++
  "@prefix xsd: <http://www.w3.org/2001/XMLSchema#> . " ++
  "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> . " ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . "

/-- Parse a Turtle body (prefixes prepended); an unparsable fixture is
the empty graph, which the guards below cannot mistake for a pass
because each one asserts a specific result count. -/
def ttl (body : String) : Graph :=
  match parseTurtle (prefixes ++ body) (some "http://example.org/doc") with
  | .ok g => g
  | .error _ => []

/-- Validate a document against itself (data graph = shapes graph). -/
def run (body : String) : ValidationReport :=
  let g := ttl body
  validate g (decodeShapesGraph g)

/-- Validate an RDF 1.2 Turtle document (triple terms) against itself. -/
def run12 (body : String) : ValidationReport :=
  let g := match parseTurtle (prefixes ++ body) (some "http://example.org/doc") .rdf12 with
    | .ok g => g
    | .error _ => []
  validate g (decodeShapesGraph g)

def components (r : ValidationReport) : List WfIri :=
  r.results.map fun v => constraintComponentIri v.constraint

def exIri (local_ : String) : WfIri := ⟨"http://example.org/" ++ local_, by simp [isIri]⟩

/-! ### §4.2.2 sh:maxCount — one result per focus node, no sh:value -/

def maxCountDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:maxCount 1 ] . " ++
  "ex:bob a ex:Person ; ex:name \"A\", \"B\" . ex:ann a ex:Person ; ex:name \"C\" ."

#guard (run maxCountDoc).conforms == false
#guard components (run maxCountDoc) == [shMaxCountCC]
#guard (run maxCountDoc).results.map (·.focus) == [.iri (exIri "bob")]
#guard (run maxCountDoc).results.map (·.value) == [none]

/-! ### §4.2.1 sh:minCount 0 never produces a result -/

def minCountZeroDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetClass ex:Person ; sh:property [ sh:path ex:name ; sh:minCount 0 ] . " ++
  "ex:bob a ex:Person ."

#guard (run minCountZeroDoc).conforms == true
#guard (run minCountZeroDoc).results.length == 0

/-! ### §4.6.1 sh:not flips conformance -/

def notDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n, ex:m ; sh:not [ sh:class ex:C ] . ex:n a ex:C . ex:m a ex:D ."

#guard components (run notDoc) == [shNotCC]
#guard (run notDoc).results.map (·.focus) == [.iri (exIri "n")]

/-! ### §4.1.2 sh:datatype — ill-formed literals do not match -/

def datatypeDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"aldi\"^^xsd:integer, \"12\"^^xsd:integer, \"300\"^^xsd:byte, \"3\"^^xsd:byte ; " ++
  "sh:datatype xsd:integer ."

#guard (run datatypeDoc).results.length == 3   -- "aldi" and both xsd:byte values

def byteDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"300\"^^xsd:byte, \"c\"^^xsd:byte, \"3\"^^xsd:byte ; sh:datatype xsd:byte ."

#guard (run byteDoc).results.length == 2

/-! ### §1.4 / §4.1.1 sh:class — SHACL instance through rdfs:subClassOf* -/

def classDoc : String :=
  "ex:Sub rdfs:subClassOf ex:Mid . ex:Mid rdfs:subClassOf ex:Super . ex:x a ex:Sub . ex:y a ex:Other . " ++
  "ex:S a sh:NodeShape ; sh:targetNode ex:x, ex:y ; sh:class ex:Super ."

#guard (run classDoc).results.map (·.focus) == [.iri (exIri "y")]
#guard isShaclInstance (ttl classDoc) (.iri (exIri "x")) (exIri "Super") == true
#guard isShaclInstance (ttl classDoc) (.iri (exIri "x")) (exIri "Sub") == true
#guard isShaclInstance (ttl classDoc) (.iri (exIri "y")) (exIri "Super") == false

/-! ### §2.1.3.1 implicit class target -/

def implicitDoc : String :=
  "ex:C a rdfs:Class, sh:NodeShape ; sh:nodeKind sh:BlankNode . ex:i a ex:C ."

#guard components (run implicitDoc) == [shNodeKindCC]

/-! ### §4.4.3 sh:pattern with sh:flags -/

def patternDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"John\", \"Mark\" ; sh:pattern \"^joh\" ; sh:flags \"i\" ."

#guard (run patternDoc).results.map (·.value) == [some (.literal (Literal.string "Mark"))]

/-! ### §2.3.1 paths: sequence, inverse, zero-or-more, alternative -/

def seqDoc : String :=
  "ex:a ex:p ex:b . ex:b ex:q ex:c . ex:c a ex:C . ex:a2 ex:p ex:b2 . ex:b2 ex:q ex:c2 . " ++
  "ex:S a sh:PropertyShape ; sh:targetNode ex:a, ex:a2 ; sh:path ( ex:p ex:q ) ; sh:class ex:C ."

#guard (run seqDoc).results.map (·.value) == [some (.iri (exIri "c2"))]

def invDoc : String :=
  "ex:child ex:parent ex:dad . ex:S a sh:PropertyShape ; sh:targetNode ex:dad ; " ++
  "sh:path [ sh:inversePath ex:parent ] ; sh:minCount 2 ."

#guard components (run invDoc) == [shMinCountCC]
#guard evalPath (ttl invDoc) (.iri (exIri "dad")) (.inverse (.pred (exIri "parent"))) == [.iri (exIri "child")]

def starDoc : String :=
  "ex:a ex:next ex:b . ex:b ex:next ex:c . ex:c ex:next ex:a ."

#guard (evalPath (ttl starDoc) (.iri (exIri "a")) (.zeroOrMore (.pred (exIri "next")))).length == 3
#guard (evalPath (ttl starDoc) (.iri (exIri "a")) (.oneOrMore (.pred (exIri "next")))).length == 3
#guard (evalPath (ttl starDoc) (.iri (exIri "a")) (.zeroOrOne (.pred (exIri "next")))).length == 2
#guard (evalPath (ttl starDoc) (.iri (exIri "a"))
  (.alt [.pred (exIri "next"), .inverse (.pred (exIri "next"))])).length == 2

/-- Path → RDF → Path round trip (`Report.pathToRdf` is the inverse of `decodePath`). -/
def roundTrip (p : Path) : Bool :=
  let (t, ts, _) := pathToRdf p 0
  decodePath ts t (ts.length + 1) == p

#guard roundTrip (.seq [.pred (exIri "p"), .inverse (.pred (exIri "q"))])
#guard roundTrip (.alt [.pred (exIri "p"), .zeroOrMore (.pred (exIri "q"))])
#guard roundTrip (.oneOrMore (.seq [.pred (exIri "p"), .pred (exIri "q")]))
#guard roundTrip (.zeroOrOne (.pred (exIri "p")))

/-! ### §4.8.1 sh:closed — one result per offending triple -/

def closedDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:closed true ; sh:ignoredProperties ( rdf:type ) ; " ++
  "sh:property [ sh:path ex:ok ] . ex:n a ex:C ; ex:ok 1 ; ex:bad 2 ; ex:bad 3 ."

#guard (run closedDoc).results.length == 2
#guard (run closedDoc).results.all fun v => v.path == some (.pred (exIri "bad"))

/-- §4.8.1: the triples checked are those "that [have] a value node as
[their] subject" — for a property shape, the path's values, not the
focus node. -/
def closedPropertyDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:p ; sh:closed true ; " ++
  "sh:ignoredProperties ( ex:ok ) ] . ex:n ex:p ex:v . ex:v ex:ok 1 ; ex:bad 2 ."

#guard (run closedPropertyDoc).results.map (·.path) == [some (.pred (exIri "bad"))]
#guard (run closedPropertyDoc).results.map (·.focus) == [.iri (exIri "n")]

/-! ### SHACL 1.2 sh:closed sh:ByTypes — collectProperties over the shapes graph -/

def closedByTypesDoc : String :=
  "ex:Root a rdfs:Class, sh:NodeShape ; sh:property [ sh:path ex:rootP ] ; sh:closed sh:ByTypes . " ++
  "ex:Sub a rdfs:Class, sh:NodeShape ; rdfs:subClassOf ex:Root ; sh:property [ sh:path ex:subP ] . " ++
  "ex:SubShape a sh:NodeShape ; sh:targetClass ex:Sub ; sh:node ex:Extra . " ++
  "ex:Extra a sh:NodeShape ; sh:property [ sh:path ex:extraP ] . " ++
  "ex:bad a ex:Root ; ex:subP 1 . ex:ok1 a ex:Root ; ex:rootP 1 . " ++
  "ex:ok2 a ex:Sub ; ex:rootP 1 ; ex:subP 2 ; ex:extraP 3 ."

-- ex:Root's own instances may use ex:rootP only; an ex:Sub instance
-- also ex:subP (its own shape), ex:rootP (superclass) and ex:extraP
-- (sh:targetClass ex:Sub, then sh:node ex:Extra).
#guard (run closedByTypesDoc).results.map (·.focus) == [.iri (exIri "bad")]
#guard (run closedByTypesDoc).results.map (·.path) == [some (.pred (exIri "subP"))]
#guard components (run closedByTypesDoc) == [shClosedCC]
#guard (collectProperties (ttl closedByTypesDoc) (exIri "Sub")).contains (exIri "extraP")
#guard !(collectProperties (ttl closedByTypesDoc) (exIri "Root")).contains (exIri "subP")

/-! ### §4.4.5 sh:uniqueLang — lexical "true" only -/

def uniqueLangDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:label ; sh:uniqueLang true ] . " ++
  "ex:n ex:label \"a\"@en, \"b\"@EN, \"c\"@de ."

#guard components (run uniqueLangDoc) == [shUniqueLangCC]

def uniqueLangOneDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:label ; sh:uniqueLang \"1\"^^xsd:boolean ] . " ++
  "ex:n ex:label \"a\"@en, \"b\"@en ."

#guard (run uniqueLangOneDoc).conforms == true

/-- SHACL 1.2 §UniqueLangConstraintComponent: the base direction is part
of the key ("1"@ar--rtl and "1"@ar are different). Parsed as RDF 1.2. -/
def uniqueLangDirOkDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:label ; sh:uniqueLang true ] . " ++
  "ex:n ex:label \"A\"@ar, \"A\"@ar--ltr, \"A\"@ar--rtl ."

def uniqueLangDirBadDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:label ; sh:uniqueLang true ] . " ++
  "ex:n ex:label \"A\"@ar--ltr, \"B\"@ar--ltr, \"C\"@ar ."

#guard (run12 uniqueLangDirOkDoc).conforms == true
#guard (run12 uniqueLangDirBadDoc).results.length == 1

/-! ### §4.5.3 sh:lessThan — one result per incomparable pair -/

def lessThanDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:first ; sh:lessThan ex:second ] . " ++
  "ex:n ex:first 1, 2 ; ex:second \"a\", \"b\" ."

#guard (run lessThanDoc).results.length == 4

def lessThanOkDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:first ; sh:lessThan ex:second ] . " ++
  "ex:n ex:first 1, 2 ; ex:second 3, 4.5 ."

#guard (run lessThanOkDoc).conforms == true

/-! ### §4.3 value range on xsd:dateTime (timezone comparability) -/

#guard numericCmpLe (Literal.string "2002-10-10T12:00:00") (Literal.string "x") == none
#guard dtCmp "2002-10-10T12:00:00-05:00" "2002-10-10T12:00:01-05:00" == some (-1)
#guard dtCmp "2002-10-10T12:00:00-05:00" "2002-10-10T17:00:00Z" == some 0
#guard dtCmp "2002-10-10T12:00:00-05:00" "2002-10-10T12:00:00" == none

def dateTimeDoc : String :=
  "ex:S a sh:NodeShape ; sh:minInclusive \"2002-10-10T12:00:00-05:00\"^^xsd:dateTime ; " ++
  "sh:targetNode \"2002-10-10T12:00:00-05:00\"^^xsd:dateTime, \"2002-10-09T12:00:00-05:00\"^^xsd:dateTime, " ++
  "\"2002-10-10T12:00:00\"^^xsd:dateTime ."

#guard (run dateTimeDoc).results.length == 2   -- the earlier value and the naive one

/-! ### §4.7.2 sh:qualifiedValueShape with sh:qualifiedValueShapesDisjoint -/

def qualifiedDoc : String :=
  "ex:Hand a sh:NodeShape ; sh:targetNode ex:h ; sh:property ex:d1, ex:d4 . " ++
  "ex:d1 sh:path ex:digit ; sh:qualifiedMinCount 1 ; sh:qualifiedValueShape [ sh:class ex:Thumb ] ; sh:qualifiedValueShapesDisjoint true . " ++
  "ex:d4 sh:path ex:digit ; sh:qualifiedMinCount 4 ; sh:qualifiedValueShape [ sh:class ex:Finger ] ; sh:qualifiedValueShapesDisjoint true . " ++
  "ex:h ex:digit ex:f1, ex:f2, ex:f3, ex:ft . ex:f1 a ex:Finger . ex:f2 a ex:Finger . ex:f3 a ex:Finger . ex:ft a ex:Finger, ex:Thumb ."

#guard components (run qualifiedDoc) == [shQualifiedMinCountCC, shQualifiedMinCountCC]

/-! ### §4.6.4 sh:xone, §4.8.2 sh:hasValue, §4.8.3 sh:in, §4.4.4 sh:languageIn -/

def xoneDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b, ex:c ; sh:xone ( [ sh:class ex:C ] [ sh:class ex:D ] ) . " ++
  "ex:a a ex:C . ex:b a ex:C, ex:D . ex:c a ex:E ."

#guard (run xoneDoc).results.map (·.focus) == [.iri (exIri "b"), .iri (exIri "c")]

def hasValueInDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:property [ sh:path ex:p ; sh:hasValue ex:v ; sh:in ( ex:v ex:w ) ] . " ++
  "ex:n ex:p ex:w ."

#guard components (run hasValueInDoc) == [shHasValueCC]

def languageInDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"Hill\"@en-NZ, \"Berg\"@de, \"Hill\" ; sh:languageIn ( \"en\" \"mi\" ) ."

#guard (run languageInDoc).results.length == 2

/-! ### §2.1.2 / §2.1.4 targetSubjectsOf, targetObjectsOf; §3.6.1.3 custom severity -/

def subjObjDoc : String :=
  "ex:S1 a sh:NodeShape ; sh:targetSubjectsOf ex:p ; sh:nodeKind sh:BlankNode . " ++
  "ex:S2 a sh:NodeShape ; sh:targetObjectsOf ex:p ; sh:nodeKind sh:Literal ; sh:severity ex:Mine . " ++
  "ex:a ex:p ex:b ."

#guard (run subjObjDoc).results.length == 2
#guard (run subjObjDoc).results.map (·.severity) == [.violation, .custom (exIri "Mine")]

/-! ### SHACL 1.2 §severity / §conformance-definition: sh:Debug and sh:Trace

A result at a severity outside the conformance-disallow set (default
sh:Violation, sh:Warning, sh:Info) is reported but does not make the
report non-conforming; one inside it does. -/

def debugDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"x\" ; sh:datatype xsd:integer ; sh:severity sh:Debug ."

#guard (run debugDoc).results.length == 1
#guard (run debugDoc).conforms == true
#guard (run debugDoc).results.map (·.severity) == [.debug]

def traceDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"x\" ; sh:datatype xsd:integer ; sh:severity sh:Trace ."

#guard (run traceDoc).conforms == true
#guard (run traceDoc).results.map (·.severity) == [.trace]

def warningDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"x\" ; sh:datatype xsd:integer ; sh:severity sh:Warning ."

#guard (run warningDoc).conforms == false

/-- §conformanceDisallows: an engine-chosen set `{sh:Violation}` lets a
sh:Warning result conform, and the report states the set. -/
def runWith (body : String) (cfg : ValidationConfig) : ValidationReport :=
  let g := ttl body
  validate g (decodeShapesGraph g) cfg

#guard (runWith warningDoc { disallowed := some [.violation] }).conforms == true
#guard (runWith warningDoc { disallowed := some [.violation] }).results.length == 1
#guard (reportToGraph (runWith warningDoc { disallowed := some [.violation] })).any fun t =>
         t.p == shConformanceDisallows && t.o == .iri shViolation
#guard !((reportToGraph (run warningDoc)).any fun t => t.p == shConformanceDisallows)
#guard (runWith debugDoc { disallowed := some [.debug] }).conforms == false

/-- Conformance checking inside sh:not uses the same set: `ex:Inner`'s
only result is at sh:Debug, so `ex:n` CONFORMS to `ex:Inner` and
sh:not reports it. -/
def debugNotDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:not ex:Inner . " ++
  "ex:Inner sh:class ex:C ; sh:severity sh:Debug ."

#guard components (run debugNotDoc) == [shNotCC]
#guard (run debugNotDoc).conforms == false
#guard (runWith debugNotDoc { disallowed := some [.debug] }).conforms == true

/-! ### SHACL 1.2 list-valued sh:class / sh:datatype / sh:nodeKind (union)

§ClassConstraintComponent: "Use lists for union semantics"; the same
list form for sh:datatype and sh:nodeKind; sh:TripleTerm is the node
kind of triple terms. -/

def classListDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b, ex:c, \"lit\" ; sh:class ( ex:A ex:B ) . " ++
  "ex:a a ex:A . ex:b a ex:B . ex:c a ex:C ."

#guard (run classListDoc).results.map (·.focus) == [.iri (exIri "c"), .literal (Literal.string "lit")]
#guard components (run classListDoc) == [shClassCC, shClassCC]

def datatypeListDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"a\", \"b\"@en, 42, ex:i ; " ++
  "sh:datatype ( xsd:string rdf:langString ) ."

#guard (run datatypeListDoc).results.length == 2   -- 42 and ex:i

def nodeKindListDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, \"lit\", <<( ex:a ex:p ex:b )>> ; " ++
  "sh:nodeKind ( sh:BlankNode sh:IRI ) ."

#guard (run12 nodeKindListDoc).results.length == 2   -- the literal and the triple term

def tripleTermKindDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, <<( ex:a ex:p ex:b )>> ; sh:nodeKind sh:TripleTerm ."

#guard (run12 tripleTermKindDoc).results.map (·.focus) == [.iri (exIri "a")]

/-! ### SHACL 1.2 §SingleLineConstraintComponent -/

def singleLineDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"one\", \"two\\nlines\", \"cr\\rhere\", ex:i ; " ++
  "sh:singleLine true ."

#guard (run singleLineDoc).results.length == 2
#guard components (run singleLineDoc) == [shSingleLineCC, shSingleLineCC]

def singleLineFalseDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"two\\nlines\" ; sh:singleLine false ."

#guard (run singleLineFalseDoc).conforms == true

/-! ### SHACL 1.2 §RootClassConstraintComponent — rdfs:subClassOf*, reflexive -/

def rootClassDoc : String :=
  "ex:Dog rdfs:subClassOf ex:Mammal . ex:Mammal rdfs:subClassOf ex:Animal . " ++
  "ex:S a sh:NodeShape ; sh:targetNode ex:Dog, ex:Animal, ex:Car, \"Dog\" ; sh:rootClass ex:Animal ."

#guard (run rootClassDoc).results.map (·.focus) ==
         [.iri (exIri "Car"), .literal (Literal.string "Dog")]
#guard components (run rootClassDoc) == [shRootClassCC, shRootClassCC]

/-! ### SHACL 1.2 SHACL lists and the list constraint components

§terminology "SHACL Lists": exactly one rdf:first and one rdf:rest, no
rdf:rest+ cycle; rdf:nil is the empty list. "Each value node v must be
a SHACL list - if v is not a SHACL list there is a validation result." -/

def listsDoc : String :=
  "ex:l2 rdf:first 1 ; rdf:rest ( 2 ) . ex:l3 rdf:first 1 ; rdf:rest ( 2 1 ) . " ++
  "ex:cyc rdf:first 1 ; rdf:rest ex:cyc . ex:two rdf:first 1, 2 ; rdf:rest rdf:nil . " ++
  "ex:mixed rdf:first ex:a ; rdf:rest ( \"b\" ) ."

#guard shaclListMembers (ttl listsDoc) (.iri rdfNil) == some []
#guard (shaclListMembers (ttl listsDoc) (.iri (exIri "l3"))).map (·.length) == some 3
#guard shaclListMembers (ttl listsDoc) (.iri (exIri "cyc")) == none
#guard shaclListMembers (ttl listsDoc) (.iri (exIri "two")) == none
#guard shaclListMembers (ttl listsDoc) (.iri (exIri "notAList")) == none

def minListDoc : String :=
  listsDoc ++ " ex:S a sh:NodeShape ; sh:targetNode ex:l2, rdf:nil, ex:cyc ; sh:minListLength 1 ."

#guard (run minListDoc).results.map (·.focus) == [.iri rdfNil, .iri (exIri "cyc")]

def maxListDoc : String :=
  listsDoc ++ " ex:S a sh:NodeShape ; sh:targetNode ex:l2, ex:l3, rdf:nil ; sh:maxListLength 2 ."

#guard (run maxListDoc).results.map (·.focus) == [.iri (exIri "l3")]
#guard components (run maxListDoc) == [shMaxListLengthCC]

def uniqueMembersDoc : String :=
  listsDoc ++ " ex:S a sh:NodeShape ; sh:targetNode ex:l2, ex:l3, ex:x ; sh:uniqueMembers true ."

-- ex:l3 has the duplicate 1 (one sh:detail); ex:x is not a list (no detail).
#guard (run uniqueMembersDoc).results.map (·.focus) == [.iri (exIri "l3"), .iri (exIri "x")]
#guard (run uniqueMembersDoc).results.map (·.details.length) == [1, 0]
#guard ((run uniqueMembersDoc).results.flatMap (·.details)).map (·.value) ==
         [some (.literal (L4Factoidal.SPARQL.mkTypedLiteral "1" xsdInteger))]

def uniqueMembersFalseDoc : String :=
  listsDoc ++ " ex:S a sh:NodeShape ; sh:targetNode ex:l3 ; sh:uniqueMembers false ."

#guard (run uniqueMembersFalseDoc).conforms == true

def memberShapeDoc : String :=
  listsDoc ++ " ex:S a sh:NodeShape ; sh:targetNode ex:mixed, ex:x, rdf:nil ; sh:memberShape ex:I . " ++
  "ex:I sh:nodeKind sh:IRI ."

-- ex:mixed has the literal member "b" (its nodeKind result is the detail);
-- ex:x is not a list; rdf:nil has no members and conforms.
#guard (run memberShapeDoc).results.map (·.focus) == [.iri (exIri "mixed"), .iri (exIri "x")]
#guard components (run memberShapeDoc) == [shMemberShapeCC, shMemberShapeCC]
#guard ((run memberShapeDoc).results.flatMap (·.details)).map
         (fun d => constraintComponentIri d.constraint) == [shNodeKindCC]
#guard (reportToGraph (run memberShapeDoc)).any fun t => t.p == shDetail

/-! ### SHACL 1.2 §SubsetOfConstraintComponent and §SomeValueConstraintComponent -/

def subsetOfDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b ; " ++
  "sh:property [ sh:path ex:fav ; sh:subsetOf ex:child ] . " ++
  "ex:a ex:fav ex:x ; ex:child ex:x, ex:y . ex:b ex:fav ex:x, ex:z ; ex:child ex:x ."

#guard (run subsetOfDoc).results.map (·.value) == [some (.iri (exIri "z"))]
#guard components (run subsetOfDoc) == [shSubsetOfCC]

def someValueDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:alice, ex:bob, ex:carol ; " ++
  "sh:property [ sh:path ex:tends ; sh:someValue [ sh:class ex:Duck ] ] . " ++
  "ex:d a ex:Duck . ex:c a ex:Cow . ex:alice ex:tends ex:c . ex:bob ex:tends ex:c, ex:d ."

-- ex:alice tends no duck; ex:carol tends nothing; ex:bob conforms.
#guard (run someValueDoc).results.map (·.focus) == [.iri (exIri "alice"), .iri (exIri "carol")]
#guard (run someValueDoc).results.map (·.value) == [none, none]
#guard components (run someValueDoc) == [shSomeValueCC, shSomeValueCC]

/-! ### SHACL 1.2 targets: sh:targetWhere, sh:shape, sh:ShapeClass -/

def targetWhereDoc : String :=
  "ex:Adult a sh:NodeShape ; sh:targetWhere [ sh:class ex:Person ; " ++
  "sh:property [ sh:path ex:age ; sh:minInclusive 18 ; sh:minCount 1 ] ] ; " ++
  "sh:property [ sh:path ex:voted ; sh:minCount 1 ] . " ++
  "ex:a a ex:Person ; ex:age 20 . ex:b a ex:Person ; ex:age 10 . ex:c a ex:Person ; ex:age 30 ; ex:voted 1 ."

-- ex:a and ex:c are targets (adults); only ex:a lacks ex:voted; ex:b is no target.
#guard (run targetWhereDoc).results.map (·.focus) == [.iri (exIri "a")]
#guard components (run targetWhereDoc) == [shMinCountCC]

def shapeLinkDoc : String :=
  "ex:S a sh:NodeShape ; sh:property [ sh:path ex:p ; sh:maxCount 0 ] . " ++
  "ex:n sh:shape ex:S ; ex:p 1 . ex:m ex:p 2 ."

-- ex:n is linked to ex:S in the data graph; ex:m is not.
#guard (run shapeLinkDoc).results.map (·.focus) == [.iri (exIri "n")]

def shapeClassDoc : String :=
  "ex:Super a sh:ShapeClass ; sh:in ( ex:ok ) . ex:Sub rdfs:subClassOf ex:Super . " ++
  "ex:ok a ex:Sub . ex:bad a ex:Sub ."

#guard (run shapeClassDoc).results.map (·.focus) == [.iri (exIri "bad")]
#guard components (run shapeClassDoc) == [shInCC]

/-! ### SHACL 1.2 §UniqueValuesForConstraintComponent -/

def uniqueValuesForDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetClass ex:R ; sh:uniqueValuesFor ( ex:id ex:scheme ) . " ++
  "ex:r1 a ex:R ; ex:id 1 ; ex:scheme ex:A . ex:r2 a ex:R ; ex:id 1 ; ex:scheme ex:A . " ++
  "ex:r3 a ex:R ; ex:id 1 ; ex:scheme ex:B . ex:r4 a ex:R ; ex:id 2 . ex:r5 a ex:R ; ex:id 2 . " ++
  "ex:other ex:id 1 ; ex:scheme ex:B ."

-- ex:r1 and ex:r2 share the full key; ex:r3 shares it only with ex:other,
-- which is no target; ex:r4 and ex:r5 have no ex:scheme, so no key.
#guard (run uniqueValuesForDoc).results.map (·.focus) == [.iri (exIri "r1"), .iri (exIri "r2")]
#guard (run uniqueValuesForDoc).results.map (·.value) == [none, none]
#guard components (run uniqueValuesForDoc) == [shUniqueValuesForCC, shUniqueValuesForCC]

/-! ### SHACL 1.2 Node Expressions §NodeByExpressionConstraintComponent -/

def nodeByExpressionDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b ; sh:nodeByExpression ex:T . " ++
  "ex:T a sh:NodeShape ; sh:class ex:C . ex:a a ex:C ."

#guard (run nodeByExpressionDoc).results.map (·.focus) == [.iri (exIri "b")]
#guard components (run nodeByExpressionDoc) == [shNodeByExpressionCC]
#guard (run nodeByExpressionDoc).results.map (·.sourceConstraint) == [some (.iri (exIri "T"))]
#guard (reportToGraph (run nodeByExpressionDoc)).any fun t =>
         t.p == shSourceConstraint && t.o == .iri (exIri "T")

/-! ### SHACL 1.2 sh:values and the node-expression evaluator

With the Core evaluator an IRI node expression is its own output
(§IRIExpression). A caller-supplied evaluator decides blank-node
expressions — here one that maps every blank node to `ex:a`, standing
in for a SHACL-SPARQL select expression. -/

def valuesDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; " ++
  "sh:property [ sh:path ex:p ; sh:values ex:v ; sh:minCount 2 ] . ex:n ex:p ex:w ."

#guard (run valuesDoc).conforms == true   -- ex:w (path) and ex:v (sh:values)

def bnodeTargetDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode [ ex:anything 1 ] ; sh:class ex:C ."

def toA (e : Term) (_ : Option Term) : List Term :=
  match e with | .bnode _ => [.iri (exIri "a")] | _ => [e]

#guard (runWith bnodeTargetDoc { evalExpr := toA }).results.map (·.focus) == [.iri (exIri "a")]

/-! ### SHACL 1.2 constraint reifiers: sh:severity, sh:message, sh:deactivated

§severity / §message / §deactivated: a reifier of a triple whose subject
is the shape and whose predicate is a parameter sets that constraint's
severity or message, or deactivates it. RDF 1.2 annotation syntax. -/

def reifiedSeverityDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode \"x\" ; " ++
  "sh:datatype xsd:integer {| sh:severity sh:Warning ; sh:message \"not an integer\" |} ; " ++
  "sh:nodeKind sh:IRI ."

-- sh:datatype at sh:Warning with its message; sh:nodeKind keeps sh:Violation.
#guard (run12 reifiedSeverityDoc).results.map (fun v => (constraintComponentIri v.constraint, v.severity)) ==
         [(shDatatypeCC, .warning), (shNodeKindCC, .violation)]
#guard (run12 reifiedSeverityDoc).results.map (·.message.map (·.val.lexicalForm)) ==
         [some "not an integer", none]

def reifiedDeactivatedDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:datatype xsd:boolean {| sh:deactivated true |} ; " ++
  "sh:property ex:P {| sh:deactivated true |} ; sh:nodeKind sh:Literal . " ++
  "ex:P sh:path ex:p ; sh:minCount 1 ."

-- Only sh:nodeKind remains active.
#guard components (run12 reifiedDeactivatedDoc) == [shNodeKindCC]

/-! ### SHACL 1.2 §ReifierShapeConstraintComponent -/

def reifierShapeDoc (required : String) : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:a, ex:b, ex:c ; sh:property ex:SP . " ++
  "ex:SP sh:path ex:p ; sh:reifierShape ex:R ; sh:reificationRequired " ++ required ++ " . " ++
  "ex:R a sh:NodeShape ; sh:property [ sh:path ex:src ; sh:minCount 1 ] . " ++
  "ex:a ex:p 1 {| ex:src ex:x |} . ex:b ex:p 2 {| ex:other 3 |} . ex:c ex:p 3 ."

-- ex:b's reifier lacks ex:src; with sh:reificationRequired, ex:c has no reifier.
#guard (run12 (reifierShapeDoc "false")).results.map (·.focus) == [.iri (exIri "b")]
#guard (run12 (reifierShapeDoc "true")).results.map (·.focus) ==
         [.iri (exIri "b"), .iri (exIri "c")]
#guard components (run12 (reifierShapeDoc "true")) == [shReifierShapeCC, shReifierShapeCC]

/-! ### §3.6.1 sh:deactivated -/

def deactivatedDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:deactivated true ; sh:nodeKind sh:Literal ."

#guard (run deactivatedDoc).conforms == true

/-! ### §3.6 the report graph -/

def reportG : Graph := reportToGraph (run maxCountDoc)

#guard reportG.any fun t => t.p == shConforms && t.o == .literal (boolLiteral false)
#guard (reportG.filter fun t => t.p == shResult).length == 1
#guard (reportG.filter fun t => t.p == shSourceConstraintComponent && t.o == .iri shMaxCountCC).length == 1
#guard (reportG.filter fun t => t.p == shResultPath && t.o == .iri (exIri "name")).length == 1
-- Every minted blank node is distinct (the suite's "not shared" precondition).
#guard (dedupLabels (reportG.bnodes)).length == reportG.bnodes.length
-- A conforming report is two triples.
#guard (reportToGraph (run minCountZeroDoc)).length == 2

/-! ### SHACL-SPARQL (Part 2) is decoded, not named as unsupported

Since the SHACL-SPARQL stage, `sh:sparql` and the §6 constraint
components are evaluated (`SHACL/Sparql.lean`); the one remaining
entry of `sparqlFeaturePredicates` is the SPARQL-based TARGET
(`sh:target`, SHACL-AF). -/

def sparqlDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:n ; sh:sparql [ sh:select \"SELECT $this WHERE { }\" ] ."

#guard (decodeShapesGraph (ttl sparqlDoc)).unsupported == ([] : List String)
#guard (decodeShapesGraph (ttl sparqlDoc)).shapes.any (fun s =>
         s.constraints.any fun c => match c with | .sparql _ _ _ _ => true | _ => false)

def sparqlTargetDoc : String :=
  "ex:S a sh:NodeShape ; sh:target [ sh:select \"SELECT $this WHERE { }\" ] ."

#guard (decodeShapesGraph (ttl sparqlTargetDoc)).unsupported
         == ["sh:target (SPARQL-based targets)"]

/-! ### SHACL-SPARQL Part 2 — the evaluator

`Sparql.lean`. These pin the clauses the W3C `sparql/*` manifests
exercise; the suite itself is run by `lake exe l4shacl`. Every query
below uses full IRIs — a `sh:sparql` query text carries no ambient
prefix map unless the shape declares `sh:prefixes` (§5.2). -/

/-- Validate a document against itself with SHACL-SPARQL enabled; the
raw graph is passed twice because §5.3.1's `$shapesGraph` needs the
shapes graph's own triples. -/
def runSparql (body : String) : ValidationReport :=
  let g := ttl body
  validateWithSparql g g (decodeShapesGraph g)

/-! #### §5.1 every SELECT solution is a validation result -/

def sparqlSelectDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:bob ; sh:sparql [ " ++
  "sh:select \"SELECT $this ?value WHERE { $this <http://example.org/name> ?value }\" ] . " ++
  "ex:bob ex:name \"A\", \"B\" ."

#guard (runSparql sparqlSelectDoc).conforms == false
#guard (runSparql sparqlSelectDoc).results.length == 2
#guard components (runSparql sparqlSelectDoc) == [shSPARQLConstraintComponent,
                                                  shSPARQLConstraintComponent]
#guard (runSparql sparqlSelectDoc).failure == none

/-! #### §5.3 `$this` is pre-bound INSIDE the pattern

The whole WHERE clause is one FILTER, so a post-hoc join of a
`{this ↦ focus}` row would leave `$this` unbound while the FILTER runs
and would find nothing. One result means the substitution reached the
FILTER expression (the `sparql/pre-binding/pre-binding-001` shape). -/

def prebindFilterDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:bob ; sh:sparql [ " ++
  "sh:select \"SELECT $this WHERE { FILTER ($this = <http://example.org/bob>) }\" ] ."

#guard (runSparql prebindFilterDoc).conforms == false
#guard (runSparql prebindFilterDoc).results.length == 1
#guard (runSparql prebindFilterDoc).results.map (·.focus) == [.iri (exIri "bob")]

-- The focus node is still in the result rows after substitution:
-- `SELECT $this` projects it through the pre-binding row.
#guard (runSparql prebindFilterDoc).results.map (·.value) == [some (.iri (exIri "bob"))]

/-! #### §5.3.2 the pre-binding restrictions are failures, not results -/

def minusDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:bob ; sh:sparql [ " ++
  "sh:select \"SELECT $this WHERE { $this ?p ?o MINUS { ?x ?y ?z } }\" ] . " ++
  "ex:bob ex:name \"A\" ."

#guard (runSparql minusDoc).failure.isSome
#guard (runSparql minusDoc).results.isEmpty

def serviceDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:bob ; sh:sparql [ " ++
  "sh:select \"SELECT $this WHERE { SERVICE <http://example.org/sparql> { $this ?p ?o } }\" ] ."

#guard (runSparql serviceDoc).failure.isSome

def bindPreboundDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode ex:bob ; sh:sparql [ " ++
  "sh:select \"SELECT $this WHERE { BIND (<http://example.org/x> AS $this) }\" ] ."

#guard (runSparql bindPreboundDoc).failure.isSome

-- A sub-SELECT that DOES project `$this` is accepted; `SELECT *`
-- counts as not projecting (`pre-binding-006` versus `-007`).
#guard (prebindingUnsupported (.subSelect
          (.mk (.select (.vars [.var "this"])) [] .empty none [] {} none none))).isNone
#guard (prebindingUnsupported (.subSelect
          (.mk (.select .all) [] .empty none [] {} none none))).isSome

/-! #### §5.3.1 `$PATH` renders as SPARQL 1.1 property-path syntax -/

#guard pathToSparql (.pred (exIri "name")) == "<http://example.org/name>"
#guard pathToSparql (.inverse (.pred (exIri "name"))) == "^<http://example.org/name>"
#guard pathToSparql (.seq [.pred (exIri "a"), .inverse (.pred (exIri "b"))])
         == "<http://example.org/a>/(^<http://example.org/b>)"
#guard pathToSparql (.zeroOrMore (.alt [.pred (exIri "a"), .pred (exIri "b")]))
         == "(<http://example.org/a>|<http://example.org/b>)*"
#guard substitutePath "SELECT $this WHERE { $this $PATH ?value }" (some (.pred (exIri "age")))
         == "SELECT $this WHERE { $this <http://example.org/age> ?value }"

/-! #### §6 a SPARQL-based constraint component

`ex:C` is recognised structurally (a `sh:parameter` plus a validator),
its `sh:maxVal` parameter is bound on the PROPERTY shape `ex:P`, and
the ASK validator runs once per value node (§6.2.1). -/

def askComponentDoc : String :=
  "ex:C sh:parameter [ sh:path ex:maxVal ] ; " ++
  "sh:validator [ sh:ask \"ASK { FILTER ($value <= $maxVal) }\" ] . " ++
  "ex:S a sh:NodeShape ; sh:targetNode ex:bob ; sh:property ex:P . " ++
  "ex:P sh:path ex:age ; ex:maxVal 10 . " ++
  "ex:bob ex:age 5, 20 ."

#guard (runSparql askComponentDoc).conforms == false
#guard (runSparql askComponentDoc).results.length == 1
#guard components (runSparql askComponentDoc) == [exIri "C"]
#guard (runSparql askComponentDoc).results.map (fun v =>
          match v.value with
          | some (.literal l) => l.val.lexicalForm
          | _ => "") == ["20"]

/-! ### SHACL-SPARQL 1.2 node expressions in validation

§SelectExpression and §SPARQLExprExpression, reached through sh:values
and sh:targetNode by `validateFull` (`NodeExpr.lean`). -/

def runFull (body : String) : ValidationReport :=
  let g := ttl body
  validateFull g g (decodeShapesGraph g)

-- "http://example.org/abc" has 22 characters.
def sparqlExprDoc (n : Nat) : String :=
  "ex:S a sh:PropertyShape ; sh:targetNode ex:abc ; sh:path ex:len ; " ++
  "sh:values [ sh:sparqlExpr \"STRLEN(STR($this))\" ] ; sh:datatype xsd:integer ; " ++
  s!"sh:hasValue {n} ."

#guard (runFull (sparqlExprDoc 22)).conforms == true
#guard (runFull (sparqlExprDoc 23)).conforms == false
#guard components (runFull (sparqlExprDoc 23)) == [shHasValueCC]
-- With the Core evaluator the blank node is a constant value, not 22.
#guard (run (sparqlExprDoc 22)).conforms == false

def selectTargetDoc : String :=
  "ex:S a sh:NodeShape ; sh:targetNode [ sh:select " ++
  "\"SELECT ?x WHERE { ?x <http://example.org/age> ?a FILTER (?a < 18) }\" ] ; " ++
  "sh:class ex:Adult . ex:kid ex:age 10 . ex:old ex:age 40 ."

#guard (runFull selectTargetDoc).results.map (·.focus) == [.iri (exIri "kid")]

/-- `$this` is pre-bound to the focus node in a select expression. -/
def selectThisDoc : String :=
  "ex:e ex:expr [ sh:select \"SELECT ?o WHERE { $this <http://example.org/p> ?o }\" ] . " ++
  "ex:f ex:p 7 . ex:g ex:p 8 ."

def selectThisExpr : Term :=
  (((ttl selectThisDoc).find? fun t => t.p == exIri "expr").map (·.o)).getD (.bnode "none")

#guard evalSparqlNodeExpr (ttl selectThisDoc) (ttl selectThisDoc) selectThisExpr
         (some (.iri (exIri "f"))) [] ==
       some [.literal (L4Factoidal.SPARQL.mkTypedLiteral "7" xsdInteger)]
-- "A failure is produced when one of the scope variables is called this."
#guard evalSparqlNodeExpr (ttl selectThisDoc) (ttl selectThisDoc) selectThisExpr
         (some (.iri (exIri "f"))) [("this", .iri (exIri "g"))] == some []
-- An IRI is no SPARQL node expression.
#guard (evalSparqlNodeExpr (ttl selectThisDoc) [] (.iri (exIri "e")) none []).isNone

-- An ill-formed SPARQL node expression is a validation failure.
def badSelectDoc : String :=
  "ex:S a sh:PropertyShape ; sh:targetNode ex:n ; sh:path ex:p ; " ++
  "sh:values [ sh:select \"SELECT ?x ?y WHERE { }\" ] ."

#guard (runFull badSelectDoc).failure.isSome
#guard (runFull selectTargetDoc).failure.isNone

end L4Factoidal.SHACL.Tests
