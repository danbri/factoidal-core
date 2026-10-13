/-
L4Factoidal.TailRecursionTwins — the axiom report and run-time checks for
the loop twins of https://github.com/danbri/factoidal/issues/752 (OKR batch 1
KR 2.6, https://github.com/danbri/factoidal/issues/768).

Each twin is a tail-recursive (or core-library) form of a readable
definition whose recursion depth grew with the length or the value of data.
The equality theorem is in the module of the definition, next to the
`@[csimp]` theorem that makes the compiler run the twin. This module only
reports what those proofs depend on (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound` only) and evaluates small cases against
constants, positive and negative. A `#guard` that compares the readable form
with its twin would run the twin on both sides, because `csimp` applies to
the evaluated code too. No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.Geo.Types
import L4Factoidal.Geo.Wkt
import L4Factoidal.Math.Sigmoid
import L4Factoidal.MathML.Core
import L4Factoidal.SPARQL.Expr
import L4Factoidal.SPARQL.PropertyPath
import L4Factoidal.SPARQL.Parser
import L4Factoidal.XPath.Number
import L4Factoidal.XSD.Facets
import L4Factoidal.XSD.Datatypes
import L4Factoidal.VC.Multibase
import L4Factoidal.Cottas.OnDiskStore
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.XmlCanon
import L4Factoidal.Regex.XPath
import L4Factoidal.JSONLD.Frame
import L4Factoidal.SHACL.Validation
import L4Factoidal.XML.Validity
import L4Factoidal.Syntax.RdfXml

namespace L4Factoidal.TailRecursionTwins

/-! ## Values: the twin against the readable form, and against a constant -/

#guard Geo.Scaled.pow10Fast 3 = 1000
#guard Geo.Scaled.pow10Fast 0 = 1
#guard SPARQL.pow10Fast 5 = 100000
#guard XPath.Num.pow10Fast 2 = 100
#guard XSD.pow10Fast 4 = 10000
#guard Math.Sigmoid.pow10Fast 1 = 10
#guard MathML.powNatFast (2, 3) 3 = (8, 27)
#guard MathML.powNatFast (2, 3) 0 = (1, 1)

#guard SPARQL.countDigitsFuelFast 12345 12345 = 5
#guard SPARQL.countDigitsFuelFast 9 9 = 1
#guard SPARQL.countDigitsFuelFast 100 100 != 2
#guard XSD.natDigitsFast 0 = 1
#guard XSD.natDigitsFast 1000000 = 7
#guard XSD.natDigitsFast 99 != 3
#guard (Geo.Wkt.takeDigitsFast "0123x".toList) = (123, 4, ['x'])
#guard (Geo.Wkt.takeDigitsFast "x1".toList) = (0, 0, ['x', '1'])
#guard VC.Multibase.natToBytesBEFast 0 = []
#guard VC.Multibase.natToBytesBEFast 258 = [1, 2]
#guard VC.Multibase.natToBytesBEFast 256 != [1]

#guard Regex.regexReplace "a.b.c" "\\." "-" "" = "a-b-c"
#guard Regex.regexReplace "abc" "x" "-" "" = "abc"
#guard Regex.regexReplace "aXbX" "X" "-" "" != "a-bX"
#guard SHACL.distinctDupsFast (fun a b => a == b)
    (fun x => ([1, 2, 1, 3, 3, 3].filter (· == x)).length) [] [1, 2, 1, 3, 3, 3] = [1, 3]
#guard SHACL.distinctDupsFast (fun a b => a == b)
    (fun x => ([1, 2].filter (· == x)).length) [] [1, 2] = []

/-! ## Axioms -/

#print axioms Geo.Scaled.pow10_eq_fast
#print axioms Math.Sigmoid.pow10_eq_fast
#print axioms SPARQL.pow10_eq_fast
#print axioms XPath.Num.pow10_eq_fast
#print axioms XSD.pow10_eq_fast
#print axioms MathML.powNat_eq_fast
#print axioms SPARQL.countDigitsFuel_eq_fast
#print axioms XSD.natDigits_eq_fast
#print axioms Geo.Wkt.takeDigits_eq_fast
#print axioms VC.Multibase.natToBytesBE_eq_fast
#print axioms Cottas.OnDiskStore.namedGraphsAux_eq_fast
#print axioms RDF.Graph.dedup_eq_fast
#print axioms SPARQL.dedupPath_eq_fast
#print axioms Regex.replaceLoop_eq_fast
#print axioms RDF.XmlCanon.walk_eq_fast
#print axioms JSONLD.FState.replaceFirstMatch_eq_fast
#print axioms SHACL.distinctDupsBy_eq_fast
#print axioms XML.validate_eq_fast
#print axioms SPARQL.pCollectionCells_eq
#print axioms SPARQL.pCollection_eq_fast
#print axioms Syntax.RdfXml.collectionCells_eq
#print axioms Syntax.RdfXml.collectionList_eq_fast
#print axioms Syntax.RdfXml.serializeNode_eq_fast
#print axioms Syntax.RdfXml.serializeNodes_eq_fast

end L4Factoidal.TailRecursionTwins
