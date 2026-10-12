/-
L4Factoidal.OWL.RdfBased.BalancedTests — `#guard` cases for the
balanced condition of OWL 2 RDF-Based Semantics § 7.3
(`RdfBased/Balanced.lean`), built from REAL documents of the W3C OWL 2
test catalog (`third_party/testing/owl/all.rdf`), copied verbatim and
parsed by the RDF/XML parser of this tree (`Syntax.RdfXml`). The case id
is on each document.

Positive cases (the pair is balanced): `WebOnt-equivalentClass-004`
(PositiveEntailmentTest) and `WebOnt-description-logic-101`
(InconsistencyTest, checked against `inconsistencyGoal`). A check that
answered "not balanced" for every pair fails them.

Negative cases, one condition each, so a check that answered
"balanced" for every pair fails them:

* 2.1 in G1: `WebOnt-unionOf-003` (the individuals `#a` and `#b` have
  no `rdf:type owl:NamedIndividual`);
* 2.1 in G2: `New-Feature-ReflexiveProperty-001` (the conclusion uses
  `Peter` as an individual and does not declare it) and `chain2trans1`
  (the conclusion types `#p` `owl:TransitiveProperty` and does not
  declare it an object property);
* 2.2 and 5.2-5.5: `New-Feature-ObjectQCR-001` (the conclusion's
  restriction and its literal `2` are not in the premise; the renaming of
  blank nodes is one-to-one: two copies of the restriction do not map to
  one);
* 3, the IRI branch, as a POSITIVE for that condition: `chain2trans1`
  (both documents name the ontology `http://example.org/ontology`);
* 1 and 3: `WebOnt-I5.5-005` (the conclusion has no ontology header);
* 4.1: `WebOnt-AnnotationProperty-002` (an annotation assertion with
  `first:ap` in the conclusion);
* 4.2: the premise of `WebOnt-imports-011` in the place of G2 (no
  conclusion of the catalog states an ontology property; no document of
  the catalog has a deprecation statement (4.3) or an annotation property
  axiom (4.4), so those two conditions have no case here);
* 5.1: `WebOnt-I5.8-011` (the conclusion declares `xsd:integer` and
  `xsd:string` as datatypes; the premise is an empty ontology).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.RdfBased.Balanced
import L4Factoidal.Syntax.RdfXml

namespace L4Factoidal.OWL.RdfBased.BalancedTests

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.OWL.RdfBased.Balanced

/-! ## The documents -/

/-- `WebOnt-equivalentClass-004`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def eqc004P : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/equivalentClass/premises004\" >\n" ++
  "    <owl:Ontology/>\n" ++
  "    <owl:Class rdf:ID=\"c1\">\n" ++
  "             <owl:intersectionOf rdf:parseType=\"Collection\">\n" ++
  "                <owl:Restriction>\n" ++
  "                   <owl:onProperty rdf:resource=\"#p\"/>\n" ++
  "                   <owl:cardinality\n" ++
  " rdf:datatype=\"http://www.w3.org/2001/XMLSchema#nonNegativeInteger\"\n" ++
  "                   >1</owl:cardinality>\n" ++
  "                </owl:Restriction>\n" ++
  "              </owl:intersectionOf>\n" ++
  "           </owl:Class>\n" ++
  "    <owl:Class rdf:ID=\"c2\">\n" ++
  "             <owl:intersectionOf rdf:parseType=\"Collection\">\n" ++
  "                <owl:Restriction>\n" ++
  "                   <owl:onProperty rdf:resource=\"#p\"/>\n" ++
  "                   <owl:cardinality\n" ++
  " rdf:datatype=\"http://www.w3.org/2001/XMLSchema#nonNegativeInteger\"\n" ++
  "                   >1</owl:cardinality>\n" ++
  "                </owl:Restriction>\n" ++
  "              </owl:intersectionOf>\n" ++
  "     </owl:Class>\n" ++
  "     <owl:ObjectProperty rdf:ID=\"p\"/>\n" ++
  "</rdf:RDF>"

/-- `WebOnt-equivalentClass-004`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def eqc004C : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/equivalentClass/conclusions004\" >\n" ++
  "  <owl:Ontology/>\n" ++
  "  <owl:Class rdf:about=\"premises004#c1\">\n" ++
  "     <owl:equivalentClass>\n" ++
  "       <owl:Class rdf:about=\"premises004#c2\"/>\n" ++
  "     </owl:equivalentClass>\n" ++
  "  </owl:Class>\n" ++
  "</rdf:RDF>"

/-- `WebOnt-description-logic-101`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def dl101P : String :=
  "<rdf:RDF\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/description-logic/inconsistent101\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\" xmlns:xsd=\"http://www.w3.org/2001/XMLSchema#\">\n" ++
  "    <owl:Ontology rdf:about=\"\"/>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#Unsatisfiable\">\n" ++
  "        <owl:equivalentClass>\n" ++
  "            <owl:Class>\n" ++
  "                <owl:intersectionOf rdf:parseType=\"Collection\">\n" ++
  "                    <owl:Class rdf:about=\"http://oiled.man.example.net/test#c\"/>\n" ++
  "                    <owl:Class rdf:about=\"http://oiled.man.example.net/test#d\"/>\n" ++
  "                </owl:intersectionOf>\n" ++
  "            </owl:Class>\n" ++
  "        </owl:equivalentClass>\n" ++
  "    </owl:Class>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#c\">\n" ++
  "        <rdfs:subClassOf>\n" ++
  "            <owl:Class>\n" ++
  "                <owl:complementOf>\n" ++
  "                    <owl:Class rdf:about=\"http://oiled.man.example.net/test#d\"/>\n" ++
  "                </owl:complementOf>\n" ++
  "            </owl:Class>\n" ++
  "        </rdfs:subClassOf>\n" ++
  "    </owl:Class>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#d\"/>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#f\">\n" ++
  "        <rdfs:subClassOf>\n" ++
  "            <owl:Class rdf:about=\"http://oiled.man.example.net/test#d\"/>\n" ++
  "        </rdfs:subClassOf>\n" ++
  "    </owl:Class>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#c1\">\n" ++
  "        <rdfs:subClassOf>\n" ++
  "            <owl:Class rdf:about=\"http://oiled.man.example.net/test#d1\"/>\n" ++
  "        </rdfs:subClassOf>\n" ++
  "        <rdfs:subClassOf>\n" ++
  "            <owl:Class>\n" ++
  "                <owl:complementOf>\n" ++
  "                    <owl:Class rdf:about=\"http://oiled.man.example.net/test#d1\"/>\n" ++
  "                </owl:complementOf>\n" ++
  "            </owl:Class>\n" ++
  "        </rdfs:subClassOf>\n" ++
  "    </owl:Class>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#d1\"/>\n" ++
  "    <owl:Class rdf:about=\"http://oiled.man.example.net/test#e3\">\n" ++
  "        <rdfs:subClassOf>\n" ++
  "            <owl:Class rdf:about=\"http://oiled.man.example.net/test#c\"/>\n" ++
  "        </rdfs:subClassOf>\n" ++
  "    </owl:Class>\n" ++
  "    <owl:ObjectProperty rdf:about=\"http://oiled.man.example.net/test#r\"/>\n" ++
  "    <rdf:Description>\n" ++
  "        <rdf:type rdf:resource=\"http://oiled.man.example.net/test#Unsatisfiable\"/>\n" ++
  "    </rdf:Description>\n" ++
  "</rdf:RDF>"

/-- `WebOnt-unionOf-003`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def union003P : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/unionOf/premises003\" >\n" ++
  "   <owl:Ontology/>\n" ++
  "   <owl:Class rdf:ID=\"A\">\n" ++
  "     <owl:oneOf rdf:parseType=\"Collection\">\n" ++
  "       <owl:Thing rdf:ID=\"a\"/>\n" ++
  "     </owl:oneOf>\n" ++
  "   </owl:Class>\n" ++
  "   <owl:Class rdf:ID=\"B\">\n" ++
  "     <owl:oneOf rdf:parseType=\"Collection\">\n" ++
  "       <owl:Thing rdf:ID=\"b\"/>\n" ++
  "     </owl:oneOf>\n" ++
  "   </owl:Class>\n" ++
  "   <owl:Class rdf:ID=\"A-and-B\">\n" ++
  "     <owl:oneOf rdf:parseType=\"Collection\">\n" ++
  "       <owl:Thing rdf:about=\"#a\"/>\n" ++
  "       <owl:Thing rdf:about=\"#b\"/>\n" ++
  "     </owl:oneOf>\n" ++
  "   </owl:Class>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `WebOnt-unionOf-003`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def union003C : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/unionOf/conclusions003\" >\n" ++
  "   \n" ++
  "\n" ++
  "   <owl:Ontology/>\n" ++
  "   <owl:Class rdf:about=\"premises003#A-and-B\">\n" ++
  "     <owl:unionOf rdf:parseType=\"Collection\">\n" ++
  "       <owl:Class rdf:about=\"premises003#A\"/>\n" ++
  "       <owl:Class rdf:about=\"premises003#B\"/>\n" ++
  "     </owl:unionOf>\n" ++
  "   </owl:Class>\n" ++
  "\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `New-Feature-ReflexiveProperty-001`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def refl001P : String :=
  "<?xml version=\"1.0\"?>\n" ++
  "<rdf:RDF\n" ++
  "  xml:base  = \"http://example.org/\"\n" ++
  "  xmlns     = \"http://example.org/\"\n" ++
  "  xmlns:owl = \"http://www.w3.org/2002/07/owl#\"\n" ++
  "  xmlns:rdf = \"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
  "\n" ++
  "<owl:Ontology/>\n" ++
  "\n" ++
  "<owl:ObjectProperty rdf:about=\"knows\" />\n" ++
  "<owl:NamedIndividual rdf:about=\"Peter\" />\n" ++
  "\n" ++
  "<owl:ReflexiveProperty rdf:about=\"knows\" />\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `New-Feature-ReflexiveProperty-001`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def refl001C : String :=
  "<?xml version=\"1.0\"?>\n" ++
  "<rdf:RDF\n" ++
  "  xml:base  = \"http://example.org/\"\n" ++
  "  xmlns     = \"http://example.org/\"\n" ++
  "  xmlns:owl = \"http://www.w3.org/2002/07/owl#\"\n" ++
  "  xmlns:rdf = \"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
  "\n" ++
  "<owl:Ontology/>\n" ++
  "\n" ++
  "<owl:ObjectProperty rdf:about=\"knows\" />\n" ++
  "\n" ++
  "<rdf:Description rdf:about=\"Peter\">\n" ++
  "  <knows rdf:resource=\"Peter\" />\n" ++
  "</rdf:Description>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `WebOnt-I5.8-011`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def i58011P : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\">\n" ++
  "  <owl:Ontology/>\n" ++
  "</rdf:RDF>"

/-- `WebOnt-I5.8-011`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def i58011C : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/I5.8/conclusions011\" >\n" ++
  "\n" ++
  "  <owl:Ontology/>\n" ++
  "  <rdfs:Datatype rdf:about=\"http://www.w3.org/2001/XMLSchema#integer\"/>\n" ++
  "  <rdfs:Datatype rdf:about=\"http://www.w3.org/2001/XMLSchema#string\"/>\n" ++
  "</rdf:RDF>"

/-- `New-Feature-ObjectQCR-001`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def qcr001P : String :=
  "<?xml version=\"1.0\"?>\n" ++
  "<rdf:RDF\n" ++
  "  xml:base  = \"http://example.org/\"\n" ++
  "  xmlns     = \"http://example.org/\"\n" ++
  "  xmlns:owl = \"http://www.w3.org/2002/07/owl#\"\n" ++
  "  xmlns:rdf = \"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
  "\n" ++
  "<owl:Ontology/>\n" ++
  "\n" ++
  "<owl:ObjectProperty rdf:about=\"fatherOf\" />\n" ++
  "<owl:Class rdf:about=\"Man\" />\n" ++
  "\n" ++
  "<rdf:Description rdf:about=\"Peter\">\n" ++
  "  <fatherOf rdf:resource=\"Stewie\" />\n" ++
  "  <fatherOf rdf:resource=\"Chris\" />\n" ++
  "</rdf:Description>\n" ++
  "\n" ++
  "<Man rdf:about=\"Stewie\" />\n" ++
  "<Man rdf:about=\"Chris\" />\n" ++
  "\n" ++
  "<rdf:Description rdf:about=\"Stewie\">\n" ++
  "  <owl:differentFrom rdf:resource=\"Chris\" />\n" ++
  "</rdf:Description>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `New-Feature-ObjectQCR-001`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def qcr001C : String :=
  "<?xml version=\"1.0\"?>\n" ++
  "<rdf:RDF\n" ++
  "  xml:base  = \"http://example.org/\"\n" ++
  "  xmlns     = \"http://example.org/\"\n" ++
  "  xmlns:owl = \"http://www.w3.org/2002/07/owl#\"\n" ++
  "  xmlns:rdf = \"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
  "\n" ++
  "<owl:Ontology/>\n" ++
  "\n" ++
  "<owl:ObjectProperty rdf:about=\"fatherOf\" />\n" ++
  "<owl:Class rdf:about=\"Man\" />\n" ++
  "\n" ++
  "<rdf:Description rdf:about=\"Peter\">\n" ++
  "  <rdf:type>\n" ++
  "    <owl:Restriction>\n" ++
  "      <owl:onProperty rdf:resource=\"fatherOf\" />\n" ++
  "      <owl:minQualifiedCardinality rdf:datatype=\"http://www.w3.org/2001/XMLSchema#nonNegativeInteger\">2</owl:minQualifiedCardinality>\n" ++
  "      <owl:onClass rdf:resource=\"Man\" />\n" ++
  "    </owl:Restriction>\n" ++
  "  </rdf:type>\n" ++
  "</rdf:Description>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `WebOnt-AnnotationProperty-002`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def ap002P : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xmlns:first=\"http://www.w3.org/2002/03owlt/AnnotationProperty/premises002#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/AnnotationProperty/premises002\" >\n" ++
  "\n" ++
  "  <owl:Ontology/>\n" ++
  "  <owl:Class rdf:ID=\"A\">\n" ++
  "    <first:ap>\n" ++
  "       <owl:Class rdf:ID=\"B\"/>\n" ++
  "    </first:ap>\n" ++
  "  </owl:Class>\n" ++
  "  <owl:AnnotationProperty rdf:ID=\"ap\"/>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `WebOnt-AnnotationProperty-002`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def ap002C : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xmlns:first=\"http://www.w3.org/2002/03owlt/AnnotationProperty/premises002#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/AnnotationProperty/conclusions002\" >\n" ++
  "\n" ++
  " <owl:Ontology/>\n" ++
  " <owl:Class rdf:about=\"premises002#A\">\n" ++
  "    <first:ap>\n" ++
  "       <owl:Thing />\n" ++
  "    </first:ap>\n" ++
  "  </owl:Class>\n" ++
  "  <owl:AnnotationProperty rdf:about=\"premises002#ap\"/>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `chain2trans1`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def c2t1P : String :=
  "<rdf:RDF \n" ++
  "     xml:base=\"http://example.org/ontology\"\n" ++
  "     xmlns:xsd=\"http://www.w3.org/2001/XMLSchema#\"\n" ++
  "     xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\"\n" ++
  "     xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "     xmlns:owl=\"http://www.w3.org/2002/07/owl#\">\n" ++
  "\n" ++
  "    <owl:Ontology rdf:about=\"\"/>\n" ++
  "    <owl:ObjectProperty rdf:about=\"#p\"/>\n" ++
  "\n" ++
  "    <rdf:Description rdf:about=\"#p\">\n" ++
  "        <owl:propertyChainAxiom rdf:parseType=\"Collection\">\n" ++
  "            <rdf:Description rdf:about=\"#p\"/>\n" ++
  "            <rdf:Description rdf:about=\"#p\"/>\n" ++
  "        </owl:propertyChainAxiom>\n" ++
  "    </rdf:Description>\n" ++
  "</rdf:RDF>"

/-- `chain2trans1`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def c2t1C : String :=
  "<?xml version=\"1.0\"?>\n" ++
  "<rdf:RDF \n" ++
  "     xml:base=\"http://example.org/ontology\"\n" ++
  "     xmlns:xsd=\"http://www.w3.org/2001/XMLSchema#\"\n" ++
  "     xmlns:rdfs=\"http://www.w3.org/2000/01/rdf-schema#\"\n" ++
  "     xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "     xmlns:owl=\"http://www.w3.org/2002/07/owl#\">\n" ++
  "    <owl:Ontology rdf:about=\"\"/>\n" ++
  "    <owl:TransitiveProperty rdf:about=\"#p\"/>\n" ++
  "</rdf:RDF>"

/-- `WebOnt-I5.5-005`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def i55005P : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/I5.5/premises005\" >\n" ++
  "    <owl:Class rdf:ID=\"a\" />\n" ++
  "</rdf:RDF>"

/-- `WebOnt-I5.5-005`, the conclusion document (RDF/XML, verbatim from `all.rdf`). -/
def i55005C : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\"\n" ++
  "    xmlns:owl=\"http://www.w3.org/2002/07/owl#\"\n" ++
  "    xml:base=\"http://www.w3.org/2002/03owlt/I5.5/conclusions005\" >\n" ++
  "   \n" ++
  "   <owl:Class>\n" ++
  "     <owl:unionOf>\n" ++
  "       <rdf:List>\n" ++
  "         <rdf:first>\n" ++
  "           <owl:Class rdf:about=\"premises005#a\"/>\n" ++
  "         </rdf:first>\n" ++
  "         <rdf:rest rdf:resource = \"http://www.w3.org/1999/02/22-rdf-syntax-ns#nil\"/>\n" ++
  "       </rdf:List>\n" ++
  "     </owl:unionOf>\n" ++
  "   </owl:Class>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-- `WebOnt-imports-011`, the premise document (RDF/XML, verbatim from `all.rdf`). -/
def imp011P : String :=
  "<rdf:RDF\n" ++
  "    xmlns:rdf='http://www.w3.org/1999/02/22-rdf-syntax-ns#'\n" ++
  "    xmlns:rdfs='http://www.w3.org/2000/01/rdf-schema#'\n" ++
  "    xmlns:owl='http://www.w3.org/2002/07/owl#'\n" ++
  "    xmlns:ont='http://www.w3.org/2002/03owlt/imports/support011-A#'\n" ++
  "    xml:base='http://www.w3.org/2002/03owlt/imports/premises011' >\n" ++
  "\n" ++
  "    <owl:Ontology rdf:about=''>\n" ++
  "        <owl:imports \n" ++
  "     rdf:resource=\"http://www.w3.org/2002/03owlt/imports/support011-A\"/>\n" ++
  "    </owl:Ontology>\n" ++
  "\n" ++
  "    <ont:Man rdf:about='http://example.org/data#Socrates'/>\n" ++
  "\n" ++
  "</rdf:RDF>"

/-! ## Reading them

The premise is parsed as it is; the conclusion's blank nodes get the
prefix `c_`, as `l4owl-probe` gives them (`speciesDocs`), so the two
documents share no blank-node label. A document that does not parse
gives the empty graph; the first guards below fail the build then. -/

def parse (txt : String) : Graph :=
  match RdfXml.parseRdfXml txt (some "http://example.org/balanced-tests") with
  | .ok g => g
  | .error _ => []

def parseC (txt : String) : Graph := (parse txt).prefixBnodes "c_"

/-- The condition numbers of the defects of a pair. -/
def conds (g1 g2 : Graph) : List String := (balancedDefectsOf g1 g2).map (·.cond)

/-- Does some defect name condition `k` and mention `s`? -/
def hasDefect (g1 g2 : Graph) (k s : String) : Bool :=
  (balancedDefectsOf g1 g2).any (fun d => d.cond == k && (d.what.splitOn s).length > 1)

#guard [eqc004P, eqc004C, dl101P, union003P, union003C, refl001P, refl001C, i58011P,
        i58011C, qcr001P, qcr001C, ap002P, ap002C, c2t1P, c2t1C, i55005P, i55005C,
        imp011P].all
  (fun t => !(parse t).isEmpty)

/-! ## Positive: balanced pairs -/

-- `WebOnt-equivalentClass-004`: every IRI of both documents is declared,
-- the conclusion has an anonymous header, no literal, no expression.
#guard balancedDefectsOf (parse eqc004P) (parseC eqc004C) == []
#guard isBalanced (parse eqc004P) (parseC eqc004C)

-- `WebOnt-description-logic-101`: classes and the property are declared;
-- the one individual is a blank node (an anonymous individual needs no
-- declaration).
#guard balancedDefectsOf (parse dl101P) inconsistencyGoal == []

/-! ## Negative: one condition each -/

-- 2.1 in G1: `#a` and `#b` are used as individuals, never declared.
#guard hasDefect (parse union003P) (parseC union003C) "2.1" "G1: "
#guard hasDefect (parse union003P) (parseC union003C) "2.1" "unionOf/premises003#a"
#guard !isBalanced (parse union003P) (parseC union003C)
-- The same premise is not balanced against the inconsistency goal either:
-- condition 2.1 reads G1 alone.
#guard (balancedDefectsOf (parse union003P) inconsistencyGoal).any (·.cond == "2.1")

-- 2.1 in G2 only: the premise declares `Peter`, the conclusion does not.
#guard hasDefect (parse refl001P) (parseC refl001C) "2.1" "G2: http://example.org/Peter"
#guard !hasDefect (parse refl001P) (parseC refl001C) "2.1" "G1: "
#guard !isBalanced (parse refl001P) (parseC refl001C)

-- 2.1 in G2: a property characteristic needs the object property declaration.
#guard hasDefect (parse c2t1P) (parseC c2t1C) "2.1" "G2: http://example.org/ontology#p"
-- 3, IRI branch: the conclusion's header IRI is the premise's ontology IRI.
#guard !(conds (parse c2t1P) (parseC c2t1C)).contains "3"

-- 2.2 and 5.2-5.5: the restriction and its literal are only in G2.
#guard hasDefect (parse qcr001P) (parseC qcr001C) "2.2" "\"2\"^^xsd:nonNegativeInteger"
#guard (conds (parse qcr001P) (parseC qcr001C)).contains "5.2-5.5"
-- Against itself the conclusion's expression IS a subgraph: the renaming
-- search finds it (a check that never embedded would fail this).
#guard structuralEmbed (parseC qcr001C) ((parseC qcr001C).prefixBnodes "d_") == .found
#guard structuralEmbed (parse qcr001P) (parseC qcr001C) == .notFound
-- One-to-one: two copies of the restriction (different blank nodes) cannot
-- both go to the one copy in G1; they can go to two copies.
#guard structuralEmbed (parseC qcr001C)
  (parseC qcr001C ++ (parseC qcr001C).prefixBnodes "e_") == .notFound
#guard structuralEmbed ((parseC qcr001C).prefixBnodes "d_" ++ (parseC qcr001C).prefixBnodes "f_")
  (parseC qcr001C ++ (parseC qcr001C).prefixBnodes "e_") == .found

-- 4.1: an annotation assertion in the conclusion.
#guard hasDefect (parse ap002P) (parseC ap002C) "4.1" "premises002#ap"

-- 5.1: declarations of the conclusion that the premise does not carry.
#guard hasDefect (parse i58011P) (parseC i58011C) "5.1" "xsd:integer rdf:type rdfs:Datatype"
#guard !isBalanced (parse i58011P) (parseC i58011C)

-- 1 and 3: the conclusion of `WebOnt-I5.5-005` has no ontology header (the
-- disputed fixture of https://github.com/danbri/factoidal/issues/711).
#guard hasDefect (parse i55005P) (parseC i55005C) "1" "no-ontology-header"
#guard hasDefect (parse i55005P) (parseC i55005C) "3" "no ontology header"

-- 4.2: no conclusion of the catalog states an ontology property, so the
-- premise of `WebOnt-imports-011` (its header imports `support011-A`) is put
-- in the place of G2. The same document is also not balanced against
-- itself by condition 3: its header has two triples.
#guard hasDefect (parse imp011P) (parseC imp011P) "4.2" "owl:imports"
#guard hasDefect (parse imp011P) (parseC imp011P) "3" "consists of 2 triples"

/-! ## The inconsistency goal

`inconsistencyGoal` alone, against a premise that is the goal itself, is
balanced: no condition reads anything in it. -/

#guard balancedDefectsOf inconsistencyGoal inconsistencyGoal == []

end L4Factoidal.OWL.RdfBased.BalancedTests
