/-
L4Factoidal.OWL.RdfBased.Balanced — the condition "balanced" of OWL 2
RDF-Based Semantics § 7.3, checked for a pair of RDF graphs (G1, G2).

Specification: OWL 2 Web Ontology Language RDF-Based Semantics (Second
Edition), W3C Recommendation 11 December 2012, § 7.2 (Theorem 7.1, the
correspondence theorem) and § 7.3 (Definition (Balanced), the balancing
lemma, and the proof of relationship 4 of the theorem),
<https://www.w3.org/TR/owl2-rdf-based-semantics/#Correspondence_Theorem>.
Issue: <https://github.com/danbri/factoidal/issues/732>. Design record:
`docs/designissues/2026-10-10-owl2-rdf-based-semantics.md` § 6.2.

## Why the condition matters

Theorem 7.1 says that for an OWL 2 DL pair (G1*, G2*) there EXIST graphs
G1, G2 with the same Direct Semantics meaning such that a Direct
Semantics entailment of F(G2) by F(G1) gives an RDF-Based entailment of
G2 by G1. The proof in § 7.3 constructs (G1, G2) by the balancing lemma
and then proves relationship 4 for that pair using only the fact that
the pair is balanced ("Since the pair ( G1 , G2 ) is balanced, ..."). So
for an input pair that is ALREADY balanced, the pair itself can be used:
a Direct Semantics entailment of the input conclusion carries over to the
RDF-Based Semantics. For a pair that is not balanced, it does not:
§ 7.1 gives a pair that is a Direct entailment and not an RDF-Based one.

## The definition, as the specification states it

"A pair of RDF graphs ( G1 , G2 ) is called balanced, if and only if G1
and G2 are OWL 2 DL ontologies in RDF graph form, such that all the
following conditions hold":

1. "F(G1) and F(G2) mutually meet the restrictions on OWL 2 DL
   ontologies as specified in Section 3 of the OWL 2 Structural
   Specification".
2. Nodes in G1 and G2: (2.1) "for every IRI u occurring in G1 or G2 that
   corresponds to a non-built-in entity in F(G1) or F(G2), respectively,
   the graph contains, for every entity type T of u, a declaration
   statement of the form "u rdf:type t""; (2.2) "every plain or typed
   literal occurring in G2 also occurs in G1".
3. "G2 contains exactly one ontology header consisting of a single RDF
   triple of the form "x rdf:type owl:Ontology", where x is either a
   blank node or, if an ontology IRI is used in G1, may alternatively
   equal that ontology IRI".
4. G2 does not contain: (4.1) the RDF encoding of an annotation; (4.2) a
   statement with an ontology property such as "owl:imports"; (4.3) a
   deprecation statement; (4.4) "an annotation property axiom based on
   "rdfs:subClassOf", "rdfs:domain" and "rdfs:range"".
5. "Any of the following sub graphs of G2 is also a sub graph of G1": an
   entity declaration (5.1), a property expression (5.2), a class
   expression (5.3), a data range (5.4), an RDF sequence (5.5).

## How each condition is read here

* 1 and "OWL 2 DL ontologies in RDF graph form": the caller passes the
  violations `SyntaxDL.speciesViolations` reports for the pair (the
  species checker of `l4owl-probe --species`, which reads the conclusion
  against the union of both documents). `balancedDefectsOf` computes
  them for two graphs.
* 2.1: `usesOfTriple` reads the entity type of each non-built-in IRI
  from the position it takes in a triple (the reverse mapping, OWL 2
  Mapping to RDF Graphs § 3.2, Tables 10 to 16), and the graph must
  type the IRI with the vocabulary class of Table 7 of that mapping
  (`owl:Class`, `rdfs:Datatype`, `owl:ObjectProperty`,
  `owl:DatatypeProperty`, `owl:AnnotationProperty`,
  `owl:NamedIndividual`). A position that admits two entity types (the
  filler of `owl:someValuesFrom` is a class or a datatype; the predicate
  of an assertion is an object, data or annotation property) is met by
  either declaration. Built-in means: an IRI of the `owl:`, `rdf:`,
  `rdfs:` or `xsd:` namespace (`SyntaxDL.iriReserved`).
* 2.2: literal identity of RDF 1.1 Concepts § 3.3 (lexical form,
  datatype IRI, language tag).
* 3: the root header of G2 (`SyntaxDL.rootHeaderKeys`) is the only
  subject typed `owl:Ontology`, and no other triple has it as subject. An
  IRI header must equal a root header IRI of G1.
* 4.1: a triple whose predicate is a built-in annotation property
  (Structural Specification § 5.5) or an IRI declared
  `owl:AnnotationProperty` in either graph; an `owl:Axiom` or
  `owl:Annotation` node; `owl:annotatedSource`, `owl:annotatedProperty`,
  `owl:annotatedTarget`. 4.2: `owl:imports`, `owl:priorVersion`,
  `owl:backwardCompatibleWith`, `owl:incompatibleWith`, `owl:versionIRI`
  (the members of IOXP in Table 5.3 of the RDF-Based Semantics), or an
  IRI declared `owl:OntologyProperty`. 4.3: `owl:deprecated`, `rdf:type
  owl:DeprecatedClass`, `rdf:type owl:DeprecatedProperty`. 4.4: a
  triple whose subject is an annotation property and whose predicate is
  `rdfs:subClassOf` (the specification's wording), `rdfs:subPropertyOf`
  (the encoding of `SubAnnotationPropertyOf` in Table 16 of the
  mapping), `rdfs:domain` or `rdfs:range`.
* 5.1: every triple `u rdf:type t` of G2 with `u` an IRI and `t` a
  vocabulary class of Table 7 is a triple of G1.
* 5.2 to 5.5: the triples of G2 that encode expressions and sequences
  (`structuralTriple`: a blank-node subject with a predicate of Tables 3,
  11 to 15 of the mapping, or a facet) must be a subgraph of G1 under ONE
  one-to-one renaming of their blank nodes to blank nodes of G1
  (`structuralEmbed`). The renaming is allowed because the two graphs
  come from different documents and RDF-Based entailment of G2 does not
  depend on the names of its blank nodes; it must be one-to-one, because
  identifying two blank nodes of G2 makes a stronger conclusion than G2.
  The search is bounded (`embedBudget`); a search that runs out of
  steps is reported as a defect, never as balanced.

## What is not proved here

This module CHECKS the condition. It does not prove Theorem 7.1, whose
§ 7.3 text is a proof sketch ("some technical aspects of the theorem are
only coarsely treated"), and it does not prove that `usesOfTriple` finds
every entity type the reverse mapping assigns. A defect in the check
can only make an unbalanced pair look balanced if it MISSES a use or a
structural triple; the `#guard` cases in `BalancedTests.lean` test each
condition on real W3C catalog documents, positive and negative.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.SyntaxDL

namespace L4Factoidal.OWL.RdfBased.Balanced

open L4Factoidal.RDF
open L4Factoidal.OWL.SyntaxDL

/-! ## Vocabulary not in `SyntaxDL` -/

def owlNamedIndividualC : String := nsOwl ++ "NamedIndividual"
def owlThingC           : String := nsOwl ++ "Thing"
def owlNothingC         : String := nsOwl ++ "Nothing"
def owlAxiomC           : String := nsOwl ++ "Axiom"
def owlAnnotationC      : String := nsOwl ++ "Annotation"
def owlDeprecatedClassC : String := nsOwl ++ "DeprecatedClass"
def owlDeprecatedPropC  : String := nsOwl ++ "DeprecatedProperty"
def owlAllDisjointClassesC    : String := nsOwl ++ "AllDisjointClasses"
def owlAllDisjointPropertiesC : String := nsOwl ++ "AllDisjointProperties"
def owlAllDifferentC    : String := nsOwl ++ "AllDifferent"

def rdfsSubClassOfP     : String := nsRdfs ++ "subClassOf"
def owlDisjointWithP    : String := nsOwl ++ "disjointWith"
def owlDisjointUnionOfP : String := nsOwl ++ "disjointUnionOf"
def owlOnPropertiesP    : String := nsOwl ++ "onProperties"
def owlSomeValuesFromP  : String := nsOwl ++ "someValuesFrom"
def owlAllValuesFromP   : String := nsOwl ++ "allValuesFrom"
def owlOnClassP         : String := nsOwl ++ "onClass"
def owlOnDataRangeP     : String := nsOwl ++ "onDataRange"
def owlHasKeyP          : String := nsOwl ++ "hasKey"
def owlWithRestrictionsP : String := nsOwl ++ "withRestrictions"
def owlDeprecatedP      : String := nsOwl ++ "deprecated"
def owlAnnotatedSourceP   : String := nsOwl ++ "annotatedSource"
def owlAnnotatedPropertyP : String := nsOwl ++ "annotatedProperty"
def owlAnnotatedTargetP   : String := nsOwl ++ "annotatedTarget"
def rdfLangRangeP       : String := nsRdf ++ "langRange"

/-- The ontology properties: the IRIs with `I(E) ∈ IOXP` in Table 5.3
of the RDF-Based Semantics. -/
def ontologyProps : List String :=
  [owlImportsP, owlPriorVersionP, nsOwl ++ "backwardCompatibleWith",
   nsOwl ++ "incompatibleWith", nsOwl ++ "versionIRI"]

/-- OWL 2 Mapping to RDF Graphs, Table 7: the vocabulary class that
declares each entity type. -/
def declarationClasses : List String :=
  [owlClassC, rdfsDatatypeC, owlObjPropC, owlDataPropC, owlAnnPropC,
   owlNamedIndividualC]

/-! ## Condition 2.1: entity types from positions -/

/-- One use of a non-built-in IRI as an entity: its key (`"I" ++ iri`,
the `SyntaxDL` convention), the declaration classes any one of which
declares the entity type of the use, and the position, for the report. -/
structure Use where
  key   : String
  decls : List String
  pos   : String
deriving BEq, Repr

def clsD  : List String := [owlClassC]
def dtD   : List String := [rdfsDatatypeC]
def ceD   : List String := [owlClassC, rdfsDatatypeC]
def objD  : List String := [owlObjPropC]
def dataD : List String := [owlDataPropC]
def odD   : List String := [owlObjPropC, owlDataPropC]
def propD : List String := [owlObjPropC, owlDataPropC, owlAnnPropC]
def indD  : List String := [owlNamedIndividualC]

/-- The key of a term that is a non-built-in IRI. -/
def entityKeyT : Term → Option String
  | .iri i => if iriReserved i.val then none else some ("I" ++ i.val)
  | _ => none

def entityKeyS : Subject → Option String
  | .iri i => if iriReserved i.val then none else some ("I" ++ i.val)
  | .bnode _ => none

def useT (o : Term) (d : List String) (pos : String) : List Use :=
  match entityKeyT o with
  | some k => [⟨k, d, pos⟩]
  | none => []

def useS (s : Subject) (d : List String) (pos : String) : List Use :=
  match entityKeyS s with
  | some k => [⟨k, d, pos⟩]
  | none => []

/-- The members of the RDF list `o` (Table 3 of the mapping). -/
def useMembers (g : Graph) (o : Term) (d : List String) (pos : String) : List Use :=
  (collectionMembers g o g.length).flatMap (fun m => useT m d pos)

/-- The local name of an IRI of a built-in namespace, for the report. -/
def shortP (p : String) : String :=
  if p.startsWith nsOwl then "owl:" ++ (p.drop nsOwl.length).toString
  else if p.startsWith nsRdfs then "rdfs:" ++ (p.drop nsRdfs.length).toString
  else if p.startsWith nsRdf then "rdf:" ++ (p.drop nsRdf.length).toString
  else if p.startsWith nsXsd then "xsd:" ++ (p.drop nsXsd.length).toString
  else p

/-- The entity uses one triple makes, read by the position of each IRI
(OWL 2 Mapping to RDF Graphs § 3.2, Tables 10 to 16). `g` is the graph
the triple belongs to; it decides list members and the declared type of
a property where the position alone does not. -/
def usesOfTriple (g : Graph) (t : Triple) : List Use :=
  let p := t.p.val
  let sk := subjKey t.s
  let posOf := fun (what : String) => s!"{what} ({shortP p})"
  if p == rdfTypeP then
    match t.o with
    | .iri o =>
        if o.val == owlThingC || o.val == owlNothingC then
          useS t.s indD "an individual (rdf:type owl:Thing or owl:Nothing)"
        else if objCharacteristics.contains o.val then
          useS t.s objD s!"an object property (rdf:type {shortP o.val})"
        else if o.val == owlFunctionalPropC then
          useS t.s odD "a property (rdf:type owl:FunctionalProperty)"
        else if iriReserved o.val then []
        else
          useT t.o clsD "a class (object of rdf:type)" ++
          useS t.s indD "an individual (subject of rdf:type)"
    | .bnode _ => useS t.s indD "an individual (subject of rdf:type)"
    | _ => []
  else if p == rdfsSubClassOfP || p == owlDisjointWithP || p == owlComplementOfP then
    useS t.s clsD (posOf "a class") ++ useT t.o clsD (posOf "a class")
  else if p == owlEquivClassP then
    useS t.s ceD (posOf "a class or datatype") ++ useT t.o ceD (posOf "a class or datatype")
  else if p == owlUnionOfP || p == owlIntersectionOfP then
    useS t.s ceD (posOf "a class or datatype") ++
    useMembers g t.o ceD (posOf "a class or datatype, list member")
  else if p == owlOneOfP then
    useS t.s ceD (posOf "a class or datatype") ++
    useMembers g t.o indD (posOf "an individual, list member")
  else if p == owlDisjointUnionOfP then
    useS t.s clsD (posOf "a class") ++ useMembers g t.o clsD (posOf "a class, list member")
  else if p == owlMembersP then
    if hasTypeSp g sk owlAllDisjointClassesC then
      useMembers g t.o clsD (posOf "a class, list member")
    else if hasTypeSp g sk owlAllDisjointPropertiesC then
      useMembers g t.o odD (posOf "a property, list member")
    else if hasTypeSp g sk owlAllDifferentC then
      useMembers g t.o indD (posOf "an individual, list member")
    else []
  else if p == owlDistinctMembersP then
    useMembers g t.o indD (posOf "an individual, list member")
  else if p == owlOnPropertyP then useT t.o odD (posOf "a property")
  else if p == owlOnPropertiesP then useMembers g t.o dataD (posOf "a data property, list member")
  else if p == owlSomeValuesFromP || p == owlAllValuesFromP then
    useT t.o ceD (posOf "a class or datatype")
  else if p == owlOnClassP then useT t.o clsD (posOf "a class")
  else if p == owlOnDataRangeP || p == owlOnDatatypeP || p == owlDtComplementP then
    useT t.o dtD (posOf "a datatype")
  else if p == owlHasValueP then useT t.o indD (posOf "an individual")
  else if p == rdfsDomainP then
    useS t.s propD (posOf "a property") ++
    (if hasTypeSp g sk owlAnnPropC then [] else useT t.o clsD (posOf "a class"))
  else if p == rdfsRangeP then
    useS t.s propD (posOf "a property") ++
    (if hasTypeSp g sk owlAnnPropC then []
     else if hasTypeSp g sk owlDataPropC then useT t.o dtD (posOf "a datatype")
     else if hasTypeSp g sk owlObjPropC then useT t.o clsD (posOf "a class")
     else useT t.o ceD (posOf "a class or datatype"))
  else if p == rdfsSubPropertyOfP || p == owlEquivPropP then
    useS t.s propD (posOf "a property") ++ useT t.o propD (posOf "a property")
  else if p == owlPropDisjointP then
    useS t.s odD (posOf "a property") ++ useT t.o odD (posOf "a property")
  else if p == owlInverseOfP then
    useS t.s objD (posOf "an object property") ++ useT t.o objD (posOf "an object property")
  else if p == owlChainP then
    useS t.s objD (posOf "an object property") ++
    useMembers g t.o objD (posOf "an object property, list member")
  else if p == owlHasKeyP then
    useS t.s clsD (posOf "a class") ++ useMembers g t.o odD (posOf "a property, list member")
  else if p == owlSameAsP || p == owlDifferentFromP then
    useS t.s indD (posOf "an individual") ++ useT t.o indD (posOf "an individual")
  else if p == owlSourceIndP || p == owlTargetIndP then useT t.o indD (posOf "an individual")
  else if p == owlAssertionPropP then useT t.o odD (posOf "a property")
  else if iriReserved p then []
  else
    -- An assertion with a non-built-in predicate: an object or data
    -- property assertion (Table 16), or an annotation assertion (Table 17).
    let pk := "I" ++ p
    let pu : Use := ⟨pk, propD, "a property (predicate of an assertion)"⟩
    if hasTypeSp g pk owlAnnPropC then [pu]
    else
      pu :: (useS t.s indD "an individual (subject of a property assertion)" ++
        (if hasTypeSp g pk owlObjPropC
         then useT t.o indD "an individual (object of an object property assertion)"
         else []))

/-- The uses in `g` that `g` does not declare (condition 2.1), one per
key and declaration set. -/
def missingDeclarations (g : Graph) : List Use :=
  let uses := g.flatMap (usesOfTriple g)
  let missing := uses.filter (fun u => !(u.decls.any (hasTypeSp g u.key)))
  missing.foldl (fun acc u =>
    if acc.any (fun v => v.key == u.key && v.decls == u.decls) then acc else acc ++ [u]) []

/-! ## Condition 2.2: literals -/

def literalsOf (g : Graph) : List Term :=
  g.filterMap (fun t => match t.o with | .literal _ => some t.o | _ => none)

/-- The literals of `g2` that do not occur in `g1`. -/
def missingLiterals (g1 g2 : Graph) : List Term :=
  (literalsOf g2).eraseDups.filter (fun l => !(g1.any (fun t => t.o == l)))

def showLiteral : Term → String
  | .literal l =>
      match l.val.langTag with
      | some tag => s!"\"{l.val.lexicalForm}\"@{tag}"
      | none => s!"\"{l.val.lexicalForm}\"^^{shortP l.val.datatype.val}"
  | _ => "(not a literal)"

/-! ## Condition 3: the ontology header of G2 -/

def showKey (k : String) : String :=
  if k.startsWith "I" then shortP (k.drop 1).toString else "_:" ++ (k.drop 1).toString

def headerDefects (g1 g2 : Graph) : List String :=
  match dedupStrs (subjectsTyped g2 owlOntologyC) with
  | [] => ["G2 has no ontology header (no triple x rdf:type owl:Ontology)"]
  | [x] =>
      let n := (g2.filter (fun t => subjKey t.s == x)).length
      (if n == 1 then []
       else [s!"the ontology header {showKey x} of G2 consists of {n} triples, not one"]) ++
      (if x.startsWith "B" || (rootHeaderKeys g1).contains x then []
       else [s!"the ontology header of G2 is the IRI {showKey x}, which is neither a blank node \
nor the ontology IRI of G1"])
  | hs => [s!"G2 has {hs.length} ontology headers, not one"]

/-! ## Condition 4: what G2 must not contain -/

def isAnnotationProp (g1 g2 : Graph) (iri : String) : Bool :=
  builtinAnnProps.contains iri || hasTypeSp g1 ("I" ++ iri) owlAnnPropC ||
  hasTypeSp g2 ("I" ++ iri) owlAnnPropC

def isOntologyProp (g1 g2 : Graph) (iri : String) : Bool :=
  ontologyProps.contains iri || hasTypeSp g1 ("I" ++ iri) owlOntPropC ||
  hasTypeSp g2 ("I" ++ iri) owlOntPropC

/-- The condition (4.1 to 4.4) one triple of G2 violates, if any. -/
def forbiddenCond (g1 g2 : Graph) (t : Triple) : Option String :=
  let p := t.p.val
  let typedAs := fun (c : String) => p == rdfTypeP && termIsIri t.o c
  let subjAnn := match t.s with
    | .iri i => isAnnotationProp g1 g2 i.val
    | .bnode _ => false
  if isOntologyProp g1 g2 p then some "4.2"
  else if p == owlDeprecatedP || typedAs owlDeprecatedClassC || typedAs owlDeprecatedPropC then
    some "4.3"
  else if subjAnn && (p == rdfsSubClassOfP || p == rdfsSubPropertyOfP ||
                      p == rdfsDomainP || p == rdfsRangeP) then some "4.4"
  else if isAnnotationProp g1 g2 p || typedAs owlAxiomC || typedAs owlAnnotationC ||
          p == owlAnnotatedSourceP || p == owlAnnotatedPropertyP ||
          p == owlAnnotatedTargetP then some "4.1"
  else none

def showSubj : Subject → String
  | .iri i => shortP i.val
  | .bnode b => "_:" ++ b

def showObj : Term → String
  | .iri i => shortP i.val
  | .bnode b => "_:" ++ b
  | t@(.literal _) => showLiteral t
  | .tripleTerm _ _ _ => "(triple term)"

def showTripleB (t : Triple) : String :=
  s!"{showSubj t.s} {shortP t.p.val} {showObj t.o}"

/-! ## Condition 5.1: declarations of G2 are in G1 -/

def isDeclarationTriple (t : Triple) : Bool :=
  t.p.val == rdfTypeP &&
  (match t.s with | .iri _ => true | .bnode _ => false) &&
  (match t.o with | .iri o => declarationClasses.contains o.val | _ => false)

def declarationsNotInG1 (g1 g2 : Graph) : List Triple :=
  g2.filter (fun t => isDeclarationTriple t && !(g1.contains t))

/-! ## Conditions 5.2 to 5.5: expressions and sequences of G2 are in G1 -/

/-- The predicates of the encodings of property expressions (Table 11
of the mapping), class expressions (Tables 13 and 15), data ranges
(Tables 12 and 14) and sequences (Table 3). -/
def exprPreds : List String :=
  [owlInverseOfP, owlIntersectionOfP, owlUnionOfP, owlComplementOfP, owlOneOfP,
   owlOnPropertyP, owlOnPropertiesP, owlSomeValuesFromP, owlAllValuesFromP,
   owlHasValueP, owlHasSelfP, owlOnClassP, owlOnDataRangeP, owlOnDatatypeP,
   owlWithRestrictionsP, owlDtComplementP, rdfFirstP, rdfRestP] ++ cardinalityPreds

/-- The `rdf:type` objects of those encodings. -/
def exprTypes : List String := [owlRestrictionC, owlClassC, rdfsDatatypeC, rdfListC]

/-- A facet of a datatype restriction (Table 12): an `xsd:` facet or
`rdf:langRange`. -/
def isFacetPred (p : String) : Bool := p.startsWith nsXsd || p == rdfLangRangeP

/-- Does the triple belong to the encoding of an expression or a
sequence? Its subject is a blank node, and its predicate is one of
`exprPreds`, a facet, or `rdf:type` with an object of `exprTypes`. An
axiom triple whose subject is a class expression (`_:x rdfs:subClassOf
C`) is not part of the expression. -/
def structuralTriple (t : Triple) : Bool :=
  match t.s with
  | .bnode _ =>
      exprPreds.contains t.p.val || isFacetPred t.p.val ||
      (t.p.val == rdfTypeP && (match t.o with
        | .iri o => exprTypes.contains o.val
        | _ => false))
  | .iri _ => false

/-- A partial one-to-one map from blank nodes of G2 to blank nodes of G1. -/
abbrev BMap := List (BNodeId × BNodeId)

def bmapGet (m : BMap) (b : BNodeId) : Option BNodeId :=
  (m.find? (fun kv => kv.1 == b)).map Prod.snd

/-- Extend the map with `b ↦ c`, keeping it a function and one-to-one. -/
def bmapBind (m : BMap) (b c : BNodeId) : Option BMap :=
  match bmapGet m b with
  | some c' => if c' == c then some m else none
  | none => if m.any (fun kv => kv.2 == c) then none else some ((b, c) :: m)

def matchSubjectInj (m : BMap) : Subject → Subject → Option BMap
  | .bnode b, .bnode c => bmapBind m b c
  | .iri i, .iri j => if i == j then some m else none
  | _, _ => none

def matchTermInj (m : BMap) : Term → Term → Option BMap
  | .bnode b, .bnode c => bmapBind m b c
  | .bnode _, _ => none
  | x, y => if x == y then some m else none

def matchTripleInj (m : BMap) (pat t : Triple) : Option BMap :=
  if pat.p == t.p then
    match matchSubjectInj m pat.s t.s with
    | some m' => matchTermInj m' pat.o t.o
    | none => none
  else none

/-- One frame of the depth-first search: the pattern to place, the
patterns after it, the map so far, and the candidates of G1 not tried
yet for the pattern. -/
structure Frame where
  head  : Triple
  rest  : List Triple
  map   : BMap
  cands : List Triple

/-- The answer of a bounded search. -/
inductive Embed where
  | found
  | notFound
  | budget
deriving DecidableEq, Repr

def candidatesFor (g1 : Graph) (pat : Triple) : List Triple :=
  g1.filter (fun t => t.p == pat.p)

/-- Depth-first search over an explicit stack of frames. Each step is a
tail call, so the C stack does not grow with the number of patterns;
`fuel` counts steps. -/
def embedLoop (g1 : Graph) : Nat → List Frame → Embed
  | 0, _ => .budget
  | _ + 1, [] => .notFound
  | n + 1, fr :: stack =>
      match fr.cands with
      | [] => embedLoop g1 n stack
      | c :: cs =>
          let stack' := { fr with cands := cs } :: stack
          match matchTripleInj fr.map fr.head c with
          | none => embedLoop g1 n stack'
          | some m' =>
              match fr.rest with
              | [] => .found
              | p :: ps =>
                  embedLoop g1 n
                    ({ head := p, rest := ps, map := m', cands := candidatesFor g1 p } :: stack')

def bnodesOfTriple (t : Triple) : List BNodeId :=
  (match t.s with | .bnode b => [b] | .iri _ => []) ++
  (match t.o with | .bnode b => [b] | _ => [])

/-- Search order: next the first remaining pattern whose subject is a
blank node already placed, else the first that mentions one, else the
first. The order changes the work, not the answer. Tail recursive. -/
def orderLoop : Nat → List BNodeId → List Triple → List Triple → List Triple
  | 0, _, rem, acc => acc.reverse ++ rem
  | _ + 1, _, [], acc => acc.reverse
  | n + 1, seen, r0 :: rs, acc =>
      let rem := r0 :: rs
      let bySubj := rem.find? (fun t => match t.s with
        | .bnode b => seen.contains b
        | .iri _ => false)
      let pick := match bySubj with
        | some t => t
        | none => (rem.find? (fun t => (bnodesOfTriple t).any seen.contains)).getD r0
      orderLoop n (seen ++ bnodesOfTriple pick) (rem.erase pick) (pick :: acc)

def orderPatterns (pats : List Triple) : List Triple :=
  orderLoop pats.length [] pats []

/-- Steps of the bounded search. -/
def embedBudget : Nat := 200000

/-- The structural triples of G2. -/
def structuralOf (g2 : Graph) : List Triple := g2.filter structuralTriple

/-- Is there ONE one-to-one renaming of the blank nodes of the
structural triples of `g2` that makes them triples of `g1`? -/
def structuralEmbed (g1 g2 : Graph) : Embed :=
  match orderPatterns (structuralOf g2) with
  | [] => .found
  | p :: ps =>
      embedLoop g1 embedBudget
        [{ head := p, rest := ps, map := [], cands := candidatesFor g1 p }]

/-! ## The check -/

/-- A reason the pair is not balanced: the condition of Definition
(Balanced), numbered as in this module's header, and what violates it. -/
structure Defect where
  cond : String
  what : String
deriving BEq, Repr

def Defect.text (d : Defect) : String := s!"condition {d.cond}: {d.what}"

def useDefects (which : String) (g : Graph) : List Defect :=
  (missingDeclarations g).map fun u =>
    ⟨"2.1", s!"{which}: {showKey u.key} is used as {u.pos} and is not declared \
({String.intercalate " or " (u.decls.map (fun d => "rdf:type " ++ shortP d))})"⟩

def structuralDefects (g1 g2 : Graph) : List Defect :=
  match structuralEmbed g1 g2 with
  | .found => []
  | .budget =>
      [⟨"5.2-5.5", s!"not decided: the search for a blank-node renaming ran out of \
{embedBudget} steps"⟩]
  | .notFound =>
      let pats := structuralOf g2
      let alone := pats.find? (fun p => !(g1.any (fun t => (matchTripleInj [] p t).isSome)))
      let eg := match alone with
        | some p => s!"; no triple of G1 has the form {showTripleB p}"
        | none => "; each triple has a match alone, but no one-to-one renaming serves all"
      [⟨"5.2-5.5", s!"the {pats.length} triples of G2 that encode expressions and sequences \
are not a subgraph of G1 under a renaming of blank nodes{eg}"⟩]

/-- Every defect of the pair `(g1, g2)`. `dlViolations` are the species
violations of the pair (condition 1), as `SyntaxDL.speciesViolations`
reports them; the caller computes them because the species check reads
the documents before their imports are merged. The empty list means the
pair is balanced. -/
def balancedDefects (dlViolations : List String) (g1 g2 : Graph) : List Defect :=
  (dlViolations.map fun v => ⟨"1", s!"not OWL 2 DL: {v}"⟩) ++
  useDefects "G1" g1 ++ useDefects "G2" g2 ++
  ((missingLiterals g1 g2).map fun l =>
    ⟨"2.2", s!"the literal {showLiteral l} of G2 does not occur in G1"⟩) ++
  ((headerDefects g1 g2).map fun s => ⟨"3", s⟩) ++
  (g2.filterMap fun t => (forbiddenCond g1 g2 t).map fun c =>
    ⟨c, s!"G2 contains {showTripleB t}"⟩) ++
  ((declarationsNotInG1 g1 g2).map fun t =>
    ⟨"5.1", s!"the declaration {showTripleB t} of G2 is not in G1"⟩) ++
  structuralDefects g1 g2

/-- The species violations of a pair of graphs that carry no imports,
the way `l4owl-probe --species` computes them for a case with a
conclusion. -/
def pairSpeciesViolations (g1 g2 : Graph) : List String :=
  speciesViolations g1 g1 true g2 (g1 ++ g2)

def balancedDefectsOf (g1 g2 : Graph) : List Defect :=
  balancedDefects (pairSpeciesViolations g1 g2) g1 g2

def isBalanced (g1 g2 : Graph) : Bool := (balancedDefectsOf g1 g2).isEmpty

/-! ## The conclusion of an InconsistencyTest

An InconsistencyTest has no conclusion document. Theorem 7.1 is about
entailment, so the pair checked for an InconsistencyTest is (G1,
`inconsistencyGoal`): an anonymous ontology header and `owl:Thing
rdfs:subClassOf owl:Nothing`.

* Under the Direct Semantics, an ontology with no model entails every
  ontology, so F(G1) entails F(inconsistencyGoal) when F(G1) is
  inconsistent.
* Under the RDF-Based Semantics, no interpretation satisfies
  `inconsistencyGoal`: `rdfs:subClassOf` gives ICEXT(I(owl:Thing)) ⊆
  ICEXT(I(owl:Nothing)) (RDF Semantics, RDFS conditions), Table 5.2
  gives ICEXT(I(owl:Thing)) = IR and ICEXT(I(owl:Nothing)) = ∅, and IR is
  not empty. So a G1 that RDF-Based entails it has no RDF-Based model.

The goal has no literal, no non-built-in IRI, no annotation, no
expression and no sequence, and its header is one triple with a blank
node, so on the side of G2 every condition holds; the pair is balanced
exactly when G1 is an OWL 2 DL ontology that declares its entities
(conditions 1 and 2.1). -/
def inconsistencyGoal : Graph :=
  [ ⟨.bnode "balanced_goal_header",
     ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩,
     .iri ⟨"http://www.w3.org/2002/07/owl#Ontology", rfl⟩⟩
  , ⟨.iri ⟨"http://www.w3.org/2002/07/owl#Thing", rfl⟩,
     ⟨"http://www.w3.org/2000/01/rdf-schema#subClassOf", rfl⟩,
     .iri ⟨"http://www.w3.org/2002/07/owl#Nothing", rfl⟩⟩ ]

end L4Factoidal.OWL.RdfBased.Balanced
