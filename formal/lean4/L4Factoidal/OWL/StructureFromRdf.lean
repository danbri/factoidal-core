/-
L4Factoidal.OWL.StructureFromRdf — from an RDF graph back to the
structural specification.

Spec: OWL 2 Web Ontology Language Mapping to RDF Graphs (Second Edition),
https://www.w3.org/TR/owl2-mapping-to-rdf/ section 3 (Mapping from RDF
Graphs to the Structural Specification). `ontologyOfGraph g` reads the
axioms of the ontology whose RDF graph is `g` as `Struct.Axiom` values,
so that a check written over the structural specification (the OWL 2
profiles, `OWL.Profiles`) can be asked of an RDF/XML document.

## What it reads, and its answer for what it does not

* Declarations (section 3.1.2, Table 7): the IRIs typed `owl:Class`,
  `rdfs:Datatype`, `owl:ObjectProperty`, `owl:DatatypeProperty`,
  `owl:AnnotationProperty`. They decide whether a restriction, a
  property axiom or an assertion is an object or a data construct.
* Property expressions, data ranges and class expressions on blank
  nodes (Tables 11 to 15), by recursion with a fuel bound.
* Axioms (Tables 16 and 17): one axiom per main triple, and the nodes
  typed `owl:AllDisjointClasses`, `owl:AllDisjointProperties`,
  `owl:AllDifferent` and `owl:NegativePropertyAssertion`.
* `owl:intersectionOf` and `owl:unionOf` of a one-element sequence are
  read as the element (`oneOrMany`).
* Class expressions and data ranges nested more than 512 deep are not
  read (`maxNesting`): the recursion has a fixed bound on any input.
* Annotations are not read. The ontology header, annotation assertions,
  annotation property axioms and the `owl:Axiom` / `owl:Annotation`
  reification nodes give no axiom. A caller that needs annotations must
  not use this reader.

The answer is `Except`: a triple that is none of the above (a predicate
that is no declared property, a restriction whose shape is not in the
tables) is an error naming the triple, never a guess. The reader does
NOT decide that `g` is an OWL 2 DL ontology in RDF graph form; it does
not check the typing constraints or the global restrictions
(`OWL.SyntaxDL` does). For a graph that is one, every triple is read.

Tests: `ProfilesTests.lean` (functional-style documents read as parsed
and through their RDF graph), and the OWL probe compares, for every
W3C case with both an RDF/XML and a functional-style premise, the
profile verdicts of the two readings.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.Structure
import L4Factoidal.RDF.Graph
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.OWL.Struct.FromRdf

open L4Factoidal.RDF
open L4Factoidal.OWL.Struct

def nsOwl  : String := "http://www.w3.org/2002/07/owl#"
def nsRdf  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def nsRdfs : String := "http://www.w3.org/2000/01/rdf-schema#"
def nsXsd  : String := "http://www.w3.org/2001/XMLSchema#"

def rdfTypeS : String := nsRdf ++ "type"

/-- The graph by subject, and the declared entities by kind. -/
structure Ctx where
  bySubj    : Std.HashMap Subject (Array (WfIri × Term)) := {}
  classes   : Std.HashSet String := {}
  datatypes : Std.HashSet String := {}
  objProps  : Std.HashSet String := {}
  dataProps : Std.HashSet String := {}
  annProps  : Std.HashSet String := {}

/-- The types that make their subject an object property (Table 7 and
the property characteristics that only object properties have). -/
def objPropTypes : List String :=
  [nsOwl ++ "ObjectProperty", nsOwl ++ "InverseFunctionalProperty", nsOwl ++ "ReflexiveProperty",
   nsOwl ++ "IrreflexiveProperty", nsOwl ++ "SymmetricProperty", nsOwl ++ "AsymmetricProperty",
   nsOwl ++ "TransitiveProperty"]

/-- The annotation properties of the OWL 2 vocabulary (Structural
Specification section 5.5) and the ontology properties of the header. -/
def builtinAnnProps : List String :=
  [nsRdfs ++ "label", nsRdfs ++ "comment", nsRdfs ++ "seeAlso", nsRdfs ++ "isDefinedBy",
   nsOwl ++ "versionInfo", nsOwl ++ "deprecated", nsOwl ++ "priorVersion",
   nsOwl ++ "backwardCompatibleWith", nsOwl ++ "incompatibleWith", nsOwl ++ "imports",
   nsOwl ++ "versionIRI"]

def Ctx.ofGraph (g : Graph) : Ctx :=
  let c0 : Ctx :=
    { objProps := Std.HashSet.ofList [nsOwl ++ "topObjectProperty", nsOwl ++ "bottomObjectProperty"],
      dataProps := Std.HashSet.ofList [nsOwl ++ "topDataProperty", nsOwl ++ "bottomDataProperty"],
      annProps := Std.HashSet.ofList builtinAnnProps }
  g.foldl (fun c t =>
    let c := { c with bySubj := c.bySubj.insert t.s ((c.bySubj.getD t.s #[]).push (t.p, t.o)) }
    if t.p.val == rdfTypeS then
      match t.s, t.o with
      | .iri x, .iri ty =>
          let ty := ty.val
          if ty == nsOwl ++ "Class" then { c with classes := c.classes.insert x.val }
          else if ty == nsRdfs ++ "Datatype" then { c with datatypes := c.datatypes.insert x.val }
          else if objPropTypes.contains ty then { c with objProps := c.objProps.insert x.val }
          else if ty == nsOwl ++ "DatatypeProperty" then { c with dataProps := c.dataProps.insert x.val }
          else if ty == nsOwl ++ "AnnotationProperty" || ty == nsOwl ++ "OntologyProperty" then
            { c with annProps := c.annProps.insert x.val }
          else c
      | _, _ => c
    else c) c0

def Ctx.objs (c : Ctx) (s : Subject) (p : String) : List Term :=
  ((c.bySubj.getD s #[]).toList.filter (fun e => e.1.val == p)).map (·.2)

def Ctx.first (c : Ctx) (s : Subject) (p : String) : Option Term := (c.objs s p).head?

def Ctx.hasType (c : Ctx) (s : Subject) (ty : String) : Bool :=
  (c.objs s rdfTypeS).any fun
    | .iri i => i.val == ty
    | _ => false

/-- The elements of an RDF collection (Table 3); `none` when it is not
closed by `rdf:nil` within the fuel. -/
def Ctx.list (c : Ctx) : Nat → Term → Array Term → Option (List Term)
  | 0, _, _ => none
  | n + 1, t, acc =>
      match t with
      | .iri i => if i.val == nsRdf ++ "nil" then some acc.toList else none
      | .bnode b =>
          match c.first (.bnode b) (nsRdf ++ "first"), c.first (.bnode b) (nsRdf ++ "rest") with
          | some h, some r => c.list n r (acc.push h)
          | _, _ => none
      | _ => none

def Ctx.listOf (c : Ctx) (t : Term) : Option (List Term) := c.list (c.bySubj.size + 1) t #[]

def litOf : Term → Option WfLiteral
  | .literal l => some l
  | _ => none

def iriOf : Term → Option WfIri
  | .iri i => some i
  | _ => none

/-- A non-negative integer literal (the cardinality of a restriction). -/
def natOf : Term → Option Nat
  | .literal l => l.val.lexicalForm.toNat?
  | _ => none

def indOf : Term → Option Individual
  | .iri i => some (.named i)
  | .bnode b => some (.anon b)
  | _ => none

def indOfSubject : Subject → Individual
  | .iri i => .named i
  | .bnode b => .anon b

/-- Table 11: an object property, or the blank node `_:x owl:inverseOf
*:y`. -/
def Ctx.ope (c : Ctx) : Term → Option ObjPropExpr
  | .iri i => some (.prop i)
  | .bnode b =>
      match c.first (.bnode b) (nsOwl ++ "inverseOf") with
      | some (.iri p) => some (.inverse p)
      | _ => none
  | _ => none

/-- One element of `owl:withRestrictions`: a blank node with one facet
triple. -/
def Ctx.facet (c : Ctx) : Term → Option (WfIri × WfLiteral)
  | .bnode b =>
      match (c.bySubj.getD (.bnode b) #[]).toList with
      | [(f, .literal l)] => some (f, l)
      | _ => none
  | _ => none

/-- An intersection or union read from a sequence. Tables 12 and 13 map
`owl:intersectionOf` and `owl:unionOf` for a sequence of two or more
elements, and the structural specification has no intersection or union
of one operand. A sequence of ONE element is read as that element: the
only expression of the structural specification with the same extension.
(The W3C cases `WebOnt-disjointWith-003` to `-009` and `WebOnt-I5.26-*`
write `owl:intersectionOf ( A )` and are annotated as OWL 2 DL.) -/
def oneOrMany {α : Type} (mk : List α → α) : List α → α
  | [x] => x
  | xs  => mk xs

/-- The deepest nesting of class expressions and data ranges the reader
follows. An expression nested deeper is not read (the triple that holds
it is the reader's error), so the recursion below uses at most this many
stack frames whatever the graph. -/
def maxNesting : Nat := 512

/-- Table 12: data ranges. -/
def Ctx.dr (c : Ctx) : Nat → Term → Option DataRange
  | 0, _ => none
  | n + 1, t =>
      match t with
      | .iri i => some (.datatype i)
      | .bnode b =>
          let s : Subject := .bnode b
          match c.first s (nsOwl ++ "intersectionOf") with
          | some l => do return oneOrMany DataRange.intersection (← (← c.listOf l).mapM (c.dr n))
          | none =>
          match c.first s (nsOwl ++ "unionOf") with
          | some l => do return oneOrMany DataRange.union (← (← c.listOf l).mapM (c.dr n))
          | none =>
          match c.first s (nsOwl ++ "datatypeComplementOf") with
          | some d => do return .complement (← c.dr n d)
          | none =>
          match c.first s (nsOwl ++ "oneOf") with
          | some l => do return .oneOf (← (← c.listOf l).mapM litOf)
          | none =>
          match c.first s (nsOwl ++ "onDatatype"), c.first s (nsOwl ++ "withRestrictions") with
          | some (.iri dt), some l => do return .restriction dt (← (← c.listOf l).mapM c.facet)
          | _, _ => none
      | _ => none

def cardPreds : List String :=
  [nsOwl ++ "minCardinality", nsOwl ++ "maxCardinality", nsOwl ++ "cardinality",
   nsOwl ++ "minQualifiedCardinality", nsOwl ++ "maxQualifiedCardinality",
   nsOwl ++ "qualifiedCardinality"]

/-- Tables 13 to 15: the class expression the markers on `s` denote.
`s` is a blank node in a class-expression position, or an IRI that
carries a Boolean marker (Table 16: an equivalence with a named class). -/
def Ctx.ceMarkers (c : Ctx) : Nat → Subject → Option ClassExpr
  | 0, _ => none
  | n + 1, s =>
      let ce : Term → Option ClassExpr := fun
        | .iri i => some (.cls i)
        | .bnode b => c.ceMarkers n (.bnode b)
        | _ => none
      let fuel := maxNesting
      match c.first s (nsOwl ++ "intersectionOf") with
      | some l => do return oneOrMany ClassExpr.intersection (← (← c.listOf l).mapM ce)
      | none =>
      match c.first s (nsOwl ++ "unionOf") with
      | some l => do return oneOrMany ClassExpr.union (← (← c.listOf l).mapM ce)
      | none =>
      match c.first s (nsOwl ++ "complementOf") with
      | some x => do return .complement (← ce x)
      | none =>
      match c.first s (nsOwl ++ "oneOf") with
      | some l => do return .oneOf (← (← c.listOf l).mapM indOf)
      | none =>
      match c.first s (nsOwl ++ "onProperties") with
      | some l => do
          -- The n-ary data restrictions of Table 13.
          let dps ← (← c.listOf l).mapM iriOf
          match c.first s (nsOwl ++ "someValuesFrom"), c.first s (nsOwl ++ "allValuesFrom") with
          | some f, _ => return .dataSomeValuesFrom dps (← c.dr fuel f)
          | none, some f => return .dataAllValuesFrom dps (← c.dr fuel f)
          | none, none => none
      | none =>
      match c.first s (nsOwl ++ "onProperty") with
      | none => none
      | some pT =>
        let dataProp : Option WfIri :=
          match pT with
          | .iri p => if c.dataProps.contains p.val && !c.objProps.contains p.val then some p else none
          | _ => none
        let card (unq : Nat → ClassExpr) (qual : Nat → Term → Option ClassExpr) (pu pq : String) :
            Option (Option ClassExpr) :=
          match c.first s (nsOwl ++ pu), c.first s (nsOwl ++ pq) with
          | some k, _ => (natOf k).map (fun k => some (unq k))
          | none, some k =>
              match natOf k, c.first s (nsOwl ++ "onClass") <|> c.first s (nsOwl ++ "onDataRange") with
              | some k, some f => (qual k f).map some
              | _, _ => none
          | none, none => some none
        match dataProp with
        | some dp =>
            match c.first s (nsOwl ++ "someValuesFrom") with
            | some f => do return .dataSomeValuesFrom [dp] (← c.dr fuel f)
            | none =>
            match c.first s (nsOwl ++ "allValuesFrom") with
            | some f => do return .dataAllValuesFrom [dp] (← c.dr fuel f)
            | none =>
            match c.first s (nsOwl ++ "hasValue") with
            | some v => do return .dataHasValue dp (← litOf v)
            | none =>
            match card (.dataMinCard · dp none) (fun k f => (c.dr fuel f).map (fun x => ClassExpr.dataMinCard k dp (some x)))
                "minCardinality" "minQualifiedCardinality" with
            | none => none
            | some (some e) => some e
            | some none =>
            match card (.dataMaxCard · dp none) (fun k f => (c.dr fuel f).map (fun x => ClassExpr.dataMaxCard k dp (some x)))
                "maxCardinality" "maxQualifiedCardinality" with
            | none => none
            | some (some e) => some e
            | some none =>
            match card (.dataExactCard · dp none) (fun k f => (c.dr fuel f).map (fun x => ClassExpr.dataExactCard k dp (some x)))
                "cardinality" "qualifiedCardinality" with
            | some (some e) => some e
            | _ => none
        | none =>
            match c.ope pT with
            | none => none
            | some op =>
            match c.first s (nsOwl ++ "someValuesFrom") with
            | some f => do return .someValuesFrom op (← ce f)
            | none =>
            match c.first s (nsOwl ++ "allValuesFrom") with
            | some f => do return .allValuesFrom op (← ce f)
            | none =>
            match c.first s (nsOwl ++ "hasValue") with
            | some v => do return .hasValue op (← indOf v)
            | none =>
            match c.first s (nsOwl ++ "hasSelf") with
            | some _ => some (.hasSelf op)
            | none =>
            match card (.minCard · op none) (fun k f => (ce f).map (fun x => ClassExpr.minCard k op (some x)))
                "minCardinality" "minQualifiedCardinality" with
            | none => none
            | some (some e) => some e
            | some none =>
            match card (.maxCard · op none) (fun k f => (ce f).map (fun x => ClassExpr.maxCard k op (some x)))
                "maxCardinality" "maxQualifiedCardinality" with
            | none => none
            | some (some e) => some e
            | some none =>
            match card (.exactCard · op none) (fun k f => (ce f).map (fun x => ClassExpr.exactCard k op (some x)))
                "cardinality" "qualifiedCardinality" with
            | some (some e) => some e
            | _ => none

def Ctx.fuel (_c : Ctx) : Nat := maxNesting

/-- The class expression at a term: a class IRI, or the markers of a
blank node. -/
def Ctx.ce (c : Ctx) : Term → Option ClassExpr
  | .iri i => some (.cls i)
  | .bnode b => c.ceMarkers c.fuel (.bnode b)
  | _ => none

def Ctx.drOf (c : Ctx) (t : Term) : Option DataRange := c.dr c.fuel t

/-! ## Axioms -/

/-- The predicates of a property restriction (Tables 13 to 15). -/
def restrictionPreds : List String :=
  [nsOwl ++ "onProperty", nsOwl ++ "onProperties", nsOwl ++ "someValuesFrom",
   nsOwl ++ "allValuesFrom", nsOwl ++ "hasValue", nsOwl ++ "hasSelf", nsOwl ++ "onClass",
   nsOwl ++ "onDataRange"] ++ cardPreds

/-- Predicates that are part of an expression, a sequence or a
reification node, never a main triple. -/
def structuralPreds : List String :=
  [nsRdf ++ "first", nsRdf ++ "rest",
   nsOwl ++ "onProperty", nsOwl ++ "onProperties", nsOwl ++ "someValuesFrom",
   nsOwl ++ "allValuesFrom", nsOwl ++ "hasValue", nsOwl ++ "hasSelf", nsOwl ++ "onClass",
   nsOwl ++ "onDataRange", nsOwl ++ "onDatatype", nsOwl ++ "withRestrictions",
   nsOwl ++ "datatypeComplementOf", nsOwl ++ "members", nsOwl ++ "distinctMembers",
   nsOwl ++ "annotatedSource", nsOwl ++ "annotatedProperty", nsOwl ++ "annotatedTarget",
   nsOwl ++ "sourceIndividual", nsOwl ++ "assertionProperty", nsOwl ++ "targetIndividual",
   nsOwl ++ "targetValue"] ++ cardPreds

/-- Types that declare or mark their subject and assert no class
membership (Tables 5, 7, 8 and the OWL 1 forms of Table 5). -/
def markerTypes : List String :=
  [nsOwl ++ "Class", nsRdfs ++ "Class", nsOwl ++ "Restriction", nsRdfs ++ "Datatype",
   nsOwl ++ "DataRange", nsOwl ++ "ObjectProperty", nsOwl ++ "DatatypeProperty",
   nsOwl ++ "AnnotationProperty", nsOwl ++ "OntologyProperty", nsOwl ++ "NamedIndividual",
   nsOwl ++ "Ontology", nsRdf ++ "Property", nsRdf ++ "List", nsOwl ++ "Axiom",
   nsOwl ++ "Annotation", nsOwl ++ "DeprecatedClass", nsOwl ++ "DeprecatedProperty"]

/-- Nodes whose own triples are read as one unit (or not at all). -/
def unitTypes : List String :=
  [nsOwl ++ "Axiom", nsOwl ++ "Annotation", nsOwl ++ "Ontology",
   nsOwl ++ "NegativePropertyAssertion", nsOwl ++ "AllDisjointClasses",
   nsOwl ++ "AllDisjointProperties", nsOwl ++ "AllDifferent"]

def characteristicOf (ty : String) : Option ObjPropChar :=
  if ty == nsOwl ++ "FunctionalProperty" then some .functional
  else if ty == nsOwl ++ "InverseFunctionalProperty" then some .inverseFunctional
  else if ty == nsOwl ++ "ReflexiveProperty" then some .reflexive
  else if ty == nsOwl ++ "IrreflexiveProperty" then some .irreflexive
  else if ty == nsOwl ++ "SymmetricProperty" then some .symmetric
  else if ty == nsOwl ++ "AsymmetricProperty" then some .asymmetric
  else if ty == nsOwl ++ "TransitiveProperty" then some .transitive
  else none

def showTerm : Term → String
  | .iri i => "<" ++ i.val ++ ">"
  | .bnode b => "_:" ++ b
  | .literal l => "\"" ++ l.val.lexicalForm ++ "\""
  | .tripleTerm .. => "<<( ... )>>"

def showTripleShort (t : Triple) : String :=
  showTerm t.s.toTerm ++ " <" ++ t.p.val ++ "> " ++ showTerm t.o

def need {α : Type} (t : Triple) (what : String) : Option α → Except String α
  | some a => .ok a
  | none => .error s!"{what}: {showTripleShort t}"

def Ctx.isDataProp (c : Ctx) (s : Subject) : Bool :=
  match s with
  | .iri i => c.dataProps.contains i.val && !c.objProps.contains i.val
  | .bnode _ => false

def Ctx.isAnnProp (c : Ctx) (s : Subject) : Bool :=
  match s with
  | .iri i => c.annProps.contains i.val && !c.objProps.contains i.val && !c.dataProps.contains i.val
  | .bnode _ => false

def Ctx.isDatatype (c : Ctx) (s : Subject) : Bool :=
  match s with
  | .iri i => c.datatypes.contains i.val || i.val.startsWith nsXsd
  | .bnode b => c.hasType (.bnode b) (nsRdfs ++ "Datatype")

/-- The axioms of one `rdf:type` triple. -/
def Ctx.typeAxioms (c : Ctx) (t : Triple) : Except String (List Axiom) :=
  match t.o with
  | .iri ty =>
      let ty := ty.val
      if ty == nsOwl ++ "AllDisjointClasses" then do
        let l ← need t "AllDisjointClasses without owl:members" (c.first t.s (nsOwl ++ "members"))
        let ces ← need t "unread class expression in owl:members" ((c.listOf l).bind (·.mapM c.ce))
        pure [.disjointClasses [] ces]
      else if ty == nsOwl ++ "AllDisjointProperties" then do
        let l ← need t "AllDisjointProperties without owl:members" (c.first t.s (nsOwl ++ "members"))
        let ms ← need t "unread owl:members" (c.listOf l)
        if ms.any (fun m => match m with | .iri i => c.isDataProp (.iri i) | _ => false) then
          pure [.disjointDataProperties [] (← need t "unread data property" (ms.mapM iriOf))]
        else pure [.disjointObjectProperties [] (← need t "unread object property" (ms.mapM c.ope))]
      else if ty == nsOwl ++ "AllDifferent" then do
        let l ← need t "AllDifferent without members"
          (c.first t.s (nsOwl ++ "members") <|> c.first t.s (nsOwl ++ "distinctMembers"))
        pure [.differentIndividuals [] (← need t "unread individuals" ((c.listOf l).bind (·.mapM indOf)))]
      else if ty == nsOwl ++ "NegativePropertyAssertion" then do
        let src ← need t "NegativePropertyAssertion without owl:sourceIndividual"
          ((c.first t.s (nsOwl ++ "sourceIndividual")).bind indOf)
        let p ← need t "NegativePropertyAssertion without owl:assertionProperty"
          (c.first t.s (nsOwl ++ "assertionProperty"))
        match c.first t.s (nsOwl ++ "targetValue") with
        | some v =>
            pure [.negativeDataPropertyAssertion [] (← need t "unread data property" (iriOf p)) src
              (← need t "owl:targetValue is not a literal" (litOf v))]
        | none =>
            let tgt ← need t "NegativePropertyAssertion without a target"
              ((c.first t.s (nsOwl ++ "targetIndividual")).bind indOf)
            pure [.negativeObjectPropertyAssertion [] (← need t "unread object property" (c.ope p)) src tgt]
      else if markerTypes.contains ty then
        match t.s with
        | .iri x =>
            let decl (k : EntityKind) : Except String (List Axiom) := pure [.declaration [] k x]
            if ty == nsOwl ++ "Class" then decl .cls
            else if ty == nsRdfs ++ "Datatype" then decl .datatype
            else if ty == nsOwl ++ "ObjectProperty" then decl .objectProperty
            else if ty == nsOwl ++ "DatatypeProperty" then decl .dataProperty
            else if ty == nsOwl ++ "AnnotationProperty" then decl .annotationProperty
            else if ty == nsOwl ++ "NamedIndividual" then decl .namedIndividual
            else pure []
        | .bnode _ => pure []
      else
        match characteristicOf ty with
        | some ch =>
            if ch == .functional && c.isDataProp t.s then
              match t.s with
              | .iri dp => pure [.functionalDataProperty [] dp]
              | .bnode _ => .error s!"a blank node as a data property: {showTripleShort t}"
            else if ch == .functional && c.isAnnProp t.s then
              .error s!"a functional annotation property: {showTripleShort t}"
            else do
              pure [.objectPropertyCharacteristic [] ch
                (← need t "unread object property" (c.ope t.s.toTerm))]
        | none =>
            match t.o with
            | .iri cls => pure [.classAssertion [] (.cls cls) (indOfSubject t.s)]
            | _ => pure []
  | .bnode b => do
      let ce ← need t "unread class expression" (c.ceMarkers c.fuel (.bnode b))
      pure [.classAssertion [] ce (indOfSubject t.s)]
  | _ => .error s!"rdf:type with a literal object: {showTripleShort t}"

/-- The axioms of one triple (Tables 16 and 17). `units` holds the nodes
of `unitTypes`. -/
def Ctx.tripleAxioms (c : Ctx) (units : Std.HashSet Subject) (t : Triple) :
    Except String (List Axiom) :=
  let p := t.p.val
  let owl (n : String) : Bool := p == nsOwl ++ n
  let rdfs (n : String) : Bool := p == nsRdfs ++ n
  let ceS : Except String ClassExpr :=
    need t "unread class expression (subject)" (c.ce t.s.toTerm)
  let ceO : Except String ClassExpr := need t "unread class expression (object)" (c.ce t.o)
  let opeS : Except String ObjPropExpr := need t "unread object property (subject)" (c.ope t.s.toTerm)
  let opeO : Except String ObjPropExpr := need t "unread object property (object)" (c.ope t.o)
  let iriS : Except String WfIri := need t "a blank node where an IRI is required" (iriOf t.s.toTerm)
  let iriO : Except String WfIri := need t "an IRI is required as object" (iriOf t.o)
  if p == rdfTypeS then
    if units.contains t.s && !(match t.o with
        | .iri ty => [nsOwl ++ "NegativePropertyAssertion", nsOwl ++ "AllDisjointClasses",
            nsOwl ++ "AllDisjointProperties", nsOwl ++ "AllDifferent"].contains ty.val
        | _ => false) then pure []
    else c.typeAxioms t
  else if units.contains t.s then pure []
  else if restrictionPreds.contains p then
    -- Tables 13 to 15: a restriction is a blank node. On an IRI these
    -- triples are no expression of the structural specification, and
    -- passing over them would read an ontology that says less.
    match t.s with
    | .bnode _ => pure []
    | .iri _ => .error s!"a restriction on an IRI: {showTripleShort t}"
  else if structuralPreds.contains p || p.startsWith nsXsd then pure []
  else if owl "intersectionOf" || owl "unionOf" || owl "complementOf" || owl "oneOf" then
    match t.s with
    | .bnode _ => pure []
    | .iri x =>
        if c.isDatatype t.s then
          .error s!"a data range marker on a datatype IRI is not read: {showTripleShort t}"
        else do
          pure [.equivalentClasses [] [.cls x,
            ← need t "unread class expression" (c.ceMarkers c.fuel t.s)]]
  else if rdfs "subClassOf" then do pure [.subClassOf [] (← ceS) (← ceO)]
  else if owl "equivalentClass" then
    if c.isDatatype t.s then do
      pure [.datatypeDefinition [] (← iriS) (← need t "unread data range" (c.drOf t.o))]
    else do pure [.equivalentClasses [] [← ceS, ← ceO]]
  else if owl "disjointWith" then do pure [.disjointClasses [] [← ceS, ← ceO]]
  else if owl "disjointUnionOf" then do
    let ces ← need t "unread owl:disjointUnionOf" ((c.listOf t.o).bind (·.mapM c.ce))
    pure [.disjointUnion [] (← iriS) ces]
  else if rdfs "subPropertyOf" then
    if c.isDataProp t.s then do pure [.subDataPropertyOf [] (← iriS) (← iriO)]
    else if c.isAnnProp t.s then pure []
    else do pure [.subObjectPropertyOf [] (.single (← opeS)) (← opeO)]
  else if owl "propertyChainAxiom" then do
    let opes ← need t "unread owl:propertyChainAxiom" ((c.listOf t.o).bind (·.mapM c.ope))
    pure [.subObjectPropertyOf [] (.chain opes) (← opeS)]
  else if owl "equivalentProperty" then
    if c.isDataProp t.s then do pure [.equivalentDataProperties [] [← iriS, ← iriO]]
    else do pure [.equivalentObjectProperties [] [← opeS, ← opeO]]
  else if owl "propertyDisjointWith" then
    if c.isDataProp t.s then do pure [.disjointDataProperties [] [← iriS, ← iriO]]
    else do pure [.disjointObjectProperties [] [← opeS, ← opeO]]
  else if owl "inverseOf" then
    match t.s with
    | .bnode _ => pure []
    | .iri _ => do pure [.inverseObjectProperties [] (← opeS) (← opeO)]
  else if rdfs "domain" then
    if c.isDataProp t.s then do pure [.dataPropertyDomain [] (← iriS) (← ceO)]
    else if c.isAnnProp t.s then pure []
    else do pure [.objectPropertyDomain [] (← opeS) (← ceO)]
  else if rdfs "range" then
    if c.isDataProp t.s then do
      pure [.dataPropertyRange [] (← iriS) (← need t "unread data range" (c.drOf t.o))]
    else if c.isAnnProp t.s then pure []
    else do pure [.objectPropertyRange [] (← opeS) (← ceO)]
  else if owl "hasKey" then do
    let ps ← need t "unread owl:hasKey" (c.listOf t.o)
    let isData (x : Term) : Bool := match x with | .iri i => c.isDataProp (.iri i) | _ => false
    let dps ← need t "unread key data property" ((ps.filter isData).mapM iriOf)
    let opes ← need t "unread key object property" ((ps.filter (!isData ·)).mapM c.ope)
    pure [.hasKey [] (← ceS) opes dps]
  else if owl "sameAs" then do
    pure [.sameIndividual [] [indOfSubject t.s, ← need t "owl:sameAs with a literal" (indOf t.o)]]
  else if owl "differentFrom" then do
    pure [.differentIndividuals [] [indOfSubject t.s,
      ← need t "owl:differentFrom with a literal" (indOf t.o)]]
  else if c.objProps.contains p && !c.dataProps.contains p then do
    pure [.objectPropertyAssertion [] (.prop t.p) (indOfSubject t.s)
      (← need t "an object property assertion with a literal" (indOf t.o))]
  else if c.dataProps.contains p && !c.objProps.contains p then do
    pure [.dataPropertyAssertion [] t.p (indOfSubject t.s)
      (← need t "a data property assertion without a literal" (litOf t.o))]
  else if c.annProps.contains p then pure []
  else .error s!"a predicate that is no declared property: {showTripleShort t}"

/-- The nodes of `unitTypes`. -/
def Ctx.units (_c : Ctx) (g : Graph) : Std.HashSet Subject :=
  g.foldl (fun u t =>
    if t.p.val == rdfTypeS then
      match t.o with
      | .iri ty => if unitTypes.contains ty.val then u.insert t.s else u
      | _ => u
    else u) {}

def axiomsLoop (c : Ctx) (units : Std.HashSet Subject) :
    List Triple → Array Axiom → Except String (Array Axiom)
  | [], acc => .ok acc
  | t :: rest, acc =>
      match c.tripleAxioms units t with
      | .error e => .error e
      | .ok axs => axiomsLoop c units rest (acc ++ axs.toArray)

/-- **The axioms of the ontology whose RDF graph is `g`**, without
annotations and without the ontology header. An error names the first
triple the reader cannot place. -/
def ontologyOfGraph (g : Graph) : Except String Ontology :=
  let c := Ctx.ofGraph g
  match axiomsLoop c (c.units g) g #[] with
  | .error e => .error e
  | .ok axs => .ok { axioms := axs.toList }

end L4Factoidal.OWL.Struct.FromRdf
