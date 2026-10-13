/-
L4Factoidal.OWL.SyntaxDL — the OWL 2 DL species checker.

Port of `formal/fstar/OWL2.SyntaxDL.fst` (648 lines). Given the RDF
graphs of a W3C OWL 2 test case's documents, decide whether the case is
within OWL 2 DL (`test:DL`) or only OWL 2 Full (`test:FULL`). Purely
syntax-directed over parsed triples: no reasoning, no closure.

## The scope note is the F\* module's, and it is measured

Its header says so, and it is worth carrying across rather than
paraphrasing: the species facet in the W3C corpus mixes two judging
eras, the OWL 1 WebOnt classification and the OWL 2 WG's
re-annotation. The checks below are the subset of the Mapping to RDF
Graphs reverse mapping and the Structural Specification global
restrictions "that the corpus actually discriminates on, validated
check-by-check against all 489 species-annotated cases in
`third_party/testing/owl/all.rdf` (323 species-DL, 166
species-FULL-only)".

Two graph-identical premise pairs carry opposite species verdicts
(`WebOnt-I5.5-005` against `WebOnt-I5.5-006`), so the facet covers the
CONCLUSION document too — which is why `speciesIsDl` takes five
arguments rather than one graph.

## Nine per-triple checks, plus three global ones

| # | Check |
|---|---|
| 1 | reserved-vocabulary subject — redefining a built-in |
| 2 | untyped or undeclared assertion predicate |
| 3 | `rdf:type` object discipline |
| 4 | `owl:onProperty` filler must be a property |
| 5 | object property with a literal object |
| 6 | literal datatype usable in DL |
| 7 | data-property `rdfs:range` and `owl:onDatatype` fillers |
| 8 | `rdf:List` node discipline — one `rdf:first`, one `rdf:rest` |
| 9 | a property strictly inside its own `owl:propertyChainAxiom` |

and, over the whole graph: illegal punning, non-simple properties under
a cardinality restriction, and the document header discipline.

## Entity keys

`"I" ++ iri` for IRIs and `"B" ++ label` for blank nodes, so one string
list covers both node kinds. Carried over unchanged: the punning check
reads the `"I"` prefix to skip blank-node keys, because a blank node
typed both `owl:Class` and `owl:Restriction` is legitimate.
-/
import L4Factoidal.RDF.Graph
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.OWL.SyntaxDL

open L4Factoidal.RDF

/-! ## Vocabulary -/

def nsOwl  : String := "http://www.w3.org/2002/07/owl#"
def nsRdf  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def nsRdfs : String := "http://www.w3.org/2000/01/rdf-schema#"
def nsXsd  : String := "http://www.w3.org/2001/XMLSchema#"

def iriReserved (i : String) : Bool :=
  i.startsWith nsOwl || i.startsWith nsRdf || i.startsWith nsRdfs ||
  i.startsWith nsXsd

def rdfTypeP  : String := nsRdf ++ "type"
def rdfFirstP : String := nsRdf ++ "first"
def rdfRestP  : String := nsRdf ++ "rest"
def rdfNilI   : String := nsRdf ++ "nil"

def owlOntologyC    : String := nsOwl ++ "Ontology"
def owlClassC       : String := nsOwl ++ "Class"
def owlRestrictionC : String := nsOwl ++ "Restriction"
def owlObjPropC     : String := nsOwl ++ "ObjectProperty"
def owlDataPropC    : String := nsOwl ++ "DatatypeProperty"
def owlAnnPropC     : String := nsOwl ++ "AnnotationProperty"
def owlOntPropC     : String := nsOwl ++ "OntologyProperty"
def owlDataRangeC   : String := nsOwl ++ "DataRange"
def rdfsDatatypeC   : String := nsRdfs ++ "Datatype"

def owlImportsP        : String := nsOwl ++ "imports"
def owlPriorVersionP   : String := nsOwl ++ "priorVersion"
def owlOnPropertyP     : String := nsOwl ++ "onProperty"
def owlInverseOfP      : String := nsOwl ++ "inverseOf"
def owlIntersectionOfP : String := nsOwl ++ "intersectionOf"
def owlUnionOfP        : String := nsOwl ++ "unionOf"
def owlComplementOfP   : String := nsOwl ++ "complementOf"
def owlOneOfP          : String := nsOwl ++ "oneOf"
def owlEquivClassP     : String := nsOwl ++ "equivalentClass"
def owlOnDatatypeP     : String := nsOwl ++ "onDatatype"
def owlChainP          : String := nsOwl ++ "propertyChainAxiom"
def rdfsDomainP        : String := nsRdfs ++ "domain"
def rdfsRangeP         : String := nsRdfs ++ "range"

/-- Property-characteristic classes whose members are object properties
    in the OWL 2 RDF mapping. -/
def objCharacteristics : List String :=
  [nsOwl ++ "SymmetricProperty", nsOwl ++ "TransitiveProperty",
   nsOwl ++ "InverseFunctionalProperty", nsOwl ++ "AsymmetricProperty",
   nsOwl ++ "ReflexiveProperty", nsOwl ++ "IrreflexiveProperty"]

def owlFunctionalPropC : String := nsOwl ++ "FunctionalProperty"

/-- The OWL 2 datatype map (Structural Specification §4) plus
    `rdfs:Literal`, `rdf:XMLLiteral`, `rdf:PlainLiteral` and
    `rdf:langString`. -/
def builtinDatatypes : List String :=
  [nsRdfs ++ "Literal",
   nsRdf ++ "XMLLiteral", nsRdf ++ "PlainLiteral", nsRdf ++ "langString",
   nsOwl ++ "real", nsOwl ++ "rational",
   nsXsd ++ "string", nsXsd ++ "boolean", nsXsd ++ "decimal",
   nsXsd ++ "integer", nsXsd ++ "double", nsXsd ++ "float",
   nsXsd ++ "date", nsXsd ++ "time", nsXsd ++ "dateTime",
   nsXsd ++ "dateTimeStamp", nsXsd ++ "gYear", nsXsd ++ "gMonth",
   nsXsd ++ "gDay", nsXsd ++ "gYearMonth", nsXsd ++ "gMonthDay",
   nsXsd ++ "duration", nsXsd ++ "yearMonthDuration",
   nsXsd ++ "dayTimeDuration",
   nsXsd ++ "byte", nsXsd ++ "short", nsXsd ++ "int", nsXsd ++ "long",
   nsXsd ++ "unsignedByte", nsXsd ++ "unsignedShort",
   nsXsd ++ "unsignedInt", nsXsd ++ "unsignedLong",
   nsXsd ++ "negativeInteger", nsXsd ++ "nonNegativeInteger",
   nsXsd ++ "nonPositiveInteger", nsXsd ++ "positiveInteger",
   nsXsd ++ "hexBinary", nsXsd ++ "base64Binary", nsXsd ++ "anyURI",
   nsXsd ++ "language", nsXsd ++ "normalizedString", nsXsd ++ "token",
   nsXsd ++ "NMTOKEN", nsXsd ++ "Name", nsXsd ++ "NCName"]

/-- Built-in annotation properties (Structural Specification §5.5). -/
def builtinAnnProps : List String :=
  [nsRdfs ++ "label", nsRdfs ++ "comment", nsRdfs ++ "seeAlso",
   nsRdfs ++ "isDefinedBy",
   nsOwl ++ "versionInfo", nsOwl ++ "deprecated",
   nsOwl ++ "backwardCompatibleWith", nsOwl ++ "incompatibleWith",
   nsOwl ++ "priorVersion"]

/-- Built-in top and bottom properties (§5.3, §5.4). -/
def builtinProps : List String :=
  [nsOwl ++ "topObjectProperty", nsOwl ++ "bottomObjectProperty",
   nsOwl ++ "topDataProperty", nsOwl ++ "bottomDataProperty"]

/-- `rdf:type` objects that DECLARE an entity rather than assert class
    membership. -/
def declarationTypes : List String :=
  [nsOwl ++ "Class", nsOwl ++ "ObjectProperty", nsOwl ++ "DatatypeProperty",
   nsOwl ++ "AnnotationProperty", nsRdfs ++ "Datatype",
   nsOwl ++ "NamedIndividual", nsOwl ++ "Ontology",
   nsOwl ++ "DeprecatedClass", nsOwl ++ "DeprecatedProperty",
   nsOwl ++ "OntologyProperty", nsOwl ++ "DataRange"]

/-- Reserved IRIs a DL document may carry as an `rdf:type` object.

    The legacy typings `rdfs:Class`, `rdf:Property` and `rdf:List` are
    NOT here. OWL 2 Mapping to RDF Graphs §3.1.2, Table 5, removes each
    of them only when it is redundant (the node also carries the OWL 2
    typing, or the list structure); a copy that is not redundant is a
    triple no pattern of §3.2 consumes, and §3.2.5 ends "the graph G
    MUST be empty". Until 2026-10-10 the three were whitelisted
    unconditionally, which accepted `WebOnt-imports-004` (an imported
    `rdfs:Class` with no `owl:Class` declaration; annotated FULL). -/
def typeObjectWhitelist : List String :=
  declarationTypes ++ objCharacteristics ++ builtinDatatypes ++
  [owlFunctionalPropC, nsOwl ++ "Restriction",
   nsOwl ++ "Thing", nsOwl ++ "Nothing",
   nsOwl ++ "AllDifferent", nsOwl ++ "AllDisjointClasses",
   nsOwl ++ "AllDisjointProperties", nsOwl ++ "Axiom",
   nsOwl ++ "Annotation", nsOwl ++ "NegativePropertyAssertion"]

/-- Reserved IRIs acceptable as a triple SUBJECT: the built-in entities
    OWL 2 DL lets an ontology talk about. -/
def subjectWhitelist : List String :=
  [nsOwl ++ "Thing", nsOwl ++ "Nothing"] ++ builtinDatatypes ++ builtinProps

/-- `rdf:type` objects acceptable in a HEADER-LESS typing-only
    document. Narrower than `typeObjectWhitelist` on purpose: a
    header-less document typing entities with `owl:Nothing` or
    `rdfs:Class` is species-FULL throughout the corpus. -/
def headerlessTypeWhitelist : List String :=
  declarationTypes ++ [nsOwl ++ "Thing"]

def cardinalityPreds : List String :=
  [nsOwl ++ "cardinality", nsOwl ++ "minCardinality",
   nsOwl ++ "maxCardinality", nsOwl ++ "qualifiedCardinality",
   nsOwl ++ "minQualifiedCardinality", nsOwl ++ "maxQualifiedCardinality"]

/-! ## Graph accessors, over entity keys -/

def subjKey : Subject → String
  | .iri i => "I" ++ i.val
  | .bnode b => "B" ++ b

/-- `none` for a literal or a triple term: neither is a class or
    property key. -/
def termKeyDl : Term → Option String
  | .iri i => some ("I" ++ i.val)
  | .bnode b => some ("B" ++ b)
  | .literal _ => none
  | .tripleTerm _ _ _ => none

def termIsIri (o : Term) (i : String) : Bool :=
  match o with
  | .iri x => x.val == i
  | _ => false

def subjectsTyped (g : Graph) (ty : String) : List String :=
  g.filterMap (fun t =>
    if t.p.val == rdfTypeP && termIsIri t.o ty then some (subjKey t.s) else none)

def subjectsOfP (g : Graph) (p : String) : List String :=
  g.filterMap (fun t => if t.p.val == p then some (subjKey t.s) else none)

def objectKeysOf (g : Graph) (p : String) : List String :=
  g.filterMap (fun t => if t.p.val == p then termKeyDl t.o else none)

def hasTripleSp (g : Graph) (sk p : String) : Bool :=
  g.any (fun t => t.p.val == p && subjKey t.s == sk)

def findObjectSp (g : Graph) (sk p : String) : Option Term :=
  (g.find? (fun t => t.p.val == p && subjKey t.s == sk)).map (·.o)

def countSp (g : Graph) (sk p : String) : Nat :=
  (g.filter (fun t => t.p.val == p && subjKey t.s == sk)).length

def dedupStrs : List String → List String
  | [] => []
  | x :: rest => if rest.contains x then dedupStrs rest else x :: dedupStrs rest

/-- Members of an RDF collection, fuel-bounded by the graph size: each
    step consumes one `rdf:rest` link. -/
def collectionMembers (g : Graph) : Term → Nat → List Term
  | _, 0 => []
  | node, f + 1 =>
      match termKeyDl node with
      | none => []
      | some nk =>
          if termIsIri node rdfNilI then []
          else match findObjectSp g nk rdfFirstP with
               | none => []
               | some first =>
                   match findObjectSp g nk rdfRestP with
                   | none => [first]
                   | some rest => first :: collectionMembers g rest f

/-! ## The declaration index -/

structure DeclIndex where
  cls      : List String   -- typed owl:Class / owl:DeprecatedClass
  restr    : List String   -- typed owl:Restriction
  datatype : List String   -- typed rdfs:Datatype / owl:DataRange
  objProp  : List String
  dataProp : List String
  annProp  : List String   -- typed owl:AnnotationProperty / owl:OntologyProperty
  charProp : List String   -- an object characteristic or owl:FunctionalProperty
  hasDR    : List String   -- carries rdfs:domain or rdfs:range
  inv      : List String   -- takes part in owl:inverseOf, either side
  annSubj  : List String   -- typed owl:Ontology / owl:Axiom / owl:Annotation

def subjectsTypedAny (g : Graph) (tys : List String) : List String :=
  tys.flatMap (subjectsTyped g)

def buildDeclIndex (g : Graph) : DeclIndex :=
  { cls      := subjectsTypedAny g [owlClassC, nsOwl ++ "DeprecatedClass"]
  , restr    := subjectsTyped g owlRestrictionC
  , datatype := subjectsTypedAny g [rdfsDatatypeC, owlDataRangeC]
  , objProp  := subjectsTyped g owlObjPropC
  , dataProp := subjectsTyped g owlDataPropC
  , annProp  := subjectsTypedAny g [owlAnnPropC, owlOntPropC]
  , charProp := subjectsTypedAny g (owlFunctionalPropC :: objCharacteristics)
  , hasDR    := subjectsOfP g rdfsDomainP ++ subjectsOfP g rdfsRangeP
  , inv      := subjectsOfP g owlInverseOfP ++ objectKeysOf g owlInverseOfP
  , annSubj  := subjectsTypedAny g
                  [owlOntologyC, nsOwl ++ "Axiom", nsOwl ++ "Annotation"] }

/-- Acceptable wherever the RDF mapping demands a property: a declared
    object, data or annotation property; a built-in; a
    property-characteristic typing disambiguated by
    `rdfs:domain`/`rdfs:range`; or participation in `owl:inverseOf`. -/
def propEvidence (d : DeclIndex) (k : String) : Bool :=
  d.objProp.contains k || d.dataProp.contains k || d.annProp.contains k ||
  d.inv.contains k ||
  (d.charProp.contains k && (d.hasDR.contains k || d.inv.contains k))

/-- Defined as a class expression: a declared class, datatype or
    restriction, or a node carrying class-expression structure. -/
def classEvidence (g : Graph) (d : DeclIndex) (k : String) : Bool :=
  d.cls.contains k || d.datatype.contains k || d.restr.contains k ||
  hasTripleSp g k owlIntersectionOfP || hasTripleSp g k owlUnionOfP ||
  hasTripleSp g k owlComplementOfP || hasTripleSp g k owlOneOfP ||
  hasTripleSp g k owlOnPropertyP

/-- Usable in a DL data-range position: built-in, declared as a class
    (the legacy corpus shape), or carrying a datatype definition. -/
def datatypeEvidence (g : Graph) (d : DeclIndex) (dt : String) : Bool :=
  builtinDatatypes.contains dt ||
  d.cls.contains ("I" ++ dt) ||
  hasTripleSp g ("I" ++ dt) owlEquivClassP ||
  hasTripleSp g ("I" ++ dt) owlOnDatatypeP ||
  hasTripleSp g ("I" ++ dt) owlOneOfP

/-! ## Header discipline, per DOCUMENT and before imports merge -/

/-- Acceptable in a header-less document: only entity typings whose
    subject is a blank node or a non-reserved IRI, and whose object is
    a declaration class, `owl:Thing`, a blank node, or a non-reserved
    IRI. -/
def typingOnlyTriple (t : Triple) : Bool :=
  t.p.val == rdfTypeP &&
  (match t.s with
   | .bnode _ => true
   | .iri i => !(iriReserved i.val)) &&
  (match t.o with
   | .bnode _ => true
   | .literal _ => false
   | .tripleTerm _ _ _ => false
   | .iri o => headerlessTypeWhitelist.contains o.val || !(iriReserved o.val))

/-- No `owl:Ontology` header (unless the document is typing-only), or
    more than one header that is not the object of `owl:imports` or
    `owl:priorVersion` — no unique root ontology node. -/
def docHeaderViolations (g : Graph) : List String :=
  let headers := dedupStrs (subjectsTyped g owlOntologyC)
  let nonroot := objectKeysOf g owlImportsP ++ objectKeysOf g owlPriorVersionP
  let roots := headers.filter (fun h => !(nonroot.contains h))
  match headers with
  | [] => if g.all typingOnlyTriple then [] else ["no-ontology-header"]
  | _ => if roots.length > 1 then ["multiple-root-ontology-headers"] else []

/-! ## Body checks, on the merged graph -/

/-- Every element but the last: the strict interior for the role-chain
    regularity check. -/
def dropLastTerm : List Term → List Term
  | [] => []
  | [_] => []
  | x :: rest => x :: dropLastTerm rest

/-- Does `sk` carry the typing `sk rdf:type ty`? -/
def hasTypeSp (g : Graph) (sk ty : String) : Bool :=
  g.any (fun t => t.p.val == rdfTypeP && subjKey t.s == sk && termIsIri t.o ty)

def rdfsClassC    : String := nsRdfs ++ "Class"
def rdfPropertyC  : String := nsRdf ++ "Property"
def rdfListC      : String := nsRdf ++ "List"

/-- The property typings whose presence makes `x rdf:type rdf:Property`
    redundant (Table 5, rows 7 to 13). -/
def propertyTypings : List String :=
  [owlObjPropC, owlFunctionalPropC, nsOwl ++ "InverseFunctionalProperty",
   nsOwl ++ "TransitiveProperty", owlDataPropC, owlAnnPropC, owlOntPropC]

/-- OWL 2 Mapping to RDF Graphs §3.1.2, Table 5: "Triples to be Removed
    for Backwards Compatibility with OWL 1 DL". A triple of the right-
    hand column is removed from G when the pattern of the left-hand
    column is present:

    * `x rdf:type rdfs:Class` when `x` is also typed `owl:Class`,
      `rdfs:Datatype`, `owl:DataRange` or `owl:Restriction`;
    * `x rdf:type owl:Class` when `x` is also typed `owl:Restriction`;
    * `x rdf:type rdf:Property` when `x` is also typed with an OWL
      property class;
    * `x rdf:type rdf:List` when `x` has `rdf:first` and `rdf:rest`.

    (The first row, `x rdf:type owl:Ontology`, is the header discipline
    and is handled by `docHeaderViolations`.) -/
def table5Redundant (g : Graph) (t : Triple) : Bool :=
  if t.p.val != rdfTypeP then false
  else match t.o with
  | .iri o =>
      let sk := subjKey t.s
      if o.val == rdfsClassC then
        hasTypeSp g sk owlClassC || hasTypeSp g sk rdfsDatatypeC ||
        hasTypeSp g sk owlDataRangeC || hasTypeSp g sk owlRestrictionC
      else if o.val == owlClassC then hasTypeSp g sk owlRestrictionC
      else if o.val == rdfPropertyC then propertyTypings.any (hasTypeSp g sk)
      else if o.val == rdfListC then
        hasTripleSp g sk rdfFirstP && hasTripleSp g sk rdfRestP
      else false
  | _ => false

/-- G after Table 5. -/
def dropTable5Redundant (g : Graph) : Graph :=
  g.filter (fun t => !table5Redundant g t)

/-- The keys of the ROOT ontology headers of a graph: typed
    `owl:Ontology` and not the object of an `owl:imports` or
    `owl:priorVersion` link from a different node. -/
def rootHeaderKeys (g : Graph) : List String :=
  let headers := dedupStrs (subjectsTyped g owlOntologyC)
  -- A header that imports itself is still a root: only a link from a
  -- DIFFERENT header makes a node a non-root.
  let nonroot := g.filterMap (fun t =>
    if (t.p.val == owlImportsP || t.p.val == owlPriorVersionP) &&
       termKeyDl t.o != some (subjKey t.s) then termKeyDl t.o else none)
  headers.filter (fun h => !(nonroot.contains h))

/-- The keys of the ROOT ontology headers of one document: typed
    `owl:Ontology` and not the object of an `owl:imports` or
    `owl:priorVersion` link from another node (the nested `<owl:Ontology rdf:about=...>` objects
    of OWL 1 style documents are not roots), plus the `owl:versionIRI`
    objects of those roots (`rootHeaderKeys` gives the roots alone). -/
def rootOntologyKeys (g : Graph) : List String :=
  let roots := rootHeaderKeys g
  roots ++ (g.filterMap (fun t =>
    if t.p.val == nsOwl ++ "versionIRI" && roots.contains (subjKey t.s)
    then termKeyDl t.o else none))

/-- Canonical parsing step CP 2.1 (Structural Specification §3.6): "Retrieve
    the ontology document DI from I". All steps of the process MUST be
    completed, so an `owl:imports` target that cannot be retrieved makes
    the document unparseable and therefore not an OWL 2 DL ontology
    document (OWL 2 Conformance §2.1.1).

    `available` holds the IRIs the caller can retrieve; `none` means the
    caller cannot say, and no retrieval failure is asserted. A document
    is also retrievable at its own ontology IRI and version IRI
    (Structural Specification §3.2: "If O contains an ontology IRI OI but
    no version IRI, then the ontology document of O SHOULD be accessible
    via the IRI OI"), so `own` holds the root header keys of the
    documents the check reads. -/
def unresolvedImportViolations (available : Option (List String)) (own : List String)
    (g : Graph) : List String :=
  match available with
  | none => []
  | some av =>
      (dedupStrs (objectKeysOf g owlImportsP)).filterMap (fun k =>
        if k.startsWith "I" && !(av.contains (k.drop 1).toString) && !(own.contains k)
        then some ("unresolved-import: " ++ (k.drop 1).toString) else none)

def tripleViolations (g : Graph) (d : DeclIndex) (t : Triple) : List String :=
  let v1 :=                                   -- reserved-vocabulary subject
    match t.s with
    | .iri i =>
        if iriReserved i.val && !(subjectWhitelist.contains i.val)
        then ["reserved-vocabulary-subject: " ++ i.val] else []
    | _ => []
  let v2 :=                                   -- undeclared assertion predicate
    if iriReserved t.p.val then []
    else if builtinAnnProps.contains t.p.val || builtinProps.contains t.p.val then []
    else if propEvidence d ("I" ++ t.p.val) then []
    else if d.annSubj.contains (subjKey t.s) then []
    else ["untyped-predicate: " ++ t.p.val]
  let v3 :=                                   -- rdf:type object discipline
    if t.p.val != rdfTypeP then []
    else match t.o with
    | .literal _ => ["literal-as-type-object"]
    | .tripleTerm _ _ _ => ["triple-term-as-type-object"]
    | .bnode b =>
        if classEvidence g d ("B" ++ b) then [] else ["undefined-bnode-class-expression"]
    | .iri o =>
        if iriReserved o.val then
          (if typeObjectWhitelist.contains o.val then []
           else ["reserved-vocabulary-as-class: " ++ o.val])
        else if classEvidence g d ("I" ++ o.val) then []
        else ["untyped-class: " ++ o.val]
  let v4 :=                                   -- owl:onProperty filler
    if t.p.val != owlOnPropertyP then []
    else match t.o with
    | .literal _ => ["literal-as-onProperty"]
    | .tripleTerm _ _ _ => ["triple-term-as-onProperty"]
    | .bnode b => if d.inv.contains ("B" ++ b) then [] else ["undefined-bnode-onProperty"]
    | .iri o =>
        if builtinProps.contains o.val then []
        else if iriReserved o.val then ["reserved-vocabulary-as-onProperty: " ++ o.val]
        else if propEvidence d ("I" ++ o.val) then []
        else ["untyped-onProperty: " ++ o.val]
  let v5 :=                                   -- object property, literal object
    match t.o with
    | .literal _ =>
        if d.objProp.contains ("I" ++ t.p.val)
        then ["object-property-with-literal-object: " ++ t.p.val] else []
    | _ => []
  let v6 :=                                   -- literal datatype usable in DL
    match t.o with
    | .literal l =>
        let dt := l.val.datatype.val
        if datatypeEvidence g d dt then []
        else if iriReserved dt then ["reserved-vocabulary-as-datatype: " ++ dt]
        else ["undefined-datatype: " ++ dt]
    | _ => []
  let v7 :=                                   -- range / onDatatype fillers
    if (t.p.val == rdfsRangeP && d.dataProp.contains (subjKey t.s))
       || t.p.val == owlOnDatatypeP then
      match t.o with
      | .iri o =>
          if datatypeEvidence g d o.val then []
          else if iriReserved o.val then ["reserved-vocabulary-as-datatype: " ++ o.val]
          else ["undefined-datatype: " ++ o.val]
      | _ => []
    else []
  let v8 :=                                   -- rdf:List node discipline
    if t.p.val == rdfFirstP || t.p.val == rdfRestP then
      let sk := subjKey t.s
      if countSp g sk rdfFirstP == 1 && countSp g sk rdfRestP == 1 then []
      else ["malformed-rdf-list-node"]
    else []
  let v9 :=                                   -- property inside its own chain
    if t.p.val == owlChainP then
      let members := collectionMembers g t.o g.length
      let interior := match members with
                      | [] => []
                      | _ :: tl => dropLastTerm tl
      let self := subjKey t.s
      if interior.any (fun m => termKeyDl m == some self)
      then ["property-inside-own-chain: " ++ self] else []
    else []
  v1 ++ v2 ++ v3 ++ v4 ++ v5 ++ v6 ++ v7 ++ v8 ++ v9

/-- Illegal punning. Blank-node keys are skipped — a blank node typed
    both `owl:Class` and `owl:Restriction` is legitimate — which is what
    the `"I"` prefix test is for. -/
def punningViolationsKeys (d : DeclIndex) : List String → List String
  | [] => []
  | k :: rest =>
      let here :=
        if !(k.startsWith "I") then []
        else
          (if d.cls.contains k && d.datatype.contains k
           then ["illegal-punning-class-datatype: " ++ k] else []) ++
          (if d.objProp.contains k && d.dataProp.contains k
           then ["illegal-punning-object-data-property: " ++ k] else []) ++
          (if d.objProp.contains k && d.annProp.contains k
           then ["illegal-punning-object-annotation-property: " ++ k] else []) ++
          (if d.dataProp.contains k && d.annProp.contains k
           then ["illegal-punning-data-annotation-property: " ++ k] else [])
      here ++ punningViolationsKeys d rest

def punningViolations (d : DeclIndex) : List String :=
  punningViolationsKeys d (dedupStrs (d.cls ++ d.objProp ++ d.dataProp))

/-! ## Structural Specification §11: the global restrictions

Read off the RDF graph, over the axioms of the whole closure (the caller
passes the merged graph). The clauses, in the order of §11.2:

* the restriction on `owl:topDataProperty`;
* the restrictions on datatypes: a built-in datatype is not redefined, a
  datatype has at most one definition, and definitions are acyclic;
* the restriction on simple roles (§11.1 defines "simple");
* the restriction on the property hierarchy (regularity);
* the restrictions on anonymous individuals.

Object property expressions are `Ope`: a property key and whether it is
inverted. A node `_:x owl:inverseOf P` denotes `ObjectInverseOf( P )`
(Mapping to RDF Graphs Table 1); `P owl:inverseOf Q` with an IRI subject is
the axiom `InverseObjectProperties( P Q )`. -/

structure Ope where
  key : String
  inv : Bool
deriving DecidableEq

def Ope.flip (o : Ope) : Ope := { o with inv := !o.inv }

def owlSameAsP          : String := nsOwl ++ "sameAs"
def owlDifferentFromP   : String := nsOwl ++ "differentFrom"
def owlHasSelfP         : String := nsOwl ++ "hasSelf"
def owlHasValueP        : String := nsOwl ++ "hasValue"
def owlEquivPropP       : String := nsOwl ++ "equivalentProperty"
def owlPropDisjointP    : String := nsOwl ++ "propertyDisjointWith"
def owlMembersP         : String := nsOwl ++ "members"
def owlDistinctMembersP : String := nsOwl ++ "distinctMembers"
def owlSourceIndP       : String := nsOwl ++ "sourceIndividual"
def owlTargetIndP       : String := nsOwl ++ "targetIndividual"
def owlOnDatatypeP'     : String := nsOwl ++ "onDatatype"
def owlDtComplementP    : String := nsOwl ++ "datatypeComplementOf"
def rdfsSubPropertyOfP  : String := nsRdfs ++ "subPropertyOf"
def owlTopObjectP       : String := nsOwl ++ "topObjectProperty"
def owlBottomObjectP    : String := nsOwl ++ "bottomObjectProperty"
def owlTopDataP         : String := nsOwl ++ "topDataProperty"
def owlAssertionPropP   : String := nsOwl ++ "assertionProperty"

/-- The expression a term denotes in object-property position. -/
def opeOfTerm (g : Graph) (t : Term) : Option Ope :=
  match t with
  | .iri i => some ⟨"I" ++ i.val, false⟩
  | .bnode b =>
      match findObjectSp g ("B" ++ b) owlInverseOfP with
      | some (.iri p) => some ⟨"I" ++ p.val, true⟩
      | _ => none
  | _ => none

def subjTermDl : Subject → Term
  | .iri i => .iri i
  | .bnode b => .bnode b

def opeOfSubject (g : Graph) (s : Subject) : Option Ope := opeOfTerm g (subjTermDl s)

/-- The relation → of §11.1: sub-property, equivalence, inverse and
symmetry axioms, closed under taking inverses ("if OPE1 → OPE2 holds,
then INV(OPE1) → INV(OPE2) holds as well"). -/
def hierarchyEdges (g : Graph) : List (Ope × Ope) :=
  let direct : List (Ope × Ope) := g.flatMap (fun t =>
    if t.p.val == rdfsSubPropertyOfP then
      match opeOfSubject g t.s, opeOfTerm g t.o with
      | some a, some b => [(a, b)]
      | _, _ => []
    else if t.p.val == owlEquivPropP then
      match opeOfSubject g t.s, opeOfTerm g t.o with
      | some a, some b => [(a, b), (b, a)]
      | _, _ => []
    else if t.p.val == owlInverseOfP then
      match t.s, t.o with
      | .iri p, .iri q =>
          [(⟨"I" ++ p.val, false⟩, ⟨"I" ++ q.val, true⟩),
           (⟨"I" ++ q.val, true⟩, ⟨"I" ++ p.val, false⟩)]
      | _, _ => []
    else [])
  let symmetric : List (Ope × Ope) :=
    (subjectsTyped g (nsOwl ++ "SymmetricProperty")).filterMap (fun k =>
      if k.startsWith "I" then some (⟨k, false⟩, ⟨k, true⟩) else none)
  let base := direct ++ symmetric
  base ++ base.map (fun (a, b) => (a.flip, b.flip))

/-- The forward closure of `start` under `edges`: every `OPE'` with
`start →* OPE'`. -/
def forwardClosure (edges : List (Ope × Ope)) (start : List Ope) : Nat → List Ope
  | 0 => start
  | f + 1 =>
      let added := (edges.filterMap (fun (a, b) =>
        if start.contains a && !(start.contains b) then some b else none)).eraseDups
      if added.isEmpty then start else forwardClosure edges (start ++ added) f

/-- Composite object property expressions (§11.1): the top and bottom
object properties, the targets of a chain axiom with n > 1, and the
transitive ones; each together with its inverse. -/
def compositeOpes (g : Graph) : List Ope :=
  let top : List Ope := [⟨"I" ++ owlTopObjectP, false⟩, ⟨"I" ++ owlBottomObjectP, false⟩]
  let trans : List Ope := (subjectsTyped g (nsOwl ++ "TransitiveProperty")).filterMap (fun k =>
    if k.startsWith "I" then some ⟨k, false⟩ else none)
  let chains : List Ope := g.filterMap (fun t =>
    if t.p.val == owlChainP && (collectionMembers g t.o g.length).length ≥ 2
    then opeOfSubject g t.s else none)
  let seeds := top ++ trans ++ chains
  seeds ++ seeds.map Ope.flip

/-- The keys of the non-simple object properties: those reachable by →*
from a composite expression. -/
def nonsimpleKeys (g : Graph) : List String :=
  let edges := hierarchyEdges g
  let ns := forwardClosure edges (compositeOpes g) (edges.length + 1)
  (ns.map (·.key)).eraseDups

/-- Restriction on simple roles (§11.2): cardinality restrictions,
`ObjectHasSelf`, and the functional, inverse-functional, irreflexive,
asymmetric and disjointness axioms contain only simple object
properties. -/
def simpleRoleViolations (g : Graph) (ns : List String) : List String :=
  let keyOfTerm := fun (t : Term) => (opeOfTerm g t).map (·.key)
  let restrictions := (dedupStrs (subjectsOfP g owlOnPropertyP)).flatMap (fun r =>
    if cardinalityPreds.any (fun cp => hasTripleSp g r cp) || hasTripleSp g r owlHasSelfP then
      match (findObjectSp g r owlOnPropertyP).bind keyOfTerm with
      | some k => if ns.contains k then ["non-simple-property-in-restriction: " ++ k] else []
      | none => []
    else [])
  let characteristics :=
    [nsOwl ++ "FunctionalProperty", nsOwl ++ "InverseFunctionalProperty",
     nsOwl ++ "IrreflexiveProperty", nsOwl ++ "AsymmetricProperty"].flatMap (fun ty =>
      (subjectsTyped g ty).flatMap (fun k =>
        if ns.contains k then ["non-simple-property-in-characteristic: " ++ k] else []))
  let disjoint := g.flatMap (fun t =>
    if t.p.val == owlPropDisjointP then
      [opeOfSubject g t.s, opeOfTerm g t.o].flatMap (fun o? =>
        match o? with
        | some o => if ns.contains o.key then ["non-simple-property-in-disjointness: " ++ o.key] else []
        | none => [])
    else [])
  let allDisjoint := (subjectsTyped g (nsOwl ++ "AllDisjointProperties")).flatMap (fun n =>
    match findObjectSp g n owlMembersP with
    | some l =>
        (collectionMembers g l g.length).flatMap (fun m =>
          match keyOfTerm m with
          | some k => if ns.contains k then ["non-simple-property-in-disjointness: " ++ k] else []
          | none => [])
    | none => [])
  restrictions ++ characteristics ++ disjoint ++ allDisjoint

/-- The strict-order constraints `A < B` a chain axiom imposes (§11.2,
Restriction on the Property Hierarchy). The five forms: the target is the
top object property; `R o R ⊑ R`; every operand below the target; the
first operand is the target and the rest are below it; the last operand
is the target and the rest are below it. The order is on properties, with
a property and its inverse identified. -/
def chainConstraints (sup : Ope) (opes : List Ope) : List (String × String) :=
  if sup.key == "I" ++ owlTopObjectP then []
  else if opes == [sup, sup] then []
  else if opes.head? == some sup then (opes.drop 1).map (fun o => (o.key, sup.key))
  else if opes.getLast? == some sup then (opes.dropLast).map (fun o => (o.key, sup.key))
  else opes.map (fun o => (o.key, sup.key))

def chainAxioms (g : Graph) : List (Ope × List Ope) :=
  g.filterMap (fun t =>
    if t.p.val == owlChainP then
      match opeOfSubject g t.s with
      | none => none
      | some sup =>
          let ms := collectionMembers g t.o g.length
          let opes := ms.filterMap (opeOfTerm g)
          if ms.length ≥ 2 && opes.length == ms.length then some (sup, opes) else none
    else none)

/-- Transitive closure of a list of pairs, fuel-bounded by the number of
rounds. -/
def closePairs (ps : List (String × String)) : Nat → List (String × String)
  | 0 => ps
  | f + 1 =>
      let new := ps.flatMap (fun (a, b) =>
        ps.filterMap (fun (c, d) => if b == c then some (a, d) else none))
      let ps' := (ps ++ new).eraseDups
      if ps'.length == ps.length then ps else closePairs ps' f

/-- A strict partial order satisfying the constraints exists exactly when
the transitive closure of the required pairs is irreflexive and contains no
pair `A < B` with `B →* A`. -/
def regularityViolations (g : Graph) : List String :=
  let required := ((chainAxioms g).flatMap (fun (sup, opes) => chainConstraints sup opes)).eraseDups
  if required.isEmpty then [] else
  let edges := hierarchyEdges g
  let closed := closePairs required (required.length + 1)
  closed.flatMap (fun (a, b) =>
    if a == b then ["irregular-property-hierarchy: " ++ a ++ " < " ++ a]
    else if (forwardClosure edges [⟨b, false⟩] (edges.length + 1)).any (fun o => o.key == a)
    then ["irregular-property-hierarchy: " ++ a ++ " < " ++ b] else [])

/-- Restriction on owl:topDataProperty: it occurs only as the super
property of a `SubDataPropertyOf` axiom. -/
def topDataViolations (g : Graph) : List String :=
  g.filterMap (fun t =>
    let isTopS := match t.s with | .iri i => i.val == owlTopDataP | _ => false
    let isTopO := match t.o with | .iri i => i.val == owlTopDataP | _ => false
    let mentions := isTopS || t.p.val == owlTopDataP || isTopO
    let allowed := t.p.val == rdfsSubPropertyOfP && isTopO && !isTopS
    if mentions && !allowed then some "top-data-property-misused" else none)

/-- The datatypes occurring in a data range term. -/
def drDatatypes (g : Graph) : Nat → Term → List String
  | 0, _ => []
  | f + 1, .iri i => [i.val]
  | f + 1, .bnode b =>
      let k := "B" ++ b
      (match findObjectSp g k owlOnDatatypeP' with
       | some t => drDatatypes g f t | none => []) ++
      (match findObjectSp g k owlDtComplementP with
       | some t => drDatatypes g f t | none => []) ++
      [owlIntersectionOfP, owlUnionOfP].flatMap (fun p =>
        match findObjectSp g k p with
        | some l => (collectionMembers g l g.length).flatMap (drDatatypes g f)
        | none => [])
  | _, _ => []

/-- Restrictions on datatypes (§11.2): no built-in datatype is redefined,
a datatype has at most one `DatatypeDefinition`, and the definitions are
acyclic. -/
def datatypeDefinitionViolations (g : Graph) (d : DeclIndex) : List String :=
  -- the object of a datatype definition is a data range
  let isDataRange := fun (t : Term) =>
    match t with
    | .bnode b => d.datatype.contains ("B" ++ b)
    | .iri i => d.datatype.contains ("I" ++ i.val) || builtinDatatypes.contains i.val
    | _ => false
  let defs : List (String × Term) := g.filterMap (fun t =>
    if t.p.val == owlEquivClassP then
      match t.s with
      | .iri i =>
          if d.datatype.contains ("I" ++ i.val) ||
             (builtinDatatypes.contains i.val && isDataRange t.o)
          then some (i.val, t.o) else none
      | _ => none
    else none)
  let names := defs.map (·.1)
  let uses : List (String × List String) :=
    defs.map (fun (n, o) => (n, drDatatypes g (g.length + 2) o))
  let reach := fun (n : String) =>
    let step := uses.filterMap (fun (m, us) => if m == n then some us else none) |>.flatten
    -- forward closure over the definition graph
    let rec go (seen : List String) (fuel : Nat) : List String :=
      match fuel with
      | 0 => seen
      | f + 1 =>
          let more := (seen.flatMap (fun x =>
            uses.filterMap (fun (m, us) => if m == x then some us else none) |>.flatten)).eraseDups
            |>.filter (fun x => !(seen.contains x))
          if more.isEmpty then seen else go (seen ++ more) f
    go step.eraseDups (uses.length + 2)
  (names.eraseDups.flatMap (fun n =>
    (if builtinDatatypes.contains n then ["builtin-datatype-redefined: " ++ n] else []) ++
    (if (names.filter (· == n)).length > 1 then ["datatype-defined-twice: " ++ n] else []) ++
    (if (reach n).contains n then ["cyclic-datatype-definition: " ++ n] else [])))

def isBnodeTerm : Term → Bool
  | .bnode _ => true
  | _ => false

def isBnodeSubject : Subject → Bool
  | .bnode _ => true
  | _ => false

/-- Components of an undirected graph by incremental merging; `none` when an
edge joins two vertices already connected (a cycle, a parallel edge or a
loop). -/
def addEdge (comps : List (List String)) (a b : String) : Option (List (List String)) :=
  let ca := comps.find? (fun c => c.contains a)
  let cb := comps.find? (fun c => c.contains b)
  match ca, cb with
  | some x, some y =>
      if x == y then none
      else some ((x ++ y) :: comps.filter (fun c => c != x && c != y))
  | some x, none => some ((b :: x) :: comps.filter (fun c => c != x))
  | none, some y => some ((a :: y) :: comps.filter (fun c => c != y))
  | none, none => some ([a, b] :: comps)

def componentsOf (edges : List (String × String)) : Option (List (List String)) :=
  edges.foldlM (fun comps (a, b) => addEdge comps a b) []

/-! ### `componentsOf` without the scans for new vertices (https://github.com/danbri/factoidal/issues/812)

`addEdge` looks for the component of each end with `List.find?` over all
components, so n vertex-disjoint edges (a pair of blank nodes each) cost n²
(8,000 pairs 1.09 s, 32,000 pairs 14.79 s, issue 812). `componentsOfLoop`
carries the set of vertices already in a component: when neither end of an
edge is in it, no component contains them (`find?_none_of_not_covered`), so
the edge is a new two-vertex component without a scan (`addEdgeSeen_eq`).
`addEdge_covered` states which vertices a step covers; `componentsOf_eq_fast`
(`csimp`) runs the loop wherever `componentsOf` is called, with the same
components in the same order, so the forest verdict and the number of trees
without a leaf are those of `componentsOf`. An edge that touches a vertex
already in a component still scans; a chain of n blank nodes is quadratic. -/

/-- A vertex is in some component. -/
def Covered (comps : List (List String)) (v : String) : Prop := ∃ c ∈ comps, v ∈ c

theorem find?_none_of_not_covered {comps : List (List String)} {a : String}
    (h : ¬ Covered comps a) : comps.find? (fun c => c.contains a) = none := by
  rw [List.find?_eq_none]
  intro c hc hca
  exact h ⟨c, hc, by simpa using hca⟩

theorem covered_of_find? {comps : List (List String)} {a : String} {x : List String}
    (h : comps.find? (fun c => c.contains a) = some x) : x ∈ comps ∧ a ∈ x := by
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  exact ⟨h2, by simpa using h1⟩

/-- After an edge, the covered vertices are the old ones and the edge's ends. -/
theorem addEdge_covered {comps comps' : List (List String)} {a b : String}
    (h : addEdge comps a b = some comps') (v : String) :
    Covered comps' v ↔ (Covered comps v ∨ v = a ∨ v = b) := by
  unfold addEdge at h
  simp only at h
  split at h
  · rename_i x y hx hy
    obtain ⟨hxm, hax⟩ := covered_of_find? hx
    obtain ⟨hym, hby⟩ := covered_of_find? hy
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      constructor
      · rintro ⟨c, hc, hvc⟩
        simp only [List.mem_cons, List.mem_filter] at hc
        rcases hc with rfl | ⟨hc, _⟩
        · rcases List.mem_append.mp hvc with h1 | h1
          · exact Or.inl ⟨_, hxm, h1⟩
          · exact Or.inl ⟨_, hym, h1⟩
        · exact Or.inl ⟨c, hc, hvc⟩
      · rintro (⟨c, hc, hvc⟩ | rfl | rfl)
        · by_cases hcx : c = x
          · subst hcx; exact ⟨_, List.mem_cons_self .., List.mem_append_left _ hvc⟩
          · by_cases hcy : c = y
            · subst hcy; exact ⟨_, List.mem_cons_self .., List.mem_append_right _ hvc⟩
            · exact ⟨c, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, by simp [hcx, hcy]⟩), hvc⟩
        · exact ⟨_, List.mem_cons_self .., List.mem_append_left _ hax⟩
        · exact ⟨_, List.mem_cons_self .., List.mem_append_right _ hby⟩
  · rename_i x hx hy
    obtain ⟨hxm, hax⟩ := covered_of_find? hx
    simp only [Option.some.injEq] at h
    subst h
    constructor
    · rintro ⟨c, hc, hvc⟩
      simp only [List.mem_cons, List.mem_filter] at hc
      rcases hc with rfl | ⟨hc, _⟩
      · rcases List.mem_cons.mp hvc with h1 | h1
        · exact Or.inr (Or.inr h1)
        · exact Or.inl ⟨_, hxm, h1⟩
      · exact Or.inl ⟨c, hc, hvc⟩
    · rintro (⟨c, hc, hvc⟩ | rfl | rfl)
      · by_cases hcx : c = x
        · subst hcx; exact ⟨_, List.mem_cons_self .., List.mem_cons_of_mem _ hvc⟩
        · exact ⟨c, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, by simp [hcx]⟩), hvc⟩
      · exact ⟨_, List.mem_cons_self .., List.mem_cons_of_mem _ hax⟩
      · exact ⟨_, List.mem_cons_self .., List.mem_cons_self ..⟩
  · rename_i y hx hy
    obtain ⟨hym, hby⟩ := covered_of_find? hy
    simp only [Option.some.injEq] at h
    subst h
    constructor
    · rintro ⟨c, hc, hvc⟩
      simp only [List.mem_cons, List.mem_filter] at hc
      rcases hc with rfl | ⟨hc, _⟩
      · rcases List.mem_cons.mp hvc with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inl ⟨_, hym, h1⟩
      · exact Or.inl ⟨c, hc, hvc⟩
    · rintro (⟨c, hc, hvc⟩ | rfl | rfl)
      · by_cases hcy : c = y
        · subst hcy; exact ⟨_, List.mem_cons_self .., List.mem_cons_of_mem _ hvc⟩
        · exact ⟨c, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hc, by simp [hcy]⟩), hvc⟩
      · exact ⟨_, List.mem_cons_self .., List.mem_cons_self ..⟩
      · exact ⟨_, List.mem_cons_self .., List.mem_cons_of_mem _ hby⟩
  · rename_i hx hy
    simp only [Option.some.injEq] at h
    subst h
    constructor
    · rintro ⟨c, hc, hvc⟩
      rcases List.mem_cons.mp hc with rfl | hc
      · simp at hvc; rcases hvc with h1 | h1 <;> simp [h1]
      · exact Or.inl ⟨c, hc, hvc⟩
    · rintro (⟨c, hc, hvc⟩ | rfl | rfl)
      · exact ⟨c, List.mem_cons_of_mem _ hc, hvc⟩
      · exact ⟨_, List.mem_cons_self .., by simp⟩
      · exact ⟨_, List.mem_cons_self .., by simp⟩


/-- `addEdge` with the set of covered vertices beside it: when neither end is
covered, the two `find?` scans are skipped. -/
def addEdgeSeen (comps : List (List String)) (seen : Std.HashSet String) (a b : String) :
    Option (List (List String)) :=
  if !seen.contains a && !seen.contains b then some ([a, b] :: comps) else addEdge comps a b

/-- `componentsOf` as a loop that carries the covered vertices. -/
def componentsOfLoop : List (String × String) → List (List String) → Std.HashSet String →
    Option (List (List String))
  | [], comps, _ => some comps
  | (a, b) :: rest, comps, seen =>
    match addEdgeSeen comps seen a b with
    | none => none
    | some comps' => componentsOfLoop rest comps' ((seen.insert a).insert b)

theorem addEdgeSeen_eq {comps : List (List String)} {seen : Std.HashSet String} {a b : String}
    (hs : ∀ v, seen.contains v = true ↔ Covered comps v) :
    addEdgeSeen comps seen a b = addEdge comps a b := by
  unfold addEdgeSeen
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have ha : ¬ Covered comps a := fun hc => by have := (hs a).mpr hc; simp_all
    have hb : ¬ Covered comps b := fun hc => by have := (hs b).mpr hc; simp_all
    unfold addEdge
    simp only [find?_none_of_not_covered ha, find?_none_of_not_covered hb]
  · rfl

theorem componentsOfLoop_eq : ∀ (edges : List (String × String)) (comps : List (List String))
    (seen : Std.HashSet String), (∀ v, seen.contains v = true ↔ Covered comps v) →
    componentsOfLoop edges comps seen = edges.foldlM (fun comps (a, b) => addEdge comps a b) comps
  | [], comps, seen, _ => by simp [componentsOfLoop]
  | (a, b) :: rest, comps, seen, hs => by
    simp only [componentsOfLoop, List.foldlM_cons, addEdgeSeen_eq hs]
    cases h : addEdge comps a b with
    | none => rfl
    | some comps' =>
      simp only
      apply componentsOfLoop_eq
      intro v
      rw [addEdge_covered h v, Std.HashSet.contains_insert, Std.HashSet.contains_insert]
      simp only [Bool.or_eq_true, beq_iff_eq, hs v]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inr (Or.inr h1.symm)
        · exact Or.inr (Or.inl h1.symm)
        · exact Or.inl h1
      · rintro (h1 | h1 | h1)
        · exact Or.inr (Or.inr h1)
        · exact Or.inr (Or.inl h1.symm)
        · exact Or.inl h1.symm

def componentsOfFast (edges : List (String × String)) : Option (List (List String)) :=
  componentsOfLoop edges [] ∅

@[csimp] theorem componentsOf_eq_fast : @componentsOf = @componentsOfFast := by
  funext edges
  simp only [componentsOf, componentsOfFast]
  exact (componentsOfLoop_eq edges [] ∅ (fun v => by simp [Covered])).symm

#print axioms componentsOf_eq_fast

/-! The loop answers as the fold on disjoint pairs, a chain, a merge of two
components, a cycle (`none`), a parallel edge (`none`) and a loop on a new
vertex (the fold makes it a component, as before). -/
private def foldComps (es : List (String × String)) : Option (List (List String)) :=
  es.foldlM (fun comps (a, b) => addEdge comps a b) []
#guard componentsOf [("a", "b"), ("c", "d"), ("e", "f")] == foldComps [("a", "b"), ("c", "d"), ("e", "f")]
#guard componentsOf [("a", "b"), ("c", "d"), ("e", "f")] == some [["e", "f"], ["c", "d"], ["a", "b"]]
#guard componentsOf [("a", "b"), ("b", "c"), ("c", "d")] == foldComps [("a", "b"), ("b", "c"), ("c", "d")]
#guard componentsOf [("a", "b"), ("c", "d"), ("b", "c")] == foldComps [("a", "b"), ("c", "d"), ("b", "c")]
#guard componentsOf [("a", "b"), ("b", "c"), ("c", "a")] == none
#guard foldComps [("a", "b"), ("b", "c"), ("c", "a")] == none
#guard componentsOf [("a", "b"), ("a", "b")] == none
#guard componentsOf [("a", "a")] == foldComps [("a", "a")]
#guard componentsOf [("a", "a")] == some [["a", "a"]]

/-- Restrictions on the usage of anonymous individuals (§11.2). -/
def anonymousIndividualViolations (g : Graph) (d : DeclIndex) : List String :=
  let sameDiff := g.filterMap (fun t =>
    if (t.p.val == owlSameAsP || t.p.val == owlDifferentFromP) &&
       (isBnodeSubject t.s || isBnodeTerm t.o)
    then some "anonymous-individual-in-sameAs-or-differentFrom" else none)
  let allDifferent := (subjectsTyped g (nsOwl ++ "AllDifferent")).flatMap (fun n =>
    [owlMembersP, owlDistinctMembersP].flatMap (fun p =>
      match findObjectSp g n p with
      | some l =>
          if (collectionMembers g l g.length).any isBnodeTerm
          then ["anonymous-individual-in-AllDifferent"] else []
      | none => []))
  let negative := (subjectsTyped g (nsOwl ++ "NegativePropertyAssertion")).flatMap (fun n =>
    [owlSourceIndP, owlTargetIndP].flatMap (fun p =>
      match findObjectSp g n p with
      | some (.bnode _) => ["anonymous-individual-in-negative-assertion"]
      | _ => []))
  let oneOf := g.filterMap (fun t =>
    if t.p.val == owlOneOfP && !(d.datatype.contains (subjKey t.s)) &&
       (collectionMembers g t.o g.length).any isBnodeTerm
    then some "anonymous-individual-in-ObjectOneOf" else none)
  let hasValue := g.filterMap (fun t =>
    if t.p.val == owlHasValueP && isBnodeTerm t.o
    then some "anonymous-individual-in-ObjectHasValue" else none)
  -- the anonymous individual graph F
  let assertion := fun (t : Triple) => d.objProp.contains ("I" ++ t.p.val)
  let edges : List (String × String) := g.filterMap (fun t =>
    match t.s, t.o with
    | .bnode a, .bnode b => if assertion t then some ("B" ++ a, "B" ++ b) else none
    | _, _ => none)
  let namedLinks := fun (k : String) => (g.filter (fun t =>
    assertion t &&
    ((subjKey t.s == k && (match t.o with | .iri _ => true | _ => false)) ||
     (termKeyDl t.o == some k && (match t.s with | .iri _ => true | _ => false))))).length
  let verts : List String := dedupStrs (g.flatMap (fun t =>
    if assertion t then
      (match t.s with | .bnode b => ["B" ++ b] | _ => []) ++
      (match t.o with | .bnode b => ["B" ++ b] | _ => [])
    else []))
  let forest :=
    match componentsOf edges with
    | none => ["anonymous-individuals-not-a-forest"]
    | some comps =>
        let isolated := verts.filter (fun v => !(comps.any (fun c => c.contains v)))
        (comps ++ isolated.map (fun v => [v])).filterMap (fun c =>
          if c.any (fun v => namedLinks v ≤ 1) then none
          else some "anonymous-individual-tree-without-leaf")
  sameDiff ++ allDifferent ++ negative ++ oneOf ++ hasValue ++ forest

/-- All of §11.2 over one graph. -/
def globalRestrictionViolations (g : Graph) (d : DeclIndex) : List String :=
  let ns := nonsimpleKeys g
  topDataViolations g ++ datatypeDefinitionViolations g d ++
  simpleRoleViolations g ns ++ regularityViolations g ++
  anonymousIndividualViolations g d

def graphBodyViolations (g0 : Graph) : List String :=
  let g := dropTable5Redundant g0
  let d := buildDeclIndex g
  let perTriple := g.flatMap (tripleViolations g d)
  perTriple ++ punningViolations d ++ globalRestrictionViolations g d

/-! ## The species verdict -/

/-- `pDoc` is the premise document alone, `pMerged` the premise with its
    `owl:imports` closure, `cDoc` the conclusion document alone, and
    `uMerged` premise plus conclusion plus imports.

    The conclusion's entity typing is checked against the UNION — the
    corpus convention lets a conclusion use premise vocabulary — while
    its header discipline is its own document's. -/
def speciesViolations (pDoc pMerged : Graph) (hasConclusion : Bool)
    (cDoc uMerged : Graph) (available : Option (List String) := none) : List String :=
  (docHeaderViolations pDoc).map (fun v => "premise: " ++ v) ++
  (graphBodyViolations pMerged).map (fun v => "premise: " ++ v) ++
  (unresolvedImportViolations available (rootOntologyKeys pDoc) pMerged).map
    (fun v => "premise: " ++ v) ++
  (if hasConclusion then
     (docHeaderViolations cDoc).map (fun v => "conclusion: " ++ v) ++
     (graphBodyViolations uMerged).map (fun v => "conclusion: " ++ v) ++
     (unresolvedImportViolations available
        (rootOntologyKeys pDoc ++ rootOntologyKeys cDoc) uMerged).map
       (fun v => "conclusion: " ++ v)
   else [])

def speciesIsDl (pDoc pMerged : Graph) (hasConclusion : Bool)
    (cDoc uMerged : Graph) (available : Option (List String) := none) : Bool :=
  (speciesViolations pDoc pMerged hasConclusion cDoc uMerged available).isEmpty

/-- For graphs obtained from OWL 2 Functional Syntax
    (`test:normativeSyntax FUNCTIONAL`): a successful parse proves the
    `Ontology(…)` header syntactically, so only the body checks apply. -/
def speciesViolationsFunctional (p : Graph) (hasConclusion : Bool) (u : Graph) :
    List String :=
  (graphBodyViolations p).map (fun v => "premise: " ++ v) ++
  (if hasConclusion then (graphBodyViolations u).map (fun v => "conclusion: " ++ v)
   else [])

def speciesIsDlFunctional (p : Graph) (hasConclusion : Bool) (u : Graph) : Bool :=
  (speciesViolationsFunctional p hasConclusion u).isEmpty


/-! ## Build-time checks

Every check above gets a MINIMAL PAIR: a graph that passes and the same
graph perturbed so that exactly one check fires. A checker whose tests
only ever showed violations would not distinguish "rejects everything"
from "rejects the right thing". -/

section Checks

/-- A `WfIri` from a fixture string. Every string the checks below use
    is a real IRI; the fallback exists only so the helper is total. -/
private def i (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩
private def ti (s : String) : Term := .iri (i s)
private def si (s : String) : Subject := .iri (i s)
private def tr (s p o : String) : Triple := ⟨si s, i p, ti o⟩
private def trb (s p : String) (b : String) : Triple := ⟨si s, i p, .bnode b⟩
/-- A plain typed literal. An ill-formed combination becomes a blank
    node rather than needing a proof; no fixture below produces one. -/
private def litT (lex dt : String) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := i dt,
                       langTag := none, direction := none }
  if h : literalWf l then .literal ⟨l, h⟩ else .bnode "ill-formed-literal"

private def trlit (s p lex dt : String) : Triple := ⟨si s, i p, litT lex dt⟩

private def ex (s : String) : String := "http://example.org/" ++ s

/-! ### A well-formed minimal ontology passes every check -/

private def okGraph : Graph :=
  [ tr (ex "o") rdfTypeP owlOntologyC
  , tr (ex "C") rdfTypeP owlClassC
  , tr (ex "p") rdfTypeP owlObjPropC
  , tr (ex "a") rdfTypeP (ex "C")
  , tr (ex "a") (ex "p") (ex "b")
  , tr (ex "b") rdfTypeP owlClassC ]

#guard docHeaderViolations okGraph == []
#guard graphBodyViolations okGraph == []
#guard speciesIsDl okGraph okGraph false [] []

/-! ### 1. A reserved-vocabulary subject is a redefinition -/

#guard graphBodyViolations (okGraph ++ [tr (nsOwl ++ "Thing") rdfTypeP owlClassC]) == []
#guard (graphBodyViolations (okGraph ++ [tr (nsOwl ++ "Class") rdfTypeP owlClassC])).any
         (fun v => v.startsWith "reserved-vocabulary-subject")

/-! ### 2. An undeclared assertion predicate -/

#guard (graphBodyViolations (okGraph ++ [tr (ex "a") (ex "q") (ex "b")])).any
         (fun v => v.startsWith "untyped-predicate")
#guard (graphBodyViolations (okGraph ++ [tr (ex "a") (ex "q") (ex "b"),
          tr (ex "q") rdfTypeP owlObjPropC])).all
         (fun v => !v.startsWith "untyped-predicate")

/-! A built-in annotation property needs no declaration. -/

#guard graphBodyViolations (okGraph ++
  [trlit (ex "a") (nsRdfs ++ "label") "hello" (nsXsd ++ "string")]) == []

/-! ### 3. `rdf:type` object discipline -/

#guard (graphBodyViolations (okGraph ++ [tr (ex "a") rdfTypeP (ex "Undeclared")])).any
         (fun v => v.startsWith "untyped-class")
#guard (graphBodyViolations (okGraph ++
          [trlit (ex "a") rdfTypeP "x" (nsXsd ++ "string")])).contains
         "literal-as-type-object"
#guard (graphBodyViolations (okGraph ++ [trb (ex "a") rdfTypeP "b1"])).contains
         "undefined-bnode-class-expression"

/-! ### 4. `owl:onProperty` must name a property -/

#guard (graphBodyViolations (okGraph ++
          [trb (ex "R") rdfTypeP "r1", tr (ex "R") owlOnPropertyP (ex "notAProp")])).any
         (fun v => v.startsWith "untyped-onProperty")

/-! ### 5. An object property with a literal object -/

#guard (graphBodyViolations (okGraph ++
          [trlit (ex "a") (ex "p") "x" (nsXsd ++ "string")])).any
         (fun v => v.startsWith "object-property-with-literal-object")

/-! ### 6. A literal's datatype must be usable in DL -/

#guard graphBodyViolations (okGraph ++
  [trlit (ex "a") (nsRdfs ++ "comment") "x" (nsXsd ++ "string")]) == []
#guard (graphBodyViolations (okGraph ++
          [trlit (ex "a") (nsRdfs ++ "comment") "x" (ex "myType")])).any
         (fun v => v.startsWith "undefined-datatype")

/-! ### 8. An `rdf:List` node carries exactly one `rdf:first` and one
    `rdf:rest` -/

private def listOk : Graph :=
  okGraph ++ [trb (ex "L") rdfFirstP "n1", trb (ex "L") rdfRestP "n2"]
private def listBad : Graph :=
  listOk ++ [trb (ex "L") rdfFirstP "n3"]

#guard (graphBodyViolations listOk).all (fun v => v != "malformed-rdf-list-node")
#guard (graphBodyViolations listBad).contains "malformed-rdf-list-node"

/-! ### Punning: the same IRI as object AND data property -/

#guard (graphBodyViolations (okGraph ++ [tr (ex "p") rdfTypeP owlDataPropC])).any
         (fun v => v.startsWith "illegal-punning-object-data-property")

/-! A BLANK NODE typed both `owl:Class` and `owl:Restriction` is
    legitimate, which is what the `"I"` key prefix protects. -/

#guard (graphBodyViolations (okGraph ++
          [⟨.bnode "x", i rdfTypeP, ti owlClassC⟩,
           ⟨.bnode "x", i rdfTypeP, ti owlRestrictionC⟩])).all
         (fun v => !v.startsWith "illegal-punning")

/-! ### The header discipline -/

#guard docHeaderViolations [tr (ex "a") (ex "p") (ex "b")] == ["no-ontology-header"]
#guard docHeaderViolations [tr (ex "a") rdfTypeP (ex "C")] == []
#guard docHeaderViolations
  [tr (ex "o1") rdfTypeP owlOntologyC, tr (ex "o2") rdfTypeP owlOntologyC]
  == ["multiple-root-ontology-headers"]

/-! An imported second header is not a second ROOT. -/

#guard docHeaderViolations
  [tr (ex "o1") rdfTypeP owlOntologyC, tr (ex "o2") rdfTypeP owlOntologyC,
   tr (ex "o1") owlImportsP (ex "o2")] == []

/-! ### Table 5: legacy typings are dropped only when redundant

OWL 2 Mapping to RDF Graphs §3.1.2, Table 5. `okGraph` declares `C` as
`owl:Class` and `p` as `owl:ObjectProperty`. -/

-- redundant: C is also an owl:Class
#guard graphBodyViolations (okGraph ++ [tr (ex "C") rdfTypeP rdfsClassC]) == []
-- not redundant: D carries only the legacy typing
#guard (graphBodyViolations (okGraph ++ [tr (ex "D") rdfTypeP rdfsClassC])).any
         (fun v => v.startsWith "reserved-vocabulary-as-class")
-- redundant: p is also an owl:ObjectProperty
#guard graphBodyViolations (okGraph ++ [tr (ex "p") rdfTypeP rdfPropertyC]) == []
-- not redundant: q carries only the legacy typing
#guard (graphBodyViolations (okGraph ++ [tr (ex "q") rdfTypeP rdfPropertyC])).any
         (fun v => v.startsWith "reserved-vocabulary-as-class")
-- redundant: the list node has rdf:first and rdf:rest
#guard graphBodyViolations (okGraph ++
         [tr (ex "L") rdfTypeP rdfListC, trb (ex "L") rdfFirstP "n1",
          tr (ex "L") rdfRestP rdfNilI]) == []
-- not redundant: no list structure on the node
#guard (graphBodyViolations (okGraph ++ [tr (ex "L2") rdfTypeP rdfListC])).any
         (fun v => v.startsWith "reserved-vocabulary-as-class")
-- A restriction typed owl:Class is one class expression: the owl:Class
-- copy is redundant.
#guard (graphBodyViolations (okGraph ++
          [⟨.bnode "r", i rdfTypeP, ti owlClassC⟩,
           ⟨.bnode "r", i rdfTypeP, ti owlRestrictionC⟩,
           ⟨.bnode "r", i owlOnPropertyP, ti (ex "p")⟩])).all
         (fun v => !v.startsWith "reserved-vocabulary-as-class")

/-! ### CP 2.1: every `owl:imports` target must be retrievable -/

private def importing : Graph := okGraph ++ [tr (ex "o") owlImportsP (ex "i")]

#guard unresolvedImportViolations none [] importing == []
#guard unresolvedImportViolations (some []) [] importing
         == ["unresolved-import: http://example.org/i"]
#guard unresolvedImportViolations (some [ex "i"]) [] importing == []
#guard speciesIsDl importing importing false [] [] none
#guard !speciesIsDl importing importing false [] [] (some [])
#guard speciesIsDl importing importing false [] [] (some [ex "i"])

-- A document is retrievable at its own ontology IRI (§3.2), so an
-- import that points back at the root header resolves (cyclic imports
-- are allowed) ...
private def selfImport : Graph := okGraph ++ [tr (ex "o") owlImportsP (ex "o")]
#guard speciesIsDl selfImport selfImport false [] [] (some [])
-- ... but a nested, typed import object is not a root header and does
-- not make its own IRI retrievable.
private def nestedImport : Graph :=
  okGraph ++ [tr (ex "o") owlImportsP (ex "n"), tr (ex "n") rdfTypeP owlOntologyC]
#guard rootOntologyKeys nestedImport == ["Ihttp://example.org/o"]
#guard !speciesIsDl nestedImport nestedImport false [] [] (some [])
#guard speciesIsDl nestedImport nestedImport false [] [] (some [ex "n"])

/-! ### Structural Specification §11: the global restrictions

Each clause has a pair: a graph that breaks it and the nearest graph that
does not. `okGraph` declares the object property `p`. -/

private def exI (s : String) : Term := ti (ex s)

/-- Declared object properties. -/
private def objProps (ns : List String) : Graph :=
  ns.map (fun n => tr (ex n) rdfTypeP owlObjPropC)

/-- `T(SEQ y1 ... yn)`: the list cells carry the label prefix `pfx`. -/
private def listTriples (pfx : String) : List Term → Term × Graph
  | [] => (ti rdfNilI, [])
  | x :: xs =>
      let (rest, g) := listTriples pfx xs
      let lbl := pfx ++ toString xs.length
      (.bnode lbl, ⟨.bnode lbl, i rdfFirstP, x⟩ :: ⟨.bnode lbl, i rdfRestP, rest⟩ :: g)

/-- `sup owl:propertyChainAxiom (x1 ... xn)`. -/
private def chainAx (sup : String) (xs : List Term) : Graph :=
  let (h, g) := listTriples ("ch" ++ sup) xs
  ⟨si (ex sup), i owlChainP, h⟩ :: g

/-- A restriction `r` on `prop` with one extra triple. -/
private def restr (r prop pred : String) (o : Term) : Graph :=
  [⟨.bnode r, i rdfTypeP, ti owlRestrictionC⟩, ⟨.bnode r, i owlOnPropertyP, exI prop⟩,
   ⟨.bnode r, i pred, o⟩]

private def two : Term := litT "2" (nsXsd ++ "nonNegativeInteger")

private def hasV (g : Graph) (prefix_ : String) : Bool :=
  (graphBodyViolations g).any (fun v => v.startsWith prefix_)

private def trans (n : String) : Triple := tr (ex n) rdfTypeP (nsOwl ++ "TransitiveProperty")

/-! #### Simple roles -/

private def nsSimple : Graph := okGraph ++ objProps ["q", "s"]

-- a transitive property is not simple, so a cardinality restriction on it breaks §11.2 ...
#guard hasV (nsSimple ++ [trans "q"] ++ restr "r1" "q" (nsOwl ++ "minCardinality") two)
  "non-simple-property-in-restriction"
-- ... the same restriction on a simple property does not ...
#guard !(hasV (nsSimple ++ [trans "q"] ++ restr "r1" "p" (nsOwl ++ "minCardinality") two)
  "non-simple-property-in-restriction")
-- ... and a transitive property under no restriction is fine
#guard (graphBodyViolations (nsSimple ++ [trans "q"])).isEmpty
-- non-simplicity propagates UP the hierarchy: q is transitive, q is a sub-property of s
#guard hasV (nsSimple ++ [trans "q", tr (ex "q") (nsRdfs ++ "subPropertyOf") (ex "s")] ++
  restr "r1" "s" (nsOwl ++ "maxCardinality") two) "non-simple-property-in-restriction"
-- ... and not down: s is a sub-property of the transitive q, s stays simple
#guard !(hasV (nsSimple ++ [trans "q", tr (ex "s") (nsRdfs ++ "subPropertyOf") (ex "q")] ++
  restr "r1" "s" (nsOwl ++ "maxCardinality") two) "non-simple-property-in-restriction")
-- equivalence propagates both ways
#guard hasV (nsSimple ++ [trans "q", tr (ex "s") (nsOwl ++ "equivalentProperty") (ex "q")] ++
  restr "r1" "s" (nsOwl ++ "cardinality") two) "non-simple-property-in-restriction"
-- the inverse of a non-simple property is non-simple
#guard hasV (nsSimple ++ [trans "q", tr (ex "s") owlInverseOfP (ex "q")] ++
  restr "r1" "s" (nsOwl ++ "minCardinality") two) "non-simple-property-in-restriction"
-- a restriction on an ObjectInverseOf( q ) expression counts as one on q
#guard hasV (nsSimple ++ [trans "q", ⟨.bnode "iq", i owlInverseOfP, exI "q"⟩] ++
  [⟨.bnode "r1", i rdfTypeP, ti owlRestrictionC⟩, ⟨.bnode "r1", i owlOnPropertyP, .bnode "iq"⟩,
   ⟨.bnode "r1", i (nsOwl ++ "minCardinality"), two⟩]) "non-simple-property-in-restriction"
-- a chain-defined property is not simple; its operands are
#guard hasV (nsSimple ++ chainAx "q" [exI "p", exI "s"] ++
  restr "r1" "q" (nsOwl ++ "minCardinality") two) "non-simple-property-in-restriction"
#guard !(hasV (nsSimple ++ chainAx "q" [exI "p", exI "s"] ++
  restr "r1" "p" (nsOwl ++ "minCardinality") two) "non-simple-property-in-restriction")
-- owl:topObjectProperty is composite
#guard hasV (nsSimple ++
  [⟨.bnode "r1", i rdfTypeP, ti owlRestrictionC⟩,
   ⟨.bnode "r1", i owlOnPropertyP, ti (nsOwl ++ "topObjectProperty")⟩,
   ⟨.bnode "r1", i (nsOwl ++ "minCardinality"), two⟩]) "non-simple-property-in-restriction"
-- ObjectHasSelf
#guard hasV (nsSimple ++ [trans "q"] ++ restr "r1" "q" owlHasSelfP (litT "true" (nsXsd ++ "boolean")))
  "non-simple-property-in-restriction"
#guard !(hasV (nsSimple ++ restr "r1" "q" owlHasSelfP (litT "true" (nsXsd ++ "boolean")))
  "non-simple-property-in-restriction")
-- the characteristics of the second list of §11.2
#guard hasV (nsSimple ++ [trans "q", tr (ex "q") rdfTypeP (nsOwl ++ "FunctionalProperty")])
  "non-simple-property-in-characteristic"
#guard hasV (nsSimple ++ [trans "q", tr (ex "q") rdfTypeP (nsOwl ++ "InverseFunctionalProperty")])
  "non-simple-property-in-characteristic"
#guard hasV (nsSimple ++ [trans "q", tr (ex "q") rdfTypeP (nsOwl ++ "IrreflexiveProperty")])
  "non-simple-property-in-characteristic"
#guard hasV (nsSimple ++ [trans "q", tr (ex "q") rdfTypeP (nsOwl ++ "AsymmetricProperty")])
  "non-simple-property-in-characteristic"
-- reflexive and symmetric are not in the list
#guard !(hasV (nsSimple ++ [trans "q", tr (ex "q") rdfTypeP (nsOwl ++ "ReflexiveProperty")])
  "non-simple-property")
-- a simple property may carry them
#guard !(hasV (nsSimple ++ [tr (ex "s") rdfTypeP (nsOwl ++ "FunctionalProperty")])
  "non-simple-property")
-- disjointness
#guard hasV (nsSimple ++ [trans "q", tr (ex "p") (nsOwl ++ "propertyDisjointWith") (ex "q")])
  "non-simple-property-in-disjointness"
#guard !(hasV (nsSimple ++ [trans "q", tr (ex "p") (nsOwl ++ "propertyDisjointWith") (ex "s")])
  "non-simple-property-in-disjointness")
-- symmetry links a property to its inverse, which is composite when it is transitive
#guard hasV (nsSimple ++ [trans "q", tr (ex "q") rdfTypeP (nsOwl ++ "SymmetricProperty")] ++
  restr "r1" "q" (nsOwl ++ "minCardinality") two) "non-simple-property-in-restriction"

/-! #### Regularity of the property hierarchy -/

private def regV (g : Graph) : Bool := hasV g "irregular-property-hierarchy"

private def hier : Graph := okGraph ++ objProps ["hasFather", "hasBrother", "hasUncle",
  "hasChild", "hasWife", "hasAuntInLaw", "c", "s", "t"]

-- the acyclic example of §11.2
#guard !(regV (hier ++ chainAx "hasUncle" [exI "hasFather", exI "hasBrother"]
                    ++ chainAx "hasAuntInLaw" [exI "hasUncle", exI "hasWife"]))
-- the cyclic example of §11.2
#guard regV (hier ++ chainAx "hasUncle" [exI "hasFather", exI "hasBrother"]
                  ++ chainAx "hasBrother" [exI "hasChild", exI "hasUncle"])
-- the three allowed self-referential forms: R o R, R o S, S o R
#guard !(regV (hier ++ chainAx "c" [exI "c", exI "c"]))
#guard !(regV (hier ++ chainAx "c" [exI "c", exI "s"]))
#guard !(regV (hier ++ chainAx "c" [exI "s", exI "c"]))
-- the target in the middle, or at both ends of a longer chain, is cyclic
#guard regV (hier ++ chainAx "c" [exI "s", exI "c", exI "t"])
#guard regV (hier ++ chainAx "c" [exI "c", exI "s", exI "c"])
-- a chain whose first operand is the INVERSE of the target is not the form R o S
#guard regV (hier ++ [⟨.bnode "ic", i owlInverseOfP, exI "c"⟩] ++
  chainAx "c" [.bnode "ic", exI "s"])
-- a chain may target owl:topObjectProperty whatever its operands
#guard !(regV (hier ++ chainAx (nsOwl ++ "topObjectProperty") [exI "c", exI "c", exI "s"]))
-- a sub-property axiom that closes the cycle: c o s ⊑ t, t ⊑ c needs c < t but t →* c
#guard regV (hier ++ chainAx "t" [exI "c", exI "s"] ++ [tr (ex "t") (nsRdfs ++ "subPropertyOf") (ex "c")])
-- the other direction is regular
#guard !(regV (hier ++ chainAx "t" [exI "c", exI "s"] ++ [tr (ex "c") (nsRdfs ++ "subPropertyOf") (ex "t")]))

/-! #### owl:topDataProperty and datatype definitions -/

private def dataG : Graph := okGraph ++
  [tr (ex "d") rdfTypeP owlDataPropC, tr (ex "D1") rdfTypeP (nsRdfs ++ "Datatype"),
   tr (ex "D2") rdfTypeP (nsRdfs ++ "Datatype")]

#guard !(hasV (dataG ++ [tr (ex "d") (nsRdfs ++ "subPropertyOf") (nsOwl ++ "topDataProperty")])
  "top-data-property-misused")
#guard hasV (dataG ++ [tr (nsOwl ++ "topDataProperty") (nsRdfs ++ "subPropertyOf") (ex "d")])
  "top-data-property-misused"
#guard hasV (dataG ++ [tr (ex "a") (nsOwl ++ "topDataProperty") (ex "b")])
  "top-data-property-misused"

/-- `dt owl:equivalentClass _:r` with `_:r` the complement of `used`. -/
private def defines (dt r used : String) : Graph :=
  [⟨si dt, i (nsOwl ++ "equivalentClass"), .bnode r⟩,
   ⟨.bnode r, i rdfTypeP, ti (nsRdfs ++ "Datatype")⟩,
   ⟨.bnode r, i (nsOwl ++ "datatypeComplementOf"), ti used⟩]

#guard !(hasV (dataG ++ defines (ex "D1") "r1" (ex "D2") ++ defines (ex "D2") "r2" (nsXsd ++ "string"))
  "cyclic-datatype-definition")
#guard hasV (dataG ++ defines (ex "D1") "r1" (ex "D2") ++ defines (ex "D2") "r2" (ex "D1"))
  "cyclic-datatype-definition"
#guard hasV (dataG ++ defines (ex "D1") "r1" (ex "D1")) "cyclic-datatype-definition"
#guard hasV (dataG ++ defines (ex "D1") "r1" (nsXsd ++ "string") ++ defines (ex "D1") "r2" (nsXsd ++ "integer"))
  "datatype-defined-twice"
#guard !(hasV (dataG ++ defines (ex "D1") "r1" (nsXsd ++ "string")) "datatype-defined-twice")
#guard hasV (dataG ++ defines (nsXsd ++ "integer") "r1" (nsXsd ++ "string"))
  "builtin-datatype-redefined"

/-! #### Anonymous individuals -/

private def anonG : Graph := okGraph ++ [tr (ex "x1") rdfTypeP owlClassC]

private def anonV (g : Graph) (prefix_ : String) : Bool := hasV g prefix_

#guard anonV (anonG ++ [⟨.bnode "n", i (nsOwl ++ "sameAs"), exI "a"⟩])
  "anonymous-individual-in-sameAs-or-differentFrom"
#guard anonV (anonG ++ [⟨si (ex "a"), i (nsOwl ++ "differentFrom"), .bnode "n"⟩])
  "anonymous-individual-in-sameAs-or-differentFrom"
#guard !(anonV (anonG ++ [tr (ex "a") (nsOwl ++ "sameAs") (ex "b")]) "anonymous-individual")
#guard anonV (anonG ++ restr "r1" "p" owlHasValueP (.bnode "n")) "anonymous-individual-in-ObjectHasValue"
#guard !(anonV (anonG ++ restr "r1" "p" owlHasValueP (exI "a")) "anonymous-individual")
#guard anonV (anonG ++ [⟨.bnode "c", i rdfTypeP, ti owlClassC⟩] ++
  (let (h, g) := listTriples "ol" [.bnode "n"]; ⟨.bnode "c", i owlOneOfP, h⟩ :: g))
  "anonymous-individual-in-ObjectOneOf"
#guard !(anonV (anonG ++ [⟨.bnode "c", i rdfTypeP, ti owlClassC⟩] ++
  (let (h, g) := listTriples "ol" [exI "a"]; ⟨.bnode "c", i owlOneOfP, h⟩ :: g))
  "anonymous-individual")
#guard anonV (anonG ++ [⟨.bnode "npa", i rdfTypeP, ti (nsOwl ++ "NegativePropertyAssertion")⟩,
  ⟨.bnode "npa", i owlSourceIndP, .bnode "n"⟩, ⟨.bnode "npa", i owlAssertionPropP, exI "p"⟩,
  ⟨.bnode "npa", i owlTargetIndP, exI "b"⟩]) "anonymous-individual-in-negative-assertion"
-- the anonymous individual graph is a forest ...
#guard !(anonV (anonG ++ [⟨.bnode "x", i (ex "p"), .bnode "y"⟩]) "anonymous-individual")
#guard anonV (anonG ++ [⟨.bnode "x", i (ex "p"), .bnode "y"⟩, ⟨.bnode "y", i (ex "p"), .bnode "x"⟩])
  "anonymous-individuals-not-a-forest"
-- ... and each tree has a vertex with at most one link to a named individual
#guard anonV (anonG ++ [⟨.bnode "x", i (ex "p"), exI "a"⟩, ⟨.bnode "x", i (ex "p"), exI "b"⟩])
  "anonymous-individual-tree-without-leaf"
#guard !(anonV (anonG ++ [⟨.bnode "x", i (ex "p"), exI "a"⟩]) "anonymous-individual")
#guard !(anonV (anonG ++ [⟨.bnode "x", i (ex "p"), exI "a"⟩, ⟨.bnode "x", i (ex "p"), .bnode "y"⟩,
  ⟨.bnode "y", i (ex "p"), exI "b"⟩]) "anonymous-individual")

/-! ### The functional-syntax variant skips the header check only -/

/-- A header-less graph whose BODY is clean: an assertion triple makes
    it not typing-only, so the full check rejects it and the
    functional-syntax variant accepts it. That is the whole difference
    between the two entry points, in one pair. -/
private def noHeader : Graph :=
  [ tr (ex "p") rdfTypeP owlObjPropC
  , tr (ex "C") rdfTypeP owlClassC
  , tr (ex "a") rdfTypeP (ex "C")
  , tr (ex "a") (ex "p") (ex "b")
  , tr (ex "b") rdfTypeP (ex "C") ]

#guard docHeaderViolations noHeader == ["no-ontology-header"]
#guard graphBodyViolations noHeader == []
#guard !speciesIsDl noHeader noHeader false [] []
#guard speciesIsDlFunctional noHeader false []

/-! ### The conclusion document is judged too

Two cases with the SAME premise differ when the conclusion does — the
reason `speciesIsDl` takes five arguments. -/

#guard speciesIsDl okGraph okGraph true okGraph okGraph
#guard !speciesIsDl okGraph okGraph true
         [tr (ex "a") (ex "undeclared") (ex "b")]
         (okGraph ++ [tr (ex "a") (ex "undeclared") (ex "b")])

end Checks


/-! ## The species check with indexes (https://github.com/danbri/factoidal/issues/766)

The definitions above are the specification. They read the graph with list
scans: `hasTripleSp`, `findObjectSp` and `countSp` scan every triple for one
(subject, predicate) pair, `DeclIndex` membership scans a list of keys, and
the anonymous-individual check counts the named links of each blank node with
one scan of the graph per node. On QUDT 3.4.0 (130,404 triples, 4,860 blank
nodes in object property assertions) the check took 241 s, 225 s of it in the
named-link counts, and the time grew 34 times from 32,000 to 65,000 lines.

The twins below compute the same lists with three indexes built once per
graph: `spIndexOf` (subject key and predicate to the objects, in graph
order), `DeclSets` (the `DeclIndex` lists as hash sets) and `namedLinkCounts`
(the named-link count of every key). Each twin is proved equal to its
specification; `@[csimp]` theorems at the end make the compiler emit the
twins wherever the source calls `graphBodyViolations`, `speciesViolations`,
`speciesIsDl`, `speciesViolationsFunctional` or `speciesIsDlFunctional`. -/

/-! ### Subject-predicate index -/

/-- Objects of each (subject key, predicate IRI) pair, in graph order. -/
abbrev SpIndex := Std.HashMap (String × String) (List Term)

def spIndexOf (g : Graph) : SpIndex :=
  g.foldr (fun t m =>
    m.insert (subjKey t.s, t.p.val) (t.o :: m.getD (subjKey t.s, t.p.val) [])) ∅

/-- The (subject key, predicate) selector the scans use. -/
def spSel (sk p : String) (t : Triple) : Bool := t.p.val == p && subjKey t.s == sk

theorem spIndexOf_getD (g : Graph) (sk p : String) :
    (spIndexOf g).getD (sk, p) [] = (g.filter (spSel sk p)).map (·.o) := by
  induction g with
  | nil => simp [spIndexOf]
  | cons t rest ih =>
      unfold spIndexOf at ih ⊢
      rw [List.foldr_cons, Std.HashMap.getD_insert, List.filter_cons]
      by_cases h : spSel sk p t = true
      · have hk : (subjKey t.s, t.p.val) = (sk, p) := by
          simp only [spSel, Bool.and_eq_true, beq_iff_eq] at h
          rw [h.1, h.2]
        rw [hk, ih]
        simp [h]
      · have hk : ((subjKey t.s, t.p.val) == (sk, p)) = false := by
          simp only [spSel, Bool.and_eq_true, beq_iff_eq, not_and] at h
          simp only [beq_eq_false_iff_ne, ne_eq, Prod.mk.injEq, not_and]
          intro h1 h2
          exact h h2 h1
        rw [hk, ih]
        simp [h]

def hasTripleSpI (ix : SpIndex) (sk p : String) : Bool := !(ix.getD (sk, p) []).isEmpty

def findObjectSpI (ix : SpIndex) (sk p : String) : Option Term := (ix.getD (sk, p) []).head?

def countSpI (ix : SpIndex) (sk p : String) : Nat := (ix.getD (sk, p) []).length

def hasTypeSpI (ix : SpIndex) (sk ty : String) : Bool :=
  (ix.getD (sk, rdfTypeP) []).any (fun o => termIsIri o ty)

private theorem any_eq_not_isEmpty_filter (l : List Triple) (f : Triple → Bool) :
    l.any f = !(l.filter f).isEmpty := by
  induction l with
  | nil => rfl
  | cons t rest ih => by_cases h : f t = true <;> simp [h, ih]

theorem hasTripleSpI_eq (g : Graph) (sk p : String) :
    hasTripleSpI (spIndexOf g) sk p = hasTripleSp g sk p := by
  unfold hasTripleSpI hasTripleSp
  rw [spIndexOf_getD, any_eq_not_isEmpty_filter, List.isEmpty_map]
  rfl

theorem findObjectSpI_eq (g : Graph) (sk p : String) :
    findObjectSpI (spIndexOf g) sk p = findObjectSp g sk p := by
  unfold findObjectSpI findObjectSp
  rw [spIndexOf_getD, List.head?_map, List.head?_filter]
  rfl

theorem countSpI_eq (g : Graph) (sk p : String) :
    countSpI (spIndexOf g) sk p = countSp g sk p := by
  unfold countSpI countSp
  rw [spIndexOf_getD, List.length_map]
  rfl

theorem hasTypeSpI_eq (g : Graph) (sk ty : String) :
    hasTypeSpI (spIndexOf g) sk ty = hasTypeSp g sk ty := by
  unfold hasTypeSpI hasTypeSp
  rw [spIndexOf_getD]
  induction g with
  | nil => rfl
  | cons t rest ih =>
      by_cases h : spSel sk rdfTypeP t = true
      · simp only [spSel, Bool.and_eq_true, beq_iff_eq] at h
        simp [spSel, h, ih]
      · simp only [spSel, Bool.and_eq_true, beq_iff_eq, not_and] at h
        by_cases h1 : t.p.val = rdfTypeP
        · have h2 := h h1
          simp [spSel, h1, h2, ih]
        · simp [spSel, h1, ih]

/-! ### Declaration sets -/

structure DeclSets where
  cls      : Std.HashSet String
  restr    : Std.HashSet String
  datatype : Std.HashSet String
  objProp  : Std.HashSet String
  dataProp : Std.HashSet String
  annProp  : Std.HashSet String
  charProp : Std.HashSet String
  hasDR    : Std.HashSet String
  inv      : Std.HashSet String
  annSubj  : Std.HashSet String

def DeclIndex.sets (d : DeclIndex) : DeclSets :=
  { cls := .ofList d.cls, restr := .ofList d.restr, datatype := .ofList d.datatype
  , objProp := .ofList d.objProp, dataProp := .ofList d.dataProp
  , annProp := .ofList d.annProp, charProp := .ofList d.charProp
  , hasDR := .ofList d.hasDR, inv := .ofList d.inv, annSubj := .ofList d.annSubj }

theorem setContains (l : List String) (k : String) :
    (Std.HashSet.ofList l).contains k = l.contains k := Std.HashSet.contains_ofList

def propEvidenceS (s : DeclSets) (k : String) : Bool :=
  s.objProp.contains k || s.dataProp.contains k || s.annProp.contains k ||
  s.inv.contains k ||
  (s.charProp.contains k && (s.hasDR.contains k || s.inv.contains k))

theorem propEvidenceS_eq (d : DeclIndex) (k : String) :
    propEvidenceS d.sets k = propEvidence d k := by
  simp [propEvidenceS, propEvidence, DeclIndex.sets]

def classEvidenceI (ix : SpIndex) (s : DeclSets) (k : String) : Bool :=
  s.cls.contains k || s.datatype.contains k || s.restr.contains k ||
  hasTripleSpI ix k owlIntersectionOfP || hasTripleSpI ix k owlUnionOfP ||
  hasTripleSpI ix k owlComplementOfP || hasTripleSpI ix k owlOneOfP ||
  hasTripleSpI ix k owlOnPropertyP

theorem classEvidenceI_eq (g : Graph) (d : DeclIndex) (k : String) :
    classEvidenceI (spIndexOf g) d.sets k = classEvidence g d k := by
  simp [classEvidenceI, classEvidence, DeclIndex.sets, hasTripleSpI_eq]

def datatypeEvidenceI (ix : SpIndex) (s : DeclSets) (dt : String) : Bool :=
  builtinDatatypes.contains dt ||
  s.cls.contains ("I" ++ dt) ||
  hasTripleSpI ix ("I" ++ dt) owlEquivClassP ||
  hasTripleSpI ix ("I" ++ dt) owlOnDatatypeP ||
  hasTripleSpI ix ("I" ++ dt) owlOneOfP

theorem datatypeEvidenceI_eq (g : Graph) (d : DeclIndex) (dt : String) :
    datatypeEvidenceI (spIndexOf g) d.sets dt = datatypeEvidence g d dt := by
  simp [datatypeEvidenceI, datatypeEvidence, DeclIndex.sets, hasTripleSpI_eq]

/-- `collectionMembers` with the index, as a loop: the members so far are
kept in reverse in `acc`, so a long RDF list costs no stack. -/
def collectionMembersLoop (ix : SpIndex) : Term → Nat → List Term → List Term
  | _, 0, acc => acc.reverse
  | node, f + 1, acc =>
      match termKeyDl node with
      | none => acc.reverse
      | some nk =>
          if termIsIri node rdfNilI then acc.reverse
          else match findObjectSpI ix nk rdfFirstP with
               | none => acc.reverse
               | some first =>
                   match findObjectSpI ix nk rdfRestP with
                   | none => (first :: acc).reverse
                   | some rest => collectionMembersLoop ix rest f (first :: acc)

def collectionMembersI (ix : SpIndex) (node : Term) (fuel : Nat) : List Term :=
  collectionMembersLoop ix node fuel []

private theorem collectionMembersLoop_eq (g : Graph) (node : Term) (fuel : Nat)
    (acc : List Term) :
    collectionMembersLoop (spIndexOf g) node fuel acc
      = acc.reverse ++ collectionMembers g node fuel := by
  induction fuel generalizing node acc with
  | zero => simp [collectionMembersLoop, collectionMembers]
  | succ f ih =>
      unfold collectionMembersLoop collectionMembers
      cases termKeyDl node with
      | none => simp
      | some nk =>
          simp only [findObjectSpI_eq]
          cases findObjectSp g nk rdfFirstP <;> cases findObjectSp g nk rdfRestP <;>
            by_cases hn : termIsIri node rdfNilI = true <;> simp [ih, hn]

theorem collectionMembersI_eq (g : Graph) (node : Term) (fuel : Nat) :
    collectionMembersI (spIndexOf g) node fuel = collectionMembers g node fuel := by
  unfold collectionMembersI
  rw [collectionMembersLoop_eq]
  simp

/-! ### Duplicate removal -/

/-- `dedupStrs` with a hash set: the last occurrence of each string, in
order. -/
def dedupStrsFast (l : List String) : List String :=
  (l.foldr (fun x (acc : Std.HashSet String × List String) =>
    if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) (∅, [])).2

private theorem dedupFold (l : List String) :
    (∀ y, (l.foldr (fun x (acc : Std.HashSet String × List String) =>
      if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) (∅, [])).1.contains y
        = l.contains y) ∧
    (l.foldr (fun x (acc : Std.HashSet String × List String) =>
      if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) (∅, [])).2
        = dedupStrs l := by
  induction l with
  | nil => exact ⟨fun y => by simp, rfl⟩
  | cons x rest ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [List.foldr_cons]
      by_cases hx : rest.contains x = true
      · have hc : (rest.foldr (fun x (acc : Std.HashSet String × List String) =>
            if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) (∅, [])).1.contains x
              = true := by rw [h1]; exact hx
        simp only [hc, if_true]
        refine ⟨fun y => ?_, ?_⟩
        · rw [h1, List.contains_cons]
          by_cases hy : y = x
          · subst hy; rw [hx]; simp
          · simp [hy]
        · rw [h2, dedupStrs.eq_2, if_pos hx]
      · have hc : (rest.foldr (fun x (acc : Std.HashSet String × List String) =>
            if acc.1.contains x then acc else (acc.1.insert x, x :: acc.2)) (∅, [])).1.contains x
              = false := by rw [h1]; simpa using hx
        simp only [hc, Bool.false_eq_true, if_false]
        refine ⟨fun y => ?_, ?_⟩
        · rw [Std.HashSet.contains_insert, h1, List.contains_cons]
          by_cases hy : y = x
          · subst hy; simp
          · have : (x == y) = false := by simp; exact fun h => hy h.symm
            simp [this, hy]
        · rw [h2, dedupStrs.eq_2, if_neg hx]

theorem dedupStrsFast_eq (l : List String) : dedupStrsFast l = dedupStrs l :=
  (dedupFold l).2

/-! ### Named links of the anonymous individual graph -/

/-- One or two optional keys as a list without repeats. -/
def keysOf : Option String → Option String → List String
  | some a, some b => if a == b then [a] else [a, b]
  | some a, none => [a]
  | none, some b => [b]
  | none, none => []

theorem keysOf_count (k1 k2 : Option String) (k : String) :
    (keysOf k1 k2).count k = if (k1 == some k || k2 == some k) then 1 else 0 := by
  cases k1 <;> cases k2 <;> simp only [keysOf, List.count_cons, List.count_nil]
  · simp
  · rename_i b; by_cases h : b = k <;> simp [h]
  · rename_i a; by_cases h : a = k <;> simp [h]
  · rename_i a b
    by_cases hab : a = b
    · subst hab; by_cases h : a = k <;> simp [h]
    · have hab' : (a == b) = false := by simpa using hab
      rw [if_neg (by simp [hab'])]
      simp only [List.count_cons, List.count_nil]
      by_cases ha : a = k <;> by_cases hb : b = k <;> simp_all

/-- The keys whose named-link count the triple `t` raises by one (the
selector of `anonymousIndividualViolations`' `namedLinks`): its subject when
the object is an IRI, its object when the subject is an IRI, each once. -/
def linkKeys (t : Triple) : List String :=
  keysOf (match t.o with | .iri _ => some (subjKey t.s) | _ => none)
    (match t.s with | .iri _ => termKeyDl t.o | _ => none)

/-- The selector of `namedLinks k`, without the assertion test. -/
def linkSel (k : String) (t : Triple) : Bool :=
  (subjKey t.s == k && (match t.o with | .iri _ => true | _ => false)) ||
  (termKeyDl t.o == some k && (match t.s with | .iri _ => true | _ => false))

theorem linkKeys_count (t : Triple) (k : String) :
    (linkKeys t).count k = if linkSel k t then 1 else 0 := by
  unfold linkKeys
  rw [keysOf_count]
  congr 1
  unfold linkSel
  cases t.s <;> cases t.o <;> simp

def bumpKey (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + 1)

private theorem bumpKeys_getD (ks : List String) (m : Std.HashMap String Nat) (k : String) :
    (ks.foldl bumpKey m).getD k 0 = m.getD k 0 + ks.count k := by
  induction ks generalizing m with
  | nil => simp
  | cons a rest ih =>
      rw [List.foldl_cons, ih, List.count_cons]
      unfold bumpKey
      rw [Std.HashMap.getD_insert]
      by_cases h : a = k
      · subst h; simp; omega
      · have : (a == k) = false := by simpa using h
        simp [this]

/-- Each key's number of named links among the triples that pass `a`. -/
def namedLinkCounts (a : Triple → Bool) (g : Graph) : Std.HashMap String Nat :=
  g.foldl (fun m t => if a t then (linkKeys t).foldl bumpKey m else m) ∅

private theorem namedLinkCounts_fold (a : Triple → Bool) (g : Graph)
    (m : Std.HashMap String Nat) (k : String) :
    (g.foldl (fun m t => if a t then (linkKeys t).foldl bumpKey m else m) m).getD k 0
      = m.getD k 0 + (g.filter (fun t => a t && linkSel k t)).length := by
  induction g generalizing m with
  | nil => simp
  | cons t rest ih =>
      rw [List.foldl_cons, ih, List.filter_cons]
      by_cases ha : a t = true
      · simp only [ha, if_true, bumpKeys_getD, linkKeys_count, Bool.true_and]
        by_cases hl : linkSel k t = true
        · simp [hl]; omega
        · simp [hl]
      · simp [ha]

theorem namedLinkCounts_getD (a : Triple → Bool) (g : Graph) (k : String) :
    (namedLinkCounts a g).getD k 0 = (g.filter (fun t => a t && linkSel k t)).length := by
  unfold namedLinkCounts
  rw [namedLinkCounts_fold]
  simp

/-! ### Table 5 -/

def table5RedundantI (ix : SpIndex) (t : Triple) : Bool :=
  if t.p.val != rdfTypeP then false
  else match t.o with
  | .iri o =>
      let sk := subjKey t.s
      if o.val == rdfsClassC then
        hasTypeSpI ix sk owlClassC || hasTypeSpI ix sk rdfsDatatypeC ||
        hasTypeSpI ix sk owlDataRangeC || hasTypeSpI ix sk owlRestrictionC
      else if o.val == owlClassC then hasTypeSpI ix sk owlRestrictionC
      else if o.val == rdfPropertyC then propertyTypings.any (hasTypeSpI ix sk)
      else if o.val == rdfListC then
        hasTripleSpI ix sk rdfFirstP && hasTripleSpI ix sk rdfRestP
      else false
  | _ => false

theorem table5RedundantI_eq (g : Graph) (t : Triple) :
    table5RedundantI (spIndexOf g) t = table5Redundant g t := by
  unfold table5RedundantI table5Redundant
  have hty : hasTypeSpI (spIndexOf g) = hasTypeSp g := by
    funext sk ty; exact hasTypeSpI_eq g sk ty
  simp only [hty, hasTripleSpI_eq] <;> rfl

def dropTable5RedundantI (g : Graph) : Graph :=
  let ix := spIndexOf g
  g.filter (fun t => !table5RedundantI ix t)

theorem dropTable5RedundantI_eq (g : Graph) : dropTable5RedundantI g = dropTable5Redundant g := by
  simp only [dropTable5RedundantI, dropTable5Redundant, table5RedundantI_eq]

/-! ### Per-triple checks -/

def tripleViolationsI (g : Graph) (ix : SpIndex) (s : DeclSets) (t : Triple) : List String :=
  let v1 :=
    match t.s with
    | .iri i =>
        if iriReserved i.val && !(subjectWhitelist.contains i.val)
        then ["reserved-vocabulary-subject: " ++ i.val] else []
    | _ => []
  let v2 :=
    if iriReserved t.p.val then []
    else if builtinAnnProps.contains t.p.val || builtinProps.contains t.p.val then []
    else if propEvidenceS s ("I" ++ t.p.val) then []
    else if s.annSubj.contains (subjKey t.s) then []
    else ["untyped-predicate: " ++ t.p.val]
  let v3 :=
    if t.p.val != rdfTypeP then []
    else match t.o with
    | .literal _ => ["literal-as-type-object"]
    | .tripleTerm _ _ _ => ["triple-term-as-type-object"]
    | .bnode b =>
        if classEvidenceI ix s ("B" ++ b) then [] else ["undefined-bnode-class-expression"]
    | .iri o =>
        if iriReserved o.val then
          (if typeObjectWhitelist.contains o.val then []
           else ["reserved-vocabulary-as-class: " ++ o.val])
        else if classEvidenceI ix s ("I" ++ o.val) then []
        else ["untyped-class: " ++ o.val]
  let v4 :=
    if t.p.val != owlOnPropertyP then []
    else match t.o with
    | .literal _ => ["literal-as-onProperty"]
    | .tripleTerm _ _ _ => ["triple-term-as-onProperty"]
    | .bnode b => if s.inv.contains ("B" ++ b) then [] else ["undefined-bnode-onProperty"]
    | .iri o =>
        if builtinProps.contains o.val then []
        else if iriReserved o.val then ["reserved-vocabulary-as-onProperty: " ++ o.val]
        else if propEvidenceS s ("I" ++ o.val) then []
        else ["untyped-onProperty: " ++ o.val]
  let v5 :=
    match t.o with
    | .literal _ =>
        if s.objProp.contains ("I" ++ t.p.val)
        then ["object-property-with-literal-object: " ++ t.p.val] else []
    | _ => []
  let v6 :=
    match t.o with
    | .literal l =>
        let dt := l.val.datatype.val
        if datatypeEvidenceI ix s dt then []
        else if iriReserved dt then ["reserved-vocabulary-as-datatype: " ++ dt]
        else ["undefined-datatype: " ++ dt]
    | _ => []
  let v7 :=
    if (t.p.val == rdfsRangeP && s.dataProp.contains (subjKey t.s))
       || t.p.val == owlOnDatatypeP then
      match t.o with
      | .iri o =>
          if datatypeEvidenceI ix s o.val then []
          else if iriReserved o.val then ["reserved-vocabulary-as-datatype: " ++ o.val]
          else ["undefined-datatype: " ++ o.val]
      | _ => []
    else []
  let v8 :=
    if t.p.val == rdfFirstP || t.p.val == rdfRestP then
      let sk := subjKey t.s
      if countSpI ix sk rdfFirstP == 1 && countSpI ix sk rdfRestP == 1 then []
      else ["malformed-rdf-list-node"]
    else []
  let v9 :=
    if t.p.val == owlChainP then
      let members := collectionMembersI ix t.o g.length
      let interior := match members with
                      | [] => []
                      | _ :: tl => dropLastTerm tl
      let self := subjKey t.s
      if interior.any (fun m => termKeyDl m == some self)
      then ["property-inside-own-chain: " ++ self] else []
    else []
  v1 ++ v2 ++ v3 ++ v4 ++ v5 ++ v6 ++ v7 ++ v8 ++ v9

theorem tripleViolationsI_eq (g : Graph) (d : DeclIndex) (t : Triple) :
    tripleViolationsI g (spIndexOf g) d.sets t = tripleViolations g d t := by
  have hp : propEvidenceS d.sets = propEvidence d := funext (propEvidenceS_eq d)
  have hc : classEvidenceI (spIndexOf g) d.sets = classEvidence g d :=
    funext (classEvidenceI_eq g d)
  have hd : datatypeEvidenceI (spIndexOf g) d.sets = datatypeEvidence g d :=
    funext (datatypeEvidenceI_eq g d)
  have hn : countSpI (spIndexOf g) = countSp g := by
    funext sk p; exact countSpI_eq g sk p
  have hm : collectionMembersI (spIndexOf g) = collectionMembers g := by
    funext n f; exact collectionMembersI_eq g n f
  unfold tripleViolationsI tripleViolations
  rw [hp, hc, hd, hn, hm]
  simp only [DeclIndex.sets, setContains] <;> rfl

/-! ### Punning -/

def punningHereS (s : DeclSets) (k : String) : List String :=
  if !(k.startsWith "I") then []
  else
    (if s.cls.contains k && s.datatype.contains k
     then ["illegal-punning-class-datatype: " ++ k] else []) ++
    (if s.objProp.contains k && s.dataProp.contains k
     then ["illegal-punning-object-data-property: " ++ k] else []) ++
    (if s.objProp.contains k && s.annProp.contains k
     then ["illegal-punning-object-annotation-property: " ++ k] else []) ++
    (if s.dataProp.contains k && s.annProp.contains k
     then ["illegal-punning-data-annotation-property: " ++ k] else [])

def punningViolationsS (d : DeclIndex) (s : DeclSets) : List String :=
  (dedupStrsFast (d.cls ++ d.objProp ++ d.dataProp)).flatMap (punningHereS s)

private theorem punningKeys_flatMap (d : DeclIndex) (ks : List String) :
    punningViolationsKeys d ks = ks.flatMap (punningHereS d.sets) := by
  induction ks with
  | nil => rfl
  | cons k rest ih =>
      rw [punningViolationsKeys, List.flatMap_cons, ih]
      simp only [punningHereS, DeclIndex.sets, setContains]

theorem punningViolationsS_eq (d : DeclIndex) :
    punningViolationsS d d.sets = punningViolations d := by
  unfold punningViolationsS punningViolations
  rw [dedupStrsFast_eq, punningKeys_flatMap]

/-! ### Simple roles -/

def opeOfTermI (ix : SpIndex) (t : Term) : Option Ope :=
  match t with
  | .iri i => some ⟨"I" ++ i.val, false⟩
  | .bnode b =>
      match findObjectSpI ix ("B" ++ b) owlInverseOfP with
      | some (.iri p) => some ⟨"I" ++ p.val, true⟩
      | _ => none
  | _ => none

theorem opeOfTermI_eq (g : Graph) (t : Term) : opeOfTermI (spIndexOf g) t = opeOfTerm g t := by
  unfold opeOfTermI opeOfTerm
  simp only [findObjectSpI_eq] <;> rfl

def simpleRoleViolationsI (g : Graph) (ix : SpIndex) (ns : List String) : List String :=
  let keyOfTerm := fun (t : Term) => (opeOfTermI ix t).map (·.key)
  let restrictions := (dedupStrsFast (subjectsOfP g owlOnPropertyP)).flatMap (fun r =>
    if cardinalityPreds.any (fun cp => hasTripleSpI ix r cp) || hasTripleSpI ix r owlHasSelfP then
      match (findObjectSpI ix r owlOnPropertyP).bind keyOfTerm with
      | some k => if ns.contains k then ["non-simple-property-in-restriction: " ++ k] else []
      | none => []
    else [])
  let characteristics :=
    [nsOwl ++ "FunctionalProperty", nsOwl ++ "InverseFunctionalProperty",
     nsOwl ++ "IrreflexiveProperty", nsOwl ++ "AsymmetricProperty"].flatMap (fun ty =>
      (subjectsTyped g ty).flatMap (fun k =>
        if ns.contains k then ["non-simple-property-in-characteristic: " ++ k] else []))
  let disjoint := g.flatMap (fun t =>
    if t.p.val == owlPropDisjointP then
      [opeOfTermI ix (subjTermDl t.s), opeOfTermI ix t.o].flatMap (fun o? =>
        match o? with
        | some o => if ns.contains o.key then ["non-simple-property-in-disjointness: " ++ o.key] else []
        | none => [])
    else [])
  let allDisjoint := (subjectsTyped g (nsOwl ++ "AllDisjointProperties")).flatMap (fun n =>
    match findObjectSpI ix n owlMembersP with
    | some l =>
        (collectionMembersI ix l g.length).flatMap (fun m =>
          match keyOfTerm m with
          | some k => if ns.contains k then ["non-simple-property-in-disjointness: " ++ k] else []
          | none => [])
    | none => [])
  restrictions ++ characteristics ++ disjoint ++ allDisjoint

theorem simpleRoleViolationsI_eq (g : Graph) (ns : List String) :
    simpleRoleViolationsI g (spIndexOf g) ns = simpleRoleViolations g ns := by
  have ho : opeOfTermI (spIndexOf g) = opeOfTerm g := funext (opeOfTermI_eq g)
  have hh : hasTripleSpI (spIndexOf g) = hasTripleSp g := by
    funext sk p; exact hasTripleSpI_eq g sk p
  have hf : findObjectSpI (spIndexOf g) = findObjectSp g := by
    funext sk p; exact findObjectSpI_eq g sk p
  have hm : collectionMembersI (spIndexOf g) = collectionMembers g := by
    funext n f; exact collectionMembersI_eq g n f
  unfold simpleRoleViolationsI simpleRoleViolations
  simp only [ho, hh, hf, hm, dedupStrsFast_eq, opeOfSubject] <;> rfl

/-! ### Anonymous individuals -/

private theorem any_contains_flatten (comps : List (List String)) (v : String) :
    comps.any (fun c => c.contains v) = comps.flatten.contains v := by
  induction comps with
  | nil => rfl
  | cons c rest ih => rw [List.any_cons, List.flatten_cons, List.contains_append, ih]

def anonymousIndividualViolationsI (g : Graph) (ix : SpIndex) (s : DeclSets) : List String :=
  let sameDiff := g.filterMap (fun t =>
    if (t.p.val == owlSameAsP || t.p.val == owlDifferentFromP) &&
       (isBnodeSubject t.s || isBnodeTerm t.o)
    then some "anonymous-individual-in-sameAs-or-differentFrom" else none)
  let allDifferent := (subjectsTyped g (nsOwl ++ "AllDifferent")).flatMap (fun n =>
    [owlMembersP, owlDistinctMembersP].flatMap (fun p =>
      match findObjectSpI ix n p with
      | some l =>
          if (collectionMembersI ix l g.length).any isBnodeTerm
          then ["anonymous-individual-in-AllDifferent"] else []
      | none => []))
  let negative := (subjectsTyped g (nsOwl ++ "NegativePropertyAssertion")).flatMap (fun n =>
    [owlSourceIndP, owlTargetIndP].flatMap (fun p =>
      match findObjectSpI ix n p with
      | some (.bnode _) => ["anonymous-individual-in-negative-assertion"]
      | _ => []))
  let oneOf := g.filterMap (fun t =>
    if t.p.val == owlOneOfP && !(s.datatype.contains (subjKey t.s)) &&
       (collectionMembersI ix t.o g.length).any isBnodeTerm
    then some "anonymous-individual-in-ObjectOneOf" else none)
  let hasValue := g.filterMap (fun t =>
    if t.p.val == owlHasValueP && isBnodeTerm t.o
    then some "anonymous-individual-in-ObjectHasValue" else none)
  let assertion := fun (t : Triple) => s.objProp.contains ("I" ++ t.p.val)
  let edges : List (String × String) := g.filterMap (fun t =>
    match t.s, t.o with
    | .bnode a, .bnode b => if assertion t then some ("B" ++ a, "B" ++ b) else none
    | _, _ => none)
  let counts := namedLinkCounts assertion g
  let verts : List String := dedupStrsFast (g.flatMap (fun t =>
    if assertion t then
      (match t.s with | .bnode b => ["B" ++ b] | _ => []) ++
      (match t.o with | .bnode b => ["B" ++ b] | _ => [])
    else []))
  let forest :=
    match componentsOf edges with
    | none => ["anonymous-individuals-not-a-forest"]
    | some comps =>
        let inComps : Std.HashSet String := .ofList comps.flatten
        let isolated := verts.filter (fun v => !(inComps.contains v))
        (comps ++ isolated.map (fun v => [v])).filterMap (fun c =>
          if c.any (fun v => counts.getD v 0 ≤ 1) then none
          else some "anonymous-individual-tree-without-leaf")
  sameDiff ++ allDifferent ++ negative ++ oneOf ++ hasValue ++ forest

theorem anonymousIndividualViolationsI_eq (g : Graph) (d : DeclIndex) :
    anonymousIndividualViolationsI g (spIndexOf g) d.sets = anonymousIndividualViolations g d := by
  have hf : findObjectSpI (spIndexOf g) = findObjectSp g := by
    funext sk p; exact findObjectSpI_eq g sk p
  have hm : collectionMembersI (spIndexOf g) = collectionMembers g := by
    funext n f; exact collectionMembersI_eq g n f
  have hc : ∀ (a : Triple → Bool) (k : String),
      (namedLinkCounts a g).getD k 0 = (g.filter (fun t => a t && linkSel k t)).length :=
    fun a k => namedLinkCounts_getD a g k
  unfold anonymousIndividualViolationsI anonymousIndividualViolations
  simp only [hf, hm, hc, dedupStrsFast_eq, DeclIndex.sets, setContains, linkSel,
    any_contains_flatten] <;> rfl

/-! ### The body, and the species verdict -/

def globalRestrictionViolationsI (g : Graph) (ix : SpIndex) (d : DeclIndex) (s : DeclSets) :
    List String :=
  let ns := nonsimpleKeys g
  topDataViolations g ++ datatypeDefinitionViolations g d ++
  simpleRoleViolationsI g ix ns ++ regularityViolations g ++
  anonymousIndividualViolationsI g ix s

theorem globalRestrictionViolationsI_eq (g : Graph) (d : DeclIndex) :
    globalRestrictionViolationsI g (spIndexOf g) d d.sets = globalRestrictionViolations g d := by
  unfold globalRestrictionViolationsI globalRestrictionViolations
  simp only [simpleRoleViolationsI_eq, anonymousIndividualViolationsI_eq]

/-- `graphBodyViolations` with the indexes. -/
def graphBodyViolationsI (g0 : Graph) : List String :=
  let g := dropTable5RedundantI g0
  let d := buildDeclIndex g
  let s := d.sets
  let ix := spIndexOf g
  let perTriple := g.flatMap (tripleViolationsI g ix s)
  perTriple ++ punningViolationsS d s ++ globalRestrictionViolationsI g ix d s

theorem graphBodyViolationsI_eq (g0 : Graph) : graphBodyViolationsI g0 = graphBodyViolations g0 := by
  unfold graphBodyViolationsI graphBodyViolations
  rw [dropTable5RedundantI_eq]
  have ht : tripleViolationsI (dropTable5Redundant g0) (spIndexOf (dropTable5Redundant g0))
      (buildDeclIndex (dropTable5Redundant g0)).sets
      = tripleViolations (dropTable5Redundant g0) (buildDeclIndex (dropTable5Redundant g0)) :=
    funext (tripleViolationsI_eq _ _)
  simp only [ht, punningViolationsS_eq, globalRestrictionViolationsI_eq]

/-! ### The twins agree with the specification on the fixtures above

`graphBodyViolationsI_eq` proves it for every graph; these cases also check
that the anonymous-individual counts see a leaf, a tree without a leaf and a
cycle (Structural Specification §11.2), so a twin that answered `[]` for
everything would fail the build. They come before the `csimp` theorems
below, which would make a later comparison call the twin twice. -/

section Checks

private def bn (b : String) : Subject := .bnode b
private def anonBase : Graph :=
  okGraph ++ [tr (ex "q") rdfTypeP owlObjPropC]

-- `_:x` has one named link: a leaf, no violation.
private def anonLeaf : Graph := anonBase ++ [trb (ex "a") (ex "p") "x"]
-- `_:x` has two named links and no other vertex: a tree without a leaf.
private def anonNoLeaf : Graph :=
  anonBase ++ [trb (ex "a") (ex "p") "x", ⟨bn "x", i (ex "q"), ti (ex "b")⟩]
-- `_:x p _:y`, `_:y q _:x`: a cycle.
private def anonCycle : Graph :=
  anonBase ++ [⟨bn "x", i (ex "p"), .bnode "y"⟩, ⟨bn "y", i (ex "q"), .bnode "x"⟩]

#guard graphBodyViolationsI okGraph == graphBodyViolations okGraph
#guard graphBodyViolationsI okGraph == []
#guard graphBodyViolationsI anonLeaf == graphBodyViolations anonLeaf
#guard !(graphBodyViolationsI anonLeaf).contains "anonymous-individual-tree-without-leaf"
#guard graphBodyViolationsI anonNoLeaf == graphBodyViolations anonNoLeaf
#guard (graphBodyViolationsI anonNoLeaf).contains "anonymous-individual-tree-without-leaf"
#guard graphBodyViolationsI anonCycle == graphBodyViolations anonCycle
#guard (graphBodyViolationsI anonCycle).contains "anonymous-individuals-not-a-forest"
#guard graphBodyViolationsI noHeader == graphBodyViolations noHeader
#guard graphBodyViolationsI (okGraph ++ [tr (ex "a") (ex "q") (ex "b")])
         == graphBodyViolations (okGraph ++ [tr (ex "a") (ex "q") (ex "b")])
#guard (graphBodyViolationsI (okGraph ++ [tr (ex "a") (ex "q") (ex "b")])).any
         (fun v => v.startsWith "untyped-predicate")
#guard dedupStrsFast ["a", "b", "a", "c", "b"] == dedupStrs ["a", "b", "a", "c", "b"]
#guard dedupStrsFast ["a", "b", "a", "c", "b"] == ["a", "c", "b"]

end Checks

/-! ### The compiler emits the twins -/

def speciesViolationsFast (pDoc pMerged : Graph) (hasConclusion : Bool)
    (cDoc uMerged : Graph) (available : Option (List String) := none) : List String :=
  (docHeaderViolations pDoc).map (fun v => "premise: " ++ v) ++
  (graphBodyViolationsI pMerged).map (fun v => "premise: " ++ v) ++
  (unresolvedImportViolations available (rootOntologyKeys pDoc) pMerged).map
    (fun v => "premise: " ++ v) ++
  (if hasConclusion then
     (docHeaderViolations cDoc).map (fun v => "conclusion: " ++ v) ++
     (graphBodyViolationsI uMerged).map (fun v => "conclusion: " ++ v) ++
     (unresolvedImportViolations available
        (rootOntologyKeys pDoc ++ rootOntologyKeys cDoc) uMerged).map
       (fun v => "conclusion: " ++ v)
   else [])

theorem speciesViolations_eq_fast : @speciesViolations = @speciesViolationsFast := by
  funext pDoc pMerged hc cDoc uMerged av
  simp only [speciesViolations, speciesViolationsFast, graphBodyViolationsI_eq]

def speciesIsDlFast (pDoc pMerged : Graph) (hasConclusion : Bool)
    (cDoc uMerged : Graph) (available : Option (List String) := none) : Bool :=
  (speciesViolationsFast pDoc pMerged hasConclusion cDoc uMerged available).isEmpty

def speciesViolationsFunctionalFast (p : Graph) (hasConclusion : Bool) (u : Graph) :
    List String :=
  (graphBodyViolationsI p).map (fun v => "premise: " ++ v) ++
  (if hasConclusion then (graphBodyViolationsI u).map (fun v => "conclusion: " ++ v)
   else [])

def speciesIsDlFunctionalFast (p : Graph) (hasConclusion : Bool) (u : Graph) : Bool :=
  (speciesViolationsFunctionalFast p hasConclusion u).isEmpty

@[csimp] theorem graphBodyViolations_eq_fast : @graphBodyViolations = @graphBodyViolationsI :=
  funext fun g => (graphBodyViolationsI_eq g).symm

@[csimp] theorem speciesViolations_csimp : @speciesViolations = @speciesViolationsFast :=
  speciesViolations_eq_fast

@[csimp] theorem speciesIsDl_eq_fast : @speciesIsDl = @speciesIsDlFast := by
  funext pDoc pMerged hc cDoc uMerged av
  simp only [speciesIsDl, speciesIsDlFast, speciesViolations_eq_fast]

@[csimp] theorem speciesViolationsFunctional_eq_fast :
    @speciesViolationsFunctional = @speciesViolationsFunctionalFast := by
  funext p hc u
  simp only [speciesViolationsFunctional, speciesViolationsFunctionalFast, graphBodyViolationsI_eq]

@[csimp] theorem speciesIsDlFunctional_eq_fast :
    @speciesIsDlFunctional = @speciesIsDlFunctionalFast := by
  funext p hc u
  simp only [speciesIsDlFunctional, speciesIsDlFunctionalFast,
    speciesViolationsFunctional_eq_fast]

#print axioms speciesViolations_eq_fast
#print axioms graphBodyViolationsI_eq
#print axioms anonymousIndividualViolationsI_eq
#print axioms namedLinkCounts_getD
#print axioms spIndexOf_getD
#print axioms dedupStrsFast_eq
#print axioms collectionMembersI_eq

end L4Factoidal.OWL.SyntaxDL
