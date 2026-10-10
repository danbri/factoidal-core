/-
L4Factoidal.OWL.OwlXml — the OWL 2 XML Serialization reader.

Spec: OWL 2 Web Ontology Language XML Serialization (Second Edition),
https://www.w3.org/TR/owl2-xml-serialization/ — the XML Schema of section
3.4 fixes every element and attribute below. The serialization mirrors the
structural specification, so the reader produces the SAME
`L4Factoidal.OWL.Struct.Ontology` as the functional-style reader, and the
RDF graph of an OWL/XML document is the mapping of that structure
(`Ontology.toGraph`).

## Reading rules (section 3.1)

* On any entity element exactly one of an `IRI` attribute or an
  `abbreviatedIRI` attribute appears; both or neither is a failure.
* A value of type `xsd:anyURI` (`IRI`, `ontologyIRI`, `versionIRI`,
  `datatypeIRI`, `facet`, the text of `Import`, `IRI` and `AbbreviatedIRI`
  elements) is resolved against `xml:base` of the `Ontology` element.
  Literal CONTENT is never resolved.
* An abbreviated IRI expands through the `Prefix` elements of the same
  document; the four prefixes `owl`, `rdf`, `rdfs`, `xsd` are implicitly
  declared, as in the functional-style syntax.
* A `Literal` with `xml:lang` is a language-tagged literal; with
  `datatypeIRI` a typed literal; with neither a plain string.

Anything outside the schema is a clean `none`.
-/
import L4Factoidal.OWL.FunctionalSyntax
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Document
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.OWL.OwlXml

open L4Factoidal.RDF
open L4Factoidal.OWL.Struct
open L4Factoidal.XML

/-! ## A smaller tree: elements only -/

/-- An element with its local name, attributes (names as written), element
children, and the concatenation of its character data. -/
inductive El where
  | mk (tag : String) (attrs : List (String × String)) (kids : List El) (text : String)

def localTag (s : String) : String :=
  match s.splitOn ":" with
  | [_, l] => l
  | _      => s

def textOfNodes (ns : List Node) : String :=
  String.join (ns.filterMap (fun n => match n with
    | .text t  => some t
    | .cdata t => some t
    | _ => none))

mutual

def elOf : Node → Option El
  | .element tag attrs children =>
      some (El.mk (localTag tag) (attrs.map (fun a => (a.name, a.value)))
              (elsOf children) (textOfNodes children))
  | _ => none

def elsOf : List Node → List El
  | [] => []
  | n :: rest =>
      match elOf n with
      | some e => e :: elsOf rest
      | none   => elsOf rest

end

def El.tag : El → String
  | .mk t _ _ _ => t

def El.attr (e : El) (name : String) : Option String :=
  match e with
  | .mk _ attrs _ _ => (attrs.find? (fun p => p.1 == name)).map (·.2)

def El.text : El → String
  | .mk _ _ _ t => t

/-! ## The environment: base IRI and prefixes -/

structure Env where
  base : Option String
  pfx  : List (String × String)

def Env.resolve (env : Env) (ref : String) : Option WfIri :=
  L4Factoidal.OWL.FS.mkIri (L4Factoidal.Syntax.resolveAgainst? env.base ref)

/-- `p:local` through the declared prefixes. -/
def Env.expand (env : Env) (abbrev_ : String) : Option WfIri :=
  match abbrev_.splitOn ":" with
  | pfx :: rest@(_ :: _) =>
      match L4Factoidal.OWL.FS.lookupPfx env.pfx pfx with
      | none => none
      | some ns => L4Factoidal.OWL.FS.mkIri (ns ++ String.intercalate ":" rest)
  | _ => none

/-- Exactly one of `IRI` and `abbreviatedIRI` (section 3.1). -/
def iriOfEl (env : Env) (e : El) : Option WfIri :=
  match e.attr "IRI", e.attr "abbreviatedIRI" with
  | some i, none => env.resolve i
  | none, some a => env.expand a
  | _, _ => none

/-- The IRI carried by an `IRI` or `AbbreviatedIRI` ELEMENT (text content),
used for annotation values and `AnnotationPropertyDomain`. -/
def iriOfText (env : Env) (e : El) : Option WfIri :=
  if e.tag == "IRI" then env.resolve e.text.trim
  else if e.tag == "AbbreviatedIRI" then env.expand e.text.trim
  else none

/-! ## Leaves -/

/-- A named entity element of tag `tag`. -/
def entityIri (env : Env) (tag : String) (e : El) : Option WfIri :=
  if e.tag == tag then iriOfEl env e else none

def readLiteral (env : Env) (e : El) : Option WfLiteral :=
  if e.tag != "Literal" then none
  else match e.attr "xml:lang" with
    | some lang => some (Literal.langString e.text lang)
    | none =>
      match e.attr "datatypeIRI" with
      | none => some (Literal.string e.text)
      | some dt =>
          match env.resolve dt with
          | none => none
          | some d => L4Factoidal.OWL.FS.mkLiteral e.text d none

def readIndividual (env : Env) (e : El) : Option Individual :=
  if e.tag == "NamedIndividual" then (iriOfEl env e).map Individual.named
  else if e.tag == "AnonymousIndividual" then (e.attr "nodeID").map Individual.anon
  else none

def readOPE (env : Env) : El → Option ObjPropExpr
  | .mk "ObjectProperty" attrs kids text =>
      (iriOfEl env (.mk "ObjectProperty" attrs kids text)).map ObjPropExpr.prop
  | .mk "ObjectInverseOf" _ [p] _ => (entityIri env "ObjectProperty" p).map ObjPropExpr.inverse
  | _ => none

def readList {α : Type} (f : El → Option α) : List El → Option (List α)
  | [] => some []
  | e :: es =>
      match f e with
      | none => none
      | some a => (readList f es).map (fun r => a :: r)

/-- The value of an annotation: an `IRI`/`AbbreviatedIRI` element, an
anonymous individual or a literal. -/
def readAnnValue (env : Env) (e : El) : Option AnnValue :=
  match iriOfText env e with
  | some i => some (.iri i)
  | none =>
    if e.tag == "AnonymousIndividual" then (e.attr "nodeID").map AnnValue.anon
    else (readLiteral env e).map AnnValue.lit

/-! ## Data ranges, class expressions, annotations -/

mutual

def readDR (env : Env) : El → Option DataRange
  | .mk "Datatype" attrs kids text =>
      (iriOfEl env (.mk "Datatype" attrs kids text)).map DataRange.datatype
  | .mk "DataIntersectionOf" _ kids _ =>
      match readDRs env kids with
      | some drs => if drs.length < 2 then none else some (.intersection drs)
      | none => none
  | .mk "DataUnionOf" _ kids _ =>
      match readDRs env kids with
      | some drs => if drs.length < 2 then none else some (.union drs)
      | none => none
  | .mk "DataComplementOf" _ [d] _ => (readDR env d).map DataRange.complement
  | .mk "DataOneOf" _ kids _ =>
      match readList (readLiteral env) kids with
      | some lits => if lits.isEmpty then none else some (.oneOf lits)
      | none => none
  | .mk "DatatypeRestriction" _ (dt :: facets) _ =>
      match entityIri env "Datatype" dt, readFacets env facets with
      | some d, some fs => if fs.isEmpty then none else some (.restriction d fs)
      | _, _ => none
  | _ => none

def readDRs (env : Env) : List El → Option (List DataRange)
  | [] => some []
  | e :: es =>
      match readDR env e with
      | none => none
      | some d => (readDRs env es).map (fun r => d :: r)

def readFacets (env : Env) : List El → Option (List (WfIri × WfLiteral))
  | [] => some []
  | .mk "FacetRestriction" attrs [lit] _ :: rest =>
      match attrs.find? (fun p => p.1 == "facet") with
      | none => none
      | some (_, f) =>
        match env.resolve f, readLiteral env lit, readFacets env rest with
        | some fi, some l, some r => some ((fi, l) :: r)
        | _, _, _ => none
  | _ => none

def readCE (env : Env) : El → Option ClassExpr
  | .mk "Class" attrs kids text =>
      (iriOfEl env (.mk "Class" attrs kids text)).map ClassExpr.cls
  | .mk "ObjectIntersectionOf" _ kids _ =>
      match readCEs env kids with
      | some ces => if ces.length < 2 then none else some (.intersection ces)
      | none => none
  | .mk "ObjectUnionOf" _ kids _ =>
      match readCEs env kids with
      | some ces => if ces.length < 2 then none else some (.union ces)
      | none => none
  | .mk "ObjectComplementOf" _ [c] _ => (readCE env c).map ClassExpr.complement
  | .mk "ObjectOneOf" _ kids _ =>
      match readList (readIndividual env) kids with
      | some inds => if inds.isEmpty then none else some (.oneOf inds)
      | none => none
  | .mk "ObjectSomeValuesFrom" _ [o, c] _ =>
      match readOPE env o, readCE env c with
      | some p, some ce => some (.someValuesFrom p ce)
      | _, _ => none
  | .mk "ObjectAllValuesFrom" _ [o, c] _ =>
      match readOPE env o, readCE env c with
      | some p, some ce => some (.allValuesFrom p ce)
      | _, _ => none
  | .mk "ObjectHasValue" _ [o, a] _ =>
      match readOPE env o, readIndividual env a with
      | some p, some ind => some (.hasValue p ind)
      | _, _ => none
  | .mk "ObjectHasSelf" _ [o] _ => (readOPE env o).map ClassExpr.hasSelf
  | .mk "ObjectMinCardinality" attrs kids _ => readObjCard env attrs kids ClassExpr.minCard
  | .mk "ObjectMaxCardinality" attrs kids _ => readObjCard env attrs kids ClassExpr.maxCard
  | .mk "ObjectExactCardinality" attrs kids _ => readObjCard env attrs kids ClassExpr.exactCard
  | .mk "DataSomeValuesFrom" _ kids _ =>
      match readDataFrom env kids with
      | some (ps, d) => some (.dataSomeValuesFrom ps d)
      | none => none
  | .mk "DataAllValuesFrom" _ kids _ =>
      match readDataFrom env kids with
      | some (ps, d) => some (.dataAllValuesFrom ps d)
      | none => none
  | .mk "DataHasValue" _ [p, l] _ =>
      match entityIri env "DataProperty" p, readLiteral env l with
      | some dp, some lit => some (.dataHasValue dp lit)
      | _, _ => none
  | .mk "DataMinCardinality" attrs kids _ => readDataCard env attrs kids ClassExpr.dataMinCard
  | .mk "DataMaxCardinality" attrs kids _ => readDataCard env attrs kids ClassExpr.dataMaxCard
  | .mk "DataExactCardinality" attrs kids _ => readDataCard env attrs kids ClassExpr.dataExactCard
  | _ => none

def readCEs (env : Env) : List El → Option (List ClassExpr)
  | [] => some []
  | e :: es =>
      match readCE env e with
      | none => none
      | some c => (readCEs env es).map (fun r => c :: r)

/-- `ObjectMinCardinality cardinality="n"` and friends: the property, then
an optional class expression. -/
def readObjCard (env : Env) (attrs : List (String × String)) (kids : List El)
    (mk : Nat → ObjPropExpr → Option ClassExpr → ClassExpr) : Option ClassExpr :=
  match attrs.find? (fun p => p.1 == "cardinality") with
  | none => none
  | some (_, n) =>
    if n.isEmpty || !n.all Char.isDigit then none else
    match kids with
    | [o] => (readOPE env o).map (fun p => mk n.toNat! p none)
    | [o, c] =>
        match readOPE env o, readCE env c with
        | some p, some ce => some (mk n.toNat! p (some ce))
        | _, _ => none
    | _ => none

def readDataCard (env : Env) (attrs : List (String × String)) (kids : List El)
    (mk : Nat → WfIri → Option DataRange → ClassExpr) : Option ClassExpr :=
  match attrs.find? (fun p => p.1 == "cardinality") with
  | none => none
  | some (_, n) =>
    if n.isEmpty || !n.all Char.isDigit then none else
    match kids with
    | [p] => (entityIri env "DataProperty" p).map (fun dp => mk n.toNat! dp none)
    | [p, d] =>
        match entityIri env "DataProperty" p, readDR env d with
        | some dp, some dr => some (mk n.toNat! dp (some dr))
        | _, _ => none
    | _ => none

/-- `DataPropertyExpression+ DataRange`: the properties are every child but
the last; the last is the data range. -/
def readDataFrom (env : Env) (kids : List El) : Option (List WfIri × DataRange) :=
  match kids.reverse with
  | [] => none
  | last :: revProps =>
      match readDR env last, readList (entityIri env "DataProperty") revProps.reverse with
      | some d, some ps => if ps.isEmpty then none else some (ps, d)
      | _, _ => none

/-- One `Annotation` element: annotations of the annotation first, then the
property, then the value. -/
def readAnnotation (env : Env) : El → Option Annotation
  | .mk "Annotation" _ kids _ => readAnnTail env [] kids
  | _ => none

/-- The children of an `Annotation`: leading `Annotation` elements are
collected into `acc`; the last two children are the property and the
value. -/
def readAnnTail (env : Env) (acc : List Annotation) : List El → Option Annotation
  | .mk "Annotation" a k t :: rest =>
      match readAnnotation env (.mk "Annotation" a k t) with
      | none => none
      | some x => readAnnTail env (acc ++ [x]) rest
  | [p, v] =>
      match entityIri env "AnnotationProperty" p, readAnnValue env v with
      | some ap, some av => some (.mk acc ap av)
      | _, _ => none
  | _ => none

def readAnnotations (env : Env) : List El → Option (List Annotation)
  | [] => some []
  | e :: es =>
      match readAnnotation env e with
      | none => none
      | some a => (readAnnotations env es).map (fun r => a :: r)

end

/-! ## Axioms -/

def isAnn (e : El) : Bool := e.tag == "Annotation"

def entityKindOfTag : String → Option EntityKind
  | "Class"              => some .cls
  | "Datatype"           => some .datatype
  | "ObjectProperty"     => some .objectProperty
  | "DataProperty"       => some .dataProperty
  | "AnnotationProperty" => some .annotationProperty
  | "NamedIndividual"    => some .namedIndividual
  | _ => none

def charOfTag : String → Option ObjPropChar
  | "FunctionalObjectProperty"        => some .functional
  | "InverseFunctionalObjectProperty" => some .inverseFunctional
  | "ReflexiveObjectProperty"         => some .reflexive
  | "IrreflexiveObjectProperty"       => some .irreflexive
  | "SymmetricObjectProperty"         => some .symmetric
  | "AsymmetricObjectProperty"        => some .asymmetric
  | "TransitiveObjectProperty"        => some .transitive
  | _ => none

/-- The axiom the element `tag` with annotations `anns` and operands `args`
denotes. -/
def readAxiomBody (env : Env) (tag : String) (anns : List Annotation) (args : List El) :
    Option Axiom :=
  match tag, args with
  | "Declaration", [e] =>
      match entityKindOfTag e.tag, iriOfEl env e with
      | some k, some i => some (.declaration anns k i)
      | _, _ => none
  | "SubClassOf", [a, b] =>
      match readCE env a, readCE env b with
      | some x, some y => some (.subClassOf anns x y)
      | _, _ => none
  | "EquivalentClasses", _ =>
      match readCEs env args with
      | some ces => if ces.length < 2 then none else some (.equivalentClasses anns ces)
      | none => none
  | "DisjointClasses", _ =>
      match readCEs env args with
      | some ces => if ces.length < 2 then none else some (.disjointClasses anns ces)
      | none => none
  | "DisjointUnion", c :: rest =>
      match entityIri env "Class" c, readCEs env rest with
      | some ci, some ces => if ces.length < 2 then none else some (.disjointUnion anns ci ces)
      | _, _ => none
  | "SubObjectPropertyOf", [.mk "ObjectPropertyChain" _ chain _, b] =>
      match readList (readOPE env) chain, readOPE env b with
      | some os, some sup => if os.length < 2 then none else some (.subObjectPropertyOf anns (.chain os) sup)
      | _, _ => none
  | "SubObjectPropertyOf", [a, b] =>
      match readOPE env a, readOPE env b with
      | some x, some y => some (.subObjectPropertyOf anns (.single x) y)
      | _, _ => none
  | "EquivalentObjectProperties", _ =>
      match readList (readOPE env) args with
      | some os => if os.length < 2 then none else some (.equivalentObjectProperties anns os)
      | none => none
  | "DisjointObjectProperties", _ =>
      match readList (readOPE env) args with
      | some os => if os.length < 2 then none else some (.disjointObjectProperties anns os)
      | none => none
  | "InverseObjectProperties", [a, b] =>
      match readOPE env a, readOPE env b with
      | some x, some y => some (.inverseObjectProperties anns x y)
      | _, _ => none
  | "ObjectPropertyDomain", [o, c] =>
      match readOPE env o, readCE env c with
      | some p, some ce => some (.objectPropertyDomain anns p ce)
      | _, _ => none
  | "ObjectPropertyRange", [o, c] =>
      match readOPE env o, readCE env c with
      | some p, some ce => some (.objectPropertyRange anns p ce)
      | _, _ => none
  | "SubDataPropertyOf", [a, b] =>
      match entityIri env "DataProperty" a, entityIri env "DataProperty" b with
      | some x, some y => some (.subDataPropertyOf anns x y)
      | _, _ => none
  | "EquivalentDataProperties", _ =>
      match readList (entityIri env "DataProperty") args with
      | some ps => if ps.length < 2 then none else some (.equivalentDataProperties anns ps)
      | none => none
  | "DisjointDataProperties", _ =>
      match readList (entityIri env "DataProperty") args with
      | some ps => if ps.length < 2 then none else some (.disjointDataProperties anns ps)
      | none => none
  | "DataPropertyDomain", [p, c] =>
      match entityIri env "DataProperty" p, readCE env c with
      | some dp, some ce => some (.dataPropertyDomain anns dp ce)
      | _, _ => none
  | "DataPropertyRange", [p, d] =>
      match entityIri env "DataProperty" p, readDR env d with
      | some dp, some dr => some (.dataPropertyRange anns dp dr)
      | _, _ => none
  | "FunctionalDataProperty", [p] =>
      (entityIri env "DataProperty" p).map (fun dp => .functionalDataProperty anns dp)
  | "DatatypeDefinition", [t, d] =>
      match entityIri env "Datatype" t, readDR env d with
      | some dt, some dr => some (.datatypeDefinition anns dt dr)
      | _, _ => none
  | "HasKey", c :: rest =>
      -- the object properties come first, then the data properties
      let objs := rest.takeWhile (fun e => e.tag == "ObjectProperty" || e.tag == "ObjectInverseOf")
      let datas := rest.dropWhile (fun e => e.tag == "ObjectProperty" || e.tag == "ObjectInverseOf")
      match readCE env c, readList (readOPE env) objs,
            readList (entityIri env "DataProperty") datas with
      | some ce, some os, some ds => some (.hasKey anns ce os ds)
      | _, _, _ => none
  | "SameIndividual", _ =>
      match readList (readIndividual env) args with
      | some xs => if xs.length < 2 then none else some (.sameIndividual anns xs)
      | none => none
  | "DifferentIndividuals", _ =>
      match readList (readIndividual env) args with
      | some xs => if xs.length < 2 then none else some (.differentIndividuals anns xs)
      | none => none
  | "ClassAssertion", [c, a] =>
      match readCE env c, readIndividual env a with
      | some ce, some ind => some (.classAssertion anns ce ind)
      | _, _ => none
  | "ObjectPropertyAssertion", [o, a, b] =>
      match readOPE env o, readIndividual env a, readIndividual env b with
      | some p, some x, some y => some (.objectPropertyAssertion anns p x y)
      | _, _, _ => none
  | "NegativeObjectPropertyAssertion", [o, a, b] =>
      match readOPE env o, readIndividual env a, readIndividual env b with
      | some p, some x, some y => some (.negativeObjectPropertyAssertion anns p x y)
      | _, _, _ => none
  | "DataPropertyAssertion", [p, a, l] =>
      match entityIri env "DataProperty" p, readIndividual env a, readLiteral env l with
      | some dp, some x, some lit => some (.dataPropertyAssertion anns dp x lit)
      | _, _, _ => none
  | "NegativeDataPropertyAssertion", [p, a, l] =>
      match entityIri env "DataProperty" p, readIndividual env a, readLiteral env l with
      | some dp, some x, some lit => some (.negativeDataPropertyAssertion anns dp x lit)
      | _, _, _ => none
  | "AnnotationAssertion", [p, s, v] =>
      -- the subject is an IRI element or an anonymous individual
      let subj : Option Individual :=
        match iriOfText env s with
        | some i => some (.named i)
        | none => if s.tag == "AnonymousIndividual" then (s.attr "nodeID").map Individual.anon else none
      match entityIri env "AnnotationProperty" p, subj, readAnnValue env v with
      | some ap, some sj, some av => some (.annotationAssertion anns ap sj av)
      | _, _, _ => none
  | "SubAnnotationPropertyOf", [a, b] =>
      match entityIri env "AnnotationProperty" a, entityIri env "AnnotationProperty" b with
      | some x, some y => some (.subAnnotationPropertyOf anns x y)
      | _, _ => none
  | "AnnotationPropertyDomain", [p, u] =>
      match entityIri env "AnnotationProperty" p, iriOfText env u with
      | some ap, some d => some (.annotationPropertyDomain anns ap d)
      | _, _ => none
  | "AnnotationPropertyRange", [p, u] =>
      match entityIri env "AnnotationProperty" p, iriOfText env u with
      | some ap, some d => some (.annotationPropertyRange anns ap d)
      | _, _ => none
  | _, [o] =>
      match charOfTag tag with
      | some ch => (readOPE env o).map (fun p => .objectPropertyCharacteristic anns ch p)
      | none => none
  | _, _ => none

def readAxiom (env : Env) (e : El) : Option Axiom :=
  match e with
  | .mk tag _ kids _ =>
      let annEls := kids.takeWhile isAnn
      let args := kids.dropWhile isAnn
      match readAnnotations env annEls with
      | none => none
      | some anns => readAxiomBody env tag anns args

def readAxioms (env : Env) : List El → Option (List Axiom)
  | [] => some []
  | e :: es =>
      match readAxiom env e with
      | none => none
      | some a => (readAxioms env es).map (fun r => a :: r)

/-! ## The ontology -/

/-- `Prefix name="p" IRI="..."` children. -/
def readPrefixes : List El → List (String × String)
  | [] => []
  | .mk "Prefix" attrs _ _ :: rest =>
      match attrs.find? (fun p => p.1 == "name"), attrs.find? (fun p => p.1 == "IRI") with
      | some (_, n), some (_, i) => (n, i) :: readPrefixes rest
      | _, _ => readPrefixes rest
  | _ :: rest => readPrefixes rest

def readOntologyEl (e : El) : Option Ontology :=
  match e with
  | .mk "Ontology" attrs kids _ =>
      let base := (attrs.find? (fun p => p.1 == "xml:base")).map (·.2)
      let env : Env := { base := base,
                         pfx := readPrefixes kids ++ L4Factoidal.OWL.FS.defaultPrefixes }
      let imports := kids.filter (fun k => k.tag == "Import")
      let afterPrefix := kids.filter (fun k => k.tag != "Prefix" && k.tag != "Import")
      let annEls := afterPrefix.takeWhile isAnn
      let axEls := afterPrefix.dropWhile isAnn
      let iri : Option (Option WfIri) :=
        match attrs.find? (fun p => p.1 == "ontologyIRI") with
        | none => some none
        | some (_, v) => (env.resolve v).map some
      let ver : Option (Option WfIri) :=
        match attrs.find? (fun p => p.1 == "versionIRI") with
        | none => some none
        | some (_, v) => (env.resolve v).map some
      match iri, ver, readList (fun i => env.resolve i.text.trim) imports,
            readAnnotations env annEls, readAxioms env axEls with
      | some o, some v, some imps, some anns, some axs =>
          -- a version IRI needs an ontology IRI (Structural Specification 3.1)
          if v.isSome && o.isNone then none
          else some { iri := o, versionIri := v, imports := imps,
                      annotations := anns, axioms := axs }
      | _, _, _, _, _ => none
  | _ => none

/-- Read an OWL/XML document. `none` for anything the schema does not
accept, including a document the XML parser rejects. -/
def parseOwlXml (input : String) : Option Ontology :=
  match parseXML input with
  | .error _ => none
  | .ok doc =>
      match elOf doc.root with
      | none => none
      | some e => readOntologyEl e

/-- An OWL/XML document as RDF triples. -/
def parseOwlXmlGraph (input : String) : Option (List Triple) :=
  (parseOwlXml input).map Ontology.toGraph

end L4Factoidal.OWL.OwlXml
