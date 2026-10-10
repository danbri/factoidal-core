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
import L4Factoidal.ListTR

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

/- The children of an element are read by an accumulator walk
(`elsOfAcc`): the self-call is in tail position, so it compiles to a loop
and the number of children (the axioms of an `Ontology` element) costs no
stack. Only the nesting of elements (`elOf` → `elsOfAcc` → `elOf`) takes a
frame per level. `elsOf_eq` states the result as `List.filterMap elOf`
(https://github.com/danbri/factoidal/issues/746). -/
mutual

def elOf : Node → Option El
  | .element tag attrs children =>
      some (El.mk (localTag tag) (attrs.map (fun a => (a.name, a.value)))
              (elsOfAcc children []) (textOfNodes children))
  | _ => none

/-- The elements among `ns`, after `acc` (which holds earlier ones, newest
first). -/
def elsOfAcc : List Node → List El → List El
  | [], acc => acc.reverse
  | n :: rest, acc =>
      match elOf n with
      | some e => elsOfAcc rest (e :: acc)
      | none   => elsOfAcc rest acc

end

/-- The element children of a node list, in document order. -/
def elsOf (ns : List Node) : List El := elsOfAcc ns []

theorem elsOfAcc_eq (ns : List Node) :
    ∀ acc : List El, elsOfAcc ns acc = acc.reverse ++ ns.filterMap elOf := by
  induction ns with
  | nil => intro acc; simp [elsOfAcc]
  | cons n rest ih =>
      intro acc
      cases h : elOf n with
      | none => simp [elsOfAcc, h, ih]
      | some e => simp [elsOfAcc, h, ih]

theorem elsOf_eq (ns : List Node) : elsOf ns = ns.filterMap elOf := by
  simp [elsOf, elsOfAcc_eq]

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

/-- `readList` as `List.mapM` in `Option`, which compiles to a loop: one
frame for any number of operands (`readList` conses after its recursive
call). The `csimp` theorem makes the compiler emit this form. -/
def readListTR {α : Type} (f : El → Option α) (es : List El) : Option (List α) :=
  es.mapM f

theorem readList_eq_mapM {α : Type} (f : El → Option α) :
    ∀ es : List El, readList f es = es.mapM f
  | [] => rfl
  | e :: es => by
      rw [L4Factoidal.ListTR.optionMapM_cons, ← readList_eq_mapM f es]
      simp only [readList]; cases f e <;> rfl

@[csimp] theorem readList_eq_readListTR : @readList = @readListTR := by
  funext α f es; exact readList_eq_mapM f es

/-- One `FacetRestriction` element. -/
def readFacet (env : Env) : El → Option (WfIri × WfLiteral)
  | .mk "FacetRestriction" attrs [lit] _ =>
      match attrs.find? (fun p => p.1 == "facet") with
      | none => none
      | some (_, f) =>
        match env.resolve f, readLiteral env lit with
        | some fi, some l => some (fi, l)
        | _, _ => none
  | _ => none

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

/-- `readFacets` as `List.mapM readFacet` (a loop). -/
def readFacetsTR (env : Env) (es : List El) : Option (List (WfIri × WfLiteral)) :=
  es.mapM (readFacet env)

theorem readFacets_cons (env : Env) (e : El) (es : List El) :
    readFacets env (e :: es) =
      (readFacet env e).bind (fun a => (readFacets env es).map (a :: ·)) := by
  rcases e with ⟨t, attrs, kids, text⟩
  by_cases ht : t = "FacetRestriction"
  · subst ht
    match kids with
    | [lit] =>
        simp only [readFacets, readFacet]
        cases attrs.find? (fun p => p.1 == "facet") with
        | none => rfl
        | some p =>
            obtain ⟨_, f⟩ := p
            simp only
            cases h1 : env.resolve f <;> cases h2 : readLiteral env lit <;>
              cases h3 : readFacets env es <;> simp [h1, h2, h3]
    | [] => simp [readFacets, readFacet]
    | _ :: _ :: _ => simp [readFacets, readFacet]
  · simp [readFacets, readFacet, ht]

theorem readFacets_eq_mapM (env : Env) :
    ∀ es : List El, readFacets env es = es.mapM (readFacet env)
  | [] => rfl
  | e :: es => by
      rw [L4Factoidal.ListTR.optionMapM_cons, readFacets_cons, readFacets_eq_mapM env es]

@[csimp] theorem readFacets_eq_readFacetsTR : @readFacets = @readFacetsTR := by
  funext env es; exact readFacets_eq_mapM env es

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
      match readDRsAcc env kids [] with
      | some drs => if drs.length < 2 then none else some (.intersection drs)
      | none => none
  | .mk "DataUnionOf" _ kids _ =>
      match readDRsAcc env kids [] with
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

/-- The operands of a data range, after `acc` (earlier ones, newest
first). The self-call is a tail call: one frame for any number of
operands. `readDRs_eq_mapM` states the result. -/
def readDRsAcc (env : Env) : List El → List DataRange → Option (List DataRange)
  | [], acc => some acc.reverse
  | e :: es, acc =>
      match readDR env e with
      | none => none
      | some d => readDRsAcc env es (d :: acc)

def readCE (env : Env) : El → Option ClassExpr
  | .mk "Class" attrs kids text =>
      (iriOfEl env (.mk "Class" attrs kids text)).map ClassExpr.cls
  | .mk "ObjectIntersectionOf" _ kids _ =>
      match readCEsAcc env kids [] with
      | some ces => if ces.length < 2 then none else some (.intersection ces)
      | none => none
  | .mk "ObjectUnionOf" _ kids _ =>
      match readCEsAcc env kids [] with
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

/-- The operands of a class expression, after `acc` (earlier ones, newest
first); a tail call per operand. `readCEs_eq_mapM` states the result. -/
def readCEsAcc (env : Env) : List El → List ClassExpr → Option (List ClassExpr)
  | [], acc => some acc.reverse
  | e :: es, acc =>
      match readCE env e with
      | none => none
      | some c => readCEsAcc env es (c :: acc)

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

end

/-- The operands of a data range, in document order. -/
def readDRs (env : Env) (es : List El) : Option (List DataRange) := readDRsAcc env es []

theorem readDRsAcc_eq (env : Env) (es : List El) :
    ∀ acc : List DataRange,
      readDRsAcc env es acc = (es.mapM (readDR env)).map (acc.reverse ++ ·) := by
  induction es with
  | nil => intro acc; simp [readDRsAcc]
  | cons e es ih =>
      intro acc
      rw [L4Factoidal.ListTR.optionMapM_cons]
      simp only [readDRsAcc]
      cases readDR env e with
      | none => rfl
      | some d => simp only [Option.bind_some]; rw [ih]; cases es.mapM (readDR env) <;> simp

theorem readDRs_eq_mapM (env : Env) (es : List El) : readDRs env es = es.mapM (readDR env) := by
  simp [readDRs, readDRsAcc_eq]

/-- The operands of a class expression or axiom, in document order. -/
def readCEs (env : Env) (es : List El) : Option (List ClassExpr) := readCEsAcc env es []

theorem readCEsAcc_eq (env : Env) (es : List El) :
    ∀ acc : List ClassExpr,
      readCEsAcc env es acc = (es.mapM (readCE env)).map (acc.reverse ++ ·) := by
  induction es with
  | nil => intro acc; simp [readCEsAcc]
  | cons e es ih =>
      intro acc
      rw [L4Factoidal.ListTR.optionMapM_cons]
      simp only [readCEsAcc]
      cases readCE env e with
      | none => rfl
      | some c => simp only [Option.bind_some]; rw [ih]; cases es.mapM (readCE env) <;> simp

theorem readCEs_eq_mapM (env : Env) (es : List El) : readCEs env es = es.mapM (readCE env) := by
  simp [readCEs, readCEsAcc_eq]

def readAnnotations (env : Env) : List El → Option (List Annotation)
  | [] => some []
  | e :: es =>
      match readAnnotation env e with
      | none => none
      | some a => (readAnnotations env es).map (fun r => a :: r)

/-- `readAnnotations` as `List.mapM` (a loop). -/
def readAnnotationsTR (env : Env) (es : List El) : Option (List Annotation) :=
  es.mapM (readAnnotation env)

theorem readAnnotations_eq_mapM (env : Env) :
    ∀ es : List El, readAnnotations env es = es.mapM (readAnnotation env)
  | [] => rfl
  | e :: es => by
      rw [L4Factoidal.ListTR.optionMapM_cons, ← readAnnotations_eq_mapM env es]
      simp only [readAnnotations]; cases readAnnotation env e <;> rfl

@[csimp] theorem readAnnotations_eq_readAnnotationsTR :
    @readAnnotations = @readAnnotationsTR := by
  funext env es; exact readAnnotations_eq_mapM env es

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

/-- `readAxioms` as `List.mapM` (a loop): one frame for any number of
axioms. `readAxioms` conses after its recursive call, one frame per axiom
of the document. -/
def readAxiomsTR (env : Env) (es : List El) : Option (List Axiom) :=
  es.mapM (readAxiom env)

theorem readAxioms_eq_mapM (env : Env) :
    ∀ es : List El, readAxioms env es = es.mapM (readAxiom env)
  | [] => rfl
  | e :: es => by
      rw [L4Factoidal.ListTR.optionMapM_cons, ← readAxioms_eq_mapM env es]
      simp only [readAxioms]; cases readAxiom env e <;> rfl

@[csimp] theorem readAxioms_eq_readAxiomsTR : @readAxioms = @readAxiomsTR := by
  funext env es; exact readAxioms_eq_mapM env es

/-! ## The ontology -/

/-- `Prefix name="p" IRI="..."` children. -/
def readPrefixes : List El → List (String × String)
  | [] => []
  | .mk "Prefix" attrs _ _ :: rest =>
      match attrs.find? (fun p => p.1 == "name"), attrs.find? (fun p => p.1 == "IRI") with
      | some (_, n), some (_, i) => (n, i) :: readPrefixes rest
      | _, _ => readPrefixes rest
  | _ :: rest => readPrefixes rest

/-- One `Prefix` element. -/
def readPrefix : El → Option (String × String)
  | .mk "Prefix" attrs _ _ =>
      match attrs.find? (fun p => p.1 == "name"), attrs.find? (fun p => p.1 == "IRI") with
      | some (_, n), some (_, i) => some (n, i)
      | _, _ => none
  | _ => none

/-- `readPrefixes` as `List.filterMap` (a loop). -/
def readPrefixesTR (es : List El) : List (String × String) := es.filterMap readPrefix

theorem readPrefixes_eq_filterMap : ∀ es : List El, readPrefixes es = es.filterMap readPrefix
  | [] => rfl
  | e :: es => by
      rcases e with ⟨t, attrs, kids, text⟩
      by_cases ht : t = "Prefix"
      · subst ht
        simp only [readPrefixes, readPrefix, List.filterMap_cons, readPrefixes_eq_filterMap es]
        cases attrs.find? (fun p => p.1 == "name") <;>
          cases attrs.find? (fun p => p.1 == "IRI") <;> rfl
      · simp [readPrefixes, readPrefix, ht, readPrefixes_eq_filterMap es]

@[csimp] theorem readPrefixes_eq_readPrefixesTR : @readPrefixes = @readPrefixesTR := by
  funext es; exact readPrefixes_eq_filterMap es

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
