/-
L4Factoidal.OWL.StructureRdf — the mapping from the structural
specification to RDF graphs.

Spec: OWL 2 Web Ontology Language Mapping to RDF Graphs (Second Edition),
https://www.w3.org/TR/owl2-mapping-to-rdf/ section 2:

  * 2.1 Table 1, the operator T (ontology header, declarations, class
    expressions, data ranges, axioms, sequences);
  * 2.2 Table 2, the operator TANN (annotations);
  * 2.3 translation of axioms with annotations: 2.3.1 an axiom with a
    single main triple is followed by an `owl:Axiom` node reifying the
    main triple; 2.3.2 `EquivalentClasses`, `EquivalentObjectProperties`,
    `EquivalentDataProperties` and `SameIndividual` are split into pairs
    and each pair is reified; 2.3.3 an axiom already represented by a
    blank node (`DisjointClasses` with more than two classes,
    `NegativeObjectPropertyAssertion`, ...) carries its annotations on
    that node.

## Blank nodes

"Each generated blank node is fresh in each application of a mapping
rule" (section 2.1). A counter threads through the whole translation;
a label is a family tag followed by the counter value (`owlfs_restr0`).
The ontology-header node of an ontology without an IRI has the fixed
label `owlfs_ontology`: there is one per document. Anonymous individuals
keep their node ID under the prefix `owlfs_anon_`.

Everything here is structural recursion: over the nested inductive types
of `Structure.lean` by mutual definitions, and over lists.
-/
import L4Factoidal.OWL.Structure
import L4Factoidal.RDF.Graph

namespace L4Factoidal.OWL.Struct

open L4Factoidal.RDF

/-! ## Vocabulary -/

private def nsRdfIri  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
private def nsRdfsIri : String := "http://www.w3.org/2000/01/rdf-schema#"
private def nsOwlIri  : String := "http://www.w3.org/2002/07/owl#"
private def nsXsdIri  : String := "http://www.w3.org/2001/XMLSchema#"

/-- An IRI of the RDF namespace. The default argument proves well-
formedness for the literal name at each call site, so a mistyped name is
a build error. -/
private def rdfI (s : String) (h : isIri (nsRdfIri ++ s) = true := by rfl) : WfIri :=
  ⟨nsRdfIri ++ s, h⟩
private def rdfsI (s : String) (h : isIri (nsRdfsIri ++ s) = true := by rfl) : WfIri :=
  ⟨nsRdfsIri ++ s, h⟩
private def owlI (s : String) (h : isIri (nsOwlIri ++ s) = true := by rfl) : WfIri :=
  ⟨nsOwlIri ++ s, h⟩
private def xsdI (s : String) (h : isIri (nsXsdIri ++ s) = true := by rfl) : WfIri :=
  ⟨nsXsdIri ++ s, h⟩

/-! ## The state of one translation -/

/-- The fresh-label counter and the triples produced so far, in order. -/
structure MS where
  bc  : Nat := 0
  out : Array Triple := #[]

def MS.add (st : MS) (t : Triple) : MS := { st with out := st.out.push t }

def MS.addAll (st : MS) (ts : List Triple) : MS :=
  ts.foldl (fun s t => s.add t) st

/-- A fresh blank node in the family `tag`. -/
def MS.fresh (st : MS) (tag : String) : Subject × MS :=
  (.bnode (tag ++ toString st.bc), { st with bc := st.bc + 1 })

def subjTerm : Subject → Term
  | .iri i   => .iri i
  | .bnode b => .bnode b

/-! ## Literals — Table 1, rows for `lt`

`"abc@langTag"^^rdf:PlainLiteral` maps to `"abc"@langTag`, and
`"abc@"^^rdf:PlainLiteral` to `"abc"`; every other literal maps to
itself. -/

/-- Split `abc@lang` at its LAST `@`. -/
def splitPlainLiteral (lex : String) : Option (String × String) :=
  match lex.splitOn "@" with
  | [] => none
  | [_] => none
  | parts =>
      let lang := parts.getLast!
      let text := String.intercalate "@" (parts.take (parts.length - 1))
      some (text, lang)

def mapLiteral (l : WfLiteral) : WfLiteral :=
  if l.val.datatype.val == nsRdfIri ++ "PlainLiteral" then
    match splitPlainLiteral l.val.lexicalForm with
    | none => l
    | some (text, lang) =>
        if lang.isEmpty then Literal.string text else Literal.langString text lang
  else l

/-- `"n"^^xsd:nonNegativeInteger`. -/
def natLiteral (n : Nat) : WfLiteral :=
  ⟨{ lexicalForm := toString n, datatype := xsdI "nonNegativeInteger",
     langTag := none, direction := none }, rfl⟩

/-- `"true"^^xsd:boolean`. -/
def trueLiteral : WfLiteral :=
  ⟨{ lexicalForm := "true", datatype := xsdI "boolean",
     langTag := none, direction := none }, rfl⟩

/-! ## Individuals, property expressions and sequences -/

def mapIndividual : Individual → Subject
  | .named i  => .iri i
  | .anon lbl => .bnode ("owlfs_anon_" ++ lbl)

/-- `T(ObjectInverseOf( OP ))`: a fresh `_:x owl:inverseOf OP`. -/
def mapOPE : ObjPropExpr → MS → Subject × MS
  | .prop p, st => (.iri p, st)
  | .inverse p, st =>
      let (x, st) := st.fresh "owlfs_inv"
      (x, st.add ⟨x, owlI "inverseOf", .iri p⟩)

def mapOPEs : List ObjPropExpr → MS → List Subject × MS
  | [], st => ([], st)
  | o :: os, st =>
      let (a, st) := mapOPE o st
      let (rest, st) := mapOPEs os st
      (a :: rest, st)

/-- `T(SEQ y1 ... yn)`, Table 1: the list cells are allocated head
first in the family `tag`. -/
def mapSeq (tag : String) : List Term → MS → Term × MS
  | [], st => (.iri (rdfI "nil"), st)
  | y :: ys, st =>
      let (x, st) := st.fresh tag
      let (rest, st) := mapSeq tag ys st
      (subjTerm x, st.addAll [⟨x, rdfI "first", y⟩, ⟨x, rdfI "rest", rest⟩])

/-! ## Data ranges and class expressions — Table 1 -/

mutual

def mapDR : DataRange → MS → Subject × MS
  | .datatype dt, st => (.iri dt, st)
  | .intersection drs, st =>
      let (items, st) := mapDRs drs st
      let (x, st) := st.fresh "owlfs_dtint"
      let (l, st) := mapSeq "owlfs_lst" (items.map subjTerm) st
      (x, st.addAll [⟨x, rdfI "type", .iri (rdfsI "Datatype")⟩,
                     ⟨x, owlI "intersectionOf", l⟩])
  | .union drs, st =>
      let (items, st) := mapDRs drs st
      let (x, st) := st.fresh "owlfs_dtuni"
      let (l, st) := mapSeq "owlfs_lst" (items.map subjTerm) st
      (x, st.addAll [⟨x, rdfI "type", .iri (rdfsI "Datatype")⟩,
                     ⟨x, owlI "unionOf", l⟩])
  | .complement dr, st =>
      let (d, st) := mapDR dr st
      let (x, st) := st.fresh "owlfs_dtcomp"
      (x, st.addAll [⟨x, rdfI "type", .iri (rdfsI "Datatype")⟩,
                     ⟨x, owlI "datatypeComplementOf", subjTerm d⟩])
  | .oneOf lits, st =>
      let (l, st) := mapSeq "owlfs_lst" (lits.map (fun v => Term.literal (mapLiteral v))) st
      let (x, st) := st.fresh "owlfs_dtoneof"
      (x, st.addAll [⟨x, rdfI "type", .iri (rdfsI "Datatype")⟩, ⟨x, owlI "oneOf", l⟩])
  | .restriction dt facets, st =>
      -- each (facet, value) pair gets its own node `_:yi Fi lti`
      let (nodes, st) := mapFacets facets st
      let (l, st) := mapSeq "owlfs_flst" (nodes.map subjTerm) st
      let (x, st) := st.fresh "owlfs_dtrestr"
      (x, st.addAll [⟨x, rdfI "type", .iri (rdfsI "Datatype")⟩,
                     ⟨x, owlI "onDatatype", .iri dt⟩, ⟨x, owlI "withRestrictions", l⟩])

def mapDRs : List DataRange → MS → List Subject × MS
  | [], st => ([], st)
  | d :: ds, st =>
      let (a, st) := mapDR d st
      let (rest, st) := mapDRs ds st
      (a :: rest, st)

def mapFacets : List (WfIri × WfLiteral) → MS → List Subject × MS
  | [], st => ([], st)
  | (f, v) :: fs, st =>
      let (y, st) := st.fresh "owlfs_facet"
      let st := st.add ⟨y, f, .literal (mapLiteral v)⟩
      let (rest, st) := mapFacets fs st
      (y :: rest, st)

end

/-- A restriction node: `_:x rdf:type owl:Restriction` plus `body x`. -/
def restriction (body : Subject → List Triple) (st : MS) : Subject × MS :=
  let (x, st) := st.fresh "owlfs_restr"
  (x, st.addAll (⟨x, rdfI "type", .iri (owlI "Restriction")⟩ :: body x))

/-- `_:x owl:onProperty P`. -/
def onP (p : Subject) (x : Subject) : Triple := ⟨x, owlI "onProperty", subjTerm p⟩

/-- Cardinality restrictions over an object property: the unqualified
row carries the plain predicate, the qualified row the qualified
predicate and `owl:onClass` (Table 1). -/
def objCardinality (plain qualified : WfIri) (n : Nat) (p : Subject)
    (ce : Option Subject) (st : MS) : Subject × MS :=
  match ce with
  | none =>
      restriction (fun x => [onP p x, ⟨x, plain, .literal (natLiteral n)⟩]) st
  | some c =>
      restriction (fun x => [onP p x, ⟨x, qualified, .literal (natLiteral n)⟩,
                             ⟨x, owlI "onClass", subjTerm c⟩]) st

/-- The same for a data property, with `owl:onDataRange`. -/
def dataCardinality (plain qualified : WfIri) (n : Nat) (p : WfIri)
    (dr : Option Subject) (st : MS) : Subject × MS :=
  match dr with
  | none =>
      restriction (fun x => [onP (.iri p) x, ⟨x, plain, .literal (natLiteral n)⟩]) st
  | some d =>
      restriction (fun x => [onP (.iri p) x, ⟨x, qualified, .literal (natLiteral n)⟩,
                             ⟨x, owlI "onDataRange", subjTerm d⟩]) st

/-- `DataSomeValuesFrom( DPE DR )` uses `owl:onProperty`; with two or
more properties `owl:onProperties` and a sequence (Table 1). -/
def dataValuesFrom (rel : WfIri) (dpes : List WfIri) (d : Subject) (st : MS) :
    Subject × MS :=
  match dpes with
  | [p] => restriction (fun x => [onP (.iri p) x, ⟨x, rel, subjTerm d⟩]) st
  | _ =>
      let (l, st) := mapSeq "owlfs_lst" (dpes.map Term.iri) st
      restriction (fun x => [⟨x, owlI "onProperties", l⟩, ⟨x, rel, subjTerm d⟩]) st

mutual

def mapCE : ClassExpr → MS → Subject × MS
  | .cls c, st => (.iri c, st)
  | .intersection ces, st =>
      let (items, st) := mapCEs ces st
      let (x, st) := st.fresh "owlfs_cls"
      let (l, st) := mapSeq "owlfs_lst" (items.map subjTerm) st
      (x, st.addAll [⟨x, rdfI "type", .iri (owlI "Class")⟩, ⟨x, owlI "intersectionOf", l⟩])
  | .union ces, st =>
      let (items, st) := mapCEs ces st
      let (x, st) := st.fresh "owlfs_cls"
      let (l, st) := mapSeq "owlfs_lst" (items.map subjTerm) st
      (x, st.addAll [⟨x, rdfI "type", .iri (owlI "Class")⟩, ⟨x, owlI "unionOf", l⟩])
  | .complement ce, st =>
      let (c, st) := mapCE ce st
      let (x, st) := st.fresh "owlfs_comp"
      (x, st.addAll [⟨x, rdfI "type", .iri (owlI "Class")⟩,
                     ⟨x, owlI "complementOf", subjTerm c⟩])
  | .oneOf inds, st =>
      let (l, st) := mapSeq "owlfs_lst" (inds.map (fun a => subjTerm (mapIndividual a))) st
      let (x, st) := st.fresh "owlfs_cls"
      (x, st.addAll [⟨x, rdfI "type", .iri (owlI "Class")⟩, ⟨x, owlI "oneOf", l⟩])
  | .someValuesFrom ope ce, st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      restriction (fun x => [onP p x, ⟨x, owlI "someValuesFrom", subjTerm c⟩]) st
  | .allValuesFrom ope ce, st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      restriction (fun x => [onP p x, ⟨x, owlI "allValuesFrom", subjTerm c⟩]) st
  | .hasValue ope ind, st =>
      let (p, st) := mapOPE ope st
      restriction (fun x => [onP p x, ⟨x, owlI "hasValue", subjTerm (mapIndividual ind)⟩]) st
  | .hasSelf ope, st =>
      let (p, st) := mapOPE ope st
      restriction (fun x => [onP p x, ⟨x, owlI "hasSelf", .literal trueLiteral⟩]) st
  | .minCard n ope none, st =>
      let (p, st) := mapOPE ope st
      objCardinality (owlI "minCardinality") (owlI "minQualifiedCardinality") n p none st
  | .minCard n ope (some ce), st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      objCardinality (owlI "minCardinality") (owlI "minQualifiedCardinality") n p (some c) st
  | .maxCard n ope none, st =>
      let (p, st) := mapOPE ope st
      objCardinality (owlI "maxCardinality") (owlI "maxQualifiedCardinality") n p none st
  | .maxCard n ope (some ce), st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      objCardinality (owlI "maxCardinality") (owlI "maxQualifiedCardinality") n p (some c) st
  | .exactCard n ope none, st =>
      let (p, st) := mapOPE ope st
      objCardinality (owlI "cardinality") (owlI "qualifiedCardinality") n p none st
  | .exactCard n ope (some ce), st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      objCardinality (owlI "cardinality") (owlI "qualifiedCardinality") n p (some c) st
  | .dataSomeValuesFrom dpes dr, st =>
      let (d, st) := mapDR dr st
      dataValuesFrom (owlI "someValuesFrom") dpes d st
  | .dataAllValuesFrom dpes dr, st =>
      let (d, st) := mapDR dr st
      dataValuesFrom (owlI "allValuesFrom") dpes d st
  | .dataHasValue dp lit, st =>
      restriction (fun x => [onP (.iri dp) x, ⟨x, owlI "hasValue", .literal (mapLiteral lit)⟩]) st
  | .dataMinCard n dp none, st =>
      dataCardinality (owlI "minCardinality") (owlI "minQualifiedCardinality") n dp none st
  | .dataMinCard n dp (some dr), st =>
      let (d, st) := mapDR dr st
      dataCardinality (owlI "minCardinality") (owlI "minQualifiedCardinality") n dp (some d) st
  | .dataMaxCard n dp none, st =>
      dataCardinality (owlI "maxCardinality") (owlI "maxQualifiedCardinality") n dp none st
  | .dataMaxCard n dp (some dr), st =>
      let (d, st) := mapDR dr st
      dataCardinality (owlI "maxCardinality") (owlI "maxQualifiedCardinality") n dp (some d) st
  | .dataExactCard n dp none, st =>
      dataCardinality (owlI "cardinality") (owlI "qualifiedCardinality") n dp none st
  | .dataExactCard n dp (some dr), st =>
      let (d, st) := mapDR dr st
      dataCardinality (owlI "cardinality") (owlI "qualifiedCardinality") n dp (some d) st

def mapCEs : List ClassExpr → MS → List Subject × MS
  | [], st => ([], st)
  | c :: cs, st =>
      let (a, st) := mapCE c st
      let (rest, st) := mapCEs cs st
      (a :: rest, st)

end


/-! ## Annotations — Table 2 -/

def mapAnnValue : AnnValue → Term
  | .iri i  => .iri i
  | .anon l => .bnode ("owlfs_anon_" ++ l)
  | .lit l  => .literal (mapLiteral l)

mutual

/-- `TANN( Annotation( annotations AP av ), y )`:
`y AP av`, and when the annotation is itself annotated, an
`owl:Annotation` node reifying that triple and carrying the inner
annotations. -/
def tann : Annotation → Subject → MS → MS
  | .mk anns p v, y, st =>
      let t := mapAnnValue v
      let st := st.add ⟨y, p, t⟩
      match anns with
      | [] => st
      | _ =>
          let (x, st) := st.fresh "owlfs_ann"
          let st := st.addAll [⟨x, rdfI "type", .iri (owlI "Annotation")⟩,
                               ⟨x, owlI "annotatedSource", subjTerm y⟩,
                               ⟨x, owlI "annotatedProperty", .iri p⟩,
                               ⟨x, owlI "annotatedTarget", t⟩]
          tannList anns x st

def tannList : List Annotation → Subject → MS → MS
  | [], _, st => st
  | a :: rest, y, st => tannList rest y (tann a y st)

end

/-! ## Axioms with annotations — section 2.3 -/

/-- Sections 2.3.1 and 2.3.2: every main triple is output, and when the
axiom is annotated, followed by an `owl:Axiom` node reifying it and
carrying the annotations. Several main triples (`EquivalentClasses` with
more than two members, ...) each get their own node with the annotations
repeated. -/
def reify (anns : List Annotation) (mains : List Triple) (st : MS) : MS :=
  match anns with
  | [] => st.addAll mains
  | _ =>
      mains.foldl (fun st m =>
        let st := st.add m
        let (x, st) := st.fresh "owlfs_axiom"
        let st := st.addAll [⟨x, rdfI "type", .iri (owlI "Axiom")⟩,
                             ⟨x, owlI "annotatedSource", subjTerm m.s⟩,
                             ⟨x, owlI "annotatedProperty", .iri m.p⟩,
                             ⟨x, owlI "annotatedTarget", m.o⟩]
        tannList anns x st) st

/-- The pairs `(a1,a2), (a2,a3), ...` of Table 1's equivalence rows. -/
def adjacent {α : Type} (xs : List α) : List (α × α) := xs.zip xs.tail

/-- Section 2.3.3: an axiom already represented by a blank node carries
its annotations on that node. `kind` is `AllDisjointClasses`,
`AllDisjointProperties` or `AllDifferent`. -/
def allMembers (kind : WfIri) (anns : List Annotation) (items : List Term)
    (st : MS) : MS :=
  let (x, st) := st.fresh "owlfs_all"
  let (l, st) := mapSeq "owlfs_lst" items st
  let st := st.addAll [⟨x, rdfI "type", .iri kind⟩, ⟨x, owlI "members", l⟩]
  tannList anns x st

def entityType : EntityKind → WfIri
  | .cls               => owlI "Class"
  | .datatype          => rdfsI "Datatype"
  | .objectProperty    => owlI "ObjectProperty"
  | .dataProperty      => owlI "DatatypeProperty"
  | .annotationProperty => owlI "AnnotationProperty"
  | .namedIndividual   => owlI "NamedIndividual"

def characteristicType : ObjPropChar → WfIri
  | .functional        => owlI "FunctionalProperty"
  | .inverseFunctional => owlI "InverseFunctionalProperty"
  | .reflexive         => owlI "ReflexiveProperty"
  | .irreflexive       => owlI "IrreflexiveProperty"
  | .symmetric         => owlI "SymmetricProperty"
  | .asymmetric        => owlI "AsymmetricProperty"
  | .transitive        => owlI "TransitiveProperty"

/-- A negative property assertion node (Table 1): the annotations go on
the node. `tgtPred` is `owl:targetIndividual` or `owl:targetValue`. -/
def negativeAssertion (anns : List Annotation) (src : Subject) (prop : Subject)
    (tgtPred : WfIri) (tgt : Term) (st : MS) : MS :=
  let (x, st) := st.fresh "owlfs_npa"
  let st := st.addAll [⟨x, rdfI "type", .iri (owlI "NegativePropertyAssertion")⟩,
                       ⟨x, owlI "sourceIndividual", subjTerm src⟩,
                       ⟨x, owlI "assertionProperty", subjTerm prop⟩,
                       ⟨x, tgtPred, tgt⟩]
  tannList anns x st

/-- `T(axiom)`, Table 1 and section 2.3. -/
def mapAxiom : Axiom → MS → MS
  | .declaration anns k i, st =>
      reify anns [⟨.iri i, rdfI "type", .iri (entityType k)⟩] st
  | .subClassOf anns a b, st =>
      let (x, st) := mapCE a st
      let (y, st) := mapCE b st
      reify anns [⟨x, rdfsI "subClassOf", subjTerm y⟩] st
  | .equivalentClasses anns ces, st =>
      let (xs, st) := mapCEs ces st
      reify anns ((adjacent xs).map (fun (a, b) => ⟨a, owlI "equivalentClass", subjTerm b⟩)) st
  | .disjointClasses anns ces, st =>
      let (xs, st) := mapCEs ces st
      match xs with
      | [a, b] => reify anns [⟨a, owlI "disjointWith", subjTerm b⟩] st
      | _ => allMembers (owlI "AllDisjointClasses") anns (xs.map subjTerm) st
  | .disjointUnion anns c ces, st =>
      let (xs, st) := mapCEs ces st
      let (l, st) := mapSeq "owlfs_lst" (xs.map subjTerm) st
      reify anns [⟨.iri c, owlI "disjointUnionOf", l⟩] st
  | .subObjectPropertyOf anns (.single a) b, st =>
      let (x, st) := mapOPE a st
      let (y, st) := mapOPE b st
      reify anns [⟨x, rdfsI "subPropertyOf", subjTerm y⟩] st
  | .subObjectPropertyOf anns (.chain opes) b, st =>
      let (xs, st) := mapOPEs opes st
      let (y, st) := mapOPE b st
      let (l, st) := mapSeq "owlfs_chain" (xs.map subjTerm) st
      reify anns [⟨y, owlI "propertyChainAxiom", l⟩] st
  | .equivalentObjectProperties anns opes, st =>
      let (xs, st) := mapOPEs opes st
      reify anns ((adjacent xs).map (fun (a, b) => ⟨a, owlI "equivalentProperty", subjTerm b⟩)) st
  | .disjointObjectProperties anns opes, st =>
      let (xs, st) := mapOPEs opes st
      match xs with
      | [a, b] => reify anns [⟨a, owlI "propertyDisjointWith", subjTerm b⟩] st
      | _ => allMembers (owlI "AllDisjointProperties") anns (xs.map subjTerm) st
  | .inverseObjectProperties anns a b, st =>
      let (x, st) := mapOPE a st
      let (y, st) := mapOPE b st
      reify anns [⟨x, owlI "inverseOf", subjTerm y⟩] st
  | .objectPropertyDomain anns ope ce, st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      reify anns [⟨p, rdfsI "domain", subjTerm c⟩] st
  | .objectPropertyRange anns ope ce, st =>
      let (p, st) := mapOPE ope st
      let (c, st) := mapCE ce st
      reify anns [⟨p, rdfsI "range", subjTerm c⟩] st
  | .objectPropertyCharacteristic anns ch ope, st =>
      let (p, st) := mapOPE ope st
      reify anns [⟨p, rdfI "type", .iri (characteristicType ch)⟩] st
  | .subDataPropertyOf anns a b, st =>
      reify anns [⟨.iri a, rdfsI "subPropertyOf", .iri b⟩] st
  | .equivalentDataProperties anns dps, st =>
      reify anns ((adjacent dps).map (fun (a, b) => ⟨.iri a, owlI "equivalentProperty", .iri b⟩)) st
  | .disjointDataProperties anns dps, st =>
      match dps with
      | [a, b] => reify anns [⟨.iri a, owlI "propertyDisjointWith", .iri b⟩] st
      | _ => allMembers (owlI "AllDisjointProperties") anns (dps.map Term.iri) st
  | .dataPropertyDomain anns dp ce, st =>
      let (c, st) := mapCE ce st
      reify anns [⟨.iri dp, rdfsI "domain", subjTerm c⟩] st
  | .dataPropertyRange anns dp dr, st =>
      let (d, st) := mapDR dr st
      reify anns [⟨.iri dp, rdfsI "range", subjTerm d⟩] st
  | .functionalDataProperty anns dp, st =>
      reify anns [⟨.iri dp, rdfI "type", .iri (owlI "FunctionalProperty")⟩] st
  | .datatypeDefinition anns dt dr, st =>
      let (d, st) := mapDR dr st
      reify anns [⟨.iri dt, owlI "equivalentClass", subjTerm d⟩] st
  | .hasKey anns ce opes dps, st =>
      let (c, st) := mapCE ce st
      let (xs, st) := mapOPEs opes st
      let (l, st) := mapSeq "owlfs_lst" (xs.map subjTerm ++ dps.map Term.iri) st
      reify anns [⟨c, owlI "hasKey", l⟩] st
  | .sameIndividual anns inds, st =>
      reify anns ((adjacent (inds.map mapIndividual)).map
        (fun (a, b) => ⟨a, owlI "sameAs", subjTerm b⟩)) st
  | .differentIndividuals anns inds, st =>
      match inds.map mapIndividual with
      | [a, b] => reify anns [⟨a, owlI "differentFrom", subjTerm b⟩] st
      | xs => allMembers (owlI "AllDifferent") anns (xs.map subjTerm) st
  | .classAssertion anns ce ind, st =>
      let (c, st) := mapCE ce st
      reify anns [⟨mapIndividual ind, rdfI "type", subjTerm c⟩] st
  | .objectPropertyAssertion anns (.prop p) a b, st =>
      reify anns [⟨mapIndividual a, p, subjTerm (mapIndividual b)⟩] st
  | .objectPropertyAssertion anns (.inverse p) a b, st =>
      -- `ObjectPropertyAssertion( ObjectInverseOf( OP ) a1 a2 )` is `a2 OP a1`.
      reify anns [⟨mapIndividual b, p, subjTerm (mapIndividual a)⟩] st
  | .negativeObjectPropertyAssertion anns ope a b, st =>
      let (p, st) := mapOPE ope st
      negativeAssertion anns (mapIndividual a) p (owlI "targetIndividual")
        (subjTerm (mapIndividual b)) st
  | .dataPropertyAssertion anns dp a lit, st =>
      reify anns [⟨mapIndividual a, dp, .literal (mapLiteral lit)⟩] st
  | .negativeDataPropertyAssertion anns dp a lit, st =>
      negativeAssertion anns (mapIndividual a) (.iri dp) (owlI "targetValue")
        (.literal (mapLiteral lit)) st
  | .annotationAssertion anns ap subj v, st =>
      reify anns [⟨mapIndividual subj, ap, mapAnnValue v⟩] st
  | .subAnnotationPropertyOf anns a b, st =>
      reify anns [⟨.iri a, rdfsI "subPropertyOf", .iri b⟩] st
  | .annotationPropertyDomain anns ap u, st =>
      reify anns [⟨.iri ap, rdfsI "domain", .iri u⟩] st
  | .annotationPropertyRange anns ap u, st =>
      reify anns [⟨.iri ap, rdfsI "range", .iri u⟩] st

/-! ## The ontology — Table 1, first two rows -/

/-- The ontology header node: the ontology IRI, or a fresh blank node. -/
def headerNode (o : Ontology) : Subject :=
  match o.iri with
  | some i => .iri i
  | none   => .bnode "owlfs_ontology"

def mapOntology (o : Ontology) : MS :=
  let h := headerNode o
  let st : MS := {}
  let st := st.add ⟨h, rdfI "type", .iri (owlI "Ontology")⟩
  let st := match o.versionIri with
    | some v => st.add ⟨h, owlI "versionIRI", .iri v⟩
    | none   => st
  let st := o.imports.foldl (fun s i => s.add ⟨h, owlI "imports", .iri i⟩) st
  let st := tannList o.annotations h st
  o.axioms.foldl (fun s a => mapAxiom a s) st

/-- `T(O)`: the RDF graph of an ontology, OWL 2 Mapping to RDF Graphs
section 2. -/
def Ontology.toGraph (o : Ontology) : Graph := (mapOntology o).out.toList

end L4Factoidal.OWL.Struct
