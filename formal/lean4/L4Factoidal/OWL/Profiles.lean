/-
L4Factoidal.OWL.Profiles — the OWL 2 EL, QL and RL profiles as checkers
over the structural specification.

Spec: OWL 2 Web Ontology Language Profiles (Second Edition),
https://www.w3.org/TR/owl2-profiles/ — section 2.2 (EL), 3.2 (QL), 4.2
(RL) and the complete grammars of section 6. A profile is a syntactic
subset of OWL 2: a restriction of the functional-style grammar, so the
checkers here read `Struct.Ontology` (the structural specification as
data) and nothing else. No reasoning, no closure.

What is decided here, and what is not:

* The grammar of each profile: which class expressions, data ranges,
  property expressions, individuals and axioms may occur, and where
  (`elAxiom`, `qlAxiom`, `rlAxiom`).
* The supported datatypes of each profile (sections 2.2.1, 3.2.1, 4.2.1),
  for datatypes in data ranges and for the datatypes of literals in
  axioms. `rdf:langString` (the RDF 1.1 datatype of a language-tagged
  string) is read as `rdf:PlainLiteral` with a language tag.
* OWL 2 EL's extra global restriction on range axioms and property
  chains, section 2.2.6 (`elRangeRestrictionOk`).
* NOT decided here: that the ontology is an OWL 2 DL ontology at all
  (the typing constraints and the global restrictions of Structural
  Specification section 11). Every profile requires it; the caller asks
  `OWL.SyntaxDL` for that verdict and combines the two.

Two readings of the specification text, stated so they can be changed:

* OWL 2 QL: section 3.1 (Feature Overview) lists "irreflexive
  properties (IrreflexiveObjectProperty)" among the supported axioms;
  the `ObjectPropertyAxiom` production of sections 3.2.5 and 6.2, which
  is the profile specification, has no such alternative. `qlAxiom`
  follows the production and rejects it (the W3C case
  `New-Feature-IrreflexiveProperty-001` is annotated as outside QL).
* `DatatypeDefinition` is in the `Axiom` production of all three
  grammars, and each profile supports a fixed list of datatypes. The
  axiom is accepted when its data range is in the profile; a use of the
  defined datatype elsewhere is a datatype outside the list and is
  rejected.

## Theorems

For OWL 2 RL the grammar of section 4.2 is also written as inductive
relations (`RL.Sub`, `RL.Super`, `RL.Equiv`, `RL.AxiomOk`), one
constructor per production alternative, and the checker is proved to
accept exactly that grammar: `rlSub_iff`, `rlSuper_iff`, `rlEquiv_iff`,
`rlAxiom_iff`, and for a whole ontology `inRL_iff`. So an ontology the
RL checker accepts has only axioms of the RL grammar, and every ontology
of the RL grammar is accepted. EL and QL have the same statement for
their class expressions (`elCE_iff`, `qlSub_iff`, `qlSuper_iff`), and
for the `SubClassOf` axioms of an accepted ontology (`inEL_subClassOf`,
`inQL_subClassOf`); their axiom checkers as a whole are tested, not
proved against a second statement of the grammar.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.OWL.Structure

namespace L4Factoidal.OWL.Profiles

open L4Factoidal.RDF
open L4Factoidal.OWL.Struct

/-! ## Vocabulary -/

def nsOwl  : String := "http://www.w3.org/2002/07/owl#"
def nsRdf  : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def nsRdfs : String := "http://www.w3.org/2000/01/rdf-schema#"
def nsXsd  : String := "http://www.w3.org/2001/XMLSchema#"

def owlThing : String := nsOwl ++ "Thing"

/-- The datatypes OWL 2 EL supports (section 2.2.1); OWL 2 QL supports
the same list (section 3.2.1). -/
def elDatatypes : List String :=
  [nsRdf ++ "PlainLiteral", nsRdf ++ "langString", nsRdf ++ "XMLLiteral", nsRdfs ++ "Literal",
   nsOwl ++ "real", nsOwl ++ "rational",
   nsXsd ++ "decimal", nsXsd ++ "integer", nsXsd ++ "nonNegativeInteger",
   nsXsd ++ "string", nsXsd ++ "normalizedString", nsXsd ++ "token", nsXsd ++ "Name",
   nsXsd ++ "NCName", nsXsd ++ "NMTOKEN", nsXsd ++ "hexBinary", nsXsd ++ "base64Binary",
   nsXsd ++ "anyURI", nsXsd ++ "dateTime", nsXsd ++ "dateTimeStamp"]

def qlDatatypes : List String := elDatatypes

/-- The datatypes OWL 2 RL supports (section 4.2.1). -/
def rlDatatypes : List String :=
  [nsRdf ++ "PlainLiteral", nsRdf ++ "langString", nsRdf ++ "XMLLiteral", nsRdfs ++ "Literal",
   nsXsd ++ "decimal", nsXsd ++ "integer", nsXsd ++ "nonNegativeInteger",
   nsXsd ++ "nonPositiveInteger", nsXsd ++ "positiveInteger", nsXsd ++ "negativeInteger",
   nsXsd ++ "long", nsXsd ++ "int", nsXsd ++ "short", nsXsd ++ "byte",
   nsXsd ++ "unsignedLong", nsXsd ++ "unsignedInt", nsXsd ++ "unsignedShort",
   nsXsd ++ "unsignedByte", nsXsd ++ "float", nsXsd ++ "double",
   nsXsd ++ "string", nsXsd ++ "normalizedString", nsXsd ++ "token", nsXsd ++ "language",
   nsXsd ++ "Name", nsXsd ++ "NCName", nsXsd ++ "NMTOKEN", nsXsd ++ "boolean",
   nsXsd ++ "hexBinary", nsXsd ++ "base64Binary", nsXsd ++ "anyURI",
   nsXsd ++ "dateTime", nsXsd ++ "dateTimeStamp"]

/-- The four predefined properties OWL 2 RL does not support (section
4.2.1). -/
def rlUnsupportedProperties : List String :=
  [nsOwl ++ "topObjectProperty", nsOwl ++ "bottomObjectProperty",
   nsOwl ++ "topDataProperty", nsOwl ++ "bottomDataProperty"]

/-! ## Parts shared by the three profiles -/

def dtOk (dts : List String) (dt : WfIri) : Bool := dts.contains dt.val

def litOk (dts : List String) (l : WfLiteral) : Bool := dts.contains l.val.datatype.val

def isNamed : Individual → Bool
  | .named _ => true
  | .anon _  => false

def isNamedProp : ObjPropExpr → Bool
  | .prop _    => true
  | .inverse _ => false

def opeIri : ObjPropExpr → WfIri
  | .prop p    => p
  | .inverse p => p

def isThing : ClassExpr → Bool
  | .cls c => c.val == owlThing
  | _      => false

def isClass : ClassExpr → Bool
  | .cls _ => true
  | _      => false

mutual
/-- A data range of a profile: a supported datatype, an intersection of
data ranges and, when `oneLit` (OWL 2 EL), an enumeration of exactly one
literal. -/
def drOk (dts : List String) (oneLit : Bool) : DataRange → Bool
  | .datatype dt      => dtOk dts dt
  | .intersection drs => drsOk dts oneLit drs
  | .oneOf [l]        => oneLit && litOk dts l
  | _                 => false
def drsOk (dts : List String) (oneLit : Bool) : List DataRange → Bool
  | []        => true
  | d :: rest => drOk dts oneLit d && drsOk dts oneLit rest
end

theorem drsOk_iff (dts : List String) (oneLit : Bool) (drs : List DataRange) :
    drsOk dts oneLit drs = true ↔ ∀ d ∈ drs, drOk dts oneLit d = true := by
  induction drs with
  | nil => simp [drsOk]
  | cons d rest ih => simp [drsOk, ih]

/-- An optional data range (the qualification of a data cardinality). -/
def odrOk (dts : List String) (oneLit : Bool) : Option DataRange → Bool
  | none    => true
  | some dr => drOk dts oneLit dr

/-! ## OWL 2 EL — section 2.2 -/

mutual
/-- Section 2.2.3: `ClassExpression := Class | ObjectIntersectionOf |
ObjectOneOf | ObjectSomeValuesFrom | ObjectHasValue | ObjectHasSelf |
DataSomeValuesFrom | DataHasValue`, `ObjectOneOf` of one individual, no
inverse properties (2.2.2), no anonymous individuals (2.2.1). -/
def elCE : ClassExpr → Bool
  | .cls _                    => true
  | .intersection ces         => elCEs ces
  | .oneOf [i]                => isNamed i
  | .someValuesFrom ope ce    => isNamedProp ope && elCE ce
  | .hasValue ope i           => isNamedProp ope && isNamed i
  | .hasSelf ope              => isNamedProp ope
  | .dataSomeValuesFrom _ dr  => drOk elDatatypes true dr
  | .dataHasValue _ l         => litOk elDatatypes l
  | _                         => false
def elCEs : List ClassExpr → Bool
  | []        => true
  | c :: rest => elCE c && elCEs rest
end

theorem elCEs_iff (ces : List ClassExpr) : elCEs ces = true ↔ ∀ c ∈ ces, elCE c = true := by
  induction ces with
  | nil => simp [elCEs]
  | cons c rest ih => simp [elCEs, ih]

/-- Section 2.2.5 and the complete grammar of section 6.1. -/
def elAxiom : Axiom → Bool
  | .declaration _ _ _ => true
  | .subClassOf _ sub sup => elCE sub && elCE sup
  | .equivalentClasses _ ces => elCEs ces
  | .disjointClasses _ ces => elCEs ces
  | .disjointUnion _ _ _ => false
  | .subObjectPropertyOf _ (.single ope) sup => isNamedProp ope && isNamedProp sup
  | .subObjectPropertyOf _ (.chain opes) sup => opes.all isNamedProp && isNamedProp sup
  | .equivalentObjectProperties _ opes => opes.all isNamedProp
  | .disjointObjectProperties _ _ => false
  | .inverseObjectProperties _ _ _ => false
  | .objectPropertyDomain _ ope ce => isNamedProp ope && elCE ce
  | .objectPropertyRange _ ope ce => isNamedProp ope && elCE ce
  | .objectPropertyCharacteristic _ ch ope =>
      (ch == .reflexive || ch == .transitive) && isNamedProp ope
  | .subDataPropertyOf _ _ _ => true
  | .equivalentDataProperties _ _ => true
  | .disjointDataProperties _ _ => false
  | .dataPropertyDomain _ _ ce => elCE ce
  | .dataPropertyRange _ _ dr => drOk elDatatypes true dr
  | .functionalDataProperty _ _ => true
  | .datatypeDefinition _ _ dr => drOk elDatatypes true dr
  | .hasKey _ ce opes _ => elCE ce && opes.all isNamedProp
  | .sameIndividual _ inds => inds.all isNamed
  | .differentIndividuals _ inds => inds.all isNamed
  | .classAssertion _ ce i => elCE ce && isNamed i
  | .objectPropertyAssertion _ ope s t => isNamedProp ope && isNamed s && isNamed t
  | .negativeObjectPropertyAssertion _ ope s t => isNamedProp ope && isNamed s && isNamed t
  | .dataPropertyAssertion _ _ s l => isNamed s && litOk elDatatypes l
  | .negativeDataPropertyAssertion _ _ s l => isNamed s && litOk elDatatypes l
  | .annotationAssertion _ _ _ _ => true
  | .subAnnotationPropertyOf _ _ _ => true
  | .annotationPropertyDomain _ _ _ => true
  | .annotationPropertyRange _ _ _ => true

/-! ### The global restriction of section 2.2.6

"The set of axioms Ax imposes a range restriction to a class expression
CE on an object property OP1 if Ax contains `SubObjectPropertyOf( OP1
OP2 )` ... `SubObjectPropertyOf( OPk-1 OPk )`, `ObjectPropertyRange( OPk
CE )`" for some k ≥ 1; "if Ax contains `SubObjectPropertyOf(
ObjectPropertyChain( OP1 ... OPn ) OP )` and Ax imposes a range
restriction to some class expression CE on OP then Ax MUST impose a
range restriction to CE on OPn."

Class expressions are compared by a printed form (`ceKey`); two
structurally equal expressions have equal keys, so a restriction that is
met is never reported as missed. -/

def indKey : Individual → String
  | .named i => "<" ++ i.val ++ ">"
  | .anon l  => "_:" ++ l

def opeKey : ObjPropExpr → String
  | .prop p    => "<" ++ p.val ++ ">"
  | .inverse p => "inv<" ++ p.val ++ ">"

def litKey (l : WfLiteral) : String :=
  "\"" ++ l.val.lexicalForm ++ "\"^^<" ++ l.val.datatype.val ++ ">@" ++ l.val.langTag.getD ""

mutual
def drKey : DataRange → String
  | .datatype dt      => "<" ++ dt.val ++ ">"
  | .intersection drs => "DAnd(" ++ drsKey "" drs ++ ")"
  | .union drs        => "DOr(" ++ drsKey "" drs ++ ")"
  | .complement dr    => "DNot(" ++ drKey dr ++ ")"
  | .oneOf lits       => "DOne(" ++ String.intercalate " " (lits.map litKey) ++ ")"
  | .restriction dt fs =>
      "DRes(<" ++ dt.val ++ "> " ++
        String.intercalate " " (fs.map (fun f => "<" ++ f.1.val ++ "> " ++ litKey f.2)) ++ ")"
def drsKey (acc : String) : List DataRange → String
  | []        => acc
  | d :: rest => drsKey (acc ++ drKey d ++ " ") rest
end

def odrKey : Option DataRange → String
  | none    => ""
  | some dr => drKey dr

def irisKey (is : List WfIri) : String := String.intercalate " " (is.map (fun i => "<" ++ i.val ++ ">"))

mutual
def ceKey : ClassExpr → String
  | .cls c => "<" ++ c.val ++ ">"
  | .intersection ces => "And(" ++ cesKey "" ces ++ ")"
  | .union ces => "Or(" ++ cesKey "" ces ++ ")"
  | .complement ce => "Not(" ++ ceKey ce ++ ")"
  | .oneOf inds => "One(" ++ String.intercalate " " (inds.map indKey) ++ ")"
  | .someValuesFrom ope ce => "Some(" ++ opeKey ope ++ " " ++ ceKey ce ++ ")"
  | .allValuesFrom ope ce => "All(" ++ opeKey ope ++ " " ++ ceKey ce ++ ")"
  | .hasValue ope i => "Has(" ++ opeKey ope ++ " " ++ indKey i ++ ")"
  | .hasSelf ope => "Self(" ++ opeKey ope ++ ")"
  | .minCard n ope oce => "Min(" ++ toString n ++ " " ++ opeKey ope ++ " " ++ oceKey oce ++ ")"
  | .maxCard n ope oce => "Max(" ++ toString n ++ " " ++ opeKey ope ++ " " ++ oceKey oce ++ ")"
  | .exactCard n ope oce => "Exact(" ++ toString n ++ " " ++ opeKey ope ++ " " ++ oceKey oce ++ ")"
  | .dataSomeValuesFrom dps dr => "DSome(" ++ irisKey dps ++ " " ++ drKey dr ++ ")"
  | .dataAllValuesFrom dps dr => "DAll(" ++ irisKey dps ++ " " ++ drKey dr ++ ")"
  | .dataHasValue dp l => "DHas(<" ++ dp.val ++ "> " ++ litKey l ++ ")"
  | .dataMinCard n dp odr => "DMin(" ++ toString n ++ " <" ++ dp.val ++ "> " ++ odrKey odr ++ ")"
  | .dataMaxCard n dp odr => "DMax(" ++ toString n ++ " <" ++ dp.val ++ "> " ++ odrKey odr ++ ")"
  | .dataExactCard n dp odr => "DExact(" ++ toString n ++ " <" ++ dp.val ++ "> " ++ odrKey odr ++ ")"
def cesKey (acc : String) : List ClassExpr → String
  | []        => acc
  | c :: rest => cesKey (acc ++ ceKey c ++ " ") rest
def oceKey : Option ClassExpr → String
  | none    => ""
  | some ce => ceKey ce
end

/-- The pairs `(sub, sup)` of `SubObjectPropertyOf( sub sup )` between
named properties. -/
def simpleSubProps (axs : List Axiom) : List (String × String) :=
  axs.filterMap fun
    | .subObjectPropertyOf _ (.single (.prop a)) (.prop b) => some (a.val, b.val)
    | _ => none

/-- One step up `SubObjectPropertyOf`: the properties of `ps` and their
direct super-properties. -/
def supersStep (subs : List (String × String)) (ps : List String) : List String :=
  (ps ++ (subs.filter (fun e => ps.contains e.1)).map (·.2)).eraseDups

/-- The properties reached from `p` by zero or more
`SubObjectPropertyOf` steps (`fuel` steps; the number of axioms bounds
the length of a chain without a repeat). -/
def supersLoop (subs : List (String × String)) : Nat → List String → List String
  | 0, ps     => ps
  | n + 1, ps => supersLoop subs n (supersStep subs ps)

def supersOf (subs : List (String × String)) (p : String) (fuel : Nat) : List String :=
  supersLoop subs fuel [p]

/-- The printed forms of the class expressions `Ax` imposes as a range
restriction on `p`. -/
def rangesImposed (axs : List Axiom) (p : String) : List String :=
  let sups := supersOf (simpleSubProps axs) p axs.length
  axs.filterMap fun
    | .objectPropertyRange _ (.prop q) ce => if sups.contains q.val then some (ceKey ce) else none
    | _ => none

/-- Section 2.2.6, over the axioms given (the caller passes the axiom
closure). -/
def elRangeRestrictionOk (axs : List Axiom) : Bool :=
  axs.all fun
    | .subObjectPropertyOf _ (.chain opes) (.prop op) =>
        match opes.getLast? with
        | some (.prop last) =>
            let need := rangesImposed axs op.val
            let have_ := rangesImposed axs last.val
            need.all have_.contains
        | _ => true
    | _ => true

def inEL (o : Ontology) : Bool := o.axioms.all elAxiom && elRangeRestrictionOk o.axioms

/-! ## OWL 2 QL — section 3.2 -/

/-- `subClassExpression := Class | subObjectSomeValuesFrom |
DataSomeValuesFrom`, the object filler limited to `owl:Thing`. -/
def qlSub : ClassExpr → Bool
  | .cls _                   => true
  | .someValuesFrom _ ce     => isThing ce
  | .dataSomeValuesFrom _ dr => drOk qlDatatypes false dr
  | _                        => false

mutual
/-- `superClassExpression := Class | superObjectIntersectionOf |
superObjectComplementOf | superObjectSomeValuesFrom |
DataSomeValuesFrom`. -/
def qlSuper : ClassExpr → Bool
  | .cls _                   => true
  | .intersection ces        => qlSupers ces
  | .complement ce           => qlSub ce
  | .someValuesFrom _ ce     => isClass ce
  | .dataSomeValuesFrom _ dr => drOk qlDatatypes false dr
  | _                        => false
def qlSupers : List ClassExpr → Bool
  | []        => true
  | c :: rest => qlSuper c && qlSupers rest
end

theorem qlSupers_iff (ces : List ClassExpr) : qlSupers ces = true ↔ ∀ c ∈ ces, qlSuper c = true := by
  induction ces with
  | nil => simp [qlSupers]
  | cons c rest ih => simp [qlSupers, ih]

/-- Section 3.2.5 and the complete grammar of section 6.2. -/
def qlAxiom : Axiom → Bool
  | .declaration _ _ _ => true
  | .subClassOf _ sub sup => qlSub sub && qlSuper sup
  | .equivalentClasses _ ces => ces.all qlSub
  | .disjointClasses _ ces => ces.all qlSub
  | .disjointUnion _ _ _ => false
  | .subObjectPropertyOf _ (.single _) _ => true
  | .subObjectPropertyOf _ (.chain _) _ => false
  | .equivalentObjectProperties _ _ => true
  | .disjointObjectProperties _ _ => true
  | .inverseObjectProperties _ _ _ => true
  | .objectPropertyDomain _ _ ce => qlSuper ce
  | .objectPropertyRange _ _ ce => qlSuper ce
  | .objectPropertyCharacteristic _ ch _ =>
      ch == .reflexive || ch == .symmetric || ch == .asymmetric
  | .subDataPropertyOf _ _ _ => true
  | .equivalentDataProperties _ _ => true
  | .disjointDataProperties _ _ => true
  | .dataPropertyDomain _ _ ce => qlSuper ce
  | .dataPropertyRange _ _ dr => drOk qlDatatypes false dr
  | .functionalDataProperty _ _ => false
  | .datatypeDefinition _ _ dr => drOk qlDatatypes false dr
  | .hasKey _ _ _ _ => false
  | .sameIndividual _ _ => false
  | .differentIndividuals _ inds => inds.all isNamed
  | .classAssertion _ ce i => isClass ce && isNamed i
  | .objectPropertyAssertion _ _ s t => isNamed s && isNamed t
  | .negativeObjectPropertyAssertion _ _ _ _ => false
  | .dataPropertyAssertion _ _ s l => isNamed s && litOk qlDatatypes l
  | .negativeDataPropertyAssertion _ _ _ _ => false
  | .annotationAssertion _ _ _ _ => true
  | .subAnnotationPropertyOf _ _ _ => true
  | .annotationPropertyDomain _ _ _ => true
  | .annotationPropertyRange _ _ _ => true

def inQL (o : Ontology) : Bool := o.axioms.all qlAxiom

/-! ## OWL 2 RL — section 4.2 -/

/-- An object property expression OWL 2 RL supports: not over
`owl:topObjectProperty` or `owl:bottomObjectProperty` (section 4.2.1). -/
def rlOPE (ope : ObjPropExpr) : Bool := !rlUnsupportedProperties.contains (opeIri ope).val

/-- A data property OWL 2 RL supports (section 4.2.1). -/
def rlDP (dp : WfIri) : Bool := !rlUnsupportedProperties.contains dp.val

def rlDR (dr : DataRange) : Bool := drOk rlDatatypes false dr

def rlLit (l : WfLiteral) : Bool := litOk rlDatatypes l

/-- "Class other than owl:Thing". -/
def rlClass (c : WfIri) : Bool := c.val != owlThing

mutual
/-- `subClassExpression` of section 4.2.3. -/
def rlSub : ClassExpr → Bool
  | .cls c                     => rlClass c
  | .intersection ces          => rlSubs ces
  | .union ces                 => rlSubs ces
  | .oneOf _                   => true
  | .someValuesFrom ope ce     => rlOPE ope && (isThing ce || rlSub ce)
  | .hasValue ope _            => rlOPE ope
  | .dataSomeValuesFrom dps dr => dps.all rlDP && rlDR dr
  | .dataHasValue dp l         => rlDP dp && rlLit l
  | _                          => false
def rlSubs : List ClassExpr → Bool
  | []        => true
  | c :: rest => rlSub c && rlSubs rest
end

theorem rlSubs_iff (ces : List ClassExpr) : rlSubs ces = true ↔ ∀ c ∈ ces, rlSub c = true := by
  induction ces with
  | nil => simp [rlSubs]
  | cons c rest ih => simp [rlSubs, ih]

/-- The optional class of `ObjectMaxCardinality` in a superclass
expression: absent, `owl:Thing`, or a subclass expression. -/
def rlMaxFiller : Option ClassExpr → Bool
  | none    => true
  | some ce => isThing ce || rlSub ce

mutual
/-- `superClassExpression` of section 4.2.3. -/
def rlSuper : ClassExpr → Bool
  | .cls c                    => rlClass c
  | .intersection ces         => rlSupers ces
  | .complement ce            => rlSub ce
  | .allValuesFrom ope ce     => rlOPE ope && rlSuper ce
  | .hasValue ope _           => rlOPE ope
  | .maxCard n ope oce        => n ≤ 1 && rlOPE ope && rlMaxFiller oce
  | .dataAllValuesFrom dps dr => dps.all rlDP && rlDR dr
  | .dataHasValue dp l        => rlDP dp && rlLit l
  | .dataMaxCard n dp odr     => n ≤ 1 && rlDP dp && odrOk rlDatatypes false odr
  | _                         => false
def rlSupers : List ClassExpr → Bool
  | []        => true
  | c :: rest => rlSuper c && rlSupers rest
end

theorem rlSupers_iff (ces : List ClassExpr) : rlSupers ces = true ↔ ∀ c ∈ ces, rlSuper c = true := by
  induction ces with
  | nil => simp [rlSupers]
  | cons c rest ih => simp [rlSupers, ih]

mutual
/-- `equivClassExpression` of section 4.2.3. -/
def rlEquiv : ClassExpr → Bool
  | .cls c             => rlClass c
  | .intersection ces  => rlEquivs ces
  | .hasValue ope _    => rlOPE ope
  | .dataHasValue dp l => rlDP dp && rlLit l
  | _                  => false
def rlEquivs : List ClassExpr → Bool
  | []        => true
  | c :: rest => rlEquiv c && rlEquivs rest
end

theorem rlEquivs_iff (ces : List ClassExpr) : rlEquivs ces = true ↔ ∀ c ∈ ces, rlEquiv c = true := by
  induction ces with
  | nil => simp [rlEquivs]
  | cons c rest ih => simp [rlEquivs, ih]

def rlSubProp : SubObjProp → Bool
  | .single ope => rlOPE ope
  | .chain opes => opes.all rlOPE

/-- Section 4.2.5 and the complete grammar of section 6.3. -/
def rlAxiom : Axiom → Bool
  | .declaration _ _ _ => true
  | .subClassOf _ sub sup => rlSub sub && rlSuper sup
  | .equivalentClasses _ ces => rlEquivs ces
  | .disjointClasses _ ces => rlSubs ces
  | .disjointUnion _ _ _ => false
  | .subObjectPropertyOf _ sub sup => rlSubProp sub && rlOPE sup
  | .equivalentObjectProperties _ opes => opes.all rlOPE
  | .disjointObjectProperties _ opes => opes.all rlOPE
  | .inverseObjectProperties _ a b => rlOPE a && rlOPE b
  | .objectPropertyDomain _ ope ce => rlOPE ope && rlSuper ce
  | .objectPropertyRange _ ope ce => rlOPE ope && rlSuper ce
  | .objectPropertyCharacteristic _ ch ope => ch != .reflexive && rlOPE ope
  | .subDataPropertyOf _ a b => rlDP a && rlDP b
  | .equivalentDataProperties _ dps => dps.all rlDP
  | .disjointDataProperties _ dps => dps.all rlDP
  | .dataPropertyDomain _ dp ce => rlDP dp && rlSuper ce
  | .dataPropertyRange _ dp dr => rlDP dp && rlDR dr
  | .functionalDataProperty _ dp => rlDP dp
  | .datatypeDefinition _ _ dr => rlDR dr
  | .hasKey _ ce opes dps => rlSub ce && opes.all rlOPE && dps.all rlDP
  | .sameIndividual _ _ => true
  | .differentIndividuals _ _ => true
  | .classAssertion _ ce _ => rlSuper ce
  | .objectPropertyAssertion _ ope _ _ => rlOPE ope
  | .negativeObjectPropertyAssertion _ ope _ _ => rlOPE ope
  | .dataPropertyAssertion _ dp _ l => rlDP dp && rlLit l
  | .negativeDataPropertyAssertion _ dp _ l => rlDP dp && rlLit l
  | .annotationAssertion _ _ _ _ => true
  | .subAnnotationPropertyOf _ _ _ => true
  | .annotationPropertyDomain _ _ _ => true
  | .annotationPropertyRange _ _ _ => true

def inRL (o : Ontology) : Bool := o.axioms.all rlAxiom

/-! ## The grammars as relations, and the checkers against them -/

namespace RL

/-- `subClassExpression`, one constructor per alternative of the
production in section 4.2.3. -/
inductive Sub : ClassExpr → Prop where
  | cls {c} : rlClass c = true → Sub (.cls c)
  | intersection {ces} : (∀ c ∈ ces, Sub c) → Sub (.intersection ces)
  | union {ces} : (∀ c ∈ ces, Sub c) → Sub (.union ces)
  | oneOf {inds} : Sub (.oneOf inds)
  | someThing {ope ce} : rlOPE ope = true → isThing ce = true → Sub (.someValuesFrom ope ce)
  | some {ope ce} : rlOPE ope = true → Sub ce → Sub (.someValuesFrom ope ce)
  | hasValue {ope i} : rlOPE ope = true → Sub (.hasValue ope i)
  | dataSome {dps dr} : dps.all rlDP = true → rlDR dr = true → Sub (.dataSomeValuesFrom dps dr)
  | dataHasValue {dp l} : rlDP dp = true → rlLit l = true → Sub (.dataHasValue dp l)

/-- The class of `ObjectMaxCardinality( zeroOrOne OPE [ ... ] )`. -/
inductive MaxFiller : Option ClassExpr → Prop where
  | none : MaxFiller none
  | thing {ce} : isThing ce = true → MaxFiller (some ce)
  | sub {ce} : Sub ce → MaxFiller (some ce)

/-- `superClassExpression`. -/
inductive Super : ClassExpr → Prop where
  | cls {c} : rlClass c = true → Super (.cls c)
  | intersection {ces} : (∀ c ∈ ces, Super c) → Super (.intersection ces)
  | complement {ce} : Sub ce → Super (.complement ce)
  | all {ope ce} : rlOPE ope = true → Super ce → Super (.allValuesFrom ope ce)
  | hasValue {ope i} : rlOPE ope = true → Super (.hasValue ope i)
  | maxCard {n ope oce} : n ≤ 1 → rlOPE ope = true → MaxFiller oce → Super (.maxCard n ope oce)
  | dataAll {dps dr} : dps.all rlDP = true → rlDR dr = true → Super (.dataAllValuesFrom dps dr)
  | dataHasValue {dp l} : rlDP dp = true → rlLit l = true → Super (.dataHasValue dp l)
  | dataMaxCard {n dp odr} : n ≤ 1 → rlDP dp = true → odrOk rlDatatypes false odr = true →
      Super (.dataMaxCard n dp odr)

/-- `equivClassExpression`. -/
inductive Equiv : ClassExpr → Prop where
  | cls {c} : rlClass c = true → Equiv (.cls c)
  | intersection {ces} : (∀ c ∈ ces, Equiv c) → Equiv (.intersection ces)
  | hasValue {ope i} : rlOPE ope = true → Equiv (.hasValue ope i)
  | dataHasValue {dp l} : rlDP dp = true → rlLit l = true → Equiv (.dataHasValue dp l)

/-- The axioms of OWL 2 RL (sections 4.2.5 and 6.3): the axioms of the
structural specification other than `DisjointUnion` and
`ReflexiveObjectProperty`, with class expressions in the stated
positions, supported properties, data ranges and literals. -/
inductive AxiomOk : Axiom → Prop where
  | declaration {anns k i} : AxiomOk (.declaration anns k i)
  | subClassOf {anns sub sup} : Sub sub → Super sup → AxiomOk (.subClassOf anns sub sup)
  | equivalentClasses {anns ces} : (∀ c ∈ ces, Equiv c) → AxiomOk (.equivalentClasses anns ces)
  | disjointClasses {anns ces} : (∀ c ∈ ces, Sub c) → AxiomOk (.disjointClasses anns ces)
  | subObjectPropertyOf {anns sub sup} : rlSubProp sub = true → rlOPE sup = true →
      AxiomOk (.subObjectPropertyOf anns sub sup)
  | equivalentObjectProperties {anns opes} : opes.all rlOPE = true →
      AxiomOk (.equivalentObjectProperties anns opes)
  | disjointObjectProperties {anns opes} : opes.all rlOPE = true →
      AxiomOk (.disjointObjectProperties anns opes)
  | inverseObjectProperties {anns a b} : rlOPE a = true → rlOPE b = true →
      AxiomOk (.inverseObjectProperties anns a b)
  | objectPropertyDomain {anns ope ce} : rlOPE ope = true → Super ce →
      AxiomOk (.objectPropertyDomain anns ope ce)
  | objectPropertyRange {anns ope ce} : rlOPE ope = true → Super ce →
      AxiomOk (.objectPropertyRange anns ope ce)
  | objectPropertyCharacteristic {anns ch ope} : ch ≠ .reflexive → rlOPE ope = true →
      AxiomOk (.objectPropertyCharacteristic anns ch ope)
  | subDataPropertyOf {anns a b} : rlDP a = true → rlDP b = true →
      AxiomOk (.subDataPropertyOf anns a b)
  | equivalentDataProperties {anns dps} : dps.all rlDP = true →
      AxiomOk (.equivalentDataProperties anns dps)
  | disjointDataProperties {anns dps} : dps.all rlDP = true →
      AxiomOk (.disjointDataProperties anns dps)
  | dataPropertyDomain {anns dp ce} : rlDP dp = true → Super ce →
      AxiomOk (.dataPropertyDomain anns dp ce)
  | dataPropertyRange {anns dp dr} : rlDP dp = true → rlDR dr = true →
      AxiomOk (.dataPropertyRange anns dp dr)
  | functionalDataProperty {anns dp} : rlDP dp = true → AxiomOk (.functionalDataProperty anns dp)
  | datatypeDefinition {anns dt dr} : rlDR dr = true → AxiomOk (.datatypeDefinition anns dt dr)
  | hasKey {anns ce opes dps} : Sub ce → opes.all rlOPE = true → dps.all rlDP = true →
      AxiomOk (.hasKey anns ce opes dps)
  | sameIndividual {anns inds} : AxiomOk (.sameIndividual anns inds)
  | differentIndividuals {anns inds} : AxiomOk (.differentIndividuals anns inds)
  | classAssertion {anns ce i} : Super ce → AxiomOk (.classAssertion anns ce i)
  | objectPropertyAssertion {anns ope s t} : rlOPE ope = true →
      AxiomOk (.objectPropertyAssertion anns ope s t)
  | negativeObjectPropertyAssertion {anns ope s t} : rlOPE ope = true →
      AxiomOk (.negativeObjectPropertyAssertion anns ope s t)
  | dataPropertyAssertion {anns dp s l} : rlDP dp = true → rlLit l = true →
      AxiomOk (.dataPropertyAssertion anns dp s l)
  | negativeDataPropertyAssertion {anns dp s l} : rlDP dp = true → rlLit l = true →
      AxiomOk (.negativeDataPropertyAssertion anns dp s l)
  | annotationAssertion {anns p s v} : AxiomOk (.annotationAssertion anns p s v)
  | subAnnotationPropertyOf {anns a b} : AxiomOk (.subAnnotationPropertyOf anns a b)
  | annotationPropertyDomain {anns p d} : AxiomOk (.annotationPropertyDomain anns p d)
  | annotationPropertyRange {anns p r} : AxiomOk (.annotationPropertyRange anns p r)

end RL

/-! ### OWL 2 RL: the checker accepts exactly the grammar -/

mutual
theorem rlSub_sound : ∀ ce : ClassExpr, rlSub ce = true → RL.Sub ce
  | .cls c, h => .cls (by simpa [rlSub] using h)
  | .intersection ces, h => .intersection (rlSubs_sound ces (by simpa [rlSub] using h))
  | .union ces, h => .union (rlSubs_sound ces (by simpa [rlSub] using h))
  | .oneOf _, _ => .oneOf
  | .someValuesFrom ope ce, h => by
      simp only [rlSub, Bool.and_eq_true, Bool.or_eq_true] at h
      rcases h.2 with ht | hs
      · exact .someThing h.1 ht
      · exact .some h.1 (rlSub_sound ce hs)
  | .hasValue ope _, h => .hasValue (by simpa [rlSub] using h)
  | .dataSomeValuesFrom dps dr, h => by
      simp only [rlSub, Bool.and_eq_true] at h
      exact .dataSome h.1 h.2
  | .dataHasValue dp l, h => by
      simp only [rlSub, Bool.and_eq_true] at h
      exact .dataHasValue h.1 h.2
  | .complement _, h => by simp [rlSub] at h
  | .allValuesFrom _ _, h => by simp [rlSub] at h
  | .hasSelf _, h => by simp [rlSub] at h
  | .minCard _ _ _, h => by simp [rlSub] at h
  | .maxCard _ _ _, h => by simp [rlSub] at h
  | .exactCard _ _ _, h => by simp [rlSub] at h
  | .dataAllValuesFrom _ _, h => by simp [rlSub] at h
  | .dataMinCard _ _ _, h => by simp [rlSub] at h
  | .dataMaxCard _ _ _, h => by simp [rlSub] at h
  | .dataExactCard _ _ _, h => by simp [rlSub] at h
theorem rlSubs_sound : ∀ ces : List ClassExpr, rlSubs ces = true → ∀ c ∈ ces, RL.Sub c
  | [], _ => by simp
  | c :: rest, h => by
      simp only [rlSubs, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with hxc | hx
      · exact hxc ▸ rlSub_sound c h.1
      · exact rlSubs_sound rest h.2 x hx
end

theorem rlSub_complete {ce : ClassExpr} (h : RL.Sub ce) : rlSub ce = true := by
  induction h with
  | cls h => simpa [rlSub] using h
  | intersection _ ih => simpa [rlSub, rlSubs_iff] using ih
  | union _ ih => simpa [rlSub, rlSubs_iff] using ih
  | oneOf => simp [rlSub]
  | someThing ho ht => simp [rlSub, ho, ht]
  | some ho _ ih => simp [rlSub, ho, ih]
  | hasValue ho => simpa [rlSub] using ho
  | dataSome hd hr => simp [rlSub, hd, hr]
  | dataHasValue hd hl => simp [rlSub, hd, hl]

/-- **The RL subclass-expression checker is the grammar.** -/
theorem rlSub_iff (ce : ClassExpr) : rlSub ce = true ↔ RL.Sub ce :=
  ⟨rlSub_sound ce, rlSub_complete⟩

theorem rlMaxFiller_iff (oce : Option ClassExpr) : rlMaxFiller oce = true ↔ RL.MaxFiller oce := by
  constructor
  · intro h
    match oce, h with
    | none, _ => exact .none
    | some ce, h =>
        simp only [rlMaxFiller, Bool.or_eq_true] at h
        rcases h with ht | hs
        · exact .thing ht
        · exact .sub ((rlSub_iff ce).mp hs)
  · intro h
    cases h with
    | none => rfl
    | thing ht => simp [rlMaxFiller, ht]
    | sub hs => simp [rlMaxFiller, (rlSub_iff _).mpr hs]

mutual
theorem rlSuper_sound : ∀ ce : ClassExpr, rlSuper ce = true → RL.Super ce
  | .cls c, h => .cls (by simpa [rlSuper] using h)
  | .intersection ces, h => .intersection (rlSupers_sound ces (by simpa [rlSuper] using h))
  | .complement ce, h => .complement ((rlSub_iff ce).mp (by simpa [rlSuper] using h))
  | .allValuesFrom ope ce, h => by
      simp only [rlSuper, Bool.and_eq_true] at h
      exact .all h.1 (rlSuper_sound ce h.2)
  | .hasValue ope _, h => .hasValue (by simpa [rlSuper] using h)
  | .maxCard n ope oce, h => by
      simp only [rlSuper, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .maxCard h.1.1 h.1.2 ((rlMaxFiller_iff oce).mp h.2)
  | .dataAllValuesFrom dps dr, h => by
      simp only [rlSuper, Bool.and_eq_true] at h
      exact .dataAll h.1 h.2
  | .dataHasValue dp l, h => by
      simp only [rlSuper, Bool.and_eq_true] at h
      exact .dataHasValue h.1 h.2
  | .dataMaxCard n dp odr, h => by
      simp only [rlSuper, Bool.and_eq_true, decide_eq_true_eq] at h
      exact .dataMaxCard h.1.1 h.1.2 h.2
  | .union _, h => by simp [rlSuper] at h
  | .oneOf _, h => by simp [rlSuper] at h
  | .someValuesFrom _ _, h => by simp [rlSuper] at h
  | .hasSelf _, h => by simp [rlSuper] at h
  | .minCard _ _ _, h => by simp [rlSuper] at h
  | .exactCard _ _ _, h => by simp [rlSuper] at h
  | .dataSomeValuesFrom _ _, h => by simp [rlSuper] at h
  | .dataMinCard _ _ _, h => by simp [rlSuper] at h
  | .dataExactCard _ _ _, h => by simp [rlSuper] at h
theorem rlSupers_sound : ∀ ces : List ClassExpr, rlSupers ces = true → ∀ c ∈ ces, RL.Super c
  | [], _ => by simp
  | c :: rest, h => by
      simp only [rlSupers, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with hxc | hx
      · exact hxc ▸ rlSuper_sound c h.1
      · exact rlSupers_sound rest h.2 x hx
end

theorem rlSuper_complete {ce : ClassExpr} (h : RL.Super ce) : rlSuper ce = true := by
  induction h with
  | cls h => simpa [rlSuper] using h
  | intersection _ ih => simpa [rlSuper, rlSupers_iff] using ih
  | complement hs => simpa [rlSuper] using (rlSub_iff _).mpr hs
  | all ho _ ih => simp [rlSuper, ho, ih]
  | hasValue ho => simpa [rlSuper] using ho
  | maxCard hn ho hf => simp [rlSuper, hn, ho, (rlMaxFiller_iff _).mpr hf]
  | dataAll hd hr => simp [rlSuper, hd, hr]
  | dataHasValue hd hl => simp [rlSuper, hd, hl]
  | dataMaxCard hn hd hr => simp [rlSuper, hn, hd, hr]

/-- **The RL superclass-expression checker is the grammar.** -/
theorem rlSuper_iff (ce : ClassExpr) : rlSuper ce = true ↔ RL.Super ce :=
  ⟨rlSuper_sound ce, rlSuper_complete⟩

mutual
theorem rlEquiv_sound : ∀ ce : ClassExpr, rlEquiv ce = true → RL.Equiv ce
  | .cls c, h => .cls (by simpa [rlEquiv] using h)
  | .intersection ces, h => .intersection (rlEquivs_sound ces (by simpa [rlEquiv] using h))
  | .hasValue ope _, h => .hasValue (by simpa [rlEquiv] using h)
  | .dataHasValue dp l, h => by
      simp only [rlEquiv, Bool.and_eq_true] at h
      exact .dataHasValue h.1 h.2
  | .union _, h => by simp [rlEquiv] at h
  | .complement _, h => by simp [rlEquiv] at h
  | .oneOf _, h => by simp [rlEquiv] at h
  | .someValuesFrom _ _, h => by simp [rlEquiv] at h
  | .allValuesFrom _ _, h => by simp [rlEquiv] at h
  | .hasSelf _, h => by simp [rlEquiv] at h
  | .minCard _ _ _, h => by simp [rlEquiv] at h
  | .maxCard _ _ _, h => by simp [rlEquiv] at h
  | .exactCard _ _ _, h => by simp [rlEquiv] at h
  | .dataSomeValuesFrom _ _, h => by simp [rlEquiv] at h
  | .dataAllValuesFrom _ _, h => by simp [rlEquiv] at h
  | .dataMinCard _ _ _, h => by simp [rlEquiv] at h
  | .dataMaxCard _ _ _, h => by simp [rlEquiv] at h
  | .dataExactCard _ _ _, h => by simp [rlEquiv] at h
theorem rlEquivs_sound : ∀ ces : List ClassExpr, rlEquivs ces = true → ∀ c ∈ ces, RL.Equiv c
  | [], _ => by simp
  | c :: rest, h => by
      simp only [rlEquivs, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with hxc | hx
      · exact hxc ▸ rlEquiv_sound c h.1
      · exact rlEquivs_sound rest h.2 x hx
end

theorem rlEquiv_complete {ce : ClassExpr} (h : RL.Equiv ce) : rlEquiv ce = true := by
  induction h with
  | cls h => simpa [rlEquiv] using h
  | intersection _ ih => simpa [rlEquiv, rlEquivs_iff] using ih
  | hasValue ho => simpa [rlEquiv] using ho
  | dataHasValue hd hl => simp [rlEquiv, hd, hl]

/-- **The RL equivalent-class-expression checker is the grammar.** -/
theorem rlEquiv_iff (ce : ClassExpr) : rlEquiv ce = true ↔ RL.Equiv ce :=
  ⟨rlEquiv_sound ce, rlEquiv_complete⟩

theorem rlSubs_iff_grammar (ces : List ClassExpr) : rlSubs ces = true ↔ ∀ c ∈ ces, RL.Sub c := by
  simp [rlSubs_iff, rlSub_iff]

theorem rlEquivs_iff_grammar (ces : List ClassExpr) :
    rlEquivs ces = true ↔ ∀ c ∈ ces, RL.Equiv c := by
  simp [rlEquivs_iff, rlEquiv_iff]

/-- **The RL axiom checker accepts exactly the axioms of the RL
grammar.** -/
theorem rlAxiom_iff (a : Axiom) : rlAxiom a = true ↔ RL.AxiomOk a := by
  constructor
  · intro h
    cases a with
    | declaration => exact .declaration
    | subClassOf anns sub sup =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .subClassOf ((rlSub_iff _).mp h.1) ((rlSuper_iff _).mp h.2)
    | equivalentClasses anns ces => exact .equivalentClasses ((rlEquivs_iff_grammar ces).mp h)
    | disjointClasses anns ces => exact .disjointClasses ((rlSubs_iff_grammar ces).mp h)
    | disjointUnion => simp [rlAxiom] at h
    | subObjectPropertyOf anns sub sup =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .subObjectPropertyOf h.1 h.2
    | equivalentObjectProperties => exact .equivalentObjectProperties h
    | disjointObjectProperties => exact .disjointObjectProperties h
    | inverseObjectProperties =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .inverseObjectProperties h.1 h.2
    | objectPropertyDomain =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .objectPropertyDomain h.1 ((rlSuper_iff _).mp h.2)
    | objectPropertyRange =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .objectPropertyRange h.1 ((rlSuper_iff _).mp h.2)
    | objectPropertyCharacteristic anns ch ope =>
        simp only [rlAxiom, Bool.and_eq_true, bne_iff_ne] at h
        exact .objectPropertyCharacteristic h.1 h.2
    | subDataPropertyOf =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .subDataPropertyOf h.1 h.2
    | equivalentDataProperties => exact .equivalentDataProperties h
    | disjointDataProperties => exact .disjointDataProperties h
    | dataPropertyDomain =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .dataPropertyDomain h.1 ((rlSuper_iff _).mp h.2)
    | dataPropertyRange =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .dataPropertyRange h.1 h.2
    | functionalDataProperty => exact .functionalDataProperty h
    | datatypeDefinition => exact .datatypeDefinition h
    | hasKey =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .hasKey ((rlSub_iff _).mp h.1.1) h.1.2 h.2
    | sameIndividual => exact .sameIndividual
    | differentIndividuals => exact .differentIndividuals
    | classAssertion => exact .classAssertion ((rlSuper_iff _).mp h)
    | objectPropertyAssertion => exact .objectPropertyAssertion h
    | negativeObjectPropertyAssertion => exact .negativeObjectPropertyAssertion h
    | dataPropertyAssertion =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .dataPropertyAssertion h.1 h.2
    | negativeDataPropertyAssertion =>
        simp only [rlAxiom, Bool.and_eq_true] at h
        exact .negativeDataPropertyAssertion h.1 h.2
    | annotationAssertion => exact .annotationAssertion
    | subAnnotationPropertyOf => exact .subAnnotationPropertyOf
    | annotationPropertyDomain => exact .annotationPropertyDomain
    | annotationPropertyRange => exact .annotationPropertyRange
  · intro h
    cases h with
    | declaration => rfl
    | subClassOf hs hp => simp [rlAxiom, (rlSub_iff _).mpr hs, (rlSuper_iff _).mpr hp]
    | equivalentClasses hc => exact (rlEquivs_iff_grammar _).mpr hc
    | disjointClasses hc => exact (rlSubs_iff_grammar _).mpr hc
    | subObjectPropertyOf h1 h2 => simp [rlAxiom, h1, h2]
    | equivalentObjectProperties h => exact h
    | disjointObjectProperties h => exact h
    | inverseObjectProperties h1 h2 => simp [rlAxiom, h1, h2]
    | objectPropertyDomain h1 h2 => simp [rlAxiom, h1, (rlSuper_iff _).mpr h2]
    | objectPropertyRange h1 h2 => simp [rlAxiom, h1, (rlSuper_iff _).mpr h2]
    | objectPropertyCharacteristic h1 h2 => simp [rlAxiom, h1, h2]
    | subDataPropertyOf h1 h2 => simp [rlAxiom, h1, h2]
    | equivalentDataProperties h => exact h
    | disjointDataProperties h => exact h
    | dataPropertyDomain h1 h2 => simp [rlAxiom, h1, (rlSuper_iff _).mpr h2]
    | dataPropertyRange h1 h2 => simp [rlAxiom, h1, h2]
    | functionalDataProperty h => exact h
    | datatypeDefinition h => exact h
    | hasKey h1 h2 h3 => simp [rlAxiom, (rlSub_iff _).mpr h1, h2, h3]
    | sameIndividual => rfl
    | differentIndividuals => rfl
    | classAssertion h => exact (rlSuper_iff _).mpr h
    | objectPropertyAssertion h => exact h
    | negativeObjectPropertyAssertion h => exact h
    | dataPropertyAssertion h1 h2 => simp [rlAxiom, h1, h2]
    | negativeDataPropertyAssertion h1 h2 => simp [rlAxiom, h1, h2]
    | annotationAssertion => rfl
    | subAnnotationPropertyOf => rfl
    | annotationPropertyDomain => rfl
    | annotationPropertyRange => rfl

/-- **An ontology is accepted by the RL checker exactly when every one
of its axioms is an axiom of the OWL 2 RL grammar.** -/
theorem inRL_iff (o : Ontology) : inRL o = true ↔ ∀ a ∈ o.axioms, RL.AxiomOk a := by
  simp [inRL, List.all_eq_true, rlAxiom_iff]

/-- No ontology with a `DisjointUnion` axiom is accepted as OWL 2 RL, QL
or EL (sections 2.2.5, 3.2.5, 4.2.5). -/
theorem disjointUnion_in_no_profile (o : Ontology) {anns c ces}
    (h : Axiom.disjointUnion anns c ces ∈ o.axioms) :
    inRL o = false ∧ inQL o = false ∧ inEL o = false := by
  refine ⟨?_, ?_, ?_⟩
  · apply Bool.eq_false_iff.mpr
    intro hr
    have := List.all_eq_true.mp hr _ h
    simp [rlAxiom] at this
  · apply Bool.eq_false_iff.mpr
    intro hr
    have := List.all_eq_true.mp hr _ h
    simp [qlAxiom] at this
  · apply Bool.eq_false_iff.mpr
    intro hr
    simp only [inEL, Bool.and_eq_true] at hr
    have := List.all_eq_true.mp hr.1 _ h
    simp [elAxiom] at this

/-! ### OWL 2 QL and EL: the class-expression checkers against their grammars -/

namespace QL

/-- `subClassExpression` of section 3.2.3. -/
inductive Sub : ClassExpr → Prop where
  | cls {c} : Sub (.cls c)
  | someThing {ope ce} : isThing ce = true → Sub (.someValuesFrom ope ce)
  | dataSome {dps dr} : drOk qlDatatypes false dr = true → Sub (.dataSomeValuesFrom dps dr)

/-- `superClassExpression` of section 3.2.3. -/
inductive Super : ClassExpr → Prop where
  | cls {c} : Super (.cls c)
  | intersection {ces} : (∀ c ∈ ces, Super c) → Super (.intersection ces)
  | complement {ce} : Sub ce → Super (.complement ce)
  | someClass {ope ce} : isClass ce = true → Super (.someValuesFrom ope ce)
  | dataSome {dps dr} : drOk qlDatatypes false dr = true → Super (.dataSomeValuesFrom dps dr)

end QL

/-- **The QL subclass-expression checker is the grammar.** -/
theorem qlSub_iff (ce : ClassExpr) : qlSub ce = true ↔ QL.Sub ce := by
  constructor
  · intro h
    cases ce with
    | cls => exact .cls
    | someValuesFrom ope ce => exact .someThing (by simpa [qlSub] using h)
    | dataSomeValuesFrom dps dr => exact .dataSome (by simpa [qlSub] using h)
    | _ => simp [qlSub] at h
  · intro h
    cases h with
    | cls => rfl
    | someThing h => simpa [qlSub] using h
    | dataSome h => simpa [qlSub] using h

mutual
theorem qlSuper_sound : ∀ ce : ClassExpr, qlSuper ce = true → QL.Super ce
  | .cls _, _ => .cls
  | .intersection ces, h => .intersection (qlSupers_sound ces (by simpa [qlSuper] using h))
  | .complement ce, h => .complement ((qlSub_iff ce).mp (by simpa [qlSuper] using h))
  | .someValuesFrom _ ce, h => .someClass (by simpa [qlSuper] using h)
  | .dataSomeValuesFrom _ dr, h => .dataSome (by simpa [qlSuper] using h)
  | .union _, h => by simp [qlSuper] at h
  | .oneOf _, h => by simp [qlSuper] at h
  | .allValuesFrom _ _, h => by simp [qlSuper] at h
  | .hasValue _ _, h => by simp [qlSuper] at h
  | .hasSelf _, h => by simp [qlSuper] at h
  | .minCard _ _ _, h => by simp [qlSuper] at h
  | .maxCard _ _ _, h => by simp [qlSuper] at h
  | .exactCard _ _ _, h => by simp [qlSuper] at h
  | .dataAllValuesFrom _ _, h => by simp [qlSuper] at h
  | .dataHasValue _ _, h => by simp [qlSuper] at h
  | .dataMinCard _ _ _, h => by simp [qlSuper] at h
  | .dataMaxCard _ _ _, h => by simp [qlSuper] at h
  | .dataExactCard _ _ _, h => by simp [qlSuper] at h
theorem qlSupers_sound : ∀ ces : List ClassExpr, qlSupers ces = true → ∀ c ∈ ces, QL.Super c
  | [], _ => by simp
  | c :: rest, h => by
      simp only [qlSupers, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with hxc | hx
      · exact hxc ▸ qlSuper_sound c h.1
      · exact qlSupers_sound rest h.2 x hx
end

/-- **The QL superclass-expression checker is the grammar.** -/
theorem qlSuper_iff (ce : ClassExpr) : qlSuper ce = true ↔ QL.Super ce := by
  refine ⟨qlSuper_sound ce, fun h => ?_⟩
  induction h with
  | cls => rfl
  | intersection _ ih => simpa [qlSuper, qlSupers_iff] using ih
  | complement hs => simpa [qlSuper] using (qlSub_iff _).mpr hs
  | someClass h => simpa [qlSuper] using h
  | dataSome h => simpa [qlSuper] using h

namespace EL

/-- `ClassExpression` of section 2.2.3. -/
inductive CE : ClassExpr → Prop where
  | cls {c} : CE (.cls c)
  | intersection {ces} : (∀ c ∈ ces, CE c) → CE (.intersection ces)
  | oneOf {i} : isNamed i = true → CE (.oneOf [i])
  | some {ope ce} : isNamedProp ope = true → CE ce → CE (.someValuesFrom ope ce)
  | hasValue {ope i} : isNamedProp ope = true → isNamed i = true → CE (.hasValue ope i)
  | hasSelf {ope} : isNamedProp ope = true → CE (.hasSelf ope)
  | dataSome {dps dr} : drOk elDatatypes true dr = true → CE (.dataSomeValuesFrom dps dr)
  | dataHasValue {dp l} : litOk elDatatypes l = true → CE (.dataHasValue dp l)

end EL

mutual
theorem elCE_sound : ∀ ce : ClassExpr, elCE ce = true → EL.CE ce
  | .cls _, _ => .cls
  | .intersection ces, h => .intersection (elCEs_sound ces (by simpa [elCE] using h))
  | .oneOf [i], h => .oneOf (by simpa [elCE] using h)
  | .oneOf [], h => by simp [elCE] at h
  | .oneOf (_ :: _ :: _), h => by simp [elCE] at h
  | .someValuesFrom ope ce, h => by
      simp only [elCE, Bool.and_eq_true] at h
      exact .some h.1 (elCE_sound ce h.2)
  | .hasValue ope i, h => by
      simp only [elCE, Bool.and_eq_true] at h
      exact .hasValue h.1 h.2
  | .hasSelf ope, h => .hasSelf (by simpa [elCE] using h)
  | .dataSomeValuesFrom _ dr, h => .dataSome (by simpa [elCE] using h)
  | .dataHasValue _ l, h => .dataHasValue (by simpa [elCE] using h)
  | .union _, h => by simp [elCE] at h
  | .complement _, h => by simp [elCE] at h
  | .allValuesFrom _ _, h => by simp [elCE] at h
  | .minCard _ _ _, h => by simp [elCE] at h
  | .maxCard _ _ _, h => by simp [elCE] at h
  | .exactCard _ _ _, h => by simp [elCE] at h
  | .dataAllValuesFrom _ _, h => by simp [elCE] at h
  | .dataMinCard _ _ _, h => by simp [elCE] at h
  | .dataMaxCard _ _ _, h => by simp [elCE] at h
  | .dataExactCard _ _ _, h => by simp [elCE] at h
theorem elCEs_sound : ∀ ces : List ClassExpr, elCEs ces = true → ∀ c ∈ ces, EL.CE c
  | [], _ => by simp
  | c :: rest, h => by
      simp only [elCEs, Bool.and_eq_true] at h
      intro x hx
      rcases List.mem_cons.mp hx with hxc | hx
      · exact hxc ▸ elCE_sound c h.1
      · exact elCEs_sound rest h.2 x hx
end

/-- **The EL class-expression checker is the grammar.** -/
theorem elCE_iff (ce : ClassExpr) : elCE ce = true ↔ EL.CE ce := by
  refine ⟨elCE_sound ce, fun h => ?_⟩
  induction h with
  | cls => rfl
  | intersection _ ih => simpa [elCE, elCEs_iff] using ih
  | oneOf h => simpa [elCE] using h
  | some ho _ ih => simp [elCE, ho, ih]
  | hasValue ho hi => simp [elCE, ho, hi]
  | hasSelf ho => simpa [elCE] using ho
  | dataSome h => simpa [elCE] using h
  | dataHasValue h => simpa [elCE] using h

/-- An ontology accepted as OWL 2 EL has only EL class expressions in its
`SubClassOf` axioms, and one accepted as OWL 2 QL has a QL subclass
expression under a QL superclass expression. -/
theorem inEL_subClassOf {o : Ontology} (h : inEL o = true) {anns sub sup}
    (ha : Axiom.subClassOf anns sub sup ∈ o.axioms) : EL.CE sub ∧ EL.CE sup := by
  simp only [inEL, Bool.and_eq_true] at h
  have := List.all_eq_true.mp h.1 _ ha
  simp only [elAxiom, Bool.and_eq_true] at this
  exact ⟨(elCE_iff _).mp this.1, (elCE_iff _).mp this.2⟩

theorem inQL_subClassOf {o : Ontology} (h : inQL o = true) {anns sub sup}
    (ha : Axiom.subClassOf anns sub sup ∈ o.axioms) : QL.Sub sub ∧ QL.Super sup := by
  have := List.all_eq_true.mp h _ ha
  simp only [qlAxiom, Bool.and_eq_true] at this
  exact ⟨(qlSub_iff _).mp this.1, (qlSuper_iff _).mp this.2⟩

/-! ## The name of an axiom, for a report -/

def axiomName : Axiom → String
  | .declaration .. => "Declaration"
  | .subClassOf .. => "SubClassOf"
  | .equivalentClasses .. => "EquivalentClasses"
  | .disjointClasses .. => "DisjointClasses"
  | .disjointUnion .. => "DisjointUnion"
  | .subObjectPropertyOf .. => "SubObjectPropertyOf"
  | .equivalentObjectProperties .. => "EquivalentObjectProperties"
  | .disjointObjectProperties .. => "DisjointObjectProperties"
  | .inverseObjectProperties .. => "InverseObjectProperties"
  | .objectPropertyDomain .. => "ObjectPropertyDomain"
  | .objectPropertyRange .. => "ObjectPropertyRange"
  | .objectPropertyCharacteristic _ ch _ =>
      (match ch with
       | .functional => "Functional" | .inverseFunctional => "InverseFunctional"
       | .reflexive => "Reflexive" | .irreflexive => "Irreflexive"
       | .symmetric => "Symmetric" | .asymmetric => "Asymmetric"
       | .transitive => "Transitive") ++ "ObjectProperty"
  | .subDataPropertyOf .. => "SubDataPropertyOf"
  | .equivalentDataProperties .. => "EquivalentDataProperties"
  | .disjointDataProperties .. => "DisjointDataProperties"
  | .dataPropertyDomain .. => "DataPropertyDomain"
  | .dataPropertyRange .. => "DataPropertyRange"
  | .functionalDataProperty .. => "FunctionalDataProperty"
  | .datatypeDefinition .. => "DatatypeDefinition"
  | .hasKey .. => "HasKey"
  | .sameIndividual .. => "SameIndividual"
  | .differentIndividuals .. => "DifferentIndividuals"
  | .classAssertion .. => "ClassAssertion"
  | .objectPropertyAssertion .. => "ObjectPropertyAssertion"
  | .negativeObjectPropertyAssertion .. => "NegativeObjectPropertyAssertion"
  | .dataPropertyAssertion .. => "DataPropertyAssertion"
  | .negativeDataPropertyAssertion .. => "NegativeDataPropertyAssertion"
  | .annotationAssertion .. => "AnnotationAssertion"
  | .subAnnotationPropertyOf .. => "SubAnnotationPropertyOf"
  | .annotationPropertyDomain .. => "AnnotationPropertyDomain"
  | .annotationPropertyRange .. => "AnnotationPropertyRange"

/-- The names of the axioms of `o` a profile's axiom checker rejects, in
order, without repeats. -/
def rejectedAxioms (check : Axiom → Bool) (o : Ontology) : List String :=
  ((o.axioms.filter (fun a => !check a)).map axiomName).eraseDups

end L4Factoidal.OWL.Profiles
