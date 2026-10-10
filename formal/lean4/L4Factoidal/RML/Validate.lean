/-
L4Factoidal.RML.Validate — the MUST clauses of RML-Core, checked on the
mapping graph before any source is read.

Spec: RML-Core (https://w3id.org/rml/core/spec): "Mapping to RDF with
Triples Maps", "Term Maps", "Generating values with expressions",
"Assigning Triples to Named Graphs" and "Joins". Each error names the
clause it enforces.

## Why this reads the GRAPH and not the model

`FromGraph.mappingOf` builds a `Mapping`, and building it throws away
exactly what a validator has to see: a triples map with no subject map
is dropped, a second subject map is never looked at, a term map with two
expressions keeps one. Validation therefore walks the same RDF graph the
reader walks, with the reader's own accessors, so that the two cannot
disagree about what a shortcut property means.

## What is NOT checked here

Anything that needs a record is a DATA error and is reported by the
evaluator (`generateTermE`): a value that is not an IRI, an ill-formed
language tag from a language map, an ill-typed literal, a reference that
selects an array. A missing source file is a SOURCE error.

## Positions

A term map's rules depend on where it sits. `Position` carries that, and
the same node is checked once per position it occupies.
-/
import L4Factoidal.RML.FromGraph
import L4Factoidal.RML.JsonPath
import L4Factoidal.RML.Error
import L4Factoidal.RDF.LangTag

namespace L4Factoidal.RML

open L4Factoidal.RDF

inductive Position where
  | subject | predicate | object | graph | datatype | language | child | parent
deriving Repr, DecidableEq, Inhabited

def Position.label : Position → String
  | .subject   => "subject map"
  | .predicate => "predicate map"
  | .object    => "object map"
  | .graph     => "graph map"
  | .datatype  => "datatype map"
  | .language  => "language map"
  | .child     => "child map"
  | .parent    => "parent map"

/-- RML-Core, Term Maps, "Explicitly Defined Term Types": the term types
    a map in each position may state.

    The graph row is wider than the specification's list for a graph map
    (`rml:IRI`, `rml:URI`): "Assigning Triples to Named Graphs" says a
    triple can go to a blank-node-named graph and gives an example whose
    graph map states `rml:termType rml:BlankNode`. The two passages
    disagree; the example is the one a test case can exercise, so the
    blank node is allowed. `rml:UnsafeIRI` is allowed wherever
    `rml:IRI` is, since RMLTC0027b uses it on a subject map. -/
def allowedTermTypes : Position → List TermType
  | .subject   => [.iri, .uri, .unsafeIri, .blankNode]
  | .predicate => [.iri, .uri, .unsafeIri]
  | .object    => [.iri, .uri, .unsafeIri, .blankNode, .literal]
  | .graph     => [.iri, .uri, .unsafeIri, .blankNode]
  | .datatype  => [.iri, .uri, .unsafeIri]
  | .language  => [.literal]
  | .child     => [.iri, .uri, .unsafeIri, .blankNode, .literal]
  | .parent    => [.iri, .uri, .unsafeIri, .blankNode, .literal]

def rmlIri (local' : String) : String := rmlNs ++ local'

/-- How many values `(n, rml:p)` has. -/
def countOf (g : Graph) (n p : String) : Nat := (objectsOf g n (rmlIri p)).length

/-- The reference formulation IRI of the logical source at `ls`. A blank
    node typed `rml:XPathReferenceFormulation` names the XPath
    formulation (RML-IO, "Reference formulations"). -/
def formulationAt (g : Graph) (ls : String) : String :=
  match objOf g ls (rmlIri "referenceFormulation") with
  | some (.iri i) => i.val
  | some (.bnode b) =>
      if (objectsOf g ("_:" ++ b) rdfTypeStr).any (fun t => match t with
           | .iri i => i.val == rmlIri "XPathReferenceFormulation" | _ => false)
      then rmlIri "XPath" else ""
  | _ => ""

def jsonPathIri : String := rmlIri "JSONPath"

/-- The logical source node of a triples map, if it states one. -/
def logicalSourceNode (g : Graph) (tm : String) : Option String :=
  (nodesOf g tm (rmlIri "logicalSource")).head?

/-- Is `expr` a valid reference expression in `formulation`? The
    formulations this port can parse are checked; any other is taken as
    valid, since a check this port cannot make is not a rejection. -/
def validReference (formulation expr : String) : Bool :=
  if formulation == jsonPathIri then (parseJsonPath expr).isSome
  else !expr.isEmpty

structure Ctx where
  g           : Graph
  /-- The triples map the term map belongs to, for error sites. -/
  tm          : String
  /-- The reference formulation its references are written in. -/
  formulation : String

def Ctx.site (c : Ctx) (pos : Position) (n : String) : String :=
  s!"{c.tm} {pos.label} {n}"

/-- The expression properties of a term map. A map may state exactly one
    of the first three (RML-Core, "Generating values with expressions");
    a gather map may add a name for its head node (RML-CC). -/
def expressionProps : List String :=
  ["constant", "reference", "template", "functionExecution", "quotedTriplesMap"]

/-- The term type a map in `pos` has when it states none (RML-Core,
    "Default Term Types"). An object map is a literal map when it is
    reference-valued or carries a language or datatype. -/
def effectiveTermType (g : Graph) (pos : Position) (n : String) (explicit : Option TermType)
    : TermType :=
  match explicit with
  | some t => t
  | none =>
      if pos == .object &&
         (countOf g n "reference" > 0 || countOf g n "language" > 0 ||
          countOf g n "languageMap" > 0 || countOf g n "datatype" > 0 ||
          countOf g n "datatypeMap" > 0)
      then .literal else .iri

/-- Check the constant a map states, by position (RML-Core, Term Maps:
    "Constant RDF Terms" and the position rules: a subject map generates
    an IRI or blank node, a predicate map an IRI, an object map an IRI,
    blank node or literal, a datatype map an IRI; and blank nodes may not
    be constants). -/
def checkConstant (c : Ctx) (pos : Position) (n : String) (t : Term) : List RmlError :=
  let bad (why : String) : List RmlError :=
    [RmlError.mapping (c.site pos n) "RML-Core, Term Maps: constant RDF terms" why]
  match pos, t with
  | .subject,   .iri _ => []
  | .subject,   _      => bad "a subject map must generate an IRI or a blank node, and a constant cannot be a blank node"
  | .predicate, .iri _ => []
  | .predicate, _      => bad "a predicate map must generate an IRI"
  | .object,    .iri _ => []
  | .object,    .literal _ => []
  | .object,    _      => bad "a constant object must be an IRI or a literal"
  | .graph,     .iri _ => []
  | .graph,     _      => bad "a graph map should generate an IRI"
  | .datatype,  .iri _ => []
  | .datatype,  _      => bad "a datatype map must generate an IRI"
  | .language,  .literal l =>
      if isWellFormedLangTag l.val.lexicalForm then []
      else bad s!"'{l.val.lexicalForm}' is not a well-formed BCP 47 language tag"
  | .language,  _      => bad "a language map must generate a language tag"
  | _, _ => []

/-- Check one template: strict syntax, then each reference expression
    in the reference formulation. -/
def checkTemplate (c : Ctx) (pos : Position) (n raw : String) : List RmlError :=
  match parseTemplateStrict raw with
  | .error msg =>
      [RmlError.mapping (c.site pos n)
        "RML-Core, Generating values with expressions: string templates"
        s!"template \"{raw}\" is not valid: {msg}"]
  | .ok segs =>
      segs.filterMap (fun seg => match seg with
        | .reference r =>
            if validReference c.formulation r then none
            else some (RmlError.mapping (c.site pos n)
              "RML-Core, Generating values with expressions: reference expressions"
              s!"'{r}' is not a valid reference expression")
        | .literal _ => none)

/-- All the checks for one term map node `n` in `pos`, except the ones
    for its datatype map and language map, which are term maps in their
    own right and are checked by `checkTermMap`. -/
def checkTermMapNoDt (c : Ctx) (pos : Position) (n : String) : List RmlError :=
  let g := c.g
  let site := c.site pos n
  let err (clause msg : String) : List RmlError := [RmlError.mapping site clause msg]
  let nExpr := (expressionProps.map (countOf g n)).foldl (· + ·) 0
  let hasGather := countOf g n "gather" > 0
  let consts := objectsOf g n (rmlIri "constant")
  -- exactly one value per expression property, and one expression
  let multi := expressionProps.filterMap (fun p =>
    if countOf g n p > 1 then
      some (RmlError.mapping site
        "RML-Core, Generating values with expressions: expression map"
        s!"more than one rml:{p}")
    else none)
  let tooMany :=
    if nExpr > 1 && !hasGather then
      err "RML-Core, Generating values with expressions: expression map"
        "a term map has at most one of rml:constant, rml:reference and rml:template"
    else []
  -- term type
  let ttVals := objectsOf g n (rmlIri "termType")
  let ttErrs : List RmlError :=
    if ttVals.length > 1 then
      err "RML-Core, Term Maps: term type" "a term map has at most one rml:termType"
    else match ttVals.head? with
      | none => []
      | some v =>
          let known : Option TermType := match v with
            | .iri i => termTypeOf i.val
            | _ => none
          match known with
          | none => err "RML-Core, Term Maps: term type" "rml:termType is not one of the RML term types"
          | some tt =>
              -- a constant has no term type; stating one has no effect
              if !consts.isEmpty then []
              else if (allowedTermTypes pos).contains tt then []
              else err "RML-Core, Term Maps: explicitly defined term types"
                     s!"a {pos.label} may not have this term type"
  let explicitTt : Option TermType :=
    match ttVals.head? with
    | some (.iri i) => termTypeOf i.val
    | _ => none
  -- an expression is required unless the map is a blank-node map
  let needExpr :=
    if nExpr == 0 && !hasGather && explicitTt != some .blankNode then
      err "RML-Core, Term Maps: term map"
        "a term map needs a constant, a reference or a template (only a blank-node map may have none)"
    else []
  let constErrs := consts.flatMap (checkConstant c pos n)
  let tplErrs := (objectsOf g n (rmlIri "template")).flatMap (fun t => match t with
    | .literal l => checkTemplate c pos n l.val.lexicalForm
    | _ => err "RML-Core, Generating values with expressions: template" "rml:template must be a string")
  let refErrs := (objectsOf g n (rmlIri "reference")).flatMap (fun t => match t with
    | .literal l =>
        if validReference c.formulation l.val.lexicalForm then []
        else err "RML-Core, Generating values with expressions: reference"
               s!"'{l.val.lexicalForm}' is not a valid reference expression"
    | _ => err "RML-Core, Generating values with expressions: reference" "rml:reference must be a string")
  -- datatype and language
  let nDt := countOf g n "datatypeMap" + countOf g n "datatype"
  let nLg := countOf g n "languageMap" + countOf g n "language"
  let dtlg : List RmlError :=
    (if nDt > 1 then err "RML-Core, Datatypes of Literals" "at most one datatype map" else []) ++
    (if nLg > 1 then err "RML-Core, Language tags" "at most one language map" else []) ++
    (if nDt > 0 && nLg > 0 then
       err "RML-Core, Term Maps" "a term map has a datatype map or a language map, not both"
     else []) ++
    (if (nDt > 0 || nLg > 0) &&
        effectiveTermType g pos n explicitTt != .literal then
       err "RML-Core, Language tags and Datatypes of Literals"
         "only a term map with term type rml:Literal may have a datatype or a language"
     else [])
  let dtShortcut := (objectsOf g n (rmlIri "datatype")).flatMap (fun t =>
    checkConstant c .datatype n t)
  let lgShortcut := (objectsOf g n (rmlIri "language")).flatMap (fun t =>
    checkConstant c .language n t)
  multi ++ tooMany ++ ttErrs ++ needExpr ++ constErrs ++ tplErrs ++ refErrs ++
    dtlg ++ dtShortcut ++ lgShortcut

/-- The checks for a term map and, one level down, for its datatype map
    and language map. -/
def checkTermMap (c : Ctx) (pos : Position) (n : String) : List RmlError :=
  let g := c.g
  checkTermMapNoDt c pos n ++
    (nodesOf g n (rmlIri "datatypeMap")).flatMap (checkTermMapNoDt c .datatype) ++
    (nodesOf g n (rmlIri "languageMap")).flatMap (checkTermMapNoDt c .language)

/-- A join condition has exactly one child and one parent expression
    (RML-Core, "Joins": join condition). -/
def checkJoin (cChild cParent : Ctx) (site j : String) : List RmlError :=
  let g := cChild.g
  let side (c : Ctx) (short mapProp : String) (pos : Position) : List RmlError :=
    let nShort := countOf g j short
    let maps := nodesOf g j (rmlIri mapProp)
    if nShort + countOf g j mapProp != 1 then
      [RmlError.mapping site "RML-Core, Joins: join condition"
        s!"a join condition has exactly one rml:{short} or rml:{mapProp}"]
    else
      (objectsOf g j (rmlIri short)).flatMap (fun t => match t with
        | .literal l =>
            if validReference c.formulation l.val.lexicalForm then []
            else [RmlError.mapping site "RML-Core, Joins: join condition"
                   s!"'{l.val.lexicalForm}' is not a valid reference expression"]
        | _ => [RmlError.mapping site "RML-Core, Joins: join condition"
                 s!"rml:{short} must be a string"])
      ++ maps.flatMap (checkTermMap c pos)
  side cChild "child" "childMap" .child ++ side cParent "parent" "parentMap" .parent

/-- The logical source of a triples map, read the way the model reads
    it, for the "effectively equal" test of RML-Core "Joins". -/
def logicalSourceOf (g : Graph) (tm : String) : LogicalSource :=
  sourceAt g ((logicalSourceNode g tm).getD "")

/-- Two logical sources are effectively equal when every effective
    property is the same; the names of the nodes do not count. -/
def effectivelyEqual (a b : LogicalSource) : Bool := a == b

/-- A referencing object map: exactly one parent triples map, and join
    conditions unless the two logical sources are effectively equal. -/
def checkRefObjectMap (c : Ctx) (tmNodes : List String) (n : String) : List RmlError :=
  let g := c.g
  let site := c.site .object n
  let parents := nodesOf g n (rmlIri "parentTriplesMap")
  let joins := nodesOf g n (rmlIri "joinCondition")
  match parents with
  | [p] =>
      if !tmNodes.contains p then
        [RmlError.mapping site "RML-Core, Joins: referencing object map"
          s!"rml:parentTriplesMap {p} is not a triples map"]
      else
        let parentLs := (logicalSourceNode g p).getD ""
        let parentCtx : Ctx := { g := g, tm := p, formulation := formulationAt g parentLs }
        let need :=
          if joins.isEmpty &&
             !effectivelyEqual (logicalSourceOf g c.tm) (logicalSourceOf g p) then
            [RmlError.mapping site "RML-Core, Joins: join condition"
              "the logical sources are not effectively equal, so the referencing object map needs a join condition"]
          else []
        need ++ joins.flatMap (checkJoin c parentCtx site)
  | _ => [RmlError.mapping site "RML-Core, Joins: referencing object map"
           "a referencing object map has exactly one rml:parentTriplesMap"]

def checkPredicateObjectMap (c : Ctx) (tmNodes : List String) (pom : String) : List RmlError :=
  let g := c.g
  let site := s!"{c.tm} predicate-object map {pom}"
  let nPred := countOf g pom "predicateMap" + countOf g pom "predicate"
  let nObj := countOf g pom "objectMap" + countOf g pom "object"
  let shape :=
    (if nPred == 0 then
       [RmlError.mapping site "RML-Core, Mapping to RDF with Triples Maps: predicate-object map"
         "a predicate-object map has at least one predicate map"] else []) ++
    (if nObj == 0 then
       [RmlError.mapping site "RML-Core, Mapping to RDF with Triples Maps: predicate-object map"
         "a predicate-object map has at least one object map or referencing object map"] else [])
  let preds := (nodesOf g pom (rmlIri "predicateMap")).flatMap (checkTermMap c .predicate)
  let predShort := (objectsOf g pom (rmlIri "predicate")).flatMap
    (checkConstant c .predicate pom)
  let objs := (nodesOf g pom (rmlIri "objectMap")).flatMap (fun o =>
    if countOf g o "parentTriplesMap" > 0 then checkRefObjectMap c tmNodes o
    else checkTermMap c .object o)
  let objShort := (objectsOf g pom (rmlIri "object")).flatMap (checkConstant c .object pom)
  let graphs := (nodesOf g pom (rmlIri "graphMap")).flatMap (checkTermMap c .graph)
  let graphShort := (objectsOf g pom (rmlIri "graph")).flatMap (checkConstant c .graph pom)
  shape ++ preds ++ predShort ++ objs ++ objShort ++ graphs ++ graphShort

/-- Check the logical source of a triples map: the iterator must be a
    valid expression in the reference formulation. -/
def checkLogicalSource (c : Ctx) : List RmlError :=
  let g := c.g
  match logicalSourceNode g c.tm with
  | none => []
  | some ls =>
      let site := s!"{c.tm} logical source {ls}"
      match objectsOf g ls (rmlIri "iterator") with
      | [] => []
      | [.literal l] =>
          if c.formulation == jsonPathIri && (parseJsonPath l.val.lexicalForm).isNone then
            [RmlError.mapping site "RML-Core, Defining Iterables and Logical Sources: iterator"
              s!"'{l.val.lexicalForm}' is not a valid JSONPath iterator"]
          else []
      | _ => [RmlError.mapping site "RML-Core, Defining Iterables and Logical Sources: iterator"
               "a logical source has at most one rml:iterator, and it is a string"]

/-- Check one triples map. -/
def checkTriplesMap (g : Graph) (tmNodes : List String) (tm : String) : List RmlError :=
  let ls := (logicalSourceNode g tm).getD ""
  let c : Ctx := { g := g, tm := tm, formulation := formulationAt g ls }
  let site := tm
  let nSm := countOf g tm "subjectMap" + countOf g tm "subject"
  let subjShape :=
    if nSm == 0 then
      [RmlError.mapping site "RML-Core, Mapping to RDF with Triples Maps: triples map"
        "a triples map has exactly one subject map, and this one has none"]
    else if nSm > 1 then
      [RmlError.mapping site "RML-Core, Mapping to RDF with Triples Maps: triples map"
        "a triples map has exactly one subject map, and this one has more than one"]
    else []
  let nLs := countOf g tm "logicalSource"
  let lsShape :=
    if nLs > 1 then
      [RmlError.mapping site "RML-Core, Mapping to RDF with Triples Maps: triples map"
        "a triples map has at most one logical source"]
    else []
  let subjMaps := (nodesOf g tm (rmlIri "subjectMap")).flatMap (fun sm =>
    checkTermMap c .subject sm ++
    (objectsOf g sm (rmlIri "class")).flatMap (fun t => match t with
      | .iri _ => []
      | _ => [RmlError.mapping (c.site .subject sm)
               "RML-Core, Typing Resources (rml:class)" "the values of rml:class must be IRIs"]) ++
    (nodesOf g sm (rmlIri "graphMap")).flatMap (checkTermMap c .graph) ++
    (objectsOf g sm (rmlIri "graph")).flatMap (checkConstant c .graph sm))
  let subjShort := (objectsOf g tm (rmlIri "subject")).flatMap (checkConstant c .subject tm)
  let poms := (nodesOf g tm (rmlIri "predicateObjectMap")).flatMap
    (checkPredicateObjectMap c tmNodes)
  subjShape ++ lsShape ++ checkLogicalSource c ++ subjMaps ++ subjShort ++ poms

/-- Every violation of an RML-Core MUST clause in the mapping graph. An
    empty list means the mapping is valid as far as it can be judged
    without a record. -/
def validateMapping (g : Graph) : List RmlError :=
  let nodes := triplesMapNodes g
  nodes.flatMap (checkTriplesMap g nodes)

end L4Factoidal.RML
