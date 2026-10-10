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
  /-- Every triples map node of the document, for references to them. -/
  tmNodes     : List String := []

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
def checkTermMapBase (c : Ctx) (pos : Position) (n : String) : List RmlError :=
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
      ++ maps.flatMap (checkTermMapBase c pos)
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

/-- The checks for the gather properties of a term map (RML-CC,
    "Vocabulary definition"): a gather map has exactly one `rml:gather`, a
    non-empty list of term maps (or referencing members), exactly one
    `rml:gatherAs` that names a list or a container, at most one
    `rml:strategy` that is `rml:append` or `rml:cartesianProduct`, and at
    most one boolean `rml:allowEmptyListAndContainer`. The properties
    mean nothing without `rml:gather`. -/
def checkGather (c : Ctx) (pos : Position) (n : String) : List RmlError :=
  let g := c.g
  let site := c.site pos n
  let err (msg : String) : List RmlError :=
    [RmlError.mapping site "RML-CC, Vocabulary definition: rml:GatherMap" msg]
  let nG := countOf g n "gather"
  let others := ["gatherAs", "strategy", "allowEmptyListAndContainer"].filter
    (fun p => countOf g n p > 0)
  if nG == 0 then
    (if others.isEmpty then []
     else err "rml:gatherAs, rml:strategy and rml:allowEmptyListAndContainer need rml:gather")
  else
    let kindErrs :=
      match objectsOf g n (rmlIri "gatherAs") with
      | [.iri i] => if (gatherKindOf i.val).isSome then []
                    else err "rml:gatherAs is rdf:List, rdf:Seq, rdf:Bag or rdf:Alt"
      | _ => err "a gather map has exactly one rml:gatherAs"
    let stratErrs :=
      match objectsOf g n (rmlIri "strategy") with
      | [] => []
      | [.iri i] => if (gatherStrategyOf i.val).isSome then []
                    else err "rml:strategy is rml:append or rml:cartesianProduct"
      | _ => err "a gather map has at most one rml:strategy"
    let emptyErrs :=
      match objectsOf g n (rmlIri "allowEmptyListAndContainer") with
      | [] => []
      | [.literal l] => if l.val.lexicalForm == "true" || l.val.lexicalForm == "false" then []
                        else err "rml:allowEmptyListAndContainer is true or false"
      | _ => err "a gather map has at most one rml:allowEmptyListAndContainer"
    let items :=
      match objectsOf g n (rmlIri "gather") with
      | [h] => listItems g h
      | _ => []
    let listErrs :=
      if nG > 1 then err "a gather map has exactly one rml:gather"
      else if items.isEmpty then err "rml:gather is a non-empty list of term maps"
      else []
    let memberErrs := items.flatMap (fun t => match nodeKey t with
      | none => err "a member of a gather map is a term map"
      | some k =>
          if countOf g k "parentTriplesMap" > 0 then
            -- a referencing member
            (nodesOf g k (rmlIri "parentTriplesMap")).flatMap (fun p =>
              if c.tmNodes.contains p then []
              else err s!"rml:parentTriplesMap {p} is not a triples map")
          else checkTermMapNoDt c pos k)
    kindErrs ++ stratErrs ++ emptyErrs ++ listErrs ++ memberErrs

/-- The triples maps a triples map quotes: the `rml:quotedTriplesMap` of
    its subject map and of its object maps. -/
def quotedTargets (g : Graph) (tm : String) : List String :=
  let sms := nodesOf g tm (rmlIri "subjectMap")
  let oms := (nodesOf g tm (rmlIri "predicateObjectMap")).flatMap
    (fun p => nodesOf g p (rmlIri "objectMap"))
  (sms ++ oms).flatMap (fun n => nodesOf g n (rmlIri "quotedTriplesMap"))

/-- Does a triples map quote itself, directly or through the maps it
    quotes? A quoted triple would then contain itself. The search stops
    after as many steps as there are triples maps. -/
def quotesItself (g : Graph) (count : Nat) (start : String) : Bool :=
  let rec go : Nat → List String → Bool
    | 0, _ => false
    | f + 1, frontier =>
        let next := (frontier.flatMap (quotedTargets g)).eraseDups
        next.contains start || (!next.isEmpty && go f next)
  go (count + 1) [start]

/-- The checks for the star map properties of a term map (RML-star,
    "Generating quoted triples with RML-star" and "Generating quoted
    triples from multiple sources"): `rml:quotedTriplesMap` belongs to a
    subject map or an object map, names a triples map, and, when that map
    has a logical source that is not effectively equal to the one of the
    map that quotes it, comes with at least one join condition. -/
def checkStar (c : Ctx) (pos : Position) (n : String) : List RmlError :=
  let g := c.g
  let site := c.site pos n
  let err (msg : String) : List RmlError :=
    [RmlError.mapping site "RML-star, Generating quoted triples with RML-star" msg]
  match nodesOf g n (rmlIri "quotedTriplesMap") with
  | [] => []
  | qs =>
      let position :=
        if pos == .subject || pos == .object then []
        else err "rml:quotedTriplesMap is the property of a star map, which is a subject map or an object map"
      let joins := nodesOf g n (rmlIri "joinCondition")
      let perTarget := qs.flatMap (fun q =>
        if !c.tmNodes.contains q then
          err s!"rml:quotedTriplesMap {q} is not a triples map"
        else
          let parentCtx : Ctx :=
            { g := g, tm := q, formulation := formulationAt g ((logicalSourceNode g q).getD "")
              tmNodes := c.tmNodes }
          (if joins.isEmpty &&
              !effectivelyEqual (logicalSourceOf g c.tm) (logicalSourceOf g q) then
             [RmlError.mapping site "RML-star, Generating quoted triples from multiple sources"
               "the logical sources are not effectively equal, so the star map needs a join condition"]
           else []) ++
          joins.flatMap (checkJoin c parentCtx site))
      position ++ perTarget

/-- The checks for a term map, its datatype map and language map, its
    gather properties and its star map properties. -/
def checkTermMap (c : Ctx) (pos : Position) (n : String) : List RmlError :=
  checkTermMapBase c pos n ++ checkGather c pos n ++ checkStar c pos n

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
  -- RML-star: a quoted triples map is named by a star map, which sits in a
  -- subject map or an object map; the predicate-object map itself is not
  -- one, and a predicate-object map without an object map is not valid
  -- for that reason either way.
  let onPom : List RmlError :=
    if countOf g pom "quotedTriplesMap" > 0 then
      [RmlError.mapping site "RML-star, Generating quoted triples with RML-star"
        "rml:quotedTriplesMap is the property of a star map; a predicate-object map has it in an object map"]
    else []
  shape ++ onPom ++ preds ++ predShort ++ objs ++ objShort ++ graphs ++ graphShort

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
  let c : Ctx := { g := g, tm := tm, formulation := formulationAt g ls, tmNodes := tmNodes }
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
  -- RML-star: the classes are subclasses of rml:TriplesMap, and the shapes of the
  -- specification (shapes/star.ttl) allow one of them, not both.
  let typed := fun (cls : String) => (objectsOf g tm rdfTypeStr).any (fun t => match t with
    | .iri i => i.val == rmlIri cls | _ => false)
  let bothClasses :=
    if typed "AssertedTriplesMap" && typed "NonAssertedTriplesMap" then
      [RmlError.mapping site "RML-star, Generating quoted triples with RML-star: shapes"
        "a triples map is an rml:AssertedTriplesMap or an rml:NonAssertedTriplesMap, not both"]
    else []
  -- RML-star: "rml:NonAssertedTriplesMap must always be called with
  -- rml:quotedTriplesMap": a non-asserted map that nothing quotes generates nothing.
  let neverQuoted :=
    if typed "NonAssertedTriplesMap" &&
       !(tmNodes.any (fun other => (quotedTargets g other).contains tm)) then
      [RmlError.mapping site "RML-star, Generating quoted triples with RML-star"
        "an rml:NonAssertedTriplesMap must be named by an rml:quotedTriplesMap"]
    else []
  let cyclic :=
    if quotesItself g tmNodes.length tm then
      [RmlError.mapping site "RML-star, Generating deeply nested quoted triples"
        "a triples map cannot quote itself, directly or through the maps it quotes"]
    else []
  let poms := (nodesOf g tm (rmlIri "predicateObjectMap")).flatMap
    (checkPredicateObjectMap c tmNodes)
  subjShape ++ lsShape ++ bothClasses ++ neverQuoted ++ cyclic ++ checkLogicalSource c ++
    subjMaps ++ subjShort ++ poms

/-- Every violation of an RML-Core MUST clause in the mapping graph. An
    empty list means the mapping is valid as far as it can be judged
    without a record. -/
def validateMapping (g : Graph) : List RmlError :=
  let nodes := triplesMapNodes g
  nodes.flatMap (checkTriplesMap g nodes)

end L4Factoidal.RML
