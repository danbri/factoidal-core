/-
L4Factoidal.RML.FromGraph — read a mapping document, which is RDF,
into `RML.Model`.

A mapping is not a file format: it is a GRAPH, and the reader walks it
by predicate. A term (subject, predicate, object) that the model has
no place for is skipped rather than guessed at; a triples map with no
subject map produces no triples at all, which is what a mapping that
says nothing about subjects should produce.
-/
import L4Factoidal.RML.Model
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RML

open L4Factoidal.RDF

def rmlNs : String := "http://w3id.org/rml/"
def rdfTypeStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- A subject or object as the key the reader indexes by. Blank nodes
    and IRIs are both node identities here, so one string names
    either — and the two spaces are kept apart by the `_:` prefix,
    which no IRI has. -/
def nodeKey : Term → Option String
  | .iri i   => some i.val
  | .bnode b => some ("_:" ++ b)
  | _        => none

def subjKey : Subject → String
  | .iri i   => i.val
  | .bnode b => "_:" ++ b

/-- Every object of `(s, rml:p)`. -/
def objectsOf (g : Graph) (s : String) (p : String) : List Term :=
  (g.filter (fun t => subjKey t.s == s && t.p.val == p)).map (·.o)

def objOf (g : Graph) (s p : String) : Option Term := (objectsOf g s p).head?

def strOf (g : Graph) (s p : String) : Option String :=
  (objOf g s p).bind (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | _          => none)

def nodesOf (g : Graph) (s p : String) : List String :=
  (objectsOf g s p).filterMap nodeKey

/-- The `rml:termType` an IRI names. -/
def termTypeOf (iri : String) : Option TermType :=
  if iri == rmlNs ++ "IRI" then some .iri
  else if iri == rmlNs ++ "URI" then some .uri
  else if iri == rmlNs ++ "UnsafeIRI" then some .unsafeIri
  else if iri == rmlNs ++ "BlankNode" then some .blankNode
  else if iri == rmlNs ++ "Literal" then some .literal
  else none

/-- A TERM MAP at node `n` without its gather map, or the SHORTCUT form
    where the value sits directly on the parent (`rml:predicate ex:id`
    rather than `rml:predicateMap [ rml:constant ex:id ]`). -/
def baseTermMapAt (g : Graph) (n : String) : TermMap :=
  let form : TermMapForm :=
    match strOf g n (rmlNs ++ "template") with
    | some t => .template t
    | none =>
      match strOf g n (rmlNs ++ "reference") with
      | some r => .reference r
      | none =>
        match objOf g n (rmlNs ++ "constant") with
        | some t => .constant t
        | none   => .unknown
  { form     := form
    termType := (strOf g n (rmlNs ++ "termType")).bind termTypeOf
    datatype := strOf g n (rmlNs ++ "datatype")
    language := strOf g n (rmlNs ++ "language")
    targets  := nodesOf g n (rmlNs ++ "logicalTarget") }

/-- A constant term map from a shortcut object. -/
def constantMap (t : Term) : TermMap := { form := .constant t }

/-- One side of a join: the `rml:child` / `rml:parent` SHORTCUT (a
    reference expression) or the `rml:childMap` / `rml:parentMap` term
    map, which may hold a template. -/
def joinSide (g : Graph) (j : String) (short mapProp : String) : Option TermMap :=
  match strOf g j (rmlNs ++ short) with
  | some r => some { form := .reference r }
  | none   => (nodesOf g j (rmlNs ++ mapProp)).head?.map (baseTermMapAt g)

def joinsAt (g : Graph) (n : String) : List JoinCondition :=
  (nodesOf g n (rmlNs ++ "joinCondition")).filterMap (fun j =>
    match joinSide g j "child" "childMap", joinSide g j "parent" "parentMap" with
    | some c, some p => some { child := c, parent := p }
    | _, _           => none)

/-- The star map facts of a term map at `n` (RML-star): the quoted
    triples map and the join conditions between its logical source and
    the star map's own. -/
def quotedAt (g : Graph) (n : String) : Option QuotedSpec :=
  (nodesOf g n (rmlNs ++ "quotedTriplesMap")).head?.map
    (fun q => { parent := q, joins := joinsAt g n })

def rdfFirstStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#first"
def rdfRestStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#rest"
def rdfNilStr : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#nil"

/-- The items of an RDF collection whose head is the term `h`, in order.
    The walk is bounded by the size of the graph, so a cyclic or
    malformed list ends instead of looping. -/
def listItems (g : Graph) (h : Term) : List Term :=
  let rec go (fuel : Nat) (cur : Term) (acc : List Term) : List Term :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
        match cur with
        | .iri i => if i.val == rdfNilStr then acc else acc
        | .bnode b =>
            let first := (g.filter (fun t => subjKey t.s == "_:" ++ b && t.p.val == rdfFirstStr)).map (·.o)
            let rest := (g.filter (fun t => subjKey t.s == "_:" ++ b && t.p.val == rdfRestStr)).map (·.o)
            match first.head?, rest.head? with
            | some f, some r => go fuel r (acc ++ [f])
            | some f, none => acc ++ [f]
            | _, _ => acc
        | _ => acc
  go (g.length + 1) h []

def gatherKindOf (iri : String) : Option GatherKind :=
  let r := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
  if iri == r ++ "List" then some .list
  else if iri == r ++ "Seq" then some .seq
  else if iri == r ++ "Bag" then some .bag
  else if iri == r ++ "Alt" then some .alt
  else none

def gatherStrategyOf (iri : String) : Option GatherStrategy :=
  if iri == rmlNs ++ "append" then some .append
  else if iri == rmlNs ++ "cartesianProduct" then some .cartesianProduct
  else none

/-- How deep gather maps nest before the reader stops reading (a
    mapping graph could be cyclic). -/
def readFuel : Nat := 8

/-- A Function Map, Parameter Map or Return Map at `n`: the shortcut
    property (`rml:function`, `rml:parameter`, `rml:return`) holds the
    named node itself, the map property (`rml:functionMap`,
    `rml:parameterMap`, `rml:returnMap`) holds a term map that generates
    it (RML-FNML, "Definitions"). -/
def fnSlotAt (g : Graph) (n : String) (shortcut mapProp : String) : Option TermMap :=
  match (objectsOf g n (rmlNs ++ shortcut)).head? with
  | some t => some (constantMap t)
  | none => (nodesOf g n (rmlNs ++ mapProp)).head?.map (baseTermMapAt g)

mutual

/-- A term map at `n`, with the gather map, the star map, the function
    execution and the condition it carries, to a depth. -/
def termMapAtF : Nat → Graph → String → TermMap
  | 0, g, n => baseTermMapAt g n
  | f + 1, g, n =>
      let base := baseTermMapAt g n
      let fx := (nodesOf g n (rmlNs ++ "functionExecution")).head?.bind (execAt f g)
      { base with
        gather := gatherAt f g n
        quoted := quotedAt g n
        form := (match fx with | some fe => .function fe | none => base.form)
        fnReturn := fnSlotAt g n "return" "returnMap"
        condition := (nodesOf g n (rmlNs ++ "condition")).head?.map (termMapAtF f g) }

/-- The function execution at `x` (RML-FNML): the Function Map and the
    inputs, each a Parameter Map with the term map that supplies its
    value (`rml:inputValueMap`, or the constant `rml:inputValue`). -/
def execAt : Nat → Graph → String → Option FnExec
  | 0, _, _ => none
  | f + 1, g, x =>
      (fnSlotAt g x "function" "functionMap").map (fun fm =>
        { function := fm
          inputs := (nodesOf g x (rmlNs ++ "input")).filterMap (fun i =>
            match fnSlotAt g i "parameter" "parameterMap" with
            | none => none
            | some pm =>
                let value : Option TermMap :=
                  match (objectsOf g i (rmlNs ++ "inputValue")).head? with
                  | some t => some (constantMap t)
                  | none => (nodesOf g i (rmlNs ++ "inputValueMap")).head?.map (termMapAtF f g)
                value.map (fun v => { parameter := pm, value := v })) })

/-- The gather map at `n`: its members (term maps, or referencing
    members), `rml:gatherAs`, `rml:strategy` and
    `rml:allowEmptyListAndContainer`. `none` when `n` has no
    `rml:gather`. -/
def gatherAt : Nat → Graph → String → Option GatherSpec
  | 0, _, _ => none
  | f + 1, g, n =>
      match (objectsOf g n (rmlNs ++ "gather")).head? with
      | none => none
      | some h =>
          let members : List GatherMember := (listItems g h).filterMap (fun t =>
            (nodeKey t).map (fun k =>
              match (nodesOf g k (rmlNs ++ "parentTriplesMap")).head? with
              | some parent => GatherMember.ref parent (joinsAt g k)
              | none => GatherMember.term (termMapAtF f g k)))
          some { members := members
                 kind := ((strOf g n (rmlNs ++ "gatherAs")).bind gatherKindOf).getD .list
                 strategy := ((strOf g n (rmlNs ++ "strategy")).bind gatherStrategyOf).getD .append
                 allowEmpty := (strOf g n (rmlNs ++ "allowEmptyListAndContainer")) == some "true" }

end

/-- A TERM MAP at node `n`. -/
def termMapAt (g : Graph) (n : String) : TermMap := termMapAtF readFuel g n

/-- Term maps for a property that has both a MAP form and a SHORTCUT
    form — `rml:predicateMap` / `rml:predicate`, `rml:objectMap` /
    `rml:object`, `rml:graphMap` / `rml:graph`. Both are collected:
    a predicate-object map may state several of each. -/
def mapsFor (g : Graph) (n : String) (mapProp shortcutProp : String) : List TermMap :=
  (nodesOf g n (rmlNs ++ mapProp)).map (termMapAt g)
  ++ (objectsOf g n (rmlNs ++ shortcutProp)).map constantMap

/-- An object map: a `rml:parentTriplesMap` makes it a reference, and
    everything else makes it a term map. -/
def objectMapAt (g : Graph) (n : String) : ObjectMap :=
  match (nodesOf g n (rmlNs ++ "parentTriplesMap")).head? with
  | some parent => .ref parent (joinsAt g n)
  | none =>
      .term (termMapAt g n)
        ((nodesOf g n (rmlNs ++ "datatypeMap")).head?.map (termMapAt g))
        ((nodesOf g n (rmlNs ++ "languageMap")).head?.map (termMapAt g))

def pomAt (g : Graph) (n : String) : PredicateObjectMap :=
  { predicates := mapsFor g n "predicateMap" "predicate"
    objects    := (nodesOf g n (rmlNs ++ "objectMap")).map (objectMapAt g)
                  ++ (objectsOf g n (rmlNs ++ "object")).map
                       (fun t => ObjectMap.term (constantMap t) none none)
    graphs     := mapsFor g n "graphMap" "graph" }

/-- The reference formulation IRI of the logical source at `ls`. A blank
    node typed `rml:XPathReferenceFormulation` names the XPath
    formulation (RML-IO, "Reference formulations"). -/
def formulationAt (g : Graph) (ls : String) : String :=
  match objOf g ls (rmlNs ++ "referenceFormulation") with
  | some (.iri i) => i.val
  | some (.bnode b) =>
      if (objectsOf g ("_:" ++ b) rdfTypeStr).any (fun t => match t with
           | .iri i => i.val == rmlNs ++ "XPathReferenceFormulation" | _ => false)
      then rmlNs ++ "XPath" else ""
  | _ => ""

/-- The XPath namespace declarations of a reference formulation node
    (RML-IO, `rml:namespace` with `rml:namespacePrefix` and
    `rml:namespaceURL`). -/
def namespacesAt (g : Graph) (ls : String) : List (String × String) :=
  match objOf g ls (rmlNs ++ "referenceFormulation") with
  | some (.bnode b) =>
      (nodesOf g ("_:" ++ b) (rmlNs ++ "namespace")).filterMap (fun ns =>
        match strOf g ns (rmlNs ++ "namespacePrefix"), strOf g ns (rmlNs ++ "namespaceURL") with
        | some p, some u => some (p, u)
        | _, _ => none)
  | _ => []

/-- The logical source at node `n`: the source access description
    (`rml:source`) and the reference formulation and iterator. -/
def sourceAt (g : Graph) (n : String) : LogicalSource :=
  let src := (nodesOf g n (rmlNs ++ "source")).head?
  let srcStr := fun (p : String) => (src.bind (fun s => strOf g s (rmlNs ++ p)))
  { path           := (srcStr "path").getD ""
    iterator       := strOf g n (rmlNs ++ "iterator")
    refFormulation := formulationAt g n
    root           := (srcStr "root").getD ""
    encoding       := (srcStr "encoding").getD ""
    compression    := (srcStr "compression").getD ""
    nulls          := (src.map (fun s =>
                         (objectsOf g s (rmlNs ++ "null")).filterMap (fun t => match t with
                           | .literal l => some l.val.lexicalForm
                           | _ => none))).getD []
    namespaces     := namespacesAt g n
    accessKind     := (src.bind (fun s =>
                         (objectsOf g s rdfTypeStr).filterMap (fun t => match t with
                           | .iri i =>
                               if i.val.startsWith "http://www.wiwiss.fu-berlin.de/suhl/bizer/D2RQ/"
                               then some i.val else none
                           | _ => none) |>.head?)).getD "" }

/-- The logical targets of a mapping graph: every node a term map
    names with `rml:logicalTarget`, and every node typed
    `rml:LogicalTarget`. The access description is the node
    `rml:target` points at. -/
def logicalTargetsOf (g : Graph) : List LogicalTarget :=
  let typed := (g.filter (fun t =>
      t.p.val == rdfTypeStr &&
      (match t.o with | .iri i => i.val == rmlNs ++ "LogicalTarget" | _ => false))).map
    (fun t => subjKey t.s)
  let named := (g.filter (fun t => t.p.val == rmlNs ++ "logicalTarget")).filterMap
    (fun t => nodeKey t.o)
  let nodes := (typed ++ named).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) ([] : List String)
  nodes.map (fun n =>
    let acc := (nodesOf g n (rmlNs ++ "target")).head?
    let accStr := fun (p : String) => (acc.bind (fun a => strOf g a (rmlNs ++ p)))
    { id            := n
      path          := (accStr "path").getD ""
      root          := (accStr "root").getD ""
      serialization := (strOf g n (rmlNs ++ "serialization")).getD ""
      -- RML-IO puts `rml:compression` and `rml:encoding` on the target
      -- access description; the corpus also writes them beside
      -- `rml:serialization` on the logical target itself, so both are read.
      compression   := ((accStr "compression").orElse (fun _ => strOf g n (rmlNs ++ "compression"))).getD ""
      encoding      := ((accStr "encoding").orElse (fun _ => strOf g n (rmlNs ++ "encoding"))).getD ""
      accessKind    :=
        match acc with
        | none => "no access description"
        | some a =>
            if (strOf g a (rmlNs ++ "path")).isSome then ""
            else "an access description other than a file path" })

/-- The classes whose instances are triples maps. RML-star adds the
    asserted and non-asserted subclasses. -/
def triplesMapClasses : List String :=
  [rmlNs ++ "TriplesMap", rmlNs ++ "AssertedTriplesMap", rmlNs ++ "NonAssertedTriplesMap"]

/-- The properties only a triples map has. A resource that states one is a
    triples map whether or not it is typed (the RML-FNML test cases leave
    their triples maps untyped; R2RML makes the type optional too). -/
def triplesMapProperties : List String :=
  [rmlNs ++ "logicalSource", rmlNs ++ "subjectMap", rmlNs ++ "subject",
   rmlNs ++ "predicateObjectMap"]

/-- Every triples map node in the graph, once, in graph order: a node typed
    as a triples map, and a node that has a property only a triples map has. -/
def triplesMapNodes (g : Graph) : List String :=
  ((g.filter (fun t =>
      (t.p.val == rdfTypeStr &&
       (match t.o with
        | .iri i => triplesMapClasses.contains i.val
        | _      => false)) ||
      triplesMapProperties.contains t.p.val)).map (fun t => subjKey t.s)).foldl
    (fun acc n => if acc.contains n then acc else acc ++ [n]) []

/-- Every triples map in the graph. A map with NO subject map is
    dropped: it can generate nothing, and keeping it would put an
    entry in the mapping that produces no triples for a reason the
    caller cannot see. `RML.Validate` reports that case as an error;
    this reader stays total. -/
def mappingOf (g : Graph) : Mapping :=
  let tmNodes := triplesMapNodes g
  tmNodes.filterMap (fun n =>
    -- The SUBJECT map, either as a map or as the `rml:subject`
    -- shortcut. Everything else about the triples map is the same
    -- either way — reading the shortcut in a branch of its own
    -- dropped the predicate-object maps with it, so `RMLTC0029a`
    -- produced nothing at all from a mapping that has one.
    let smNode := (nodesOf g n (rmlNs ++ "subjectMap")).head?
    let subject : Option TermMap := match smNode with
      | some sm => some (termMapAt g sm)
      | none    => (objectsOf g n (rmlNs ++ "subject")).head?.map constantMap
    -- RML-star: a map typed `rml:NonAssertedTriplesMap` only quotes; one
    -- typed `rml:AssertedTriplesMap` as well asserts (the shapes forbid
    -- both, and `RML.Validate` reports it).
    let types := objectsOf g n rdfTypeStr
    let isType := fun (c : String) => types.any (fun t => match t with | .iri i => i.val == c | _ => false)
    let asserted := !isType (rmlNs ++ "NonAssertedTriplesMap") || isType (rmlNs ++ "AssertedTriplesMap")
    match subject with
    | none    => none
    | some sm =>
        some { id      := n
               asserted := asserted
               base    := strOf g n (rmlNs ++ "baseIRI")
               source  := sourceAt g ((nodesOf g n (rmlNs ++ "logicalSource")).head?.getD "")
               subject := sm
               classes := (smNode.map (fun x =>
                            (objectsOf g x (rmlNs ++ "class")).filterMap (fun t =>
                              match t with | .iri i => some i.val | _ => none))).getD []
               graphs  := (smNode.map (fun x => mapsFor g x "graphMap" "graph")).getD []
               poms    := (nodesOf g n (rmlNs ++ "predicateObjectMap")).map (pomAt g) })

end L4Factoidal.RML
