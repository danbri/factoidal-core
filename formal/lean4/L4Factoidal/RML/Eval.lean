/-
L4Factoidal.RML.Eval — run a mapping over its sources.

Spec: RML-Core §"Generating RDF terms" and §"Generating triples".

## What a record is, and why it is not a string map

A record is the JSON value one iteration of the logical source yields.
A reference is evaluated against it as a JSONPath, and the value that
comes back CARRIES ITS TYPE — `10` is an `xsd:integer`, not the string
`"10"`. Flattening a record to `String → Option String` at the door
throws that away before the term is built, and the corpus measures it
(`RMLTC0002a-JSON` expects `"10"^^xsd:integer`).

## Sources are supplied, not read

`evalMapping` takes the source documents as a list of
`(path, Json)` pairs. Reading a file needs I/O; deciding what a
mapping means does not, and keeping the second a total function of
explicit inputs is the purity doctrine this port follows everywhere.
-/
import L4Factoidal.RML.FromGraph
import L4Factoidal.RML.JsonPath
import L4Factoidal.RML.Value
import L4Factoidal.RML.Error
import L4Factoidal.RML.Record
import L4Factoidal.RML.Open
import L4Factoidal.RML.Star
import L4Factoidal.JSON.Parser

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.JSON

/-- Fill in the site of an error that does not have one yet. -/
def RmlError.withSite (site : String) (e : RmlError) : RmlError :=
  if e.site.isEmpty then { e with site := site } else e

/-- The records of a JSON document under a logical source's iterator.
    With NO iterator the whole document is one record. -/
def recordsOf (src : LogicalSource) (doc : Json) : List Json :=
  match src.iterator with
  | none     => [doc]
  | some itr => evalPath itr doc

/-- The values a reference selects from a record, with the data errors
    met (`Record.values`). -/
def refValuesE (rec' : Record) (r : String) : List RVal × List RmlError :=
  rec'.values r

/-- The values of a reference, with a data error read as no value. -/
def refValues (rec' : Record) (r : String) : List RVal := (refValuesE rec' r).1

/-- The single-value lookup `generateTerm` takes. The FIRST value
    wins; `termsOf` below is what handles the multi-valued case, and
    the two are kept apart so a single-valued position cannot silently
    take one of several. -/
def lookup1 (rec' : Record) : String → Option String := fun r =>
  (refValues rec' r).head?.map (·.lexical)

/-- Collect the terms and errors of a list of generation results. -/
def collectGen (rs : List (Except RmlError (Option Term))) : List Term × List RmlError :=
  rs.foldl (fun (acc : List Term × List RmlError) r =>
    match r with
    | .ok (some t) => (acc.1 ++ [t], acc.2)
    | .ok none     => acc
    | .error e     => (acc.1, acc.2 ++ [e])) ([], [])

/-- Every term a map generates from one record, and the data errors met
    while generating them.

    A REFERENCE map is multi-valued: `$.amounts[*]` selects three
    values and generates three terms, and taking only the first loses
    two triples that the corpus expects. A TEMPLATE map is the cross
    product of its references' values (RML-Core, "Template": the n-ary
    Cartesian product). -/
def termsOfE (base : Option String) (tm : TermMap) (rec' : Record) (naturalTypes : Bool)
    : List Term × List RmlError :=
  match tm.form with
  | .reference r =>
      let tt := tm.termType.getD (defaultTermType tm.form)
      let (vals, errs) := refValuesE rec' r
      let (ts, es) := collectGen (vals.map (fun v =>
        match tt with
        | .literal =>
            -- The SOURCE's datatype applies only when the map states
            -- neither a datatype nor a language: `rml:datatype` and
            -- `rml:language` both override it.
            let tm' := if naturalTypes && tm.datatype.isNone && tm.language.isNone
                       then { tm with datatype := v.natural } else tm
            generateTermE base tm' (fun f => if f == r then some v.lexical else none)
        | _ => generateTermE base tm (fun f => if f == r then some v.lexical else none)))
      (ts, errs ++ es)
  | .template raw =>
      -- A TEMPLATE over a multi-valued reference produces one term
      -- per COMBINATION. `$.Student[*].Name` selecting two names in
      -- `http://example.com/Student/{$.Student[*].Name}` means two
      -- subjects, and taking only the first lost half of
      -- `RMLTC0025c`'s output -- with the right predicate and the
      -- right objects on the half that survived, which is why the
      -- count was the only sign.
      let segs := parseTemplate raw
      let names := segs.foldl (fun acc seg => match seg with
        | .reference f => if acc.contains f then acc else acc ++ [f]
        | _            => acc) ([] : List String)
      let looked := names.map (fun f => refValuesE rec' f)
      let valueLists := looked.map (fun p => p.1.map (·.lexical))
      let refErrs := looked.flatMap (·.2)
      let combos := valueLists.foldl (fun acc vs =>
        acc.flatMap (fun a => vs.map (fun v => a ++ [v]))) [([] : List String)]
      let (ts, es) := collectGen (combos.map (fun combo =>
        generateTermE base tm (fun f =>
          ((names.zip combo).find? (fun (n, _) => n == f)).map (·.2))))
      (ts, refErrs ++ es)
  | _ => collectGen [generateTermE base tm (lookup1 rec')]

/-- The terms of `termsOfE`, with data errors read as missing terms. -/
def termsOf (base : Option String) (tm : TermMap) (rec' : Record) (naturalTypes : Bool)
    : List Term :=
  (termsOfE base tm rec' naturalTypes).1

/-- A term map whose value is a DATATYPE or a LANGUAGE: the lexical
    form of the first term it generates, and the errors met. -/
def stringOfE (base : Option String) (tm : TermMap) (rec' : Record)
    : Option String × List RmlError :=
  let (ts, es) := termsOfE base tm rec' false
  (ts.head?.bind (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | _          => none), es)

def stringOf (base : Option String) (tm : TermMap) (rec' : Record) : Option String :=
  (stringOfE base tm rec').1

/-- One quad, before the dataset is assembled. `targets` names the
    logical targets (RML-IO) the quad is exported to: those of every
    term map involved in generating it. Empty means the default
    target. -/
structure QuadOut where
  s : Subject
  p : WfIri
  o : Term
  g : Option Term
  targets : List String := []
deriving Repr

private def toSubject? (t : Term) : Option Subject :=
  match t with
  | .iri i   => some (.iri i)
  | .bnode b => some (.bnode b)
  | _        => none

private def toPred? (t : Term) : Option WfIri :=
  match t with | .iri i => some i | _ => none

/-- A term map in an IRI POSITION — a subject, a predicate, a graph.
    The default term type there is `iri`, not `literal`:
    `defaultTermType` reads only the FORM, and a subject map written
    `rml:subjectMap [ rml:reference "$.FirstName" ]` is a reference,
    so it defaulted to a literal and produced no subject at all
    (`RMLTC0019a`). Position decides this, and only the caller knows
    the position. -/
def asIri (tm : TermMap) : TermMap :=
  match tm.termType with
  | some _ => tm
  | none   => { tm with termType := some .iri }

/-- A term map whose value is a plain STRING — a `rml:languageMap`.
    A language tag is not an IRI, and `defaultTermType` sends a
    template to `iri`, so `rml:languageMap [ rml:template
    "{$.language}-{$.region}" ]` produced the IRI
    `http://example.com/en-GB` where the tag `en-GB` was meant
    (`RMLTC0031c`). A `rml:datatypeMap` is the opposite case and keeps
    `asIri`: a datatype IS an IRI. -/
def asLiteral (tm : TermMap) : TermMap :=
  match tm.termType with
  | some _ => tm
  | none   => { tm with termType := some .literal }

/-- A blank-node label built from a triples map's id and a record's
    position. Non-name characters are dropped: an id is an IRI, and
    `:` and `/` are not blank-node label characters. -/
def anonLabel (id : String) (i : Nat) : String :=
  String.ofList (id.toList.filter (fun c => c.isAlphanum)) ++ "r" ++ toString i

/-! ## What a generated term needs alongside it

Most terms stand alone. A GATHER map (RML-CC) generates the head of a
collection or container, and the triples that give that head its
members have to be emitted with it; so does a quoted triple (RML-star),
whose reifier needs a `rdf:reifies` triple. A term therefore travels as a
`Gen`: the term, and the `Extra`s to emit in the same graph as the
triple the term is part of.

A collection is not rendered where it is made. A NAMED collection (one
whose head is an IRI or a blank node the mapping names) that comes up
more than once -- in several iterations, or from several members of a
cartesian product -- is ONE collection, so its members are appended
across all of them (RML-CC, "Generating well-formed named collections").
That can only be decided after every iteration has run, so `GatherUse`
records the use and `renderUses` merges and renders them at the end. -/

/-- One occurrence of a collection or container: the head, what kind,
    the members in order, and where it is wanted. -/
structure GatherUse where
  head    : Term
  /-- The mapping named the head (a template, constant or reference). A
      fresh head is never merged with another. -/
  named   : Bool
  kind    : GatherKind
  members : List Term
  /-- Names the occurrence: the same collection, generated once and placed
      with several triples, carries one origin, so merging counts it once
      and does not append its members twice. -/
  origin  : String := ""
  graph   : Option Term := none
  targets : List String := []

inductive Extra where
  | triple (t : Triple)
  | collection (c : GatherUse)

structure Gen where
  term   : Term
  extras : List Extra := []

/-- Everything a stretch of evaluation produces. -/
structure Out where
  quads : List QuadOut := []
  uses  : List GatherUse := []
  errs  : List RmlError := []

instance : Append Out := ⟨fun a b =>
  { quads := a.quads ++ b.quads, uses := a.uses ++ b.uses, errs := a.errs ++ b.errs }⟩

def Out.empty : Out := {}

def Out.join (os : List Out) : Out := os.foldl (· ++ ·) Out.empty

/-- Emit the extras of a generated term in a graph, for a quad with the
    given targets. -/
def placeExtras (es : List Extra) (g : Option Term) (targets : List String) : Out :=
  Out.join (es.map (fun e => match e with
    | .triple t => { quads := [{ s := t.s, p := t.p, o := t.o, g := g, targets := targets }] }
    | .collection c => { uses := [{ c with graph := g, targets := targets }] }))

def nubStrings (xs : List String) : List String :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

/-- The cartesian product of a list of lists, in lexicographic order of
    the lists' own order. -/
def cartesian {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | xs :: rest => xs.flatMap (fun x => (cartesian rest).map (fun r => x :: r))

private def rdfIri (n : String) : WfIri :=
  if h : isIri ("http://www.w3.org/1999/02/22-rdf-syntax-ns#" ++ n)
  then ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#" ++ n, h⟩ else ⟨"urn:invalid", rfl⟩

def rdfTypeIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

private def labelOf : Term → String
  | .iri i => i.val
  | .bnode b => b
  | _ => "x"

/-- The triples of one collection or container. A list's cells are the
    head and fresh blank nodes; a container's members are numbered from 1.
    Every triple is in the use's graph and carries its targets. -/
def renderUse (u : GatherUse) : List QuadOut × List RmlError :=
  match toSubject? u.head with
  | none => ([], [RmlError.data "" "RML-CC, Gather maps: head"
              "the head of a collection or container must be an IRI or a blank node"])
  | some hs =>
      let mk (s : Subject) (p : WfIri) (o : Term) : QuadOut :=
        { s := s, p := p, o := o, g := u.graph, targets := u.targets }
      match u.kind with
      | .list =>
          let n := u.members.length
          let cellSubject (k : Nat) : Subject :=
            if k == 0 then hs else .bnode (labelOf u.head ++ "_cell" ++ toString k)
          (u.members.zipIdx.flatMap (fun (m, k) =>
            [ mk (cellSubject k) (rdfIri "first") m
            , mk (cellSubject k) (rdfIri "rest")
                (if k + 1 == n then .iri (rdfIri "nil") else (cellSubject (k + 1)).toTerm) ]), [])
      | kind =>
          let cls := match kind with | .seq => "Seq" | .alt => "Alt" | _ => "Bag"
          (mk hs rdfTypeIri (.iri (rdfIri cls)) ::
           u.members.zipIdx.map (fun (m, k) => mk hs (rdfIri ("_" ++ toString (k + 1))) m), [])

/-- Merge the NAMED uses with the same head, graph and kind, appending
    members in the order the uses were produced; leave the others. A use
    that repeats an origin in the same graph is the same collection placed
    with another triple, and is dropped. -/
def mergeUses (us : List GatherUse) : List GatherUse :=
  us.foldl (fun (acc : List GatherUse) u =>
    if acc.any (fun v => !u.origin.isEmpty && v.origin == u.origin && v.graph == u.graph) then acc
    else if !u.named then acc ++ [u]
    else
      match acc.findIdx? (fun v => v.named && v.head == u.head && v.graph == u.graph && v.kind == u.kind) with
      | some i => acc.modify i (fun v =>
          { v with members := v.members ++ u.members, targets := nubStrings (v.targets ++ u.targets) })
      | none => acc ++ [u]) []

/-- Render every collection of a run. -/
def renderUses (us : List GatherUse) : List QuadOut × List RmlError :=
  let rs := (mergeUses us).map renderUse
  (rs.flatMap (·.1), rs.flatMap (·.2))

/-- The quads of an `Out`, collections rendered. -/
def Out.finalQuads (o : Out) : List QuadOut := o.quads ++ (renderUses o.uses).1

/-- The subjects one triples map generates from one record, and the data
    errors met, for the plain forms only. `i` is the record's position,
    which an ANONYMOUS blank-node subject needs.

    `rml:subjectMap [ rml:termType rml:BlankNode ]` states a term type
    and no form at all, and means "a fresh blank node for each
    record". `generateTerm` has no form to work from and returns
    nothing, so `RMLTC0012e` produced an empty graph from a mapping
    that describes four triples. -/
def subjectsOfE (tm : TriplesMap) (rec' : Record) (i : Nat) : List Subject × List RmlError :=
  match tm.subject.form, tm.subject.termType with
  | .unknown, some .blankNode => ([.bnode (anonLabel tm.id i)], [])
  | _, _ =>
      let (ts, es) := termsOfE tm.base (asIri tm.subject) rec' false
      (ts.filterMap toSubject?, es)

def subjectsOf (tm : TriplesMap) (rec' : Record) (i : Nat) : List Subject :=
  (subjectsOfE tm rec' i).1

/-- The graph terms of a list of graph maps, each with the logical
    targets of the graph map that produced it. An EMPTY list is not "the
    default graph" -- it is "this level states no graph", and the caller
    unions the levels before deciding. -/
def graphTermsWithTargetsE (base : Option String) (gs : List TermMap) (rec' : Record)
    : List (Term × List String) × List RmlError :=
  let rs : List (List Term × List RmlError × List String) := gs.map (fun gm =>
    let r := termsOfE base (asIri gm) rec' false
    (r.1, r.2, gm.targets))
  (rs.flatMap (fun (ts, _, tg) => ts.map (fun t => (t, tg))), rs.flatMap (·.2.1))

/-- The graph terms a list of graph maps produces. -/
def graphTermsOf (base : Option String) (gs : List TermMap) (rec' : Record) : List Term :=
  ((graphTermsWithTargetsE base gs rec').1).map (·.1)

/-- The targets of the graph map(s) that generate graph `g`, across both
    levels. A quad in the default graph has none. -/
def targetsOfGraph (gts : List (Term × List String)) (g : Option Term) : List String :=
  match g with
  | none => []
  | some t => (gts.filter (fun e => e.1 == t)).flatMap (·.2)

/-- The graphs one triple goes into: the UNION of the subject map's
    graph maps and the predicate-object map's, and the default graph
    when that union is empty.

    Union, not override. R2RML and RML both say the graphs of a
    triple are the union of the two levels, and treating a
    predicate-object map's graph as a replacement put
    `student_10 practises sport_100` in the predicate-object map's
    graph only, where `RMLTC0009b` expects it in the subject map's as
    well -- one quad short, with every other quad right. -/
def graphsFor (sgraphs pgraphs : List Term) : List (Option Term) :=
  let u := sgraphs ++ pgraphs.filter (fun g => !(sgraphs.contains g))
  match u with
  | [] => [none]
  | _  => u.map some

/-- The STRINGS one side of a join produces from a record. Both sides
    go through term generation, so a template side is expanded before
    the comparison rather than compared as a template. -/
def joinValues (tm : TermMap) (rec' : Record) : List String :=
  (termsOf none tm rec' false).filterMap (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | .bnode b   => some b
    | _          => none)

/-- Does a join hold between a child record and a parent record? -/
def joinHolds (js : List JoinCondition) (child parent : Record) : Bool :=
  js.all (fun j =>
    let cs := joinValues j.child child
    let ps := joinValues j.parent parent
    cs.any (fun c => ps.contains c))

/-! ## Sources

Reading a file is the host's job (`RML.Open.FileAccess`). The evaluator
takes the iterations of every logical source ALREADY OPENED, in a
`SourceTable`, so that a parent triples map's records are not parsed
again for every child record. Two logical sources are the same entry
when they are effectively equal (RML-Core, Joins). -/

abbrev SourceTable := List (LogicalSource × Except RmlError (List Record))

/-- A triples map with no logical source at all (RML-Core allows the
    omission when every term map is constant or a blank-node map)
    iterates exactly once, over nothing. -/
def LogicalSource.isAbsent (ls : LogicalSource) : Bool :=
  ls.path.isEmpty && ls.accessKind.isEmpty && ls.refFormulation.isEmpty &&
  ls.iterator.isNone

/-- The iterations of a logical source, from the table. -/
def SourceTable.get (t : SourceTable) (ls : LogicalSource) : Except RmlError (List Record) :=
  if ls.isAbsent then .ok [Record.json .null]
  else
    match t.find? (fun e => e.1 == ls) with
    | some (_, r) => r
    | none => .error (RmlError.source ls.path
                "RML-IO, Logical Source: source" "the source was not opened")

/-- Open every distinct logical source of a mapping. -/
def buildSourceTable (m : Mapping) (fa : FileAccess) : SourceTable :=
  m.foldl (fun (acc : SourceTable) tm =>
    if tm.source.isAbsent || acc.any (fun e => e.1 == tm.source) then acc
    else acc ++ [(tm.source, openRecords tm.source fa)]) []

/-- A table over already-parsed JSON documents, by path: the form the
    virtual source and the older tests use. A path with no document is
    a source error; an invalid iterator selects nothing. -/
def jsonSourceTable (m : Mapping) (docFor : String → Option Json) : SourceTable :=
  m.foldl (fun (acc : SourceTable) tm =>
    if tm.source.isAbsent || acc.any (fun e => e.1 == tm.source) then acc
    else
      let r : Except RmlError (List Record) :=
        match docFor tm.source.path with
        | none => .error (RmlError.source tm.source.path
                    "RML-Core, Defining Iterables and Logical Sources: data source"
                    s!"the source '{tm.source.path}' cannot be read")
        | some doc => .ok ((recordsOf tm.source doc).map Record.json)
      acc ++ [(tm.source, r)]) []

structure Env where
  all : Mapping
  src : SourceTable

/-! ## Term maps, evaluated

`gensOfE` is the one place a term map becomes terms. A plain map
(constant, reference, template) goes through `termsOfE`; a gather map
builds collections. Evaluation is by FUEL, because a gather map's members
are term maps and the nesting is read from a graph that could be cyclic:
`fuel` bounds the depth and an exhausted fuel generates nothing. -/

def gatherFuel : Nat := 48

/-- The head of a collection when the mapping names none: a fresh blank
    node, distinct for every triples map, record, position in the mapping
    and member combination. -/
def freshHead (tmId path : String) (i k : Nat) : Term :=
  .bnode s!"gather_{anonLabel tmId 0}_{path}_r{i}_c{k}"

/-- The collections a gather map builds from its members' term lists:
    one for the `append` strategy, one per combination for the cartesian
    product; none when there is nothing to gather. -/
def collectionsOf (gs : GatherSpec) (lists : List (List Gen)) : List (List Gen) :=
  match gs.strategy with
  | .append => let all := lists.flatMap id; if all.isEmpty then [] else [all]
  | .cartesianProduct => if lists.any (·.isEmpty) then [] else cartesian lists

/-- A quoted triple (RML-star): the reifier of the triple term, and the
    `rdf:reifies` triple that gives the reifier its meaning, with whatever
    the triple's own terms need (a nested quoted triple's reifier, a
    collection). -/
def quotedGen (s : Subject) (p : WfIri) (o : Term) (extras : List Extra) : Gen :=
  let tt := Term.tripleTerm s p o
  { term := reifierOf tt, extras := .triple (reifiesTriple tt) :: extras }

mutual

/-- The subjects of the parent triples map for the parent records a
    referencing object map (or a gather member) selects.

    With join conditions, a parent record is selected when every join
    holds. With NONE, the two logical sources must be effectively equal
    (`RML.Validate` checks it), and the parent iteration is the SAME
    iteration as the child's (RML-Core, Joins: the example with the
    thumbnail); pairing every child with every parent record would be a
    cross product that no mapping asks for. -/
def refGensE (fuel : Nat) (env : Env) (tm : TriplesMap) (i : Nat) (rec' : Record)
    (parentId : String) (joins : List JoinCondition) : List Gen × List RmlError :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    match env.all.find? (fun p => p.id == parentId) with
    | none => ([], [])
    | some parentMap =>
        match env.src.get parentMap.source with
        | .error e => ([], [e.withSite parentMap.id])
        | .ok precs =>
            let matched :=
              if joins.isEmpty && parentMap.source == tm.source then
                precs.zipIdx.filter (fun (_, pi) => pi == i)
              else precs.zipIdx.filter (fun (prec, _) => joinHolds joins rec' prec)
            let rs : List (List Gen × List RmlError) := matched.map (fun (prec, pi) =>
              let r := subjectGensE fuel env parentMap prec pi
              (r.1.map (fun (s, ex) => ({ term := s.toTerm, extras := ex } : Gen)), r.2))
            (rs.flatMap (·.1), rs.flatMap (·.2))

/-- The members of a gather map, evaluated: the terms of each member map,
    or of a referencing member. -/
def memberGensE (fuel : Nat) (env : Env) (tm : TriplesMap) (path : String) (i : Nat)
    (gs : GatherSpec) (rec' : Record) : List (List Gen × List RmlError) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    gs.members.zipIdx.map (fun (m, k) =>
      match m with
      | .term mm => gensOfE fuel env tm (path ++ s!".m{k}") i mm rec' true
      | .ref parentId joins => refGensE fuel env tm i rec' parentId joins)

/-- All the terms a term map generates from one record, with what they
    need alongside. -/
def gensOfE (fuel : Nat) (env : Env) (tm : TriplesMap) (path : String) (i : Nat)
    (m : TermMap) (rec' : Record) (naturalTypes : Bool) : List Gen × List RmlError :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    match m.gather with
    | none =>
        match m.quoted with
        | some q => quotedGensE fuel env tm i q rec'
        | none =>
            let r := termsOfE tm.base m rec' naturalTypes
            (r.1.map (fun t => { term := t }), r.2)
    | some gs =>
        let memberRes := memberGensE fuel env tm path i gs rec'
        let collections := collectionsOf gs (memberRes.map (·.1))
        -- the heads: named by the map's expression, or fresh
        let named := match m.form with | .unknown => false | _ => true
        let headRes : List Term × List RmlError :=
          if named then termsOfE tm.base (asIri { m with gather := none }) rec' false
          else ([], [])
        let one (c : List Gen) (k : Nat) (head : Term) : Gen :=
          { term := head
            extras := .collection { head := head, named := named, kind := gs.kind,
                                    members := c.map (·.term),
                                    origin := s!"{tm.id}|{path}|r{i}|c{k}|{labelOf head}" }
                        :: c.flatMap (·.extras) }
        let gens : List Gen :=
          if collections.isEmpty then
            if gs.allowEmpty then
              match gs.kind with
              | .list => [{ term := .iri (rdfIri "nil") }]
              | _ => (if named then headRes.1 else [freshHead tm.id path i 0]).map (one [] 0)
            else []
          else
            collections.zipIdx.flatMap (fun (c, k) =>
              (if named then headRes.1 else [freshHead tm.id path i k]).map (one c k))
        (gens, (memberRes.flatMap (·.2)) ++ headRes.2)

/-- A star map (RML-star): the reifiers of the triples its quoted triples
    map generates. Without join conditions, and over the same logical
    source, the quoted triples are those the quoted map generates for the
    SAME iteration; with join conditions, for every parent iteration the
    joins select (RML-star, "Generating quoted triples from multiple
    sources"). -/
def quotedGensE (fuel : Nat) (env : Env) (tm : TriplesMap) (i : Nat) (q : QuotedSpec)
    (rec' : Record) : List Gen × List RmlError :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    match env.all.find? (fun p => p.id == q.parent) with
    | none => ([], [])
    | some qm =>
        match env.src.get qm.source with
        | .error e => ([], [e.withSite qm.id])
        | .ok precs =>
            let matched : List (Record × Nat) :=
              if q.joins.isEmpty && qm.source == tm.source then
                precs.zipIdx.filter (fun (_, pi) => pi == i)
              else precs.zipIdx.filter (fun (prec, _) => joinHolds q.joins rec' prec)
            let rs := matched.map (fun (prec, pi) => quotedTriplesOfE fuel env qm pi prec)
            (rs.flatMap (·.1), rs.flatMap (·.2))

/-- The triples a triples map generates from one record, each as a quoted
    triple: the class triples of the subject map, then those of every
    predicate-object map. Graph maps do not matter: a quoted triple is a
    triple, not a quad. -/
def quotedTriplesOfE (fuel : Nat) (env : Env) (qm : TriplesMap) (pi : Nat) (prec : Record)
    : List Gen × List RmlError :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    let sg := subjectGensE fuel env qm prec pi
    let perSubject : List (List Gen × List RmlError) := sg.1.map (fun (s, sx) =>
      let classGens : List Gen := qm.classes.filterMap (fun c =>
        if h : isIri c then some (quotedGen s rdfTypeIri (.iri ⟨c, h⟩) sx) else none)
      let pomRes : List (List Gen × List RmlError) := qm.poms.zipIdx.map (fun (pom, pk) =>
        let predRes := pom.predicates.map (fun pm => termsOfE qm.base (asIri pm) prec false)
        let preds := predRes.flatMap (fun r => r.1.filterMap toPred?)
        let objRes := pom.objects.zipIdx.map (fun (om, oi) =>
          objectGensE fuel env qm pk oi om prec pi)
        let objs := objRes.flatMap (·.1)
        (preds.flatMap (fun p => objs.map (fun o => quotedGen s p o.term (sx ++ o.extras))),
         predRes.flatMap (·.2) ++ objRes.flatMap (·.2)))
      (classGens ++ pomRes.flatMap (·.1), pomRes.flatMap (·.2)))
    (perSubject.flatMap (·.1), sg.2 ++ perSubject.flatMap (·.2))

/-- The Gens of a subject map for one record: a gather map builds a
    collection, a star map quotes triples; a plain map yields subjects as
    `subjectsOfE` does. -/
def subjectGensE (fuel : Nat) (env : Env) (tm : TriplesMap) (rec' : Record) (i : Nat)
    : List (Subject × List Extra) × List RmlError :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    if tm.subject.gather.isSome || tm.subject.quoted.isSome then
      let r := gensOfE fuel env tm "s" i (asIri tm.subject) rec' false
      (r.1.filterMap (fun g => (toSubject? g.term).map (fun s => (s, g.extras))), r.2)
    else
      let r := subjectsOfE tm rec' i
      (r.1.map (fun s => (s, [])), r.2)

/-- The terms an OBJECT map generates from one record, and the errors
    met. A term map's datatype map and language map are evaluated first
    and become the datatype and language of the literals it makes. A
    referencing object map yields the SUBJECTS of the parent triples map
    for the parent records the joins select. -/
def objectGensE (fuel : Nat) (env : Env) (tm : TriplesMap) (pi oi : Nat) (om : ObjectMap)
    (rec' : Record) (i : Nat) : List Gen × List RmlError :=
  match fuel with
  | 0 => ([], [])
  | fuel + 1 =>
    match om with
    | .term base dtm lm =>
        let dtRes : Option String × List RmlError :=
          match dtm with
          | some m => stringOfE tm.base (asIri m) rec'
          | none   => (none, [])
        let lmRes : Option String × List RmlError :=
          match lm with
          | some m => stringOfE tm.base (asLiteral m) rec'
          | none   => (none, [])
        let base1 := match dtRes.1 with
          | some d => { base with datatype := some d }
          | none   => base
        let base2 := match lmRes.1 with
          | some l => { base1 with language := some l }
          | none   => base1
        let r := gensOfE fuel env tm s!"p{pi}.o{oi}" i base2 rec' true
        (r.1, dtRes.2 ++ lmRes.2 ++ r.2)
    | .ref parentId joins => refGensE fuel env tm i rec' parentId joins

end

/-- The logical targets of an object map: those of its term map and of
    its datatype and language maps. -/
def ObjectMap.targets : ObjectMap → List String
  | .term base dtm lm =>
      base.targets ++ (dtm.map (·.targets)).getD [] ++ (lm.map (·.targets)).getD []
  | .ref _ _ => []

/-- The quads one predicate-object map generates for one subject. The
    targets of a quad are those of the subject map, the predicate map,
    the object map (with its datatype and language maps) and the graph
    map that generated the quad's graph (RML-IO, "Logical Target in
    RML": every term map involved). -/
def pomQuadsE (env : Env) (tm : TriplesMap) (pi : Nat) (sgraphs : List (Term × List String))
    (rec' : Record) (i : Nat) (s : Subject) (sExtras : List Extra)
    (pom : PredicateObjectMap) : Out :=
  let predRes : List (List WfIri × List String × List RmlError) := pom.predicates.map (fun pm =>
    let r := termsOfE tm.base (asIri pm) rec' false
    (r.1.filterMap toPred?, pm.targets, r.2))
  let pgRes := graphTermsWithTargetsE tm.base pom.graphs rec'
  let graphs := graphsFor (sgraphs.map (·.1)) (pgRes.1.map (·.1))
  let graphTargetsOf := targetsOfGraph (sgraphs ++ pgRes.1)
  let objRes : List (List Gen × List String × List RmlError) :=
    pom.objects.zipIdx.map (fun (om, oi) =>
      let r := objectGensE gatherFuel env tm pi oi om rec' i
      (r.1, om.targets, r.2))
  let outs : List Out := predRes.flatMap (fun (ps, pt, _) =>
    ps.flatMap (fun p => objRes.flatMap (fun (os, ot, _) =>
      os.flatMap (fun o => graphs.map (fun g =>
        let targets := nubStrings (tm.subject.targets ++ pt ++ ot ++ graphTargetsOf g)
        { quads := [{ s := s, p := p, o := o.term, g := g, targets := targets }] } ++
          placeExtras (sExtras ++ o.extras) g targets)))))
  Out.join outs ++ { errs := pgRes.2 ++ predRes.flatMap (·.2.2) ++ objRes.flatMap (·.2.2) }

/-- Everything one triples map generates for one subject of one record:
    the subject's own collection, the `rml:class` triples, then each
    predicate-object map's. -/
def subjectQuadsE (env : Env) (tm : TriplesMap) (sgraphs : List (Term × List String))
    (rec' : Record) (i : Nat) (s : Subject) (sExtras : List Extra) : Out :=
  let typeQuads : List QuadOut :=
    tm.classes.flatMap (fun c =>
      match (if h : isIri c then some (⟨c, h⟩ : WfIri) else none) with
      | none    => []
      | some ci => (graphsFor (sgraphs.map (·.1)) []).map (fun g =>
          ({ s := s, p := rdfTypeIri, o := .iri ci, g := g,
             targets := nubStrings (tm.subject.targets ++ targetsOfGraph sgraphs g) } : QuadOut)))
  -- the subject's own structure is emitted in the subject-level graphs even
  -- when the map has no predicate-object map
  let own : Out := Out.join ((graphsFor (sgraphs.map (·.1)) []).map (fun g =>
    placeExtras sExtras g (nubStrings (tm.subject.targets ++ targetsOfGraph sgraphs g))))
  own ++ { quads := typeQuads } ++
    Out.join (tm.poms.zipIdx.map (fun (pom, pi) =>
      pomQuadsE env tm pi sgraphs rec' i s sExtras pom))

/-- What one triples map generates from an ALREADY-INDEXED record list.

    The index travels WITH each record rather than being its position
    in this list, and that is the point: a caller that narrows the list
    — the virtual source's row pushdown — must keep each record's
    ORIGINAL index, because `anonLabel` turns it into a blank-node
    label. Renumbering after a filter moves every blank node the row
    generates, which is
    <https://github.com/danbri/factoidal/issues/558>. -/
def outOfRecords (env : Env) (tm : TriplesMap) (recs : List (Record × Nat)) : Out :=
  let per : List Out := recs.map (fun (rec', i) =>
    let sr := subjectGensE gatherFuel env tm rec' i
    let gr := graphTermsWithTargetsE tm.base tm.graphs rec'
    Out.join (sr.1.map (fun (s, ex) => subjectQuadsE env tm gr.1 rec' i s ex)) ++
      { errs := sr.2 ++ gr.2 })
  let o := Out.join per
  { o with errs := o.errs.map (RmlError.withSite tm.id) }

/-- The quads of `outOfRecords`, with data errors dropped. -/
def quadsOfRecords (env : Env) (tm : TriplesMap) (recs : List (Record × Nat)) : List QuadOut :=
  (outOfRecords env tm recs).finalQuads

/-- What one triples map generates. A source that cannot be opened is a
    SOURCE error: the file named by `rml:path` does not exist
    (`RMLTC0002e`), which is not the same as a source with no rows. -/
def outOfMap (env : Env) (tm : TriplesMap) : Out :=
  if !tm.asserted then {}
  else
  match env.src.get tm.source with
  | .error e => { errs := [e.withSite tm.id] }
  | .ok recs => outOfRecords env tm recs.zipIdx

/-- `rml:defaultGraph` names the default graph, so a graph map that
    produces it is the same as producing none. -/
def defaultGraphIri : String := rmlNs ++ "defaultGraph"

/-- A blank node of the output is scoped to ONE graph (RML-Core, "Scope of
    Blank Nodes"): the same label in two graphs is two blank nodes, so a
    triple generated into several graphs must not share its blank nodes
    between them. A quad in a named graph gets its blank nodes labelled
    with the graph; the default graph keeps the labels as they are. -/
def scopeTerm (suffix : String) : Term → Term
  | .bnode b => .bnode (b ++ suffix)
  | .tripleTerm s p o =>
      .tripleTerm (match s with | .bnode b => .bnode (b ++ suffix) | s => s) p (scopeTerm suffix o)
  | t => t

def scopeBlankNodes (qs : List QuadOut) : List QuadOut :=
  qs.map (fun q =>
    match q.g with
    | none => q
    | some gt =>
        let suffix := "~g~" ++ (match gt with
          | .iri i => i.val | .bnode b => "_:" ++ b | _ => "")
        { q with
          s := match q.s with | .bnode b => .bnode (b ++ suffix) | s => s
          o := scopeTerm suffix q.o })

/-- The outcome of running a mapping: the quads, and every reason the
    run is to be rejected. A caller that accepts a run with errors has
    chosen to read an RML-Core data error as a missing term. -/
structure EvalResult where
  quads  : List QuadOut
  errors : List RmlError

/-- Run a whole mapping over its opened sources. `defaultBase` is the
    base IRI in force where a triples map states none — the test corpus
    gives one per case (`rml:defaultBaseIRI`, `base_iri` in its own
    metadata), and without it a template that produces `Carlos` yields
    no term at all instead of `http://example.com/Carlos`
    (`RMLTC0019a`). Collections are rendered once every triples map has
    run, because a named collection is merged across them. -/
def evalMappingWith (defaultBase : Option String) (m : Mapping) (src : SourceTable)
    : EvalResult :=
  let m := m.map (fun t => { t with base := t.base.orElse (fun _ => defaultBase) })
  let env : Env := { all := m, src := src }
  let o := Out.join (m.map (outOfMap env))
  let rendered := renderUses o.uses
  { quads := scopeBlankNodes ((o.quads ++ rendered.1).map (fun q =>
      match q.g with
      | some (.iri i) => if i.val == defaultGraphIri then { q with g := none } else q
      | _             => q))
    errors := o.errs ++ rendered.2 }

/-- Run a whole mapping, opening each logical source through `fa`. -/
def evalMappingFiles (defaultBase : Option String) (m : Mapping) (fa : FileAccess)
    : EvalResult :=
  evalMappingWith defaultBase m (buildSourceTable m fa)

/-- Run a whole mapping over already-parsed JSON documents. -/
def evalMappingE (defaultBase : Option String) (m : Mapping)
    (docFor : String → Option Json) : EvalResult :=
  evalMappingWith defaultBase m (jsonSourceTable m docFor)

/-- The quads of a run over JSON documents, ignoring its errors. -/
def evalMapping (defaultBase : Option String) (m : Mapping)
    (docFor : String → Option Json) : List QuadOut :=
  (evalMappingE defaultBase m docFor).quads

end L4Factoidal.RML
