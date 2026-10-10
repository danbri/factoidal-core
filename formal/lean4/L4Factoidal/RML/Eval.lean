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
import L4Factoidal.JSON.Parser

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.JSON

/-- The records one logical source yields. With NO iterator the whole
    document is one record. -/
def recordsOf (src : LogicalSource) (doc : Json) : List Json :=
  match src.iterator with
  | none     => [doc]
  | some itr => evalPath itr doc

/-- Fill in the site of an error that does not have one yet. -/
def RmlError.withSite (site : String) (e : RmlError) : RmlError :=
  if e.site.isEmpty then { e with site := site } else e

/-- Look a reference up in one record, with the errors met on the way.

    A reference selecting SEVERAL values is not an error: RML says a term
    map generates one term per value. A reference that selects a JSON
    ARRAY or OBJECT is: it denotes no value, and RML-Core's term
    generation rules need a value to build a term from. The corpus has
    this case (`RMLTC0025b`: `$.amounts` where `$.amounts[*]` was meant)
    and expects the mapping to be rejected. `null` selects nothing, as
    RML-Core's "Empty" does (`RMLTC0013a`). -/
def refValuesE (rec' : Json) (r : String) : List RVal × List RmlError :=
  (evalPath r rec').foldl (fun (acc : List RVal × List RmlError) j =>
    match j with
    | .array _ | .object _ =>
        (acc.1, acc.2 ++ [RmlError.data "" "RML-Core, Generated RDF Term of a Term Map: reference value"
          s!"reference '{r}' selects a JSON array or object, not a value"])
    | _ =>
        match rvalOf j with
        | some v => (acc.1 ++ [v], acc.2)
        | none   => acc) ([], [])

/-- The values of a reference, with a data error read as no value. -/
def refValues (rec' : Json) (r : String) : List RVal := (refValuesE rec' r).1

/-- The single-value lookup `generateTerm` takes. The FIRST value
    wins; `termsOf` below is what handles the multi-valued case, and
    the two are kept apart so a single-valued position cannot silently
    take one of several. -/
def lookup1 (rec' : Json) : String → Option String := fun r =>
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
def termsOfE (base : Option String) (tm : TermMap) (rec' : Json) (naturalTypes : Bool)
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
def termsOf (base : Option String) (tm : TermMap) (rec' : Json) (naturalTypes : Bool)
    : List Term :=
  (termsOfE base tm rec' naturalTypes).1

/-- A term map whose value is a DATATYPE or a LANGUAGE: the lexical
    form of the first term it generates, and the errors met. -/
def stringOfE (base : Option String) (tm : TermMap) (rec' : Json)
    : Option String × List RmlError :=
  let (ts, es) := termsOfE base tm rec' false
  (ts.head?.bind (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | _          => none), es)

def stringOf (base : Option String) (tm : TermMap) (rec' : Json) : Option String :=
  (stringOfE base tm rec').1

/-- One quad, before the dataset is assembled. -/
structure QuadOut where
  s : Subject
  p : WfIri
  o : Term
  g : Option Term
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

/-- The subjects one triples map generates from one record, and the data
    errors met. `i` is the record's position, which an ANONYMOUS
    blank-node subject needs.

    `rml:subjectMap [ rml:termType rml:BlankNode ]` states a term type
    and no form at all, and means "a fresh blank node for each
    record". `generateTerm` has no form to work from and returns
    nothing, so `RMLTC0012e` produced an empty graph from a mapping
    that describes four triples. -/
def subjectsOfE (tm : TriplesMap) (rec' : Json) (i : Nat) : List Subject × List RmlError :=
  match tm.subject.form, tm.subject.termType with
  | .unknown, some .blankNode => ([.bnode (anonLabel tm.id i)], [])
  | _, _ =>
      let (ts, es) := termsOfE tm.base (asIri tm.subject) rec' false
      (ts.filterMap toSubject?, es)

def subjectsOf (tm : TriplesMap) (rec' : Json) (i : Nat) : List Subject :=
  (subjectsOfE tm rec' i).1

/-- The graph terms a list of graph maps produces. An EMPTY list is
    not "the default graph" -- it is "this level states no graph", and
    the caller unions the levels before deciding. -/
def graphTermsOfE (base : Option String) (gs : List TermMap) (rec' : Json)
    : List Term × List RmlError :=
  let rs := gs.map (fun gm => termsOfE base (asIri gm) rec' false)
  (rs.flatMap (·.1), rs.flatMap (·.2))

def graphTermsOf (base : Option String) (gs : List TermMap) (rec' : Json) : List Term :=
  (graphTermsOfE base gs rec').1

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

def rdfTypeIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-- The STRINGS one side of a join produces from a record. Both sides
    go through term generation, so a template side is expanded before
    the comparison rather than compared as a template. -/
def joinValues (tm : TermMap) (rec' : Json) : List String :=
  (termsOf none tm rec' false).filterMap (fun t => match t with
    | .literal l => some l.val.lexicalForm
    | .iri i     => some i.val
    | .bnode b   => some b
    | _          => none)

/-- Does a join hold between a child record and a parent record? -/
def joinHolds (js : List JoinCondition) (child parent : Json) : Bool :=
  js.all (fun j =>
    let cs := joinValues j.child child
    let ps := joinValues j.parent parent
    cs.any (fun c => ps.contains c))

/-- The terms an OBJECT map generates from one record, and the errors
    met. A term map's datatype map and language map are evaluated first
    and become the datatype and language of the literals it makes. A
    referencing object map yields the SUBJECTS of the parent triples map
    for the parent records the joins select. -/
def objectTermsE (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    (om : ObjectMap) (rec' : Json) : List Term × List RmlError :=
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
      let r := termsOfE tm.base base2 rec' true
      (r.1, dtRes.2 ++ lmRes.2 ++ r.2)
  | .ref parentId joins =>
      match all.find? (fun p => p.id == parentId) with
      | none => ([], [])
      | some parentMap =>
          match docFor parentMap.source.path with
          | none => ([], [RmlError.source parentMap.id
                      "RML-Core, Joins: parent logical source"
                      s!"the source '{parentMap.source.path}' of the parent triples map cannot be read"])
          | some pdoc =>
              let matched := ((recordsOf parentMap.source pdoc).zipIdx).filter
                        (fun (prec, _) => joinHolds joins rec' prec)
              let rs : List (List Term × List RmlError) := matched.map (fun (prec, pi) =>
                let r := subjectsOfE parentMap prec pi
                (r.1.map Subject.toTerm, r.2))
              (rs.flatMap (·.1), rs.flatMap (·.2))

/-- The quads one predicate-object map generates for one subject. -/
def pomQuadsE (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    (sgraphs : List Term) (rec' : Json) (s : Subject) (pom : PredicateObjectMap)
    : List QuadOut × List RmlError :=
  let predRes : List (List Term × List RmlError) :=
    pom.predicates.map (fun pm => termsOfE tm.base (asIri pm) rec' false)
  let preds : List WfIri := predRes.flatMap (fun r => r.1.filterMap toPred?)
  let pgRes := graphTermsOfE tm.base pom.graphs rec'
  let graphs := graphsFor sgraphs pgRes.1
  let objRes : List (List Term × List RmlError) :=
    pom.objects.map (fun om => objectTermsE all docFor tm om rec')
  let objs : List Term := objRes.flatMap (·.1)
  let quads : List QuadOut := preds.flatMap (fun p => objs.flatMap (fun o =>
    graphs.map (fun g => ({ s := s, p := p, o := o, g := g } : QuadOut))))
  (quads, pgRes.2 ++ predRes.flatMap (·.2) ++ objRes.flatMap (·.2))

/-- The quads one triples map generates for one subject of one record:
    the `rml:class` triples, then each predicate-object map's. -/
def subjectQuadsE (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    (sgraphs : List Term) (rec' : Json) (s : Subject) : List QuadOut × List RmlError :=
  let typeQuads : List QuadOut :=
    tm.classes.flatMap (fun c =>
      match (if h : isIri c then some (⟨c, h⟩ : WfIri) else none) with
      | none    => []
      | some ci => (graphsFor sgraphs []).map (fun g =>
          ({ s := s, p := rdfTypeIri, o := .iri ci, g := g } : QuadOut)))
  let perPom : List (List QuadOut × List RmlError) :=
    tm.poms.map (pomQuadsE all docFor tm sgraphs rec' s)
  (typeQuads ++ perPom.flatMap (·.1), perPom.flatMap (·.2))

/-- The quads one triples map generates from an ALREADY-INDEXED record
    list, and the errors met.

    The index travels WITH each record rather than being its position
    in this list, and that is the point: a caller that narrows the list
    — the virtual source's row pushdown — must keep each record's
    ORIGINAL index, because `anonLabel` turns it into a blank-node
    label. Renumbering after a filter moves every blank node the row
    generates, which is
    <https://github.com/danbri/factoidal/issues/558>. -/
def quadsOfRecordsE (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    (recs : List (Json × Nat)) : List QuadOut × List RmlError :=
  let per : List (List QuadOut × List RmlError) := recs.map (fun (rec', i) =>
    let sr := subjectsOfE tm rec' i
    let gr := graphTermsOfE tm.base tm.graphs rec'
    let perSubj : List (List QuadOut × List RmlError) :=
      sr.1.map (subjectQuadsE all docFor tm gr.1 rec')
    (perSubj.flatMap (·.1), sr.2 ++ gr.2 ++ perSubj.flatMap (·.2)))
  (per.flatMap (·.1), (per.flatMap (·.2)).map (RmlError.withSite tm.id))

/-- The quads of `quadsOfRecordsE`, with data errors dropped. -/
def quadsOfRecords (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    (recs : List (Json × Nat)) : List QuadOut :=
  (quadsOfRecordsE all docFor tm recs).1

/-- The quads one triples map generates, and the errors. `docFor`
    supplies a source document by path, and `all` the other triples maps
    a `rml:parentTriplesMap` can name. A source that cannot be read is a
    SOURCE error: the file named by `rml:path` does not exist
    (`RMLTC0002e`), which is not the same as a source with no rows. -/
def quadsOfMapE (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    : List QuadOut × List RmlError :=
  match docFor tm.source.path with
  | none => ([], [RmlError.source tm.id
              "RML-Core, Defining Iterables and Logical Sources: data source"
              s!"the source '{tm.source.path}' cannot be read"])
  | some doc => quadsOfRecordsE all docFor tm ((recordsOf tm.source doc).zipIdx)

def quadsOfMap (all : Mapping) (docFor : String → Option Json) (tm : TriplesMap)
    : List QuadOut :=
  (quadsOfMapE all docFor tm).1

/-- `rml:defaultGraph` names the default graph, so a graph map that
    produces it is the same as producing none. -/
def defaultGraphIri : String := rmlNs ++ "defaultGraph"

/-- The outcome of running a mapping: the quads, and every reason the
    run is to be rejected. A caller that accepts a run with errors has
    chosen to read an RML-Core data error as a missing term. -/
structure EvalResult where
  quads  : List QuadOut
  errors : List RmlError

/-- Run a whole mapping. `defaultBase` is the base IRI in force where
    a triples map states none — the test corpus gives one per case
    (`rml:defaultBaseIRI`, `base_iri` in its own metadata), and
    without it a template that produces `Carlos` yields no term at all
    instead of `http://example.com/Carlos` (`RMLTC0019a`). -/
def evalMappingE (defaultBase : Option String) (m : Mapping)
    (docFor : String → Option Json) : EvalResult :=
  let m := m.map (fun t => { t with base := t.base.orElse (fun _ => defaultBase) })
  let rs := m.map (quadsOfMapE m docFor)
  { quads := (rs.flatMap (·.1)).map (fun q =>
      match q.g with
      | some (.iri i) => if i.val == defaultGraphIri then { q with g := none } else q
      | _             => q)
    errors := rs.flatMap (·.2) }

/-- The quads of a run, ignoring its errors. -/
def evalMapping (defaultBase : Option String) (m : Mapping)
    (docFor : String → Option Json) : List QuadOut :=
  (evalMappingE defaultBase m docFor).quads

end L4Factoidal.RML
