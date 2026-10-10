/-
L4Factoidal.GRDDL.Agent — the GRDDL result of a document, with the
namespace (§3) and profile (§5) rules read from GRDDL RESULTS of the
second documents, computed to a fixpoint.

Spec: GRDDL, W3C Recommendation 11 September 2007
(https://www.w3.org/TR/grddl/).

§3 and §5 do not say "look for an element named
`namespaceTransformation`". They say: if the namespace document NSDOC,
identified by the IRI NS, has a GRDDL result that includes the triple
`NSDOC grddl:namespaceTransformation TX`, then TX is a GRDDL
transformation of every document whose root element has namespace name
NS (§5: the same with `grddl:profileTransformation` and a metadata
profile name). The GRDDL result of the second document is computed by
the same rules, so it may itself depend on a third document's result,
and a document may be its own namespace document (the `loop` tests).

So the GRDDL results of all the documents the source reaches are the
least solution of a system of monotone equations: a document's result is
the merge of its RDF/XML reading (if any) and the outputs of its
transformations, and its transformations are its own (§2, §4) plus the
ones the CURRENT results of its namespace and profile documents assert.
`glean` iterates that system from empty results. Each round can only
add transformations, there are finitely many documents and
transformations, and each transformation is a function of its source,
so the iteration reaches the fixpoint after at most as many rounds as
there are transformations; the round count is still bounded by `fuel`,
and `Gleaned.converged` says whether the bound was reached first. The
fixpoint is the merge of every GRDDL result: the "maximal result" of
the GRDDL Test Cases (§ Testing for Maximal Result).

## No I/O here

Retrieval is a parameter: `fetch iri` returns the representation, or
`none`. The harness passes an `IO` fetch over the vendored files; the
`#guard` cases below pass a pure table in `Id`. The fetch reports the
IRI it finally retrieved from (after HTTP redirection), because that is
the document's base IRI absent an in-document base (RFC 3986 §5.1.3),
which the base-URI tests exercise.
-/
import L4Factoidal.GRDDL.Discovery
import L4Factoidal.RDF.Graph
import L4Factoidal.RDF.Isomorphism

namespace L4Factoidal.GRDDL

open L4Factoidal.XML
open L4Factoidal.RDF
open L4Factoidal.XSLT

/-! ## Vocabulary -/

def namespaceTransformationIri : String := grddlNS ++ "namespaceTransformation"
def profileTransformationIri : String := grddlNS ++ "profileTransformation"

/-- The IRI without its fragment: the resource a retrieval targets. -/
def withoutFragment (iri : String) : String :=
  match iri.toList.findIdx? (· == '#') with
  | some i => String.ofList (iri.toList.take i)
  | none   => iri

/-- §3/§5: the objects of every triple `subj pred TX` in a GRDDL
    result, in graph order, duplicates removed. Only an IRI object names
    a transformation. -/
def assertedTransformations (g : Graph) (subj pred : String) : List String :=
  (g.filterMap (fun t =>
    let subjOk := match t.s with
      | .iri i => i.val == subj
      | .bnode _ => false
    if subjOk && t.p.val == pred then
      match t.o with
      | .iri i => some i.val
      | _      => none
    else none)).eraseDups

/-! ## Merge (§2 "the merge of F and G") -/

/-- Does a blank-node label have the form `g<digits>.<rest>` that
    `mergeApart` gives renamed labels? -/
def isMergePrefixed (b : BNodeId) : Bool :=
  match b.toList with
  | 'g' :: rest =>
      let ds := rest.takeWhile Char.isDigit
      !ds.isEmpty && (rest.drop ds.length).head? == some '.'
  | _ => false

/-- RDF 1.1 Semantics merge: blank nodes of each contribution are
    renamed apart before the union (set semantics, duplicates dropped).
    Contribution `i` gets the label prefix `g<i>.`; the digits before
    the first `.` determine `i`, so renamed labels from different
    contributions never coincide. The FIRST contribution keeps its own
    labels when none of them has that `g<digits>.` form, which keeps
    the common one-transformation result label-identical to its RDF/XML
    reading; otherwise it is renamed like the others. Plain list append
    would identify `_:b0` of one transform's output with `_:b0` of
    another's. -/
def mergeApart (gs : List Graph) : Graph :=
  let keepFirst := match gs.head? with
    | some g0 => !(g0.bnodes.any isMergePrefixed)
    | none    => true
  (gs.zipIdx.map (fun (g, i) =>
      if i == 0 && keepFirst then g
      else g.prefixBnodes ("g" ++ toString i ++ "."))).foldl Graph.union []

/-! ## Agent state -/

/-- A representation a fetch returned. -/
structure Representation where
  /-- The IRI the representation was retrieved from after any HTTP
      redirection. -/
  retrievedFrom : String
  text : String
deriving Repr, Inhabited

/-- A retrieved, well-formed XML source. -/
structure Source where
  retrievedFrom : String
  text : String
  doc : Document

/-- What the agent knows about one document, keyed by the IRI it was
    asked for (without fragment). -/
structure DocEntry where
  iri : String
  /-- `none`: not retrieved, or not well-formed XML. Either way it has
      no GRDDL result (§2 applies only to XML). -/
  src : Option Source
  txs : List String := []
  result : Graph := []

/-- A loaded stylesheet with its `xsl:import`/`xsl:include` targets. -/
abbrev Style := Document × List (String × Node)

structure AgentState where
  docs        : List DocEntry := []
  styles      : List (String × Option Style) := []
  applied     : List ((String × String) × Except String Graph) := []
  unretrieved : List String := []
  notXml      : List String := []
  refusals    : List String := []

/-- What `glean` reports. -/
structure Gleaned where
  /-- The merge of every GRDDL result the agent computed for the source. -/
  graph : Graph
  /-- The source's GRDDL transformations, every rule together. -/
  transformations : List String
  /-- The source's base IRI: in-document base, else retrieval IRI. -/
  base : String
  /-- Is the source itself RDF/XML (§3, the base case)? -/
  isRdfXml : Bool
  /-- IRIs the fetch could not supply (documents and stylesheets). -/
  unretrieved : List String
  /-- Retrieved documents that are not well-formed XML. -/
  notXml : List String
  /-- Transformations the XSLT engine declined, or whose output is not
      RDF/XML, with the reason. -/
  refusals : List String
  /-- Did the iteration reach its fixpoint within the round bound? -/
  converged : Bool

/-- §3: the namespace document a source's root element points at, and
    the namespace name the asserting triple must have as subject. -/
def namespaceOf (root : Node) : Option (String × String) :=
  (rootNamespaceUri root).bind (fun ns =>
    if ns.isEmpty then none else some (withoutFragment ns, ns))

/-- The second documents a source depends on: its namespace document
    and its custom profile documents. -/
def dependenciesOf (s : Source) : List String :=
  let root := s.doc.root
  ((namespaceOf root).map (·.1)).toList ++
    (customProfileUris s.retrievedFrom root).map withoutFragment

/-- A source's transformations, given the current results of the other
    documents: §2 + §4 from the document itself, §3 from its namespace
    document's result, §5 from each profile document's result. -/
def transformationsOf (s : Source) (resultOf : String → Graph) : List String :=
  let root := s.doc.root
  let same := sameDocumentTransformations s.retrievedFrom root
  let ns := match namespaceOf root with
    | some (docIri, nsName) =>
        assertedTransformations (resultOf docIri) nsName namespaceTransformationIri
    | none => []
  let pf := (customProfileUris s.retrievedFrom root).flatMap (fun p =>
    assertedTransformations (resultOf (withoutFragment p)) p profileTransformationIri)
  (same ++ ns ++ pf).eraseDups

section
variable {m : Type → Type} [Monad m]

/-- Retrieve and parse one document, once. -/
def loadDoc (fetch : String → m (Option Representation)) (iri : String) :
    StateT AgentState m Unit := do
  let st ← get
  if st.docs.any (·.iri == iri) then return
  match ← (fetch iri : m _) with
  | none =>
      modify fun st => { st with docs := st.docs ++ [{ iri, src := none }],
                                 unretrieved := st.unretrieved ++ [iri] }
  | some r =>
      match parseXML r.text with
      | .ok d =>
          modify fun st => { st with docs := st.docs ++
            [{ iri, src := some { retrievedFrom := r.retrievedFrom, text := r.text, doc := d } }] }
      | .error _ =>
          modify fun st => { st with docs := st.docs ++ [{ iri, src := none }],
                                     notXml := st.notXml ++ [iri] }

/-- `xsl:import` / `xsl:include` targets, theirs, and so on, `fuel`
    levels deep. Keyed by the href AS WRITTEN, which is what the XSLT
    reader looks up. -/
def loadImports (fetch : String → m (Option Representation)) :
    Nat → String → Node → StateT AgentState m (List (String × Node))
  | 0, _, _ => pure []
  | fuel + 1, styleIri, root => do
      let mut acc : List (String × Node) := []
      for (_, href) in importHrefs root do
        let target := L4Factoidal.Syntax.resolveIri styleIri href
        match ← (fetch target : m _) with
        | none =>
            modify fun st => { st with unretrieved := st.unretrieved ++ [target] }
        | some r =>
            match parseXML r.text with
            | .error _ =>
                modify fun st => { st with notXml := st.notXml ++ [target] }
            | .ok d =>
                let deeper ← loadImports fetch fuel r.retrievedFrom d.root
                acc := acc ++ [(href, d.root)] ++ deeper
      return acc

/-- Retrieve, parse and load the imports of one stylesheet, once. -/
def loadStyle (fetch : String → m (Option Representation)) (iri : String) :
    StateT AgentState m (Option Style) := do
  match (← get).styles.find? (·.1 == iri) with
  | some (_, s) => return s
  | none =>
    let s ← match ← (fetch iri : m _) with
      | none => do
          modify fun st => { st with unretrieved := st.unretrieved ++ [iri] }
          pure none
      | some r =>
          match parseXML r.text with
          | .error _ => do
              modify fun st => { st with notXml := st.notXml ++ [iri] }
              pure none
          | .ok d => do
              let imps ← loadImports fetch 4 r.retrievedFrom d.root
              pure (some (d, imps))
    modify fun st => { st with styles := st.styles ++ [(iri, s)] }
    return s

/-- Apply one transformation to one source, once (§6: run the
    stylesheet, read its output as RDF/XML against the SOURCE's base). -/
def applyOnce (fetch : String → m (Option Representation)) (tx : String)
    (docIri : String) (s : Source) : StateT AgentState m Graph := do
  match (← get).applied.find? (·.1 == (tx, docIri)) with
  | some (_, r) => return r.toOption.getD []
  | none =>
    let r ← match ← loadStyle fetch tx with
      | none => pure (Except.error s!"{tx}: not retrieved")
      | some (style, imps) =>
          pure ((applyTransformation (docBase s.retrievedFrom s.doc.root) style s.doc imps).mapError
            (fun why => s!"{tx} on {docIri}: {why}"))
    modify fun st => { st with applied := st.applied ++ [((tx, docIri), r)] }
    match r with
    | .error why =>
        modify fun st => { st with refusals := st.refusals ++ [why] }
        return []
    | .ok g => return g

/-- One document's RDF/XML reading (§3 base case): the graph its own
    `rdf:RDF` root serialises, against its base. -/
def ownGraph (s : Source) : Graph :=
  if isRdfXmlRoot s.doc.root then
    match L4Factoidal.Syntax.RdfXml.parseRdfXml s.text (some (docBase s.retrievedFrom s.doc.root)) with
    | .ok g    => g
    | .error _ => []
  else []

/-- One round: retrieve every document a known document depends on,
    then recompute every document's transformations from the previous
    round's results, and its result from those. Returns whether any
    document's transformation list changed or a document was added. -/
def round (fetch : String → m (Option Representation)) :
    StateT AgentState m Bool := do
  let before := (← get).docs
  for d in before do
    match d.src with
    | some s => for dep in dependenciesOf s do loadDoc fetch dep
    | none   => pure ()
  let docs := (← get).docs
  let resultOf (iri : String) : Graph :=
    ((docs.find? (·.iri == iri)).map (·.result)).getD []
  let mut next : List DocEntry := []
  let mut changed := docs.length != before.length
  for d in docs do
    match d.src with
    | none => next := next ++ [d]
    | some s =>
        let txs := transformationsOf s resultOf
        let mut outs : List Graph := [ownGraph s]
        for tx in txs do
          outs := outs ++ [← applyOnce fetch tx d.iri s]
        if txs != d.txs then changed := true
        next := next ++ [{ d with txs, result := mergeApart (outs.filter (!·.isEmpty)) }]
  modify fun st => { st with docs := next }
  return changed

/-- Iterate `round` until nothing changes, at most `fuel` times.
    Returns whether the fixpoint was reached. -/
def iterate (fetch : String → m (Option Representation)) :
    Nat → StateT AgentState m Bool
  | 0 => pure false
  | fuel + 1 => do
      if ← round fetch then iterate fetch fuel else pure true

/-- The GRDDL result of the resource `iri`: retrieve it, find its
    transformations by all four rules (the namespace and profile rules
    through the GRDDL results of the second documents), run them, and
    merge. `.error` when the source itself cannot be retrieved or is
    not well-formed XML, with the reason. -/
def glean (fetch : String → m (Option Representation)) (iri : String)
    (fuel : Nat := 24) : m (Except String Gleaned) := do
  let key := withoutFragment iri
  let (converged, st) ← (do loadDoc fetch key; iterate fetch fuel).run {}
  match st.docs.find? (·.iri == key) with
  | none => return .error s!"{key}: not retrieved"
  | some d => match d.src with
    | none =>
        if st.unretrieved.contains key then return .error s!"{key}: not retrieved"
        else return .error s!"{key}: not well-formed XML"
    | some s =>
        return .ok {
          graph := d.result
          transformations := d.txs
          base := docBase s.retrievedFrom s.doc.root
          isRdfXml := isRdfXmlRoot s.doc.root
          unretrieved := st.unretrieved.eraseDups
          notXml := st.notXml.eraseDups
          refusals := st.refusals.eraseDups
          converged }

end

end L4Factoidal.GRDDL
