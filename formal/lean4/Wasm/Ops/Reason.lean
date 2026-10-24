/-
Wasm.Ops.Reason — owlClosure / rhoDfClosure / rhoDfFragmentCheck /
rdfsPlusClosure: the RDFS and OWL 2 RL closures. The OWL DL ops
(`owlIsConsistent`, `owlEntails`, the tableau refuter) are in
`Wasm/Ops/ReasonDl.lean`, so the core dispatch (`Wasm/CoreDispatch.lean`)
can serve these four without linking the refuter
(https://github.com/danbri/factoidal/issues/713 stage 4).

Envelopes match `bin/npm-entry/entry_jsoo.ml`:

  owlClosure(nquads, mode)       -> {"ok":true,"nquads":"…"}
      mode "RDFS" | "OWL-RL"; unknown mode is the F* entry's error text.
  rhoDfClosure(nquads)           -> {"ok":true,"ntriples":"…","rounds":N}
  rhoDfFragmentCheck(nquads)     -> {"ok":true,"fragment":true|false}
  rdfsPlusClosure(nquads)        -> {"ok":true,"ntriples":"…","rounds":N}

Only the DEFAULT graph is closed over (the same scope cut as the F*
entry); output is N-Triples lines. `rounds` is telemetry counted by
re-driving the step function with the length test
(`Support.roundsToFixpoint`), mirroring `entry_jsoo.ml:1137`.

The "RDFS" mode runs the same closure the Lean harness's RDFS regime
path runs (`Harness/Run.lean` `closeDataset` → `Regime.rdfs.closure` →
`RDFS.fullClosure` with the minimal datatype map and the graph's own
`rdf:_n` slice).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.RDFS.RDFSPlus
import L4Factoidal.OWL.RLClosure
-- The indexed OWL 2 RL closure (semi-naive rounds since 2026-10-13, issue 756
-- item 2). `OWL.RL.closureFix` is the scanning
-- specification; this module's `@[csimp]` theorem `closureFix_eq_indexed`
-- makes the compiler emit `closureFixIndexed` for every call, but only in a
-- module where it is imported. Until 2026-10-10 this file had it through
-- `OWL.Refute`; when the OWL DL ops moved to `ReasonDl.lean` the import went
-- with them, and `owlClosure` compiled to the scanning closure (the scanning
-- rules of `OWL/RLClosure.lean`, 113 KB more code, were linked in again).
-- Keep the import explicit.
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.Syntax.NQuadsFast
import Wasm.Ops.FromDataset
import L4Factoidal.RDF.GraphOpsSet

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The `rdf:_n` slice of a graph — `rdf:_1` plus those the graph
mentions (the same computation as `Harness/Run.lean`'s `cmpSlice`). -/
private def cmpSlice (g : Graph) : List WfIri :=
  (L4Factoidal.RDFS.containerMembershipIn g).foldl
    (fun acc i => if acc.contains i then acc else acc ++ [i])
    [L4Factoidal.RDFS.rdf1]

/-- N-Triples lines for a default-graph closure result, or the error
envelope when a term cannot be serialised. -/
private def ntriplesEnvelope (key : String) (g : Graph)
    (extra : List (String × Json) := []) : String :=
  match Graph.toNTriples g .rdf12 with
  | .error e  => errJson s!"closure serialisation: {e}"
  | .ok lines => okWith (((key, Json.string lines)) :: extra)

/-- The OWL 2 RL closure of `g` as a set of triples (RDF 1.1 Concepts §3).
`OWL.RL.closureFix` adds a conclusion unless the graph holds a STRUCTURALLY
equal triple (`OWL.RL.addOne`), so when the input holds `"x"@en` and `"x"@EN`
in two triples the closure can hold `<a> <q> "x"@en` and `<a> <q> "x"@EN`, one
RDF triple written two times (measured 2026-10-24 on the `owlClosure` op with
`<a> <p> "x"@en . <a> <q> "x"@EN . <p> rdfs:subPropertyOf <q> .`).
`Graph.toSet` keeps the first of them; on a closure that is already a set it
is the identity (`Graph.toSet_of_keyNodup`).
https://github.com/danbri/factoidal/issues/973 -/
def owlRlClosureSet (g : Graph) : Graph :=
  Graph.toSet (L4Factoidal.OWL.RL.closureFix g)

theorem owlRlClosureSet_keyNodup (g : Graph) : (owlRlClosureSet g).KeyNodup :=
  Graph.toSet_keyNodup _

/-- The set keeps every triple of the closure, by engine membership. -/
theorem owlRlClosureSet_mem (u : Triple) (g : Graph) :
    (owlRlClosureSet g).mem u = true ↔ (L4Factoidal.OWL.RL.closureFix g).mem u = true :=
  Graph.mem_toSet u _

/-- The `owlClosure` envelope over an ALREADY-PARSED dataset. -/
def owlClosureParsed (ds : Dataset) (mode : String) : String :=
    let g := ds.default
    match mode with
    | "RDFS" | "rdfs" =>
        ntriplesEnvelope "nquads"
          (L4Factoidal.RDFS.fullClosure (withMinimalD []) (cmpSlice g) g)
    | "OWL-RL" | "owl-rl" | "owl_rl" =>
        ntriplesEnvelope "nquads" (owlRlClosureSet g)
    | _ =>
        errJson s!"owlClosure: unknown mode '{mode}' (expected 'RDFS' or 'OWL-RL')"

/-- `owlClosure(nquads, mode)`. -/
def owlClosure (nq mode : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => owlClosureParsed ds mode

/-- The round counter of `rhoDfClosure` steps with `RDFS.stepFast`, the
indexed round that `RDFS.stepFast_eq` proves equal to `RDFS.step`, so the
count is the same number. Until 2026-10-12 it stepped with `RDFS.step`,
whose list scans `closure`'s `@[csimp]` twin does not replace: the
counter repeated every round of the closure with scans, and it took
almost all of the op's time: `l4factoidal closure --regime rho-df` on a
160-class `rdfs:subClassOf` chain gave no result in 120 s, every gdb
stack sample was in `roundsToFixpoint` and `Graph.mem`, and `closureFix`
alone takes 1.6 s. With `stepFast` the command takes 1.6 s of CPU time,
and its output is byte-identical on the 11 inputs of
`docs/designissues/2026-10-10-rdfs-seminaive.md` § 5.
Issue https://github.com/danbri/factoidal/issues/756. -/
theorem rhoDfRounds_eq (cap : Nat) (g : Graph) :
    roundsToFixpoint L4Factoidal.RDFS.stepFast cap g
      = roundsToFixpoint L4Factoidal.RDFS.step cap g := by
  rw [show L4Factoidal.RDFS.stepFast = L4Factoidal.RDFS.step from
    funext L4Factoidal.RDFS.stepFast_eq]

/-- The `rhoDfClosure` envelope over an ALREADY-PARSED dataset. -/
def rhoDfClosureParsed (ds : Dataset) : String :=
    let g := ds.default
    let closed := L4Factoidal.RDFS.closureFix g
    let rounds :=
      roundsToFixpoint L4Factoidal.RDFS.stepFast
        (L4Factoidal.RDFS.closureFuelBound g) g
    ntriplesEnvelope "ntriples" closed [("rounds", .number (toString rounds))]

/-- `rhoDfClosure(nquads)`. -/
def rhoDfClosure (nq : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => rhoDfClosureParsed ds

/-- `rhoDfFragmentCheck(nquads)`. -/
def rhoDfFragmentCheck (nq : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds =>
      okWith [("fragment", .bool (L4Factoidal.RDFS.isRhoDfFrag ds.default))]

/-- The `rdfsPlusClosure` envelope over an ALREADY-PARSED dataset. -/
def rdfsPlusClosureParsed (ds : Dataset) : String :=
    let g := ds.default
    let closed := L4Factoidal.RDFS.rdfsPlusClosureFix g
    let rounds :=
      roundsToFixpoint L4Factoidal.RDFS.rdfsPlusStep
        (L4Factoidal.RDFS.closureFuelBound g) g
    ntriplesEnvelope "ntriples" closed [("rounds", .number (toString rounds))]

/-- `rdfsPlusClosure(nquads)`. -/
def rdfsPlusClosure (nq : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => rdfsPlusClosureParsed ds

/-! ### The same ops over datasets the caller parsed (`FromDataset.lean`)

The command line's entries (issue 724). Each answers the envelope the text op
answers on the canonical N-Quads of its datasets, for every dataset. -/

def owlClosureOf (ds : Dataset) (mode : String) : String :=
  withOpsDataset .rdf12 ds (fun d => owlClosureParsed d mode)

theorem owlClosureOf_eq (ds : Dataset) (mode : String) :
    owlClosureOf ds mode = owlClosure (Dataset.toCanonicalNQuads ds) mode := by
  unfold owlClosureOf owlClosure
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

def rhoDfClosureOf (ds : Dataset) : String :=
  withOpsDataset .rdf12 ds rhoDfClosureParsed

theorem rhoDfClosureOf_eq (ds : Dataset) :
    rhoDfClosureOf ds = rhoDfClosure (Dataset.toCanonicalNQuads ds) := by
  unfold rhoDfClosureOf rhoDfClosure
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

def rdfsPlusClosureOf (ds : Dataset) : String :=
  withOpsDataset .rdf12 ds rdfsPlusClosureParsed

theorem rdfsPlusClosureOf_eq (ds : Dataset) :
    rdfsPlusClosureOf ds = rdfsPlusClosure (Dataset.toCanonicalNQuads ds) := by
  unfold rdfsPlusClosureOf rdfsPlusClosure
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

/-! ### The command line's `closure` verb, one line at a time

`l4factoidal closure` printed the `nquads` (or `ntriples`) member of the
envelope above: the closure as one N-Triples string, encoded into a JSON
string, decoded again by the command line and printed. On the QUDT ontology
(638,420 closure triples, 72.7 MB of text) the decode alone raised the
resident set from 690 MB to 1,124 MB; before the JSON repairs of
2026-10-12 the same output needed more than 6 GB
(https://github.com/danbri/factoidal/issues/758). The command line now asks
`closureStreamOf` for the closure GRAPH and writes `Triple.toNTriplesLine` of
each triple. `closureEnvelopeOf_stream` proves that this is the text the
envelope carried: the same error text when there is one, and otherwise the
member is the concatenation of those lines, in the same order. -/

/-- The envelope the command line asked for, by its `--regime` value (any
other value is `rdfs-plus`; the command line refuses other values first). -/
def closureEnvelopeOf (ds : Dataset) (regime : String) : String :=
  match regime with
  | "rdfs" => owlClosureOf ds "RDFS"
  | "owl-rl" => owlClosureOf ds "OWL-RL"
  | "rho-df" => rhoDfClosureOf ds
  | _ => rdfsPlusClosureOf ds

/-- The closure graph each `--regime` value serialises, over the default
graph of `d`: the graph the envelope's `ntriplesEnvelope` call receives. -/
def closureGraphOfRegime (regime : String) (d : Dataset) : Graph :=
  match regime with
  | "rdfs" => L4Factoidal.RDFS.fullClosure (withMinimalD []) (cmpSlice d.default) d.default
  | "owl-rl" => owlRlClosureSet d.default
  | "rho-df" => L4Factoidal.RDFS.closureFix d.default
  | _ => L4Factoidal.RDFS.rdfsPlusClosureFix d.default

/-- The member of the envelope that holds the text, and the members after it. -/
def closureEnvelopeTail (regime : String) (d : Dataset) : String × List (String × Json) :=
  match regime with
  | "rdfs" | "owl-rl" => ("nquads", [])
  | "rho-df" =>
      ("ntriples", [("rounds", .number (toString (roundsToFixpoint L4Factoidal.RDFS.stepFast
        (L4Factoidal.RDFS.closureFuelBound d.default) d.default)))])
  | _ =>
      ("ntriples", [("rounds", .number (toString (roundsToFixpoint L4Factoidal.RDFS.rdfsPlusStep
        (L4Factoidal.RDFS.closureFuelBound d.default) d.default)))])

/-- What `l4factoidal closure --regime REGIME` writes: the closure graph,
each of whose triples has an N-Triples line, or the error text. -/
def closureStreamOf (ds : Dataset) (regime : String) : Except String Graph :=
  match datasetForOps .rdf12 ds with
  | .error e => .error (fmtParseError e)
  | .ok d =>
      let g := closureGraphOfRegime regime d
      match Graph.firstNTriplesError g .rdf12 with
      | some e => .error s!"closure serialisation: {e}"
      | none => .ok g

private theorem ntriplesEnvelope_lines (key : String) (g : Graph) (extra : List (String × Json)) :
    ntriplesEnvelope key g extra =
      match Graph.firstNTriplesError g .rdf12 with
      | some e => errJson s!"closure serialisation: {e}"
      | none => okWith ((key, Json.string (String.join (g.map (Triple.toNTriplesLine .rdf12))))
                  :: extra) := by
  unfold ntriplesEnvelope
  rw [Graph.toNTriples_eq_lines]
  cases Graph.firstNTriplesError g .rdf12 <;> rfl

/-- The envelope is the stream's error, or the stream's lines concatenated in
the member the command line printed. -/
theorem closureEnvelopeOf_stream (ds : Dataset) (regime : String) :
    closureEnvelopeOf ds regime =
      match closureStreamOf ds regime with
      | .error m => errJson m
      | .ok g =>
          okWith (((closureEnvelopeTail regime (match datasetForOps .rdf12 ds with
                      | .ok d => d | .error _ => ds)).1,
                    Json.string (String.join (g.map (Triple.toNTriplesLine .rdf12))))
                  :: (closureEnvelopeTail regime (match datasetForOps .rdf12 ds with
                      | .ok d => d | .error _ => ds)).2) := by
  unfold closureEnvelopeOf closureStreamOf owlClosureOf rhoDfClosureOf rdfsPlusClosureOf
    withOpsDataset
  cases datasetForOps .rdf12 ds with
  | error e => split <;> rfl
  | ok d =>
      simp only
      unfold closureGraphOfRegime closureEnvelopeTail
      split <;>
        simp only [owlClosureParsed, rhoDfClosureParsed, rdfsPlusClosureParsed,
          ntriplesEnvelope_lines] <;>
        cases Graph.firstNTriplesError _ .rdf12 <;> rfl

#print axioms closureEnvelopeOf_stream

/-! ### The closure graphs are sets (https://github.com/danbri/factoidal/issues/973)

RDF 1.1 Concepts §3: the closure an op writes is a graph, so each triple is
written once. The RDFS, ρdf and RDFS-Plus closures of a set are sets
(`RDF/GraphOpsSet.lean`); the OWL 2 RL closure ends with `Graph.toSet`
(`owlRlClosureSet`). The dataset the ops close over is the parse of N-Quads
text (`datasetForOps_eq`), a set by `parseNQuadsFast_isSet`. -/

/-- Each regime's closure of a dataset whose default graph is a set is a set. -/
theorem closureGraphOfRegime_keyNodup (regime : String) {d : Dataset}
    (h : d.default.KeyNodup) : (closureGraphOfRegime regime d).KeyNodup := by
  unfold closureGraphOfRegime
  split
  · exact L4Factoidal.RDFS.fullClosure_keyNodup _ _ h
  · exact owlRlClosureSet_keyNodup _
  · exact L4Factoidal.RDFS.closureFix_keyNodup h
  · exact L4Factoidal.RDFS.rdfsPlusClosureFix_keyNodup h

/-- The dataset the ops close over is a set. -/
theorem datasetForOps_isSet {mode : Mode} {ds d : Dataset}
    (h : datasetForOps mode ds = .ok d) : d.IsSet := by
  rw [datasetForOps_eq] at h
  exact parseNQuadsFast_isSet _ _ _ h

/-- What `l4factoidal closure` writes is a set, for every input dataset and
regime: no hypothesis. -/
theorem closureStreamOf_keyNodup (ds : Dataset) (regime : String) {g : Graph}
    (h : closureStreamOf ds regime = .ok g) : g.KeyNodup := by
  unfold closureStreamOf at h
  split at h
  · cases h
  · next d hd =>
    simp only at h
    split at h
    · cases h
    · cases h
      exact closureGraphOfRegime_keyNodup regime (datasetForOps_isSet hd).default

#print axioms closureGraphOfRegime_keyNodup
#print axioms closureStreamOf_keyNodup

-- Observable cardinality. `"x"@en` and `"x"@EN` are one RDF term (RDF 1.1
-- Concepts §3.3); the OWL 2 RL closure derives `<a> <q> "x"@en` from the
-- `rdfs:subPropertyOf` row while the input holds `<a> <q> "x"@EN`. Before
-- `owlRlClosureSet` the `owlClosure` envelope held both lines (2026-10-24).
private def tagCase973 : String :=
  "<urn:a> <urn:p> \"x\"@en .\n<urn:a> <urn:q> \"x\"@EN .\n" ++
  "<urn:p> <http://www.w3.org/2000/01/rdf-schema#subPropertyOf> <urn:q> .\n"
private def countAQ (r : String) : Nat := (r.splitOn "<urn:a> <urn:q> ").length - 1
#guard countAQ (owlClosure tagCase973 "OWL-RL") == 1
#guard countAQ (owlClosure tagCase973 "RDFS") == 1
#guard countAQ (rhoDfClosure tagCase973) == 1
#guard countAQ (rdfsPlusClosure tagCase973) == 1
-- The reader lower-cases language tags (https://github.com/danbri/factoidal/issues/1001),
-- so the two input lines are one term and the scanning closure holds the triple once.
#guard (L4Factoidal.OWL.RL.closureFix
  ((L4Factoidal.Dataflow.readNQuadsText .rdf12 tagCase973).toOption.map (·.default)
    |>.getD [])).countP (fun t => t.s == .iri ⟨"urn:a", by decide⟩ &&
      t.p.val == "urn:q") == 1
-- Two sub-properties of `urn:q` derive the same triple; the scanning closure and
-- the envelope each hold it once. After issue 1001 no reader input gives the
-- duplicate that the set step removed, so this file has no case where the two differ.
private def twoRoutes973 : String :=
  "<urn:a> <urn:p> \"x\" .\n<urn:a> <urn:r> \"x\" .\n" ++
  "<urn:p> <http://www.w3.org/2000/01/rdf-schema#subPropertyOf> <urn:q> .\n" ++
  "<urn:r> <http://www.w3.org/2000/01/rdf-schema#subPropertyOf> <urn:q> .\n"
#guard countAQ (owlClosure twoRoutes973 "OWL-RL") == 1
#guard (L4Factoidal.OWL.RL.closureFix
  ((L4Factoidal.Dataflow.readNQuadsText .rdf12 twoRoutes973).toOption.map (·.default)
    |>.getD [])).countP (fun t => t.s == .iri ⟨"urn:a", by decide⟩ &&
      t.p.val == "urn:q") == 1

/-! ### RDF 1.2 input (https://github.com/danbri/factoidal/issues/873)

The ops read RDF 1.2 N-Quads and write RDF 1.2 N-Triples. A triple term is a
term in object position; no rule reads the triple inside it
(`L4Factoidal/RDFS/TripleTermClosureTests.lean`). On RDF 1.1 input the
output is the same text as before: the RDF 1.2 reader accepts every RDF 1.1
document with the same dataset, and `Term.toNTriples` writes an RDF 1.1 term
in the same text in both modes. -/

private def tt873 : String := "<http://example.com/a> <http://example.com/says> <<( <http://example.com/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> )>> .\n<http://example.com/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.com/D> .\n<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> .\n"

private def has873 (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def sTypeD : String :=
  "<http://example.com/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/D>"

private def xTypeD : String :=
  "<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/D>"

-- Accepted, the asserted triple with the triple term kept, the asserted
-- derivation made, and nothing derived from inside the triple term.
#guard [owlClosure tt873 "RDFS", owlClosure tt873 "OWL-RL", rhoDfClosure tt873,
        rdfsPlusClosure tt873].all (fun r =>
  r.startsWith "{\"ok\":true" && has873 r "<<( <http://example.com/s>"
    && has873 r xTypeD && !has873 r sTypeD)
#guard (rdfsPlusClosure "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n").startsWith "{\"ok\":true"
#guard has873 (rhoDfClosure "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n") "<<( _:b1"

-- `opaque-iri` (row eq-rep-tt): the OWL 2 RL and RDFS-Plus closures
-- substitute `owl:sameAs` inside a triple term; the RDFS and rho-df closures
-- do not, and the inner triple is not asserted.
private def clark873 : String := "<http://example.com/clark> <http://example.com/reports> <<( <http://example.com/superman> <http://example.com/can> <http://example.com/fly> )>> .\n<http://example.com/clark> <http://www.w3.org/2002/07/owl#sameAs> <http://example.com/superman> .\n"
private def clarkReports : String :=
  "<http://example.com/clark> <http://example.com/reports> <<( <http://example.com/clark> <http://example.com/can> <http://example.com/fly> )>> ."
#guard has873 (owlClosure clark873 "OWL-RL") clarkReports
#guard has873 (rdfsPlusClosure clark873) clarkReports
#guard !has873 (owlClosure clark873 "RDFS") clarkReports
#guard !has873 (rhoDfClosure clark873) clarkReports
#guard [owlClosure clark873 "OWL-RL", rdfsPlusClosure clark873].all (fun r => !has873 r
  "<http://example.com/superman> <http://example.com/can> <http://example.com/fly> .")

end L4Wasm.Ops
