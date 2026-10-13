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
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.RDFS.RDFSPlus
import L4Factoidal.OWL.RLClosure
-- The indexed OWL 2 RL closure. `OWL.RL.closureFix` is the scanning
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
  match Graph.toNTriples g with
  | .error e  => errJson s!"closure serialisation: {e}"
  | .ok lines => okWith (((key, Json.string lines)) :: extra)

/-- The `owlClosure` envelope over an ALREADY-PARSED dataset. -/
def owlClosureParsed (ds : Dataset) (mode : String) : String :=
    let g := ds.default
    match mode with
    | "RDFS" | "rdfs" =>
        ntriplesEnvelope "nquads"
          (L4Factoidal.RDFS.fullClosure (withMinimalD []) (cmpSlice g) g)
    | "OWL-RL" | "owl-rl" | "owl_rl" =>
        ntriplesEnvelope "nquads" (L4Factoidal.OWL.RL.closureFix g)
    | _ =>
        errJson s!"owlClosure: unknown mode '{mode}' (expected 'RDFS' or 'OWL-RL')"

/-- `owlClosure(nquads, mode)`. -/
def owlClosure (nq mode : String) : String :=
  match parseNQuadsFast nq with
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
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => rhoDfClosureParsed ds

/-- `rhoDfFragmentCheck(nquads)`. -/
def rhoDfFragmentCheck (nq : String) : String :=
  match parseNQuadsFast nq with
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
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => rdfsPlusClosureParsed ds

/-! ### The same ops over datasets the caller parsed (`FromDataset.lean`)

The command line's entries (issue 724). Each answers the envelope the text op
answers on the canonical N-Quads of its datasets, for every dataset. -/

def owlClosureOf (ds : Dataset) (mode : String) : String :=
  withOpsDataset .rdf11 ds (fun d => owlClosureParsed d mode)

theorem owlClosureOf_eq (ds : Dataset) (mode : String) :
    owlClosureOf ds mode = owlClosure (Dataset.toCanonicalNQuads ds) mode := by
  unfold owlClosureOf owlClosure
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf11 <;> rfl

def rhoDfClosureOf (ds : Dataset) : String :=
  withOpsDataset .rdf11 ds rhoDfClosureParsed

theorem rhoDfClosureOf_eq (ds : Dataset) :
    rhoDfClosureOf ds = rhoDfClosure (Dataset.toCanonicalNQuads ds) := by
  unfold rhoDfClosureOf rhoDfClosure
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf11 <;> rfl

def rdfsPlusClosureOf (ds : Dataset) : String :=
  withOpsDataset .rdf11 ds rdfsPlusClosureParsed

theorem rdfsPlusClosureOf_eq (ds : Dataset) :
    rdfsPlusClosureOf ds = rdfsPlusClosure (Dataset.toCanonicalNQuads ds) := by
  unfold rdfsPlusClosureOf rdfsPlusClosure
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf11 <;> rfl

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
  | "owl-rl" => L4Factoidal.OWL.RL.closureFix d.default
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
  match datasetForOps .rdf11 ds with
  | .error e => .error (fmtParseError e)
  | .ok d =>
      let g := closureGraphOfRegime regime d
      match Graph.firstNTriplesError g with
      | some e => .error s!"closure serialisation: {e}"
      | none => .ok g

private theorem ntriplesEnvelope_lines (key : String) (g : Graph) (extra : List (String × Json)) :
    ntriplesEnvelope key g extra =
      match Graph.firstNTriplesError g with
      | some e => errJson s!"closure serialisation: {e}"
      | none => okWith ((key, Json.string (String.join (g.map (Triple.toNTriplesLine .rdf11))))
                  :: extra) := by
  unfold ntriplesEnvelope
  rw [Graph.toNTriples_eq_lines]
  cases Graph.firstNTriplesError g .rdf11 <;> rfl

/-- The envelope is the stream's error, or the stream's lines concatenated in
the member the command line printed. -/
theorem closureEnvelopeOf_stream (ds : Dataset) (regime : String) :
    closureEnvelopeOf ds regime =
      match closureStreamOf ds regime with
      | .error m => errJson m
      | .ok g =>
          okWith (((closureEnvelopeTail regime (match datasetForOps .rdf11 ds with
                      | .ok d => d | .error _ => ds)).1,
                    Json.string (String.join (g.map (Triple.toNTriplesLine .rdf11))))
                  :: (closureEnvelopeTail regime (match datasetForOps .rdf11 ds with
                      | .ok d => d | .error _ => ds)).2) := by
  unfold closureEnvelopeOf closureStreamOf owlClosureOf rhoDfClosureOf rdfsPlusClosureOf
    withOpsDataset
  cases datasetForOps .rdf11 ds with
  | error e => split <;> rfl
  | ok d =>
      simp only
      unfold closureGraphOfRegime closureEnvelopeTail
      split <;>
        simp only [owlClosureParsed, rhoDfClosureParsed, rdfsPlusClosureParsed,
          ntriplesEnvelope_lines] <;>
        cases Graph.firstNTriplesError _ <;> rfl

#print axioms closureEnvelopeOf_stream

end L4Wasm.Ops
