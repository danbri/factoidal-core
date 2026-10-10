/-
Wasm.Ops.Canon — canonicalizeToNQuads.

Envelope matches `bin/npm-entry/entry_jsoo.ml`:

  canonicalizeToNQuads(nquads)
    -> {"ok":true,"nquads":"…"} | {"ok":false,"error":"…"}

RDFC-1.0 canonical labels + code-point sort, via
`L4Factoidal.RDF.Canonical.canonicalize` (SHA-256, the default the
spec's §4.4 note 2 names). A run that hits the §4.4 excessive-calls
abort returns the error envelope — never the un-canonicalised
fallback dressed up as an answer.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Canonical
import L4Factoidal.Syntax.NQuadsFast
import Wasm.Ops.FromDataset

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The `canonicalizeToNQuads` envelope over an ALREADY-PARSED dataset. -/
def canonicalizeParsed (ds : Dataset) : String :=
  let r := L4Factoidal.RDF.Canonical.canonicalize ds
  if r.aborted then
    errJson "canonicalizeToNQuads: RDFC-1.0 §4.4 excessive-calls budget exceeded"
  else
    okWith [("nquads", .string r.nquads)]

/-- `canonicalizeToNQuads(nquads)`. -/
def canonicalizeToNQuads (nq : String) : String :=
  match parseNQuadsFast nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => canonicalizeParsed ds

/-- `canonicalizeToNQuads` over a dataset the caller parsed (`FromDataset.lean`,
issue 724): the envelope the text op answers on the dataset's canonical
N-Quads, for every dataset. -/
def canonicalizeOf (ds : Dataset) : String :=
  withOpsDataset .rdf11 ds canonicalizeParsed

theorem canonicalizeOf_eq (ds : Dataset) :
    canonicalizeOf ds = canonicalizeToNQuads (Dataset.toCanonicalNQuads ds) := by
  unfold canonicalizeOf canonicalizeToNQuads
  rw [withOpsDataset_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf11 <;> rfl

end L4Wasm.Ops
