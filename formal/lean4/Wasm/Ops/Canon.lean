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
import L4Factoidal.Dataflow.Reader
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Canonical
import L4Factoidal.Syntax.NQuadsFast
import Wasm.Ops.FromDataset
import L4Factoidal.RDF.Rdf11Terms

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

/-- The refusal for a dataset with an RDF 1.2 term
(https://github.com/danbri/factoidal/issues/957). RDFC-1.0 (W3C
Recommendation, 21 May 2024) is stated on RDF 1.1 datasets (§1, §4); its
hashing algorithms (§4.6 Hash First Degree Quads, §4.8 Hash N-Degree Quads)
have no rule for a blank node inside a triple term, and the W3C rdf-canon
test suite (`tests/manifest.ttl`, 86 rdfc10 cases) has no case with a triple
term. Design record:
`docs/designissues/2026-10-18-rdf12-terms-canon-and-closures.md`. -/
def canonRdf12Refusal : String :=
  "canonicalizeToNQuads: the input holds an RDF 1.2 triple term or directional "
  ++ "language-tagged string; RDFC-1.0 (W3C Recommendation 2024, sections 4.6 "
  ++ "and 4.8) defines canonical labels for RDF 1.1 datasets only and has no rule "
  ++ "for these terms (https://github.com/danbri/factoidal/issues/957)"

/-- Canonicalise an RDF 1.1 dataset; refuse a dataset with an RDF 1.2 term
with the message that names the missing rule. -/
def canonicalizeChecked (ds : Dataset) : String :=
  if ds.isRdf11 then canonicalizeParsed ds else errJson canonRdf12Refusal

/-- `canonicalizeToNQuads(nquads)`. The text is read in RDF 1.2 mode so that
an RDF 1.2 term gives the refusal above, not a parse error. -/
def canonicalizeToNQuads (nq : String) : String :=
  match L4Factoidal.Dataflow.readNQuadsText .rdf12 nq with
  | .error e => errJson (fmtParseError e)
  | .ok ds => canonicalizeChecked ds

/-- `canonicalizeToNQuads` over a dataset the caller parsed (`FromDataset.lean`,
issue 724): the envelope the text op answers on the dataset's canonical
N-Quads, for every dataset. -/
def canonicalizeOf (ds : Dataset) : String :=
  withOpsDataset .rdf12 ds canonicalizeChecked

theorem canonicalizeOf_eq (ds : Dataset) :
    canonicalizeOf ds = canonicalizeToNQuads (Dataset.toCanonicalNQuads ds) := by
  unfold canonicalizeOf canonicalizeToNQuads
  rw [withOpsDataset_eq]
  rw [L4Factoidal.Dataflow.readNQuadsText_eq]
  cases parseNQuadsFast (Dataset.toCanonicalNQuads ds) .rdf12 <;> rfl

/-! ### RDF 1.2 input (https://github.com/danbri/factoidal/issues/873)

A triple term, with or without a blank node inside it, gives the refusal; an
RDF 1.1 dataset is canonicalised as before. -/

#guard canonicalizeToNQuads "<http://example.com/a> <http://example.com/says> <<( <http://example.com/s> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> )>> .\n<http://example.com/C> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://example.com/D> .\n<http://example.com/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://example.com/C> .\n" == errJson canonRdf12Refusal
#guard canonicalizeToNQuads "<http://example.com/a> <http://example.com/says> <<( _:b1 <http://example.com/p> <http://example.com/o> )>> .\n" == errJson canonRdf12Refusal
#guard (canonicalizeToNQuads "_:x <http://example.com/p> <http://example.com/o> .\n").startsWith
  "{\"ok\":true"

/-! ### The canonical hash (https://github.com/danbri/factoidal/issues/1040)

The SHA-256 of the RDFC-1.0 canonical N-Quads document, as lowercase hex:
`Dataset.canonicalHash` of `RDF/Canonical.lean`, the `canonicalHash` of the
rdf-canonize implementations. The digest is computed in Lean
(`Crypto.hashHex`), never by the host. The same two refusals as
`canonicalizeChecked` apply: the §4.4 excessive-calls abort and an RDF 1.2
term. -/

/-- The `{"ok":true,"hash":…,"algorithm":"sha256"}` envelope over an
ALREADY-PARSED dataset. -/
def canonicalHashParsed (ds : Dataset) : String :=
  let r := L4Factoidal.RDF.Canonical.canonicalize ds
  if r.aborted then
    errJson "datasetCanonicalHash: RDFC-1.0 §4.4 excessive-calls budget exceeded"
  else
    okWith [("hash", .string (L4Factoidal.Crypto.hashHex .sha256 r.nquads)),
            ("algorithm", .string "sha256")]

/-- When the run does not abort, the hash is `Dataset.canonicalHash`. -/
theorem canonicalHashParsed_eq (ds : Dataset)
    (h : (L4Factoidal.RDF.Canonical.canonicalize ds).aborted = false) :
    canonicalHashParsed ds =
      okWith [("hash", .string (ds.canonicalHash .sha256)), ("algorithm", .string "sha256")] := by
  simp [canonicalHashParsed, h, Dataset.canonicalHash, Dataset.canonicalNQuads]

/-- The canonical hash of an RDF 1.1 dataset; the RDF 1.2 refusal otherwise. -/
def canonicalHashChecked (ds : Dataset) : String :=
  if ds.isRdf11 then canonicalHashParsed ds else errJson canonRdf12Refusal

/-- The canonical hash over a dataset the caller holds, read through its
canonical N-Quads as `canonicalizeOf` reads it, so the hash is the SHA-256
of the text `canonicalizeOf` answers. -/
def canonicalHashOf (ds : Dataset) : String :=
  withOpsDataset .rdf12 ds canonicalHashChecked

-- Two blank nodes, one edge. RDFC-1.0 labels the object `_:c14n0`, so the
-- canonical document is
-- `_:c14n1 <http://example.org/vocab#p> _:c14n0 .\n`; the digest is pinned from
-- `printf '_:c14n1 <http://example.org/vocab#p> _:c14n0 .\n' | shasum -a 256`,
-- outside Lean, so this also checks `Crypto.hashHex`.
#guard match L4Factoidal.Dataflow.readNQuadsText .rdf12 "_:b0 <http://example.org/vocab#p> _:b1 .\n" with
  | .ok ds => canonicalHashParsed ds ==
      okWith [("hash", .string "cb9ef7ede80f8b417cbd81fd6e6c63f88db6973087b4f638e69e94d8891b6e25"),
              ("algorithm", .string "sha256")]
  | .error _ => false

end L4Wasm.Ops
