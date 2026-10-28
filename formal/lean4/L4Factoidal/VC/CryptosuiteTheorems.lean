/-
L4Factoidal.VC.CryptosuiteTheorems — how the cryptosuites of
`VC/Cryptosuite.lean` relate to each other and to RDFC-1.0. Each statement
names the specification versions it is about (VC DI 1.0, VC DI EdDSA 1.0,
VC DI ECDSA 1.0, RDFC-1.0, RFC 8785); a later version is a new theorem.

  1. `vcDiEcdsa10_ecdsaRdfc2019_p256_shares_eddsaRdfc2022`: ecdsa-rdfc-2019
     with a P-256 key and eddsa-rdfc-2022 with an Ed25519 key run the same
     transformation and the same hashing; they differ only in the signature
     primitive. Both are `DataIntegrity.verifyProofValue` at SHA-256
     (`verifyDataset_eddsaRdfc2022`, `verifyDataset_ecdsaRdfc2019_p256`).
  2. `transform_rdfc10_sha256`: the RDFC transform of the table at SHA-256 is
     `DataIntegrity.canonicalizeJsonLd`, the transform of the eddsa-rdfc-2022
     code that existed before the table.
  3. `verifyDataset_canonical_only`: verification reads the document and the
     proof configuration only through their RDFC-1.0 canonical forms.
  4. `vcDi10_rdfc10_isomorphic_verify_alike`: two RDF-isomorphic credentials
     (default graphs) verify alike under every RDFC suite, every key and every
     proof value — PROVIDED `RelabellingInvariance` of RDFC-1.0, which
     `RDF/CanonicalTheorems.lean` states and has not proved (its sub-lemmas
     are proved; its own docstring lists the remaining obligations). This
     theorem reduces the VC property to that one RDFC-1.0 obligation; it does
     not discharge it. The RDFC test suite (86 of 86) is the evidence for
     the obligation today.
  5. `verifyJcs_canonical_only`: for the JCS suites, the same as 3 over
     RFC 8785 canonical text.
-/
import L4Factoidal.VC.Cryptosuite
import L4Factoidal.RDF.CanonicalTheorems

namespace L4Factoidal.VC.Cryptosuite

open L4Factoidal.RDF
open L4Factoidal.Crypto
open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.VC.DataIntegrity

/-- VC DI ECDSA 1.0 and VC DI EdDSA 1.0: ecdsa-rdfc-2019 with P-256 and
eddsa-rdfc-2022 share the transformation (RDFC-1.0) and the hash
(SHA-256, for RDFC-1.0 and for the hash data). -/
theorem vcDiEcdsa10_ecdsaRdfc2019_p256_shares_eddsaRdfc2022 :
    ecdsaRdfc2019.transform = eddsaRdfc2022.transform ∧
    Curve.p256.hashAlg = Curve.ed25519.hashAlg ∧
    (∀ loader j, transform loader ecdsaRdfc2019.transform Curve.p256.hashAlg j =
      transform loader eddsaRdfc2022.transform Curve.ed25519.hashAlg j) :=
  ⟨rfl, rfl, fun _ _ => rfl⟩

/-- VC DI EdDSA 1.0 §3.3: the table at eddsa-rdfc-2022 and an Ed25519 key is
the eddsa-rdfc-2022 verifier of `DataIntegrity`. -/
theorem verifyDataset_eddsaRdfc2022 (prims : Primitives) (pk : ByteArray)
    (document proofConfig : Dataset) (pv : String) :
    verifyDataset prims eddsaRdfc2022 ⟨.ed25519, pk⟩ document proofConfig pv =
      verifyProofValue (prims.verify .ed25519) .sha256 pk document proofConfig pv := by
  simp [verifyDataset, verifyProofValue, transformDataset, Suite.accepts, eddsaRdfc2022,
    Curve.hashAlg]

/-- VC DI ECDSA 1.0: the table at ecdsa-rdfc-2019 and a P-256 key is the same
`DataIntegrity` verifier, with the P-256 primitive. -/
theorem verifyDataset_ecdsaRdfc2019_p256 (prims : Primitives) (pk : ByteArray)
    (document proofConfig : Dataset) (pv : String) :
    verifyDataset prims ecdsaRdfc2019 ⟨.p256, pk⟩ document proofConfig pv =
      verifyProofValue (prims.verify .p256) .sha256 pk document proofConfig pv := by
  simp [verifyDataset, verifyProofValue, transformDataset, Suite.accepts, ecdsaRdfc2019,
    Curve.hashAlg]

/-- The RDFC transform of the table at SHA-256 is the transform of the
eddsa-rdfc-2022 code (`DataIntegrity.canonicalizeJsonLd`). -/
theorem transform_rdfc10_sha256 (loader : Loader) (j : Json) :
    transform loader .rdfc10 .sha256 j = canonicalizeJsonLd loader j := by
  unfold transform canonicalizeJsonLd transformDataset
  cases parseJsonLd loader (toStringCompact j) none none none none <;> rfl

/-- VC DI 1.0 with RDFC-1.0: verification reads the document and the proof
configuration only through their canonical forms. -/
theorem verifyDataset_canonical_only (prims : Primitives) (s : Suite) (pk : PublicKey)
    (d1 d2 c1 c2 : Dataset) (pv : String)
    (hd : d1.canonicalNQuads pk.curve.hashAlg = d2.canonicalNQuads pk.curve.hashAlg)
    (hc : c1.canonicalNQuads pk.curve.hashAlg = c2.canonicalNQuads pk.curve.hashAlg) :
    verifyDataset prims s pk d1 c1 pv = verifyDataset prims s pk d2 c2 pv := by
  simp only [verifyDataset, hd, hc]

/-- VC DI 1.0 and RDFC-1.0: two RDF-isomorphic credentials verify alike, under
every suite, key, proof configuration and proof value, PROVIDED RDFC-1.0's
`RelabellingInvariance` (stated, not yet proved, in `RDF/CanonicalTheorems`). -/
theorem vcDi10_rdfc10_isomorphic_verify_alike (hR : Canonical.RelabellingInvariance)
    (prims : Primitives) (s : Suite) (pk : PublicKey) (g1 g2 : Graph) (cfg : Dataset)
    (pv : String) (hiso : Graph.Isomorphic g1 g2) :
    verifyDataset prims s pk { default := g1, named := [] } cfg pv =
      verifyDataset prims s pk { default := g2, named := [] } cfg pv :=
  verifyDataset_canonical_only prims s pk _ _ cfg cfg pv (hR g1 g2 _ hiso) rfl

/-- VC DI 1.0 with RFC 8785: the JCS transform reads a JSON value only
through its canonical text. -/
theorem verifyJcs_canonical_only (loader : Loader) (alg : HashAlgorithm) (j1 j2 : Json)
    (h : jcsDocument j1 = jcsDocument j2) :
    transform loader .jcs alg j1 = transform loader .jcs alg j2 := by
  simp only [transform, h]

#print axioms vcDiEcdsa10_ecdsaRdfc2019_p256_shares_eddsaRdfc2022
#print axioms verifyDataset_eddsaRdfc2022
#print axioms verifyDataset_ecdsaRdfc2019_p256
#print axioms transform_rdfc10_sha256
#print axioms vcDi10_rdfc10_isomorphic_verify_alike
#print axioms verifyJcs_canonical_only

end L4Factoidal.VC.Cryptosuite
