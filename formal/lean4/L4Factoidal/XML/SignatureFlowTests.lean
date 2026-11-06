/- Focused admission and dataflow tests. RSA callbacks below are explicitly
test oracles for control flow, NOT crypto implementations or crypto tests.
Real RSA/HACL and independent JDK fixtures live in tests/hub/xml-signature-*. -/
import L4Factoidal.XML.SignatureFlow

namespace L4Factoidal.XML.SignatureFlow.Tests
open L4Factoidal.Dataflow

private instance {α : Type} [BEq α] : BEq (Except Refusal α) where
  beq a b := match a, b with
    | .ok x, .ok y => x == y
    | .error x, .error y => x == y
    | _, _ => false

private def features : List Feature :=
  [.xml "1.0", .signature .v11, .digest DSig.sha256Alg,
   .signatureAlgorithm DSig.rsaSha256Alg, .canonicalization DSig.excC14nAlg,
   .transform DSig.envelopedAlg]

private def policy : Policy :=
  ⟨features, [], ⟨1, 2, 262144, 262144⟩⟩

private def plan : Plan := ⟨features, [], 1, 2⟩

#guard admit features policy plan == .ok ()
#guard admit [] policy plan == .error (.unsupported (.xml "1.0"))
#guard admit features { policy with permitted := [] } plan == .error (.forbidden (.xml "1.0"))
#guard admit features policy { plan with capabilities := [.documentRead] } ==
  .error (.capabilityDenied .documentRead)
#guard admit features policy { plan with referenceCount := 0 } == .error .referenceLimit
#guard admit features policy { plan with referenceCount := 2 } == .error .referenceLimit
#guard admit features policy { plan with transformCount := 3 } == .error .transformLimit
#guard admit features { policy with limits.maxInputBytes := 0 } plan == .error .invalidLimits
-- Naming a new version does not turn it into an installed implementation.
#guard admit features policy { plan with features := [.signature .v20] } ==
  .error (.unsupported (.signature .v20))
-- Installation alone does not change a restrictive application's permission.
#guard admit (.signature .v20 :: features) policy { plan with features := [.signature .v20] } ==
  .error (.forbidden (.signature .v20))
#guard admit features { policy with capabilities := [.documentRead] }
  { plan with capabilities := [.documentRead] } == .ok ()

private def identityString : Stage Refusal String String := Stage.id
#guard (boundedStage (·.toUTF8.size) 4 identityString).run "abcd" == .ok "abcd"
#guard (boundedStage (·.toUTF8.size) 4 identityString).run "abcde" == .error .outputLimit
#guard (boundedStage (·.toUTF8.size) 4 identityString).run "😀" == .ok "😀"
#guard (boundedStage (·.toUTF8.size) 3 identityString).run "😀" == .error .outputLimit
#guard (inputBoundedStage (·.toUTF8.size) 3 identityString).run "😀" == .error .inputLimit
#guard (boundedFlow (·.toUTF8.size) (·.toUTF8.size) ⟨1, 1, 4, 4⟩ identityString).run "😀" ==
  .ok "😀"

private def reference := "<approval ID=\"a\"><payee>Mina</payee></approval>"
private def signatureXml :=
  "<approval ID=\"a\"><payee>Mina</payee><ds:Signature xmlns:ds=\"" ++ DSig.dsNs ++ "\">" ++
  "<ds:SignedInfo><ds:CanonicalizationMethod Algorithm=\"" ++ DSig.excC14nAlg ++ "\"/>" ++
  "<ds:SignatureMethod Algorithm=\"" ++ DSig.rsaSha256Alg ++ "\"/>" ++
  "<ds:Reference URI=\"#a\"><ds:Transforms><ds:Transform Algorithm=\"" ++ DSig.envelopedAlg ++ "\"/>" ++
  "<ds:Transform Algorithm=\"" ++ DSig.excC14nAlg ++ "\"/></ds:Transforms>" ++
  "<ds:DigestMethod Algorithm=\"" ++ DSig.sha256Alg ++ "\"/>" ++
  "<ds:DigestValue>5iE75vTYVe4qhkBoT4XHQpKPyoDGds0izfax0gPf3Bw=</ds:DigestValue>" ++
  "</ds:Reference></ds:SignedInfo><ds:SignatureValue>AA==</ds:SignatureValue>" ++
  "</ds:Signature></approval>"

private def runFixture (acceptSignature : Bool) (expected : String) (xml := signatureXml) :
    Except Refusal String := do
  let doc ← (parseXML xml).mapError (fun _ => Refusal.signature "XML parse failure")
  let result ← (restrictedStage (fun _ _ _ _ => acceptSignature) ⟨#[]⟩ ⟨#[]⟩ expected).run doc
  pure result.reference

-- Real XML selection, enveloped transform, C14N and SHA-256, synthetic RSA verdict.
#guard runFixture true reference == .ok reference
#guard runFixture false reference == .error (.signature "the signature value does not verify")
#guard runFixture true (reference ++ "changed") == .error .coverageMismatch
#guard runFixture true reference (signatureXml.replace "Mina" "Nina") ==
  .error (.signature "the digest of the signed element does not match")
#guard (runFixture true reference (signatureXml.replace "URI=\"#a\"" "URI=\"https://example.org/\"")) ==
  .error (.signature "the signature does not reference the document element")

end L4Factoidal.XML.SignatureFlow.Tests
