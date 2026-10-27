/-
L4Factoidal.CID.Tests — build-time tests of the CID 1.0 module
(https://github.com/danbri/factoidal/issues/1100, item 10).

There is no W3C test suite for CID 1.0 (the implementation report,
https://w3c.github.io/cid/implementations/1.0/, says "The test suite report
will be linked to from this section"). The tests are:

  * every example of the Recommendation (https://www.w3.org/TR/cid-1.0/,
    15 May 2025): Examples 1–17, 20–22 and 25–35, with the expected result.
    Examples 18 and 19 are JavaScript, tested through `baseEncode` and
    `baseDecode?`; Examples 23 and 24 are the RDF and dateTime notes, not
    documents. The text is copied from the Recommendation. Where an example
    is not JSON as printed, the guard says so, and a second guard runs the
    example with only the defect removed:
      - Examples 12–17 have `//` comments and `...` placeholders;
      - Examples 29 and 35 lack a comma between the two `assertionMethod`
        strings.
  * one negative case per MUST of §2 (one per `DocError` constructor) and
    one per processing error of §3.5.
-/
import L4Factoidal.CID.Retrieve

namespace L4Factoidal.CID.Tests

open L4Factoidal.CID
open L4Factoidal.JSON

/-! ## Helpers -/

def docOk (t : String) : Bool := (parseDocumentText t).toBool

def docErr (t : String) : Option DocError :=
  match parseDocumentText t with
  | .error e => some e
  | .ok _ => none

def methodOk (t : String) : Bool :=
  match parseJson? t with
  | some j => (parseMethod j).toBool
  | none => false

def methodErr (t : String) : Option DocError :=
  match parseJson? t with
  | some j => match parseMethod j with
    | .error e => some e
    | .ok _ => none
  | none => some .notJson

def materialOf (t : String) : Option Material :=
  match parseJson? t with
  | some j => match parseMethod j with
    | .ok m => some m.material
    | .error _ => none
  | none => none

def keyTypeOf (t : String) : Option KeyType :=
  match materialOf t with
  | some (.multikey kt _) => some kt
  | _ => none

def retrieveErr (vm : String) (r : Relationship) (t : String) : Option String :=
  match retrieveFromText vm r t with
  | .error e => some e.name
  | .ok _ => none

def retrieveOk (vm : String) (r : Relationship) (t : String) : Bool :=
  (retrieveFromText vm r t).toBool

def relOf (t : String) (r : Relationship) : List Resolved :=
  match parseDocumentText t with
  | .ok d => relationship d r
  | .error _ => []

def relIds (t : String) (r : Relationship) : List String :=
  (relOf t r).map fun x => match x with
    | .method m => "method " ++ m.id
    | .external u => "external " ++ u

/-! ## Examples of the Recommendation -/

-- Example 1 (and Example 3, the same document): Multikey, embedded.
def ex1 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example",
  "authentication": [{
      "id": "https://controller.example#authn-key-123",
      "type": "Multikey",
      "controller": "https://controller.example",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }]
}"##
#guard docOk ex1
#guard retrieveOk "https://controller.example#authn-key-123" .authentication ex1
#guard retrieveErr "https://controller.example#authn-key-123" .assertionMethod ex1
  == some "INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"
#guard relIds ex1 .authentication == ["method https://controller.example#authn-key-123"]

-- Example 2: JsonWebKey, a relative reference.
def ex2 : String := r##"{
  "id": "https://controller.example/101",
  "verificationMethod": [{
    "id": "https://controller.example/101#key-20240828",
    "type": "JsonWebKey",
    "controller": "https://controller.example/101",
    "publicKeyJwk": {
      "kid": "key-20240828",
      "kty": "EC",
      "crv": "P-256",
      "alg": "ES256",
      "x": "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU",
      "y": "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
    }
  }],
  "authentication": ["#key-20240828"]
}"##
#guard docOk ex2
#guard retrieveOk "https://controller.example/101#key-20240828" .authentication ex2
#guard relIds ex2 .authentication == ["method https://controller.example/101#key-20240828"]
-- §2.2.3 RECOMMENDED: the kid is the fragment.
#guard (match parseDocumentText ex2 with
        | .ok d => d.methods.all kidConsistent
        | .error _ => false)

-- Example 4: a controller property.
def ex4 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controllerA.example",
  "controller": "https://controllerB.example/abc",
  "authentication": [{
      "id": "https://controllerA.example#authn-key-123",
      "type": "Multikey",
      "controller": "https://controllerA.example",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }]
}"##
#guard docOk ex4
#guard (match parseDocumentText ex4 with
        | .ok d => d.controllers == ["https://controllerB.example/abc"]
        | .error _ => false)

-- Example 5: alsoKnownAs.
def ex5 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example",
  "alsoKnownAs": [
    "https://someOtherIdentifier.example/xyz",
    "https://yetAnotherIdentifier.example/987"
  ],
  "authentication": [{
      "id": "https://controller.example#authn-key-123",
      "type": "Multikey",
      "controller": "https://controller.example",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }]
}"##
#guard docOk ex5
#guard (match parseDocumentText ex5 with
        | .ok d => d.alsoKnownAs.length == 2
        | .error _ => false)

-- Example 6: a service with no id.
def ex6 : String := r##"{
  "id": "https://controller.example",
  "authentication": [{
      "id": "https://controller.example#authn-key-123",
      "type": "Multikey",
      "controller": "https://controller.example",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }],
  "service": [{
    "type": "https://social.example/ExampleSocialMediaService",
    "serviceEndpoint": "https://warbler.example/sal674"
  }]
}"##
#guard docOk ex6
#guard (match parseDocumentText ex6 with
        | .ok d => d.services.map (·.types) == [["https://social.example/ExampleSocialMediaService"]]
        | .error _ => false)

-- Examples 7 and 8 (the same document): expires and revoked.
def ex7 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example",
  "verificationMethod": [{
    "id": "https://controller.example#authn-key-123",
    "type": "Multikey",
    "controller": "https://controller.example",
    "expires": "2025-12-01T00:00:00Z",
    "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }, {
    "id": "https://controller.example/101#key-20240828",
    "type": "JsonWebKey",
    "controller": "https://controller.example/101",
    "revoked": "2024-12-10T15:28:32Z",
    "publicKeyJwk": {
      "kid": "key-20240828",
      "kty": "EC",
      "crv": "P-256",
      "alg": "ES256",
      "x": "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU",
      "y": "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
    }
  }]
}"##
#guard docOk ex7
-- 2025-12-01T00:00:00Z is 1764547200; 2024-12-10T15:28:32Z is 1733844512.
#guard (match parseDocumentText ex7 with
        | .ok d => d.methods.map (methodInForce 1764547199) == [true, false]
                && d.methods.map (methodInForce 1764547200) == [false, false]
                && d.methods.map (methodInForce 1733844511) == [true, true]
        | .error _ => false)
-- No relationship names either method.
#guard retrieveErr "https://controller.example#authn-key-123" .authentication ex7
  == some "INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"
-- The second method is in a document whose id is another URL.
#guard retrieveErr "https://controller.example/101#key-20240828" .authentication ex7
  == some "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT_ID"

-- Example 9: an Ed25519 Multikey verification method.
def ex9 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi#keys-1",
  "type": "Multikey",
  "controller": "https://controller.example/123456789abcdefghi",
  "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
}"##
#guard keyTypeOf ex9 == some .ed25519

-- Example 10: a P-384 JsonWebKey.
def ex10 : String := r##"{
  "id": "https://controller.example/123456789abcdefghi#key-1",
  "type": "JsonWebKey",
  "controller": "https://controller.example/123456789abcdefghi",
  "publicKeyJwk": {
      "kid": "key-1",
      "kty": "EC",
      "crv": "P-384",
      "alg": "ES384",
      "x": "1F14JSzKbwxO-Heqew5HzEt-0NZXAjCu8w-RiuV8_9tMiXrSZdjsWqi4y86OFb5d",
      "y": "dnd8yoq-NOJcBuEYgdVVMmSxonXg-DU90d7C4uPWb_Lkd4WIQQEH0DyeC2KUDMIU"
    }
}"##
#guard methodOk ex10

-- Example 11: a P-384 secret key. Refused in a (public) document (§2.2.3).
def ex11 : String := r##"{
  "id": "https://controller.example/123456789abcdefghi#key-1",
  "type": "JsonWebKey",
  "controller": "https://controller.example/123456789abcdefghi",
  "secretKeyJwk": {
      "id": "secret-1",
      "kty": "EC",
      "crv": "P-384",
      "alg": "ES384",
      "d": "fGwges0SX1mj4eZamUCL4qtZijy9uT15fI4gKTuRvre4Kkoju2SHM4rlFOeKVraH",
      "x": "1F14JSzKbwxO-Heqew5HzEt-0NZXAjCu8w-RiuV8_9tMiXrSZdjsWqi4y86OFb5d",
      "y": "dnd8yoq-NOJcBuEYgdVVMmSxonXg-DU90d7C4uPWb_Lkd4WIQQEH0DyeC2KUDMIU"
    }
}"##
#guard methodErr ex11 == some (.secretMaterial "https://controller.example/123456789abcdefghi#key-1" "secretKeyJwk")

-- Example 12: embedding and referencing. As printed it has `//` comments.
def ex12AsPrinted : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example",
  "authentication": [
    // this key is referenced and might be used by
    // more than one verification relationship
    "https://controllerB.example/123456789abcdefghi#keys-1",
    // this key is embedded and may *only* be used for authentication
    {
      "id": "https://controllerA.example/123456789abcdefghi#keys-2",
      "type": "Multikey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
    }
  ]
}"##
#guard docErr ex12AsPrinted == some .notJson
def ex12 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example",
  "authentication": [
    "https://controllerB.example/123456789abcdefghi#keys-1",
    {
      "id": "https://controllerA.example/123456789abcdefghi#keys-2",
      "type": "Multikey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
    }
  ]
}"##
#guard docOk ex12
#guard relIds ex12 .authentication ==
  ["external https://controllerB.example/123456789abcdefghi#keys-1",
   "method https://controllerA.example/123456789abcdefghi#keys-2"]

-- Examples 13–17: one per relationship. `...` and comments removed.
def ex13 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi",
  "authentication": [
    "https://controller.example/123456789abcdefghi#keys-1",
    {
      "id": "https://controller.example/123456789abcdefghi#keys-2",
      "type": "JsonWebKey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyJwk": {
        "crv": "Ed25519",
        "x": "VCpo2LMLhn6iWku8MKvSLg2ZAoC-nlOyPVQaO3FxVeQ",
        "kty": "OKP",
        "kid": "_Qq0UL2Fq651Q0Fjd6TvnYE-faHiOpRlPVQcY_-tA4A"
      }
    },
    {
      "id": "https://controller.example/123456789abcdefghi#keys-3",
      "type": "Multikey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
    }
  ]
}"##
#guard docOk ex13
-- keys-1 is referenced but defined nowhere: dropped (§2.3).
#guard relIds ex13 .authentication ==
  ["method https://controller.example/123456789abcdefghi#keys-2",
   "method https://controller.example/123456789abcdefghi#keys-3"]
#guard retrieveOk "https://controller.example/123456789abcdefghi#keys-2" .authentication ex13
#guard retrieveErr "https://controller.example/123456789abcdefghi#keys-1" .authentication ex13
  == some "INVALID_VERIFICATION_METHOD"
-- The RECOMMENDED kid rule is not met by keys-2 (a thumbprint kid); a lint only.
#guard (match parseDocumentText ex13 with
        | .ok d => (relationship d .authentication).map (fun r => match r with
            | .method m => kidConsistent m
            | .external _ => true) == [false, true]
        | .error _ => false)

def ex13AsPrinted : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi",
  ...
  "authentication": [
    "https://controller.example/123456789abcdefghi#keys-1"
  ]
  ...
}"##
#guard docErr ex13AsPrinted == some .notJson

def ex14 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi",
  "assertionMethod": [
    "https://controller.example/123456789abcdefghi#keys-1",
    {
      "id": "https://controller.example/123456789abcdefghi#keys-2",
      "type": "Multikey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
    }
  ]
}"##
#guard docOk ex14
#guard retrieveOk "https://controller.example/123456789abcdefghi#keys-2" .assertionMethod ex14
#guard retrieveErr "https://controller.example/123456789abcdefghi#keys-2" .authentication ex14
  == some "INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"

def ex15 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi",
  "keyAgreement": [
    "https://controller.example/123456789abcdefghi#keys-1",
    {
      "id": "https://controller.example/123#keys-2",
      "type": "Multikey",
      "controller": "https://controller.example/123",
      "publicKeyMultibase": "zDnaerx9CtbPJ1q36T5Ln5wYt3MQYeGRG5ehnPAmxcf5mDZpv"
    },
    {
      "id": "https://controller.example/123#keys-3",
      "type": "JsonWebKey",
      "controller": "https://controller.example/123",
      "publicKeyJwk": {
        "kty": "OKP",
        "crv": "X25519",
        "x": "W_Vcc7guviK-gPNDBmevVw-uJVamQV5rMNQGUwCqlH0"
      }
    }
  ]
}"##
#guard docOk ex15
-- The embedded methods have ids in another document: §3.3 does not
-- retrieve them from this one.
#guard retrieveErr "https://controller.example/123#keys-2" .keyAgreement ex15
  == some "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT_ID"

def ex16 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi",
  "capabilityInvocation": [
    "https://controller.example/123456789abcdefghi#keys-1",
    {
    "id": "https://controller.example/123456789abcdefghi#keys-2",
    "type": "Multikey",
    "controller": "https://controller.example/123456789abcdefghi",
    "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
    }
  ]
}"##
#guard docOk ex16
#guard retrieveOk "https://controller.example/123456789abcdefghi#keys-2" .capabilityInvocation ex16
#guard retrieveErr "https://controller.example/123456789abcdefghi#keys-2" .capabilityDelegation ex16
  == some "INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"

def ex17 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123456789abcdefghi",
  "capabilityDelegation": [
    "https://controller.example/123456789abcdefghi#keys-1",
    {
      "id": "https://controller.example/123456789abcdefghi#keys-2",
      "type": "JsonWebKey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyJwk": {
        "kty": "OKP",
        "crv": "Ed25519",
        "x": "O2onvM62pC1io6jQKm8Nc2UyFXcd4kOmOsBIoYtZ2ik"
      }
    },
    {
      "id": "https://controller.example/123456789abcdefghi#keys-3",
      "type": "Multikey",
      "controller": "https://controller.example/123456789abcdefghi",
      "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
    }
  ]
}"##
#guard docOk ex17
#guard retrieveOk "https://controller.example/123456789abcdefghi#keys-3" .capabilityDelegation ex17

-- Examples 18 and 19 (§3.1, §3.2 in JavaScript): base 58 through the
-- generic algorithm is the existing base-58-btc codec.
def sampleBytes : List (List UInt8) :=
  [[], [0], [0, 0], [0, 0, 1], [1], [255], [0, 255, 1, 2, 3], [0xed, 0x01, 0x8c, 0x9a, 0x11],
   (List.range 34).map (fun i => (i * 37 + 11).toUInt8)]
#guard sampleBytes.all fun bs =>
  baseEncode bs 58 VC.Multibase.base58Alphabet == VC.Multibase.base58Encode bs
#guard sampleBytes.all fun bs =>
  baseDecode? (baseEncode bs 58 VC.Multibase.base58Alphabet) 58 VC.Multibase.base58Alphabet == some bs
#guard sampleBytes.all fun bs =>
  baseDecode? (baseEncode bs 64 base64UrlAlphabet) 64 base64UrlAlphabet == some bs
-- The literal §3.1 reading of base 64 is not RFC 4648 (module header).
#guard baseEncode [0xff] 64 base64UrlAlphabet == "D_"
#guard multibaseEncode .base64url [0xff] == "u_w"
#guard baseDecode? "1x0" 58 VC.Multibase.base58Alphabet == none

-- Example 20: the minimum conformant document.
def ex20 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123",
  "verificationMethod": [{
    "id": "https://controller.example/123#key-456",
    "type": "Multikey",
    "controller": "https://controller.example/123",
    "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }],
  "authentication": ["https://controller.example/123#key-456"]
}"##
#guard docOk ex20
#guard retrieveOk "https://controller.example/123#key-456" .authentication ex20
#guard (match retrieveFromText "https://controller.example/123#key-456" .authentication ex20 with
        | .ok m => m.material == .multikey .ed25519
            ((VC.Multibase.multibaseDecode? "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu").getD []).tail.tail
        | .error _ => false)
#guard retrieveWith [] "https://controller.example/123#key-456" .authentication
  == .need "https://controller.example/123"
#guard (retrieveWith [("https://controller.example/123", ex20)]
          "https://controller.example/123#key-456" .authentication) matches .ok _

-- Example 21: an external method for capabilityInvocation.
def ex21 : String := r##"{
  "id": "https://controller.example/123",
  "capabilityInvocation": ["https://external.example/xyz#key-789"]
}"##
#guard docOk ex21
#guard relIds ex21 .capabilityInvocation == ["external https://external.example/xyz#key-789"]
-- §3.3 retrieves it from the external document, never from this one.
#guard retrieveWith [("https://controller.example/123", ex21)]
         "https://external.example/xyz#key-789" .capabilityInvocation
  == .need "https://external.example/xyz"
def external789 : String := r##"{
  "id": "https://external.example/xyz",
  "capabilityInvocation": [{
    "id": "https://external.example/xyz#key-789",
    "type": "Multikey",
    "controller": "https://external.example/xyz",
    "publicKeyMultibase": "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu"
  }]
}"##
#guard (retrieveWith [("https://external.example/xyz", external789)]
          "https://external.example/xyz#key-789" .capabilityInvocation) matches .ok _

-- Example 22: no @context; context injection (§4.2.1).
def ex22 : String := r##"{
  "id": "https://controller.example/101",
  "verificationMethod": [{
    "id": "https://controller.example/101#key-203947",
    "type": "JsonWebKey",
    "controller": "https://controller.example/101",
    "publicKeyJwk": {
      "kid": "key-203947",
      "kty": "EC",
      "crv": "P-256",
      "alg": "ES256",
      "x": "f83OJ3D2xF1Bg8vub9tLe1gHMzV76e8Tus9uPHvRVEU",
      "y": "x_FEzRu9m36HLN_tue659LNpXW6pCyStikYjKIWI5a0"
    }
  }],
  "authentication": ["#key-203947"]
}"##
#guard docOk ex22
#guard retrieveOk "https://controller.example/101#key-203947" .authentication ex22
#guard (match parseJson? ex22 with
        | some j => (injectContext j).getString? "@context" == some contextV1
        | none => false)
#guard (match parseJson? ex1 with
        | some j => injectContext j == j
        | none => false)

-- Examples 25–28 and 30: Multikey public keys of each type.
def mkVm (mb : String) : String :=
  "{\"id\": \"https://multikey.example/issuer/123#key-0\", \"type\": \"Multikey\", " ++
  "\"controller\": \"https://multikey.example/issuer/123\", \"publicKeyMultibase\": \"" ++ mb ++ "\"}"
#guard keyTypeOf (mkVm "zDnaerx9CtbPJ1q36T5Ln5wYt3MQYeGRG5ehnPAmxcf5mDZpv") == some .p256
#guard keyTypeOf (mkVm "z82LkvCwHNreneWpsgPEbV3gu1C6NFJEBg4srfJ5gdxEsMGRJUz2sG9FE42shbn2xkZJh54") == some .p384
#guard keyTypeOf (mkVm "z6Mkf5rGMoatrSj1f4CyvuHBeXJELe9RPdzo2PKGNCKVtZxP") == some .ed25519
#guard keyTypeOf (mkVm "zUC7EK3ZakmukHhuncwkbySmomv3FmrkmS36E4Ks5rsb6VQSRpoCrx6Hb8e2Nk6UvJFSdyw9NK1scFXJp21gNNYFjVWNgaqyGnkyhtagagCpQb5B7tagJu3HDbjQ8h5ypoHjwBb") == some .bls12381g2
#guard keyTypeOf (mkVm "zEPJc1vCfbG2aoZn8f3U8ggYRL4ZFfF63ZA3qFSk81WJxnCQr") == some .sm2
-- Example 25 as printed (with its @context).
def ex25 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://multikey.example/issuer/123#key-0",
  "type": "Multikey",
  "controller": "https://multikey.example/issuer/123",
  "publicKeyMultibase": "zDnaerx9CtbPJ1q36T5Ln5wYt3MQYeGRG5ehnPAmxcf5mDZpv"
}"##
#guard keyTypeOf ex25 == some .p256
-- Encoding the decoded key gives the value back.
#guard (match materialOf ex25 with
        | some (.multikey kt key) => encodePublicMultikey kt key == "zDnaerx9CtbPJ1q36T5Ln5wYt3MQYeGRG5ehnPAmxcf5mDZpv"
        | _ => false)

-- Example 29: several Multikeys. As printed, a comma is missing.
def ex29AsPrinted : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123",
  "verificationMethod": [{
    "id": "https://multikey.example/issuer/123#key-1",
    "type": "Multikey",
    "controller": "https://multikey.example/issuer/123",
    "publicKeyMultibase": "zDnaerx9CtbPJ1q36T5Ln5wYt3MQYeGRG5ehnPAmxcf5mDZpv"
  }, {
    "id": "https://multikey.example/issuer/123#key-2",
    "type": "Multikey",
    "controller": "https://multikey.example/issuer/123",
    "publicKeyMultibase": "z6Mkf5rGMoatrSj1f4CyvuHBeXJELe9RPdzo2PKGNCKVtZxP"
  }, {
    "id": "https://multikey.example/issuer/123#key-3",
    "type": "Multikey",
    "controller": "https://multikey.example/issuer/123",
    "publicKeyMultibase": "zUC7EK3ZakmukHhuncwkbySmomv3FmrkmS36E4Ks5rsb6VQSRpoCrx6Hb8e2Nk6UvJFSdyw9NK1scFXJp21gNNYFjVWNgaqyGnkyhtagagCpQb5B7tagJu3HDbjQ8h5ypoHjwBb"
  }],
  "authentication": [
    "https://controller.example/123#key-1"
  ],
  "assertionMethod": [
    "https://controller.example/123#key-2"
    "https://controller.example/123#key-3"
  ],
  "capabilityDelegation": [
    "https://controller.example/123#key-2"
  ],
  "capabilityInvocation": [
    "https://controller.example/123#key-2"
  ]
}"##
#guard docErr ex29AsPrinted == some .notJson
def ex29 : String := r##"{
  "@context": "https://www.w3.org/ns/cid/v1",
  "id": "https://controller.example/123",
  "verificationMethod": [{
    "id": "https://multikey.example/issuer/123#key-1",
    "type": "Multikey",
    "controller": "https://multikey.example/issuer/123",
    "publicKeyMultibase": "zDnaerx9CtbPJ1q36T5Ln5wYt3MQYeGRG5ehnPAmxcf5mDZpv"
  }, {
    "id": "https://multikey.example/issuer/123#key-2",
    "type": "Multikey",
    "controller": "https://multikey.example/issuer/123",
    "publicKeyMultibase": "z6Mkf5rGMoatrSj1f4CyvuHBeXJELe9RPdzo2PKGNCKVtZxP"
  }, {
    "id": "https://multikey.example/issuer/123#key-3",
    "type": "Multikey",
    "controller": "https://multikey.example/issuer/123",
    "publicKeyMultibase": "zUC7EK3ZakmukHhuncwkbySmomv3FmrkmS36E4Ks5rsb6VQSRpoCrx6Hb8e2Nk6UvJFSdyw9NK1scFXJp21gNNYFjVWNgaqyGnkyhtagagCpQb5B7tagJu3HDbjQ8h5ypoHjwBb"
  }],
  "authentication": [
    "https://controller.example/123#key-1"
  ],
  "assertionMethod": [
    "https://controller.example/123#key-2",
    "https://controller.example/123#key-3"
  ],
  "capabilityDelegation": [
    "https://controller.example/123#key-2"
  ],
  "capabilityInvocation": [
    "https://controller.example/123#key-2"
  ]
}"##
#guard docOk ex29
-- The relationships name controller.example/123#key-N, but the methods
-- have ids under multikey.example: no method is found (§3.3 step 8), and
-- relationship() drops the references (§2.3).
#guard retrieveErr "https://controller.example/123#key-1" .authentication ex29
  == some "INVALID_VERIFICATION_METHOD"
#guard relIds ex29 .assertionMethod == []

-- Examples 31–34: JsonWebKey public keys.
def jwkVm (jwk : String) : String :=
  "{\"id\": \"https://jsonwebkey.example/issuer/123#key-0\", \"type\": \"JsonWebKey\", " ++
  "\"controller\": \"https://jsonwebkey.example/issuer/123\", \"publicKeyJwk\": " ++ jwk ++ "}"
#guard methodOk (jwkVm r##"{"kty": "EC", "crv": "P-256", "x": "Ums5WVgwRkRTVVFnU3k5c2xvZllMbEcwM3NPRW91ZzN", "y": "nDQW6XZ7b_u2Sy9slofYLlG03sOEoug3I0aAPQ0exs4"}"##)
#guard methodOk (jwkVm r##"{"kty": "EC", "crv": "P-384", "x": "VUZKSlUwMGdpSXplekRwODhzX2N4U1BYdHVYWUZsaXVDR25kZ1U0UXA4bDkxeHpE", "y": "jq4QoAHKiIzezDp88s_cxSPXtuXYFliuCGndgU4Qp8l91xzD1spCmFIzQgVjqvcP"}"##)
#guard methodOk (jwkVm r##"{"kty": "OKP", "crv": "Ed25519", "x": "VCpo2LMLhn6iWku8MKvSLg2ZAoC-nlOyPVQaO3FxVeQ"}"##)
#guard methodOk (jwkVm r##"{"kty": "EC", "crv": "BLS12381G2", "x": "Ajs8lstTgoTgXMF6QXdyh3m8k2ixxURGYLMaYylVK_x0F8HhE8zk0YWiGV3CHwpQEa2sH4PBZLaYCn8se-1clmCORDsKxbbw3Js_Alu4OmkV9gmbJsy1YF2rt7Vxzs6S", "y": "BVkkrVEib-P_FMPHNtqxJymP3pV-H8fCdvPkoWInpFfM9tViyqD8JAmwDf64zU2hBV_vvCQ632ScAooEExXuz1IeQH9D2o-uY_dAjZ37YHuRMEyzh8Tq-90JHQvicOqx"}"##)

-- Example 35: several JsonWebKeys. As printed, the same missing comma.
def ex35 (sep : String) : String :=
  "{\"@context\": \"https://www.w3.org/ns/cid/v1\", \"id\": \"https://controller.example/123\", " ++
  "\"verificationMethod\": [" ++
  "{\"id\": \"https://jsonwebkey.example/issuer/123#key-1\", \"type\": \"JsonWebKey\", \"controller\": \"https://jsonwebkey.example/issuer/123\", " ++
  "\"publicKeyJwk\": {\"kty\": \"EC\", \"crv\": \"P-256\", \"x\": \"fyNYMN0976ci7xqiSdag3buk-ZCwgXU4kz9XNkBlNUI\", \"y\": \"hW2ojTNfH7Jbi8--CJUo3OCbH3y5n91g-IMA9MLMbTU\"}}, " ++
  "{\"id\": \"https://jsonwebkey.example/issuer/123#key-2\", \"type\": \"JsonWebKey\", \"controller\": \"https://jsonwebkey.example/issuer/123\", " ++
  "\"publicKeyJwk\": {\"kty\": \"EC\", \"crv\": \"P-521\", \"x\": \"ASUHPMyichQ0QbHZ9ofNx_l4y7luncn5feKLo3OpJ2nSbZoC7mffolj5uy7s6KSKXFmnNWxGJ42IOrjZ47qqwqyS\", \"y\": \"AW9ziIC4ZQQVSNmLlp59yYKrjRY0_VqO-GOIYQ9tYpPraBKUloEId6cI_vynCzlZWZtWpgOM3HPhYEgawQ703RjC\"}}, " ++
  "{\"id\": \"https://jsonwebkey.example/issuer/123#key-3\", \"type\": \"JsonWebKey\", \"controller\": \"https://jsonwebkey.example/issuer/123\", " ++
  "\"publicKeyJwk\": {\"kty\": \"OKP\", \"crv\": \"Ed25519\", \"x\": \"_eT7oDCtAC98L31MMx9J0T-w7HR-zuvsY08f9MvKne8\"}}], " ++
  "\"authentication\": [\"https://controller.example/123#key-1\"], " ++
  "\"assertionMethod\": [\"https://controller.example/123#key-2\"" ++ sep ++ " \"https://controller.example/123#key-3\"], " ++
  "\"capabilityDelegation\": [\"https://controller.example/123#key-2\"], " ++
  "\"capabilityInvocation\": [\"https://controller.example/123#key-2\"]}"
#guard docErr (ex35 "") == some .notJson
#guard docOk (ex35 ",")
#guard retrieveErr "https://controller.example/123#key-2" .assertionMethod (ex35 ",")
  == some "INVALID_VERIFICATION_METHOD"

/-! ## One negative case per MUST of §2 -/

def withVm (vm : String) : String :=
  "{\"id\": \"https://controller.example\", \"verificationMethod\": [" ++ vm ++ "]}"
def goodVm (extra : String := "") : String :=
  "{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\", \"controller\": \"https://controller.example\"" ++
  extra ++ ", \"publicKeyMultibase\": \"z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu\"}"
#guard docOk (withVm (goodVm))

#guard docErr "[1]" == some .notMap
#guard docErr "{\"verificationMethod\": []}" == some .idMissing
#guard docErr "{\"id\": 3}" == some .idNotUrl
#guard docErr "{\"id\": \"not a url\"}" == some .idNotUrl
#guard docErr "{\"id\": \"#relative\"}" == some .idNotUrl
#guard docErr "{\"id\": \"https://c.example\", \"controller\": 7}" == some .controllerInvalid
#guard docErr "{\"id\": \"https://c.example\", \"controller\": [\"https://a.example\", 7]}" == some .controllerInvalid
#guard docOk "{\"id\": \"https://c.example\", \"controller\": [\"https://a.example\", \"https://b.example\"]}"
#guard docErr "{\"id\": \"https://c.example\", \"alsoKnownAs\": \"https://a.example\"}" == some .alsoKnownAsInvalid
#guard docErr "{\"id\": \"https://c.example\", \"alsoKnownAs\": [\"no scheme\"]}" == some .alsoKnownAsInvalid
#guard docErr "{\"id\": \"https://c.example\", \"service\": {}}" == some .serviceNotSet
#guard docErr "{\"id\": \"https://c.example\", \"service\": [\"x\"]}" == some .serviceNotMap
#guard docErr "{\"id\": \"https://c.example\", \"service\": [{\"id\": \"a b\", \"type\": \"T\", \"serviceEndpoint\": \"https://e.example\"}]}"
  == some .serviceIdInvalid
#guard docErr "{\"id\": \"https://c.example\", \"service\": [{\"id\": \"#s\", \"type\": \"T\", \"serviceEndpoint\": \"https://e.example\"}, {\"id\": \"https://c.example#s\", \"type\": \"T\", \"serviceEndpoint\": \"https://e.example\"}]}"
  == some (.serviceIdDuplicate "https://c.example#s")
#guard docErr "{\"id\": \"https://c.example\", \"service\": [{\"serviceEndpoint\": \"https://e.example\"}]}"
  == some .serviceTypeInvalid
#guard docErr "{\"id\": \"https://c.example\", \"service\": [{\"type\": \"T\"}]}" == some .serviceEndpointInvalid
#guard docErr "{\"id\": \"https://c.example\", \"service\": [{\"type\": \"T\", \"serviceEndpoint\": []}]}"
  == some .serviceEndpointInvalid
#guard docOk "{\"id\": \"https://c.example\", \"service\": [{\"type\": [\"T\", \"U\"], \"serviceEndpoint\": [\"https://e.example\", {\"uri\": \"x\"}]}]}"
#guard docErr "{\"id\": \"https://c.example\", \"verificationMethod\": {}}" == some .verificationMethodNotSet
#guard docErr (withVm "\"https://controller.example#k\"") == some .methodNotMap
#guard docErr (withVm "{\"type\": \"Multikey\", \"controller\": \"https://controller.example\"}") == some .methodIdInvalid
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"controller\": \"https://controller.example\"}")
  == some (.methodTypeInvalid "https://controller.example#k")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\"}")
  == some (.methodControllerInvalid "https://controller.example#k")
#guard docErr (withVm (goodVm ", \"expires\": \"2025-12-01T00:00:00\""))
  == some (.methodExpiresInvalid "https://controller.example#k")
#guard docErr (withVm (goodVm ", \"revoked\": \"yesterday\""))
  == some (.methodRevokedInvalid "https://controller.example#k")
#guard docErr (withVm (goodVm ", \"publicKeyJwk\": {\"kty\": \"OKP\", \"crv\": \"Ed25519\", \"x\": \"VCpo2LMLhn6iWku8MKvSLg2ZAoC-nlOyPVQaO3FxVeQ\"}"))
  == some (.methodMultipleMaterial "https://controller.example#k")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\", \"controller\": \"https://controller.example\", \"publicKeyJwk\": {\"kty\": \"OKP\"}}")
  == some (.methodMaterialMismatch "https://controller.example#k" "Multikey" "publicKeyJwk")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"JsonWebKey\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \"z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu\"}")
  == some (.methodMaterialMismatch "https://controller.example#k" "JsonWebKey" "publicKeyMultibase")
-- A Multikey: not base-58-btc, a secret-key header, an unknown header, a wrong length.
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \"u7QE\"}")
  == some (.multikeyInvalid "https://controller.example#k" .notBase58btc)
#guard docErr (withVm ("{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \""
    ++ multibaseEncode .base58btc ([0x80, 0x26] ++ List.replicate 32 7) ++ "\"}"))
  == some (.multikeyInvalid "https://controller.example#k" .secretKeyHeader)
#guard docErr (withVm ("{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \""
    ++ multibaseEncode .base58btc ([0xe7, 0x01] ++ List.replicate 33 7) ++ "\"}"))
  == some (.multikeyInvalid "https://controller.example#k" .unknownHeader)
#guard docErr (withVm ("{\"id\": \"https://controller.example#k\", \"type\": \"Multikey\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \""
    ++ multibaseEncode .base58btc ([0xed, 0x01] ++ List.replicate 31 7) ++ "\"}"))
  == some (.multikeyInvalid "https://controller.example#k" (.wrongLength .ed25519 31))
-- publicKeyMultibase of another method type must still be Multibase.
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"Ed25519VerificationKey2020\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \"x123\"}")
  == some (.multibaseInvalid "https://controller.example#k")
#guard docOk (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"Ed25519VerificationKey2020\", \"controller\": \"https://controller.example\", \"publicKeyMultibase\": \"z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu\"}")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"JsonWebKey\", \"controller\": \"https://controller.example\", \"publicKeyJwk\": {\"crv\": \"Ed25519\"}}")
  == some (.jwkInvalid "https://controller.example#k")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"JsonWebKey\", \"controller\": \"https://controller.example\", \"publicKeyJwk\": \"k\"}")
  == some (.jwkInvalid "https://controller.example#k")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"JsonWebKey\", \"controller\": \"https://controller.example\", \"publicKeyJwk\": {\"kty\": \"OKP\", \"crv\": \"Ed25519\", \"x\": \"VCpo2LMLhn6iWku8MKvSLg2ZAoC-nlOyPVQaO3FxVeQ\", \"d\": \"secret\"}}")
  == some (.jwkPrivateMember "https://controller.example#k" "d")
#guard docErr (withVm "{\"id\": \"https://controller.example#k\", \"type\": \"JsonWebKey\", \"controller\": \"https://controller.example\", \"publicKeyJwk\": {\"kty\": \"oct\", \"k\": \"c2VjcmV0\"}}")
  == some (.jwkPrivateMember "https://controller.example#k" "k")
#guard docErr (withVm (goodVm ", \"secretKeyMultibase\": \"z3u2en7t5LR2WtQH5PfsqMDPFSLwhwPvAcp8f5ZH4ZDxM9nT\""))
  == some (.secretMaterial "https://controller.example#k" "secretKeyMultibase")
#guard docErr "{\"id\": \"https://c.example\", \"authentication\": \"https://c.example#k\"}"
  == some (.relationshipNotSet .authentication)
#guard docErr "{\"id\": \"https://c.example\", \"keyAgreement\": []}" == some (.relationshipEmpty .keyAgreement)
#guard docErr "{\"id\": \"https://c.example\", \"capabilityDelegation\": [3]}"
  == some (.relationshipEntryInvalid .capabilityDelegation)
#guard docErr "{\"id\": \"https://c.example\", \"assertionMethod\": [\"not a url\"]}"
  == some (.relationshipEntryInvalid .assertionMethod)
-- An embedded method is checked like any other.
#guard docErr "{\"id\": \"https://c.example\", \"capabilityInvocation\": [{\"id\": \"https://c.example#k\", \"type\": \"Multikey\", \"controller\": \"https://c.example\", \"secretKeyJwk\": {}}]}"
  == some (.secretMaterial "https://c.example#k" "secretKeyJwk")
#guard docErr "not json" == some .notJson

/-! ## One case per processing error of §3.5 -/

#guard retrieveErr "key-456" .authentication ex20 == some "INVALID_VERIFICATION_METHOD_URL"
#guard retrieveErr "https://controller.example/123#a#b" .authentication ex20 == some "INVALID_VERIFICATION_METHOD_URL"
#guard retrieveErr "https://controller.example/123#key-456" .authentication "{\"id\": 1}"
  == some "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT"
#guard retrieveErr "https://controller.example/123#key-456" .authentication "{"
  == some "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT"
#guard retrieveErr "https://controller.example/999#key-456" .authentication ex20
  == some "INVALID_CONTROLLED_IDENTIFIER_DOCUMENT_ID"
-- No fragment, an unknown fragment, a map that is not a method.
#guard retrieveErr "https://controller.example/123" .authentication ex20 == some "INVALID_VERIFICATION_METHOD"
#guard retrieveErr "https://controller.example/123#key-999" .authentication ex20 == some "INVALID_VERIFICATION_METHOD"
def svcDoc : String :=
  "{\"id\": \"https://c.example\", \"service\": [{\"id\": \"#s\", \"type\": \"T\", \"serviceEndpoint\": \"https://e.example\"}], \"authentication\": [\"#s\"]}"
#guard docOk svcDoc
#guard (match retrieveFromText "https://c.example#s" .authentication svcDoc with
        | .error (.invalidVerificationMethod (.notConforming _)) => true
        | _ => false)
-- The method's controller is another document (§3.3 step 10).
def foreignCtl : String :=
  "{\"id\": \"https://c.example\", \"authentication\": [{\"id\": \"#k\", \"type\": \"Multikey\", \"controller\": \"https://evil.example\", \"publicKeyMultibase\": \"z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu\"}]}"
#guard (match retrieveFromText "https://c.example#k" .authentication foreignCtl with
        | .error (.invalidVerificationMethod (.controllerMismatch u)) => u == "https://evil.example"
        | _ => false)
-- A relative id and controller resolve against the document id.
def relDoc : String :=
  "{\"id\": \"https://c.example/p/\", \"authentication\": [{\"id\": \"#k\", \"type\": \"Multikey\", \"controller\": \"./\", \"publicKeyMultibase\": \"z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu\"}]}"
#guard retrieveOk "https://c.example/p/#k" .authentication relDoc
#guard retrieveErr "https://controller.example/123#key-456" .keyAgreement ex20
  == some "INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"

-- §3.5 problem details.
#guard (ProcessingError.invalidRelationshipForVerificationMethod .assertionMethod).typeUrl
  == "https://w3id.org/security#INVALID_RELATIONSHIP_FOR_VERIFICATION_METHOD"
#guard (match (ProcessingError.invalidVerificationMethodUrl "x").problem.getString? "type" with
        | some t => t == "https://w3id.org/security#INVALID_VERIFICATION_METHOD_URL"
        | none => false)

/-! ## §3.4 Fragment Resolution -/

#guard (match parseJson? ex13 with
        | some j => (resolveFragment j "#keys-3").bind (·.getString? "type") == some "Multikey"
        | none => false)
#guard (match parseJson? ex2 with
        | some j => (resolveFragment j "#key-20240828").bind (·.getString? "type") == some "JsonWebKey"
        | none => false)
#guard (match parseJson? ex2 with
        | some j => resolveFragment j "#nope" == none
        | none => false)
-- A relative id matches too (§3.4 "or fragmentIdentifier").
#guard (match parseJson? svcDoc with
        | some j => (resolveFragment j "#s").bind (·.getString? "type") == some "T"
        | none => false)

/-! ## §2.4 Multibase, §2.5 Multihash, media types -/

#guard ((multibaseDecode? "z6MkmM42vxfqZQsv4ehtTjFFxQ4sQKS2w6WR7emozFAn5cxu").map (·.2.length)) == some 34
#guard multibaseDecode? "uAQID" == some (.base64url, [1, 2, 3])
#guard multibaseEncode .base64url [1, 2, 3] == "uAQID"
#guard multibaseDecode? "uAQID=" == none
#guard multibaseDecode? "fabcd" == none
#guard isMultibase "z1" && !isMultibase "z0"
-- SHA2-256("abc") as a Multihash.
def abcDigest : List UInt8 :=
  (VC.Multibase.bytesOfHex? "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad").getD []
#guard (multihashEncode .sha2_256 abcDigest).take 2 == [0x12, 0x20]
#guard multihashDecode (multihashEncode .sha2_256 abcDigest) == .ok (.sha2_256, abcDigest)
#guard multihashDecode (multihashEncode .sha3_384 abcDigest) == .error (.lengthMismatch 32 48)
#guard multihashDecode ([0x20, 0x20] ++ abcDigest) == .error (.lengthMismatch 32 48)
#guard multihashDecode ([0x13, 0x20] ++ abcDigest) == .error (.unknownHeader 0x13)
#guard multihashDecode [] == .error .empty
#guard mediaTypeAccepted "application/cid"
#guard mediaTypeAccepted "Application/LD+JSON; profile=\"x\""
#guard !mediaTypeAccepted "text/html"
#guard acceptHeader == "application/cid, application/cid+json, application/ld+json, application/json"
#guard Relationship.all.all fun r => Relationship.ofName? r.name == some r
#guard Relationship.ofName? "proofOfWork" == none

end L4Factoidal.CID.Tests
