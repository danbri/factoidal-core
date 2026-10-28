/-
L4Factoidal.VC.CryptosuiteTests — build-time `#guard`s for
`VC/Cryptosuite.lean` over the test vectors of VC DI ECDSA 1.0 (w3c/vc-di-ecdsa
`TestVectors/`, commit 59df72ca8cdb275d97eb496086fea6fac4fa7f0f, 2026-09-16,
vendored in `third_party/testing/vc-di-ecdsa-vectors/`; the strings below are
copies of those files).

Everything PURE is checked here: the RFC 8785 transform against the published
canonical documents, the hash data (SHA-256 for P-256, SHA-384 for P-384)
against the published combined hashes, did:key decoding of the published
keys, the context rule, and the whole verify pipeline with a stub primitive
that accepts exactly the published (key, hash data, signature) triple. The
real P-256 signature checks call HACL* and run in `lake exe l4vc-probe`
(section `vc-di-ecdsa`), because an extern does not evaluate at compile time.
-/
import L4Factoidal.VC.Cryptosuite
import L4Factoidal.JSON.Parser

namespace L4Factoidal.VC.CryptosuiteTests

open L4Factoidal.Crypto
open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.VC.Multibase
open L4Factoidal.VC.DataIntegrity
open L4Factoidal.VC.Cryptosuite

/-! ## Vectors -/

def unsignedJson : String := "{\n    \"@context\": [\n        \"https://www.w3.org/ns/credentials/v2\",\n        \"https://www.w3.org/ns/credentials/examples/v2\"\n    ],\n    \"id\": \"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\n    \"type\": [\"VerifiableCredential\", \"AlumniCredential\"],\n    \"name\": \"Alumni Credential\",\n    \"description\": \"A minimum viable example of an Alumni Credential.\",\n    \"issuer\": \"https://vc.example/issuers/5678\",\n    \"validFrom\": \"2023-01-01T00:00:00Z\",\n    \"credentialSubject\": {\n        \"id\": \"did:example:abcdefgh\",\n        \"alumniOf\": \"The School of Examples\"\n    }\n}"
def jcsCanonDocP256 : String := "{\"@context\":[\"https://www.w3.org/ns/credentials/v2\",\"https://www.w3.org/ns/credentials/examples/v2\"],\"credentialSubject\":{\"alumniOf\":\"The School of Examples\",\"id\":\"did:example:abcdefgh\"},\"description\":\"A minimum viable example of an Alumni Credential.\",\"id\":\"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\"issuer\":\"https://vc.example/issuers/5678\",\"name\":\"Alumni Credential\",\"type\":[\"VerifiableCredential\",\"AlumniCredential\"],\"validFrom\":\"2023-01-01T00:00:00Z\"}"
def jcsProofCanonP256 : String := "{\"@context\":[\"https://www.w3.org/ns/credentials/v2\",\"https://www.w3.org/ns/credentials/examples/v2\"],\"created\":\"2023-02-24T23:36:38Z\",\"cryptosuite\":\"ecdsa-jcs-2019\",\"proofPurpose\":\"assertionMethod\",\"type\":\"DataIntegrityProof\",\"verificationMethod\":\"did:key:zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP#zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP\"}"
def jcsProofConfigP256 : String := "{\n  \"type\": \"DataIntegrityProof\",\n  \"cryptosuite\": \"ecdsa-jcs-2019\",\n  \"created\": \"2023-02-24T23:36:38Z\",\n  \"verificationMethod\": \"did:key:zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP#zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP\",\n  \"proofPurpose\": \"assertionMethod\",\n  \"@context\": [\n    \"https://www.w3.org/ns/credentials/v2\",\n    \"https://www.w3.org/ns/credentials/examples/v2\"\n  ]\n}"
def jcsCombinedP256 : String := "fe5799489119c7fe3c528715e72bd39d2ec6b4ab345978df32e9a9312648ec2559b7cb6251b8991add1ce0bc83107e3db9dbbab5bd2c28f687db1a03abc92f19"
def jcsSigHexP256 : String := "f15c3b599eb9b3cad05df9d8e8b39a70a86375833b53743c764ac0a88c4457d60707fd7d073e03d906130631d87803f80a9824dc9939632ba92d418181be9d16"
def jcsSignedP256 : String := "{\n  \"@context\": [\n    \"https://www.w3.org/ns/credentials/v2\",\n    \"https://www.w3.org/ns/credentials/examples/v2\"\n  ],\n  \"id\": \"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\n  \"type\": [\n    \"VerifiableCredential\",\n    \"AlumniCredential\"\n  ],\n  \"name\": \"Alumni Credential\",\n  \"description\": \"A minimum viable example of an Alumni Credential.\",\n  \"issuer\": \"https://vc.example/issuers/5678\",\n  \"validFrom\": \"2023-01-01T00:00:00Z\",\n  \"credentialSubject\": {\n    \"id\": \"did:example:abcdefgh\",\n    \"alumniOf\": \"The School of Examples\"\n  },\n  \"proof\": {\n    \"type\": \"DataIntegrityProof\",\n    \"cryptosuite\": \"ecdsa-jcs-2019\",\n    \"created\": \"2023-02-24T23:36:38Z\",\n    \"verificationMethod\": \"did:key:zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP#zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP\",\n    \"proofPurpose\": \"assertionMethod\",\n    \"@context\": [\n      \"https://www.w3.org/ns/credentials/v2\",\n      \"https://www.w3.org/ns/credentials/examples/v2\"\n    ],\n    \"proofValue\": \"z5ptCet75SaEgzG4v4zJhbJtfNi74Wv7Fq15hhKouJQQjEPQvPZKaYxcMXAMLPQS2FXrkCWokNJkFVkwxNzZfD5oT\"\n  }\n}"
def rdfcCanonDocP256 : String := "<did:example:abcdefgh> <https://www.w3.org/ns/credentials/examples#alumniOf> \"The School of Examples\" .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/2018/credentials#VerifiableCredential> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/ns/credentials/examples#AlumniCredential> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/description> \"A minimum viable example of an Alumni Credential.\" .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/name> \"Alumni Credential\" .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#credentialSubject> <did:example:abcdefgh> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#issuer> <https://vc.example/issuers/5678> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#validFrom> \"2023-01-01T00:00:00Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n"
def rdfcProofCanonP256 : String := "_:c14n0 <http://purl.org/dc/terms/created> \"2023-02-24T23:36:38Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n_:c14n0 <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://w3id.org/security#DataIntegrityProof> .\n_:c14n0 <https://w3id.org/security#cryptosuite> \"ecdsa-rdfc-2019\"^^<https://w3id.org/security#cryptosuiteString> .\n_:c14n0 <https://w3id.org/security#proofPurpose> <https://w3id.org/security#assertionMethod> .\n_:c14n0 <https://w3id.org/security#verificationMethod> <did:key:zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP#zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP> .\n"
def rdfcCombinedP256 : String := "3a8a522f689025727fb9d1f0fa99a618da023e8494ac74f51015d009d35abc2e517744132ae165a5349155bef0bb0cf2258fff99dfe1dbd914b938d775a36017"
def rdfcSigHexP256 : String := "1cb4290918ffb04a55ff7ae1e55e316a9990fda8eec67325eac7fcbf2ddf9dd2b06716a657e72b284c9604df3a172ecbf06a1a475b49ac807b1d9162df855636"
def rdfcSignedP256 : String := "{\n  \"@context\": [\n    \"https://www.w3.org/ns/credentials/v2\",\n    \"https://www.w3.org/ns/credentials/examples/v2\"\n  ],\n  \"id\": \"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\n  \"type\": [\n    \"VerifiableCredential\",\n    \"AlumniCredential\"\n  ],\n  \"name\": \"Alumni Credential\",\n  \"description\": \"A minimum viable example of an Alumni Credential.\",\n  \"issuer\": \"https://vc.example/issuers/5678\",\n  \"validFrom\": \"2023-01-01T00:00:00Z\",\n  \"credentialSubject\": {\n    \"id\": \"did:example:abcdefgh\",\n    \"alumniOf\": \"The School of Examples\"\n  },\n  \"proof\": {\n    \"type\": \"DataIntegrityProof\",\n    \"cryptosuite\": \"ecdsa-rdfc-2019\",\n    \"created\": \"2023-02-24T23:36:38Z\",\n    \"verificationMethod\": \"did:key:zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP#zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP\",\n    \"proofPurpose\": \"assertionMethod\",\n    \"proofValue\": \"zaHXrr7AQdydBk3ahpCDpWbxfLokDqmCToYm2dyWvpcFVyWooC2he63w1f7UNQoAMKdhaRtcnaE2KTo5o5vTCcfw\"\n  }\n}"
def jcsCanonDocP384 : String := "{\"@context\":[\"https://www.w3.org/ns/credentials/v2\",\"https://www.w3.org/ns/credentials/examples/v2\"],\"credentialSubject\":{\"alumniOf\":\"The School of Examples\",\"id\":\"did:example:abcdefgh\"},\"description\":\"A minimum viable example of an Alumni Credential.\",\"id\":\"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\"issuer\":\"https://vc.example/issuers/5678\",\"name\":\"Alumni Credential\",\"type\":[\"VerifiableCredential\",\"AlumniCredential\"],\"validFrom\":\"2023-01-01T00:00:00Z\"}"
def jcsProofCanonP384 : String := "{\"@context\":[\"https://www.w3.org/ns/credentials/v2\",\"https://www.w3.org/ns/credentials/examples/v2\"],\"created\":\"2023-02-24T23:36:38Z\",\"cryptosuite\":\"ecdsa-jcs-2019\",\"proofPurpose\":\"assertionMethod\",\"type\":\"DataIntegrityProof\",\"verificationMethod\":\"did:key:z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ#z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ\"}"
def jcsProofConfigP384 : String := "{\n  \"type\": \"DataIntegrityProof\",\n  \"cryptosuite\": \"ecdsa-jcs-2019\",\n  \"created\": \"2023-02-24T23:36:38Z\",\n  \"verificationMethod\": \"did:key:z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ#z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ\",\n  \"proofPurpose\": \"assertionMethod\",\n  \"@context\": [\n    \"https://www.w3.org/ns/credentials/v2\",\n    \"https://www.w3.org/ns/credentials/examples/v2\"\n  ]\n}"
def jcsCombinedP384 : String := "83e5057817abb0c6872eafeaba1a9e53893c58eeb7414fb6d8aa3fa8c7917f7ad4792890b257c598baa17f4fbe6d183c3e0be671cc1881035d463158c80921973dab3534d4f8dfacf4ff2725a4115eb718e49d66de0e90e7365cd6062abf2259"
def jcsSigHexP384 : String := "8b7462ce62db0c8ff19878c4b3561c49eb71b4a743086b6d5b0eda70ecf0afc5a03fd88eb207d66b262ed87fd200a4e8e62716e0b329c032b67726b4b0fc737a44c1cefdba2fdccb3ece74cc5845aaa93374455a726f6ee4f5f30da9427f608a"
def jcsSignedP384 : String := "{\n  \"@context\": [\n    \"https://www.w3.org/ns/credentials/v2\",\n    \"https://www.w3.org/ns/credentials/examples/v2\"\n  ],\n  \"id\": \"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\n  \"type\": [\n    \"VerifiableCredential\",\n    \"AlumniCredential\"\n  ],\n  \"name\": \"Alumni Credential\",\n  \"description\": \"A minimum viable example of an Alumni Credential.\",\n  \"issuer\": \"https://vc.example/issuers/5678\",\n  \"validFrom\": \"2023-01-01T00:00:00Z\",\n  \"credentialSubject\": {\n    \"id\": \"did:example:abcdefgh\",\n    \"alumniOf\": \"The School of Examples\"\n  },\n  \"proof\": {\n    \"type\": \"DataIntegrityProof\",\n    \"cryptosuite\": \"ecdsa-jcs-2019\",\n    \"created\": \"2023-02-24T23:36:38Z\",\n    \"verificationMethod\": \"did:key:z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ#z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ\",\n    \"proofPurpose\": \"assertionMethod\",\n    \"@context\": [\n      \"https://www.w3.org/ns/credentials/v2\",\n      \"https://www.w3.org/ns/credentials/examples/v2\"\n    ],\n    \"proofValue\": \"zq3EuTeLiGurmB2JR5oL8oWEsT7u2tba4HT1oZbiMYWc5qzsoW2kLYcBcF4HM5vCpJyTkceULKrVXuJQkXeN5seL4uXrFNFRMm53GWy1Yrto8rTWxZi9DkNeWP7yUPs7ELAm\"\n  }\n}"
def rdfcCanonDocP384 : String := "<did:example:abcdefgh> <https://www.w3.org/ns/credentials/examples#alumniOf> \"The School of Examples\" .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/2018/credentials#VerifiableCredential> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://www.w3.org/ns/credentials/examples#AlumniCredential> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/description> \"A minimum viable example of an Alumni Credential.\" .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://schema.org/name> \"Alumni Credential\" .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#credentialSubject> <did:example:abcdefgh> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#issuer> <https://vc.example/issuers/5678> .\n<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> <https://www.w3.org/2018/credentials#validFrom> \"2023-01-01T00:00:00Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n"
def rdfcProofCanonP384 : String := "_:c14n0 <http://purl.org/dc/terms/created> \"2023-02-24T23:36:38Z\"^^<http://www.w3.org/2001/XMLSchema#dateTime> .\n_:c14n0 <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <https://w3id.org/security#DataIntegrityProof> .\n_:c14n0 <https://w3id.org/security#cryptosuite> \"ecdsa-rdfc-2019\"^^<https://w3id.org/security#cryptosuiteString> .\n_:c14n0 <https://w3id.org/security#proofPurpose> <https://w3id.org/security#assertionMethod> .\n_:c14n0 <https://w3id.org/security#verificationMethod> <did:key:z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ#z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ> .\n"
def rdfcCombinedP384 : String := "e32805a26492eac777aa7a138f6d8da3c74e0c7be7b296dcaccf97420c3b92eaad7be6449ca565e165031567f5c7cbc18bf6e01df72c5b62f91b685231915ac4b8c58ea95f002c6b8f6bfafa1b251df476b56b8e01518e317dab099d3ecbff96"
def rdfcSigHexP384 : String := "177ac088806c2506d49f0bfec16056a6a80ace62cd029888ad561aba22a59d192d77d9b1fc28df80dea5ee6c8bceb16f1b8bff6bd6ff2d8f8778bdde48bafa7b6cc1f914c0168b5c04499882f632deea9cb7d977e888bb0e1ee9fb20ff03b025"
def rdfcSignedP384 : String := "{\n  \"@context\": [\n    \"https://www.w3.org/ns/credentials/v2\",\n    \"https://www.w3.org/ns/credentials/examples/v2\"\n  ],\n  \"id\": \"urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33\",\n  \"type\": [\n    \"VerifiableCredential\",\n    \"AlumniCredential\"\n  ],\n  \"name\": \"Alumni Credential\",\n  \"description\": \"A minimum viable example of an Alumni Credential.\",\n  \"issuer\": \"https://vc.example/issuers/5678\",\n  \"validFrom\": \"2023-01-01T00:00:00Z\",\n  \"credentialSubject\": {\n    \"id\": \"did:example:abcdefgh\",\n    \"alumniOf\": \"The School of Examples\"\n  },\n  \"proof\": {\n    \"type\": \"DataIntegrityProof\",\n    \"cryptosuite\": \"ecdsa-rdfc-2019\",\n    \"created\": \"2023-02-24T23:36:38Z\",\n    \"verificationMethod\": \"did:key:z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ#z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ\",\n    \"proofPurpose\": \"assertionMethod\",\n    \"proofValue\": \"z967Mvv5bxtmLNqTzPZ8KmJjFmFXaAKeQNzq7GWnQkMcLtaGSSmuozE5WtJ8PipMe178B1tE28K1vsJur9bGVJhz6jgSJsRHFSQeqgH8hhjcg8gZDFJC1b9FsR5ggNmDBqHv\"\n  }\n}"
def p256PublicMultibase : String := "zDnaepBuvsQ8cpsWrVKw8fbpGpvPeNSjVPTWoq6cRqaYzBKVP"
def p384PublicMultibase : String := "z82LkuBieyGShVBhvtE2zoiD6Kma4tJGFtkAhxR5pfkp5QPw4LutoYWhvQCnGjdVn14kujQ"

def j (s : String) : Json := (parseJson? s).getD .null

/-! ## RFC 8785 transform -/

#guard transform Loader.none .jcs .sha256 (j unsignedJson) == .ok jcsCanonDocP256
#guard transform Loader.none .jcs .sha384 (j unsignedJson) == .ok jcsCanonDocP384
#guard transform Loader.none .jcs .sha256 (j jcsProofConfigP256) == .ok jcsProofCanonP256
#guard transform Loader.none .jcs .sha384 (j jcsProofConfigP384) == .ok jcsProofCanonP384

/-! ## Hash data: SHA-256 for P-256, SHA-384 for P-384 -/

#guard hashDataHex Curve.p256.hashAlg jcsCanonDocP256 jcsProofCanonP256 == jcsCombinedP256
#guard hashDataHex Curve.p384.hashAlg jcsCanonDocP384 jcsProofCanonP384 == jcsCombinedP384
#guard hashDataHex Curve.p256.hashAlg rdfcCanonDocP256 rdfcProofCanonP256 == rdfcCombinedP256
#guard hashDataHex Curve.p384.hashAlg rdfcCanonDocP384 rdfcProofCanonP384 == rdfcCombinedP384

/-! ## Keys -/

def vmP256 : String := s!"did:key:{p256PublicMultibase}#{p256PublicMultibase}"
def vmP384 : String := s!"did:key:{p384PublicMultibase}#{p384PublicMultibase}"

#guard (publicKeyOfDidKey? vmP256).map (fun k => (k.curve, k.key.size)) == some (.p256, 33)
#guard (publicKeyOfDidKey? vmP384).map (fun k => (k.curve, k.key.size)) == some (.p384, 49)
#guard (publicKeyOfDidKey? s!"did:key:{p256PublicMultibase}").isSome
-- the fragment must be the same key
#guard (publicKeyOfDidKey? s!"did:key:{p256PublicMultibase}#{p384PublicMultibase}").isNone
#guard (publicKeyOfDidKey? vmP256).map didKeyVerificationMethod == some vmP256
#guard (publicKeyOfDidKey? vmP384).map didKeyVerificationMethod == some vmP384
-- the vectors' verificationMethod is that did:key
#guard ((j jcsSignedP256).field? "proof" |>.bind (·.getString? "verificationMethod")) == some vmP256

/-! ## Suites and curves -/

#guard Suite.ofName? "ecdsa-rdfc-2019" == some ecdsaRdfc2019
#guard Suite.ofName? "ecdsa-jcs-2019" == some ecdsaJcs2019
#guard Suite.ofName? "eddsa-rdfc-2022" == some eddsaRdfc2022
#guard Suite.ofName? "ecdsa-sd-2023" == none
#guard ecdsaRdfc2019.accepts .p256 && ecdsaRdfc2019.accepts .p384 && !ecdsaRdfc2019.accepts .ed25519
#guard eddsaRdfc2022.accepts .ed25519 && !eddsaRdfc2022.accepts .p256

/-! ## Contexts (VC DI, Verify Proof) -/

#guard contextStartsWith (some (j "[\"a\",\"b\"]")) (j "[\"a\"]")
#guard contextStartsWith (some (j "[\"a\",\"b\"]")) (j "[\"a\",\"b\"]")
#guard contextStartsWith (some (.string "a")) (.string "a")
#guard !contextStartsWith (some (j "[\"a\",\"b\"]")) (j "[\"b\"]")
#guard !contextStartsWith (some (j "[\"a\"]")) (j "[\"a\",\"b\"]")
#guard !contextStartsWith none (.string "a")

/-! ## The verify pipeline with a stub primitive

`stub` accepts exactly the published triple: the vector's key, the vector's
hash data, the vector's signature. So a `.ok ()` below says that the
pipeline rebuilt the published hash data from the signed document. -/

def stubFor (curve : Curve) (vm combined sigHex : String) : Primitives :=
  { verify := fun c pk msg sig =>
      c == curve && (publicKeyOfDidKey? vm).any (·.key.data == pk.data) &&
      hexOfByteArray msg == combined && hexOfByteArray sig == sigHex
    available := fun _ => true }

def stubP256 : Primitives := stubFor .p256 vmP256 jcsCombinedP256 jcsSigHexP256
def stubP384 : Primitives := stubFor .p384 vmP384 jcsCombinedP384 jcsSigHexP384

#guard verifyDocument Loader.none stubP256 (j jcsSignedP256) == .ok ()
#guard verifyDocument Loader.none stubP384 (j jcsSignedP384) == .ok ()
-- the other curve's primitive does not accept it
#guard verifyDocument Loader.none stubP384 (j jcsSignedP256) == .error (.di .signatureRejected)

/-- The signed vector with one field of the credential changed. -/
def tampered : Json :=
  setField "name" (.string "Alumni Credential!") (j jcsSignedP256)

#guard verifyDocument Loader.none stubP256 tampered == .error (.di .signatureRejected)

/-- The signed vector with a proof `@context` the document does not start with. -/
def badContext : Json :=
  match (j jcsSignedP256).field? "proof" with
  | some p => setField "proof" (setField "@context" (j "[\"https://example.org/other\"]") p) (j jcsSignedP256)
  | none => .null

#guard verifyDocument Loader.none stubP256 badContext == .error .contextNotPrefix

-- a target without P-384 refuses, naming the curve
#guard verifyDocument Loader.none { stubP384 with available := fun c => c != .p384 } (j jcsSignedP384)
  == .error (.curveUnavailable "P-384")

-- the wrong purpose, an unknown suite
#guard verifyDocument Loader.none stubP256 (j jcsSignedP256) "authentication"
  == .error (.di (.wrongPurpose "assertionMethod" "authentication"))

def renamedSuite : Json :=
  match (j jcsSignedP256).field? "proof" with
  | some p => setField "proof" (setField "cryptosuite" (.string "ecdsa-xyz") p) (j jcsSignedP256)
  | none => .null

#guard verifyDocument Loader.none stubP256 renamedSuite == .error (.unknownCryptosuite "ecdsa-xyz")

/-! ## Create, then verify, with a stub signer

The stub signer "signs" with the hash data itself and the stub verifier
accepts a signature equal to the message: a round trip through
`secureDocument` and `verifyDocument` with no cryptography, which checks that
create and verify build the same hash data. -/

def echoSigner (c : Curve) (vm : String) : Signer :=
  { curve := c, verificationMethod := vm, sign := fun m => some m }

def echoPrims : Primitives :=
  { verify := fun _ _ msg sig => msg.data == sig.data, available := fun _ => true }

#guard (secureDocument Loader.none (echoSigner .p256 vmP256) ecdsaJcs2019 "assertionMethod"
    "2023-02-24T23:36:38Z" (j unsignedJson)).toOption.map
    (verifyDocument Loader.none echoPrims) == some (.ok ())
#guard (secureDocument Loader.none (echoSigner .p384 vmP384) ecdsaJcs2019 "assertionMethod"
    "2023-02-24T23:36:38Z" (j unsignedJson)).toOption.map
    (verifyDocument Loader.none echoPrims) == some (.ok ())
-- the secured JCS document's proof configuration is the published one
#guard ((secureDocument Loader.none (echoSigner .p256 vmP256) ecdsaJcs2019 "assertionMethod"
    "2023-02-24T23:36:38Z" (j unsignedJson)).toOption.bind (·.field? "proof")
    |>.map (fun p => jcsDocument (withoutField "proofValue" p))) == some jcsProofCanonP256
-- a suite refuses a key of another family
#guard (secureDocument Loader.none (echoSigner .ed25519 vmP256) ecdsaJcs2019 "assertionMethod"
    "" (j unsignedJson)).toOption.isNone

end L4Factoidal.VC.CryptosuiteTests
