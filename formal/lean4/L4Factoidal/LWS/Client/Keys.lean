/-
L4Factoidal.LWS.Client.Keys — a new `did:key` agent for the LWS client, from
random bytes the host gives. https://github.com/danbri/factoidal/issues/1065

A self-issued credential (lws10-authn-ssi-cid) names its agent by a `did:key`
(W3C CCG did:key method). The client signs with the matching private key
(`Machine.selfIssuedJwt`): ES256 for a P-256 key, EdDSA for an Ed25519 key.
This module makes the key pair and the identifier:

* The private key is the first 32 bytes of the host's random bytes. For P-256
  the primitive refuses a scalar outside `[1, n-1]` (`es256Public` is `none`)
  and the next 32 bytes are tried; the host gives 64 bytes.
* The public key comes from the primitive (`Authz.Crypto`, HACL\*).
* The identifier is `did:key:` and a multibase base58btc value (the Multibase
  draft, prefix `z`) of the multicodec prefix and the public key: `0xed 0x01`
  and the 32 bytes for Ed25519 (`VC.DidKey.didKeyOfPublicKey`); `0x80 0x24`
  and the 33-byte SEC 1 compressed point for P-256 (the multicodec table
  entry `p256-pub`, code `0x1200`).
* The key id is the identifier, `#`, and the multibase value
  (did:key method, "Create a did:key", the one verification method).

`Authz.multikeyJwk?` is the inverse that the authorization server uses, so
the identifier made here is the identifier a server reads the key from.
-/
import L4Factoidal.LWS.Client.Machine
import L4Factoidal.Authz.SubjectToken
import L4Factoidal.VC.DidKey

namespace L4Factoidal.LWS.Client

open L4Factoidal.JSON
open L4Factoidal.VC.Multibase

/-- The multicodec prefix of a P-256 public key: `0x1200` as a varint. -/
def p256PubPrefix : Bytes := [0x80, 0x24]

/-- The SEC 1 §2.3.3 compressed point of a raw `x || y` P-256 public key:
`0x02` (even `y`) or `0x03` (odd `y`), then `x`. -/
def compressP256 (xy : ByteArray) : ByteArray :=
  let lastY := xy.get! 63
  ByteArray.mk #[if lastY % 2 == 1 then 3 else 2] ++ xy.extract 0 32

/-- The Multikey value of a raw P-256 public key. -/
def p256PublicKeyToMultikey (xy : ByteArray) : String :=
  multibaseEncodeBase58btc (p256PubPrefix ++ ofByteArray (compressP256 xy))

/-- A new agent: the identifier, the key id and the key the client signs
with. -/
structure NewAgent where
  agent : String
  kid : String
  key : SelfIssued

/-- The agent of a private key, or `none` when the primitive refuses it. -/
def agentOfSecret (C : L4Factoidal.Authz.Crypto) (alg : L4Factoidal.Authz.SigAlg)
    (sk : ByteArray) : Option NewAgent :=
  if sk.size != 32 then none else
  match alg with
  | .es256 =>
      (C.es256Public sk).bind fun xy =>
        if xy.size != 64 then none else
        let mk := p256PublicKeyToMultikey xy
        let did := "did:key:" ++ mk
        some { agent := did, kid := did ++ "#" ++ mk
               key := { subject := did, keyId := did ++ "#" ++ mk, alg, privateKey := sk } }
  | .eddsa =>
      (C.eddsaPublic sk).bind fun pk =>
        if pk.size != 32 then none else
        let mk := ed25519PublicKeyToMultikey (ofByteArray pk)
        let did := "did:key:" ++ mk
        some { agent := did, kid := did ++ "#" ++ mk
               key := { subject := did, keyId := did ++ "#" ++ mk, alg, privateKey := sk } }

/-- A new `did:key` agent from the host's random bytes: the first 32-byte
candidate (of the first 64 bytes) the primitive accepts. -/
def newAgent (C : L4Factoidal.Authz.Crypto) (alg : L4Factoidal.Authz.SigAlg)
    (random : ByteArray) : Option NewAgent :=
  match agentOfSecret C alg (random.extract 0 32) with
  | some a => some a
  | none => if random.size < 64 then none else agentOfSecret C alg (random.extract 32 64)

def newAgentJson (a : NewAgent) : Json :=
  .object [("agent", .string a.agent), ("kid", .string a.kid), ("selfIssued", selfIssuedJson a.key)]

end L4Factoidal.LWS.Client
