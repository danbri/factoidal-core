/-
L4Factoidal.SAML.Assertion — validation of a signed SAML 2.0 assertion
used as an authentication credential
(https://github.com/danbri/factoidal/issues/926).

Specs: Assertions and Protocols for the OASIS Security Assertion Markup
Language (SAML) V2.0 ("SAML Core"), OASIS Standard 15 March 2005, and its
§5 signature profile (`L4Factoidal.XML.DSig`); Profiles for SAML V2.0
§4.1.4.2 (bearer subject confirmation); LWS 1.0 Authentication Suite:
SAML 2.0 (lws10-authn-saml): "SAML tokens used as authentication
credentials MUST be signed", the subject is `saml:NameID`, the issuer
`saml:Issuer`, the client the `Recipient` of
`saml:SubjectConfirmationData`, the audience `saml:Audience`; RFC 8693 §3:
token type `urn:ietf:params:oauth:token-type:saml2` is "a base64url-encoded
SAML 2.0 assertion".

## What is accepted

  * At most `maxTokenChars` characters of base64url (RFC 4648 §5, no
    padding) whose octets are UTF-8 XML. An XML declaration, if present,
    names UTF-8 or no encoding.
  * The document element is `saml:Assertion` with `Version="2.0"`, one
    `saml:Issuer` (an entity identifier: no `Format`, or the entity
    format), one `saml:Subject`, one `saml:Conditions`.
  * The issuer is one of the caller's trusted identity providers (trust is
    out of band, lws10-authn-saml "Validation"), and the enveloped
    signature verifies under THAT provider's RSA key
    (`DSig.verifyEnveloped`). A key in `ds:KeyInfo` is never used.
  * `saml:Conditions`: `NotOnOrAfter` required, `NotBefore` optional,
    both UTC (SAML Core §1.3.3), checked with `leeway` seconds of skew;
    one or more `saml:AudienceRestriction` and nothing else (an unknown
    condition makes the assertion invalid, SAML Core §2.5.1.1; `OneTimeUse`
    and `ProxyRestriction` are refused). Every AudienceRestriction must
    name the caller's audience (SAML Core §2.5.1.4).
  * `saml:Subject`: one `saml:NameID` (its text is the subject) and one
    `saml:SubjectConfirmation` with the bearer method, whose
    `saml:SubjectConfirmationData` has `Recipient` (the client) and
    `NotOnOrAfter`, and no `NotBefore` (Profiles §4.1.4.2).

## Encrypted assertions (`validateWith`)

SAML Core §2.3.4 `saml:EncryptedAssertion` and §2.2.4 `saml:EncryptedID`
(https://github.com/danbri/factoidal/issues/1073), XML Encryption 1.1 in
the profile of `L4Factoidal.XML.Enc`:

  * When the policy has decryption keys (`Policy.decryptKeys`), a subject
    token whose document element is `saml:EncryptedAssertion` is decrypted
    (`Enc.decryptWrapped`), and the decrypted `saml:Assertion`, made the
    document element with the namespace bindings it was parsed with, goes
    through the same checks as an assertion that was not encrypted: the
    issuer, the enveloped signature under that identity provider's key,
    the conditions and the subject. An encrypted assertion whose content is
    not signed is refused ("exactly one ds:Signature").
  * After the signature is verified, a `saml:EncryptedID` child of
    `saml:Subject` is decrypted to the `saml:NameID` it holds. The
    signature covers the encrypted form, as SAML Core §2.2.4 makes it.
  * With no decryption key both are refused, as before, naming the issue.
  * `saml:EncryptedAttribute` is refused: the claims read no attribute, and
    an encrypted element is never skipped. Expected-failure guard in
    `SAML/Tests.lean`, https://github.com/danbri/factoidal/issues/1073.

AES is a `CipherCall.Cipher`: `validateWith` answers `Outcome.need req` when
the cipher needs the host (the wasm replay); `validate` takes no keys and
refuses every encrypted element.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.DSig
import L4Factoidal.XML.Enc
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.LWS.AccessPolicy

namespace L4Factoidal.SAML

open L4Factoidal.XML
open L4Factoidal.XML.DSig
open L4Factoidal.XML.Canonical (rootScope)

def samlNs : String := "urn:oasis:names:tc:SAML:2.0:assertion"
def bearerMethod : String := "urn:oasis:names:tc:SAML:2.0:cm:bearer"
def entityFormat : String := "urn:oasis:names:tc:SAML:2.0:nameid-format:entity"
def encryptionIssue : String := "https://github.com/danbri/factoidal/issues/1073"

/-- The longest subject token read, in characters (48 KiB of XML). -/
def maxTokenChars : Nat := 65536

/-- A trusted identity provider: its entity identifier and RSA public key. -/
structure Idp where
  entityId : String
  n : ByteArray
  e : ByteArray

structure Policy where
  idps : List Idp
  /-- The audience the assertion must be restricted to (this server). -/
  audience : String
  now : Nat
  leeway : Nat := 60
  /-- Private keys for `saml:EncryptedAssertion` and `saml:EncryptedID`
  (`validateWith`); none: every encrypted element is refused. -/
  decryptKeys : L4Factoidal.XML.Enc.Keys := {}

/-- What a valid assertion says. -/
structure Claims where
  issuer : String
  nameId : String
  recipient : String
  deriving Repr, BEq, DecidableEq

/-! ## Decoding -/

/-- The deepest element nesting read. A SAML assertion nests about six
levels; the bound keeps every tree walk of the signature check at a
constant stack depth. -/
def maxDepth : Nat := 32

/-- Is the element nesting of `cs` at most `maxDepth`? A scan of the text
before it is parsed: `<` not followed by `/`, `!` or `?` opens a level,
`</` and `/>` close one. Markup inside a comment or CDATA section can only
make the count larger, so the scan refuses, never accepts, too much. A
tail call per character. -/
def nestingOk (cs : List Char) (d : Nat) : Bool := L4Factoidal.XML.Enc.nestingWithin maxDepth cs d

def decodeToken (token : String) : Except String Document := do
  if token.length > maxTokenChars then throw "the SAML assertion is too large"
  let bytes ← (L4Factoidal.JOSE.Base64Url.decode token).elim
    (.error "the subject token is not base64url") .ok
  let text ← (String.fromUTF8? bytes).elim (.error "the SAML assertion is not UTF-8") .ok
  if !nestingOk text.toList 0 then throw s!"the SAML assertion nests more than {maxDepth} levels"
  let d ← match parseXML text with
    | .ok d => pure d
    | .error _ => throw "the SAML assertion is not well-formed XML"
  match d.decl with
  | some x =>
      match x.encoding with
      | some enc => if enc.toLower != "utf-8" then throw s!"the SAML assertion declares encoding {enc}"
      | none => pure ()
  | none => pure ()
  pure d

/-! ## Reading the assertion -/

def samlKids (e : El) (l : String) : List El := e.children.filter (·.is samlNs l)

def one (e : El) (l : String) : Except String El :=
  match samlKids e l with
  | [x] => .ok x
  | [] => .error s!"saml:{e.lname} has no saml:{l}"
  | _ => .error s!"saml:{e.lname} has more than one saml:{l}"

def textOf (e : El) : Except String String :=
  match e.text? with
  | some t => if (trimWs t).isEmpty then .error s!"saml:{e.lname} is empty" else .ok (trimWs t)
  | none => .error s!"saml:{e.lname} must hold text only"

/-- An `xs:dateTime` in UTC, as seconds since the epoch. -/
def utcTime? (s : String) : Option Int :=
  if s.endsWith "Z" then L4Factoidal.LWS.AccessPolicy.parseXsdDateTime? s else none

def timeAttr (e : El) (a : String) : Except String (Option Int) :=
  match e.attr? a with
  | none => .ok none
  | some v => (utcTime? v).elim (.error s!"{a} is not a UTC xs:dateTime") (.ok ∘ some)

def isEncrypted (e : El) : Bool :=
  e.ns == samlNs && ["EncryptedAssertion", "EncryptedID", "EncryptedAttribute"].contains e.lname

/-- The document element and its issuer, before the signature is checked:
only to choose the key. -/
def assertionIssuer (d : Document) : Except String (El × String) := do
  let a ← (elOf? rootScope d.root).elim (.error "no document element") .ok
  if isEncrypted a then
    throw s!"encrypted SAML assertions are not accepted ({encryptionIssue})"
  if !a.is samlNs "Assertion" then throw "the subject token is not a saml:Assertion"
  if a.attr? "Version" != some "2.0" then throw "the assertion is not SAML 2.0"
  let i ← one a "Issuer"
  match i.attr? "Format" with
  | some f => if f != entityFormat then throw "the issuer is not an entity identifier"
  | none => pure ()
  pure (a, ← textOf i)

def timesOk (p : Policy) (notBefore notOnOrAfter : Option Int) : Except String Unit := do
  let now : Int := p.now
  match notOnOrAfter with
  | none => throw "the assertion has no NotOnOrAfter"
  | some t => if t + p.leeway ≤ now then throw "the assertion has expired"
  match notBefore with
  | some t => if t > now + p.leeway then throw "the assertion is not valid yet"
  | none => pure ()

def conditionsOk (p : Policy) (a : El) : Except String Unit := do
  let c ← one a "Conditions"
  if !c.elementOnly then throw "saml:Conditions has unexpected content"
  timesOk p (← timeAttr c "NotBefore") (← timeAttr c "NotOnOrAfter")
  let rs := c.children
  if rs.isEmpty then throw "the assertion has no saml:AudienceRestriction"
  for r in rs do
    if !r.is samlNs "AudienceRestriction" then
      throw s!"the condition {r.lname} is not supported"
    if !r.elementOnly then throw "saml:AudienceRestriction has unexpected content"
    let auds ← r.children.mapM fun x =>
      if x.is samlNs "Audience" then textOf x else .error "saml:AudienceRestriction holds other than saml:Audience"
    if !auds.contains p.audience then
      throw "the assertion's audience does not include this authorization server"

/-- The subject and the client, from `saml:Subject`. -/
def subjectOf (p : Policy) (a : El) : Except String (String × String) := do
  let s ← one a "Subject"
  if !s.elementOnly then throw "saml:Subject has unexpected content"
  if s.children.any isEncrypted then
    throw s!"encrypted SAML identifiers are not accepted ({encryptionIssue})"
  match s.children with
  | [nid, sc] =>
      if !nid.is samlNs "NameID" then throw "saml:Subject must begin with saml:NameID"
      let sub ← textOf nid
      if !sc.is samlNs "SubjectConfirmation" then throw "saml:Subject has an unexpected child"
      if sc.attr? "Method" != some bearerMethod then throw "the subject confirmation is not bearer"
      let scd ← one sc "SubjectConfirmationData"
      if sc.children.length != 1 then throw "saml:SubjectConfirmation has an unexpected child"
      if (scd.attr? "NotBefore").isSome then
        throw "a bearer saml:SubjectConfirmationData must not have NotBefore"
      timesOk p none (← timeAttr scd "NotOnOrAfter")
      let r ← (scd.attr? "Recipient").elim (.error "saml:SubjectConfirmationData has no Recipient") .ok
      if r.isEmpty then throw "saml:SubjectConfirmationData has an empty Recipient"
      pure (sub, r)
  | _ => throw "saml:Subject must be one saml:NameID and one saml:SubjectConfirmation"

/-- The claims of an assertion whose signature verified. -/
def claimsOf (p : Policy) (a : El) (issuer : String) : Except String Claims := do
  if countNode isEncrypted a.parent 0 a.node != 0 then
    throw s!"encrypted SAML elements are not accepted ({encryptionIssue})"
  conditionsOk p a
  let (sub, r) ← subjectOf p a
  pure { issuer, nameId := sub, recipient := r }

/-! ## Validation -/

/-- Validate a base64url-encoded SAML 2.0 assertion. The signature is
checked before any claim is read, with the key of the identity provider the
assertion names. -/
def validate (rsa : RsaVerify) (p : Policy) (token : String) : Except String Claims :=
  match decodeToken token with
  | .error w => .error w
  | .ok d =>
      match assertionIssuer d with
      | .error w => .error w
      | .ok (a, iss) =>
          match p.idps.find? (·.entityId == iss) with
          | none => .error s!"the assertion's issuer {iss} is not a trusted identity provider"
          | some idp =>
              match verifyEnveloped rsa idp.n idp.e d with
              | .error w => .error w
              | .ok () => claimsOf p a iss

/-- A valid assertion was decoded, its issuer is a trusted identity
provider of the policy, and its signature verified under that provider's
key, whatever the verifier is. -/
theorem validate_ok {rsa : RsaVerify} {p : Policy} {token : String} {c : Claims}
    (h : validate rsa p token = .ok c) :
    ∃ d idp, decodeToken token = .ok d ∧ idp ∈ p.idps ∧ idp.entityId = c.issuer ∧
      verifyEnveloped rsa idp.n idp.e d = .ok () := by
  unfold validate at h
  cases hd : decodeToken token with
  | error w => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h; dsimp only at h
    cases ha : assertionIssuer d with
    | error w => rw [ha] at h; cases h
    | ok ai =>
      obtain ⟨a, iss⟩ := ai
      rw [ha] at h; dsimp only at h
      cases hf : p.idps.find? (·.entityId == iss) with
      | none => rw [hf] at h; cases h
      | some idp =>
        rw [hf] at h; dsimp only at h
        cases hv : verifyEnveloped rsa idp.n idp.e d with
        | error w => rw [hv] at h; cases h
        | ok u =>
          rw [hv] at h; dsimp only at h
          have hiss : c.issuer = iss := by
            unfold claimsOf at h
            simp only [bind, Except.bind] at h
            split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · rename_i x _
                  obtain ⟨_, _⟩ := x
                  cases h; rfl
          have hmem := List.mem_of_find?_eq_some hf
          have heq : idp.entityId = iss := by
            have := List.find?_some hf
            simpa using this
          exact ⟨d, idp, rfl, hmem, heq.trans hiss.symm, hv⟩

/-! ## Encrypted assertions -/

open L4Factoidal.XML.Enc (Failure)

/-- Why `validateWith` gives no claims: a refusal with its reason, or an AES
request the host has to answer first. -/
inductive Outcome where
  | refused (msg : String)
  | need (req : L4Factoidal.Crypto.CipherCall.Req)

def Outcome.message : Outcome → String
  | .refused m => m
  | .need r => s!"an AES request ({r.op.name}) is not answered yet"

def ofEnc : Failure → Outcome
  | .refused m => .refused m
  | .decryptFailed => .refused L4Factoidal.XML.Enc.decryptionError
  | .need r => .need r

def liftS {α : Type} : Except String α → Except Outcome α
  | .ok a => .ok a
  | .error w => .error (.refused w)

def liftE {α : Type} : L4Factoidal.XML.Enc.M α → Except Outcome α
  | .ok a => .ok a
  | .error f => .error (ofEnc f)

/-- Decryption limits: the nesting bound of `decodeToken`; no CBC. -/
def encOpts : L4Factoidal.XML.Enc.Opts := { maxDepth := maxDepth }

/-- `f` over a list, the results in order; a tail call per item. -/
def mapAcc {α β ε : Type} (f : α → Except ε β) : List α → List β → Except ε (List β)
  | [], acc => .ok acc.reverse
  | x :: xs, acc =>
      match f x with
      | .ok y => mapAcc f xs (y :: acc)
      | .error e => .error e

/-- The assertion with each `saml:EncryptedID` child of `saml:Subject`
replaced by the `saml:NameID` it holds. -/
def decryptSubjectIds (cipher : L4Factoidal.Crypto.CipherCall.Cipher) (prims : L4Factoidal.XML.Enc.Prims)
    (keys : L4Factoidal.XML.Enc.Keys) (a : El) : Except Outcome El := do
  let inSubject (s : El) (n : Node) : Except Outcome Node :=
    match elOf? s.scope n with
    | some e =>
        if e.is samlNs "EncryptedID" then do
          let m ← liftE (L4Factoidal.XML.Enc.decryptWrapped cipher prims keys encOpts a.node e 3)
          match elOf? e.scope m with
          | some x => if x.is samlNs "NameID" then pure m else throw (.refused "saml:EncryptedID does not hold a saml:NameID")
          | none => throw (.refused "saml:EncryptedID does not hold a saml:NameID")
        else pure n
    | none => pure n
  let inAssertion (n : Node) : Except Outcome Node :=
    match elOf? a.scope n, n with
    | some s, .element t attrs kids =>
        if s.is samlNs "Subject" then do
          let kids' ← mapAcc (inSubject s) kids []
          pure (.element t attrs kids')
        else pure n
    | _, _ => pure n
  let kids' ← mapAcc inAssertion a.kids []
  let node : Node := match a.node with
    | .element t attrs _ => .element t attrs kids'
    | n => n
  match elOf? a.parent node with
  | some a' => pure a'
  | none => throw (.refused "no document element")

/-- The document of a subject token: the token's own, or, for a
`saml:EncryptedAssertion` when `p.decryptKeys` is not empty, the decrypted
assertion made the document element. -/
def openToken (cipher : L4Factoidal.Crypto.CipherCall.Cipher) (prims : L4Factoidal.XML.Enc.Prims)
    (p : Policy) (token : String) : Except Outcome Document := do
  let d0 ← liftS (decodeToken token)
  let r ← liftS ((elOf? rootScope d0.root).elim (.error "no document element") .ok)
  if r.is samlNs "EncryptedAssertion" && !p.decryptKeys.isEmpty then do
    let n ← liftE (L4Factoidal.XML.Enc.decryptWrapped cipher prims p.decryptKeys encOpts d0.root r 1)
    pure { d0 with root := L4Factoidal.XML.Enc.withScope r.scope n }
  else pure d0

/-- The checks of `validate` on an opened document, with `saml:EncryptedID`
decrypted after the signature is verified. -/
def checkDoc (cipher : L4Factoidal.Crypto.CipherCall.Cipher) (prims : L4Factoidal.XML.Enc.Prims)
    (rsa : RsaVerify) (p : Policy) (d : Document) : Except Outcome Claims :=
  match assertionIssuer d with
  | .error w => .error (.refused w)
  | .ok (a, iss) =>
      match p.idps.find? (·.entityId == iss) with
      | none => .error (.refused s!"the assertion's issuer {iss} is not a trusted identity provider")
      | some idp =>
          match verifyEnveloped rsa idp.n idp.e d with
          | .error w => .error (.refused w)
          | .ok () =>
              match (if p.decryptKeys.isEmpty then .ok a else decryptSubjectIds cipher prims p.decryptKeys a) with
              | .error o => .error o
              | .ok a' =>
                  match claimsOf p a' iss with
                  | .error w => .error (.refused w)
                  | .ok c => .ok c

/-- `validate`, and also a `saml:EncryptedAssertion` subject token and a
`saml:EncryptedID` subject when `p.decryptKeys` is not empty. -/
def validateWith (cipher : L4Factoidal.Crypto.CipherCall.Cipher) (prims : L4Factoidal.XML.Enc.Prims)
    (rsa : RsaVerify) (p : Policy) (token : String) : Except Outcome Claims :=
  match openToken cipher prims p token with
  | .error o => .error o
  | .ok d => checkDoc cipher prims rsa p d

/-- The issuer of the claims `claimsOf` returns is the issuer it was given. -/
theorem claimsOf_issuer {p : Policy} {a : El} {iss : String} {c : Claims}
    (h : claimsOf p a iss = .ok c) : c.issuer = iss := by
  unfold claimsOf at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i x _
        obtain ⟨_, _⟩ := x
        cases h; rfl

/-- Claims from `validateWith`, encrypted or not, come from a document whose
enveloped signature verified under the key of a trusted identity provider
whose entity identifier is the claims' issuer, whatever the cipher, the
primitives and the verifier are. -/
theorem validateWith_ok {cipher : L4Factoidal.Crypto.CipherCall.Cipher}
    {prims : L4Factoidal.XML.Enc.Prims} {rsa : RsaVerify} {p : Policy} {token : String} {c : Claims}
    (h : validateWith cipher prims rsa p token = .ok c) :
    ∃ d idp, idp ∈ p.idps ∧ idp.entityId = c.issuer ∧ verifyEnveloped rsa idp.n idp.e d = .ok () := by
  unfold validateWith at h
  cases ho : openToken cipher prims p token with
  | error o => rw [ho] at h; cases h
  | ok d =>
    rw [ho] at h; dsimp only at h
    unfold checkDoc at h
    cases ha : assertionIssuer d with
    | error w => rw [ha] at h; cases h
    | ok ai =>
      obtain ⟨a, iss⟩ := ai
      rw [ha] at h; dsimp only at h
      cases hf : p.idps.find? (·.entityId == iss) with
      | none => rw [hf] at h; cases h
      | some idp =>
        rw [hf] at h; dsimp only at h
        cases hv : verifyEnveloped rsa idp.n idp.e d with
        | error w => rw [hv] at h; cases h
        | ok u =>
          rw [hv] at h; dsimp only at h
          split at h
          · cases h
          · rename_i a' _
            cases hc : claimsOf p a' iss with
            | error w => rw [hc] at h; cases h
            | ok c' =>
              rw [hc] at h; cases h
              have hmem := List.mem_of_find?_eq_some hf
              have heq : idp.entityId = iss := by
                have := List.find?_some hf
                simpa using this
              exact ⟨d, idp, hmem, heq.trans (claimsOf_issuer hc).symm, hv⟩

end L4Factoidal.SAML
