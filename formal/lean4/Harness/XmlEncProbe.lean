/-
Harness/XmlEncProbe — XML Encryption 1.1 (`L4Factoidal/XML/Enc.lean`) and
SAML encrypted assertions (`SAML.validateWith`) with the REAL primitives:
HACL* RSA-OAEP, P-256 and X25519, and HACL* Vale AES-GCM (`nativeCipher`),
against the Apache Santuario fixtures of `tests/xmlenc/fixtures.json`
(`tests/xmlenc/MakeFixtures.java`). https://github.com/danbri/factoidal/issues/1084,
https://github.com/danbri/factoidal/issues/1073.

A HARNESS, not part of the verified library: it reads a file, calls the
externs (which a `#guard` cannot), and prints. The decisions it exercises
are the ones `#guard`s check over stubs (`XML/EncTests.lean`,
`SAML/Tests.lean`).

The native cipher has AES-GCM only: AES Key Wrap and AES-CBC are host
(WebCrypto) operations (design record
`docs/designissues/2026-10-27-xml-encryption-and-jwe.md`;
https://github.com/danbri/factoidal/issues/677). The fixtures that need
them are counted HOST-ONLY here and run in `tests/xmlenc/wasm.mjs`; each of
them must fail here, so a native cipher that starts to answer them is seen.

Run from `formal/lean4` or the repository root:
  lake exe l4xmlenc-probe [path/to/fixtures.json]
Exit 0 when nothing fails; 1 otherwise.
-/
import Wasm.Ops.XmlEnc
import L4Factoidal.SAML.Assertion
import L4Factoidal.Authz.Keys
import L4Factoidal.VC.Multibase

namespace XmlEncProbe

open L4Factoidal.JSON
open L4Factoidal.XML
open L4Factoidal.XML.Enc
open L4Factoidal.Crypto.CipherCall
open L4Factoidal.XML.Canonical (canonDocument)

structure Score where
  pass : Nat := 0
  fail : Nat := 0
  hostOnly : Nat := 0
  failures : List String := []

def Score.ok (s : Score) (b : Bool) (name : String) : Score :=
  if b then { s with pass := s.pass + 1 } else { s with fail := s.fail + 1, failures := s.failures ++ [name] }

def canonOf (x : String) : Option String :=
  match parseXML x with
  | .ok d => some (canonDocument d)
  | .error _ => none

def native : List (Req × Ans) → Cipher := fun _ => nativeCipher

def run (f : (List (Req × Ans) → Cipher) → Prims → String → String) (arg : Json) : Json :=
  match parseJson (f native nativePrims arg.toString) with
  | .ok j => j
  | .error _ => .object [("ok", .bool false), ("error", .string "unparseable envelope")]

def isOk (j : Json) : Bool := j.field? "ok" == some (.bool true) && (j.getString? "document").isSome

def errorHas (j : Json) (frag : String) : Bool :=
  match j.getString? "error" with
  | some e => (e.splitOn frag).length ≥ 2
  | none => false

def sameDoc (j : Json) (expected : String) : Bool :=
  match j.getString? "document" with
  | some d => (canonOf d).isSome && canonOf d == canonOf expected
  | none => false

/-- The content CipherValue's first character changed. -/
def tamper (doc : String) : String :=
  let parts := doc.splitOn "<xenc:CipherValue>"
  match parts.getLast? with
  | some last =>
      let c := last.front
      "<xenc:CipherValue>".intercalate (parts.dropLast ++ [String.singleton (if c == 'A' then 'B' else 'A') ++ (last.drop 1).toString])
  | none => doc

def publicJwk (k : Json) : Json :=
  match k with
  | .object fs => .object (fs.filter (·.1 != "d"))
  | j => j

def keysOfFixture (keys : Json) : Keys :=
  match keys with
  | .array _ => (L4Wasm.Ops.XmlEnc.keysOf (.object [("keys", keys)])).toOption.getD {}
  | _ => {}

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | [p] => pure (System.FilePath.mk p)
    | _ =>
        let a : System.FilePath := "tests/xmlenc/fixtures.json"
        let b : System.FilePath := "../../tests/xmlenc/fixtures.json"
        pure (if ← a.pathExists then a else b)
  let text ← IO.FS.readFile path
  let fx ← match parseJson text with
    | .ok j => pure j
    | .error _ => throw (IO.userError s!"{path} is not JSON")
  let keys := (fx.field? "keys").getD (.array [])
  let mut s : Score := {}
  -- Santuario's EncryptedData, decrypted.
  for c in ((fx.field? "cases").bind Json.asArray?).getD [] do
    let name := (c.getString? "name").getD "?"
    let doc := (c.getString? "document").getD ""
    let expected := (c.getString? "expected").getD ""
    let nat := c.field? "native" == some (.bool true)
    let outcome := (c.getString? "outcome").getD ""
    let r := run L4Wasm.Ops.XmlEnc.decryptWith (.object [("document", .string doc), ("keys", keys)])
    if outcome == "refused" then
      s := s.ok (errorHas r "rsa-1_5") s!"{name}: refused"
    else if outcome == "needsAllowCbc" then
      s := s.ok (errorHas r "allowCbc") s!"{name}: CBC refused without allowCbc"
      let r2 := run L4Wasm.Ops.XmlEnc.decryptWith
        (.object [("document", .string doc), ("keys", keys), ("allowCbc", .bool true)])
      if isOk r2 then s := s.ok false s!"{name}: CBC answered natively" else s := { s with hostOnly := s.hostOnly + 1 }
    else if nat then
      s := s.ok (sameDoc r expected) s!"{name}: decrypt"
      if name == "gcm128-oaep-mgf1p" then
        let t := run L4Wasm.Ops.XmlEnc.decryptWith (.object [("document", .string (tamper doc)), ("keys", keys)])
        s := s.ok (r.getString? "error" == none && t.getString? "error" == some decryptionError)
          s!"{name}: an altered ciphertext gives the one error"
    else
      if isOk r then s := s.ok false s!"{name}: a host-only case was answered natively"
      else s := { s with hostOnly := s.hostOnly + 1 }
  -- Lean's encryption, decrypted by Lean, with HACL* and Vale.
  let rsaJwk := match keys with
    | .array (k :: _) => publicJwk k
    | _ => .null
  for (alg, kt) in [("aes128-gcm", "rsa-oaep-mgf1p"), ("aes256-gcm", "rsa-oaep-sha256")] do
    let rnd ← IO.getRandomBytes 96
    let e := run L4Wasm.Ops.XmlEnc.encryptWith (.object
      [("document", .string "<a xmlns=\"urn:x\"><b>secret é</b></a>"), ("recipient", rsaJwk),
       ("algorithm", .string alg), ("keyTransport", .string kt), ("random", .string (base64 rnd))])
    let d := run L4Wasm.Ops.XmlEnc.decryptWith (.object [("document", (e.field? "document").getD .null), ("keys", keys)])
    let hidden := (((e.getString? "document").getD "secret").splitOn "secret").length == 1
    s := s.ok (isOk e && hidden && sameDoc d "<a xmlns=\"urn:x\"><b>secret é</b></a>") s!"encrypt {alg} {kt}: round trip"
  -- The W3C XML Encryption 1.1 test cases (tests/xmlenc/w3c/PROVENANCE.md).
  let w3cDir := (path.parent.getD ".") / "w3c"
  let w3cText ← IO.FS.readFile (w3cDir / "cases.json")
  let w3cKeysText ← IO.FS.readFile (w3cDir / "keys.json")
  match parseJson w3cText, parseJson w3cKeysText with
  | .ok w3c, .ok w3cKeys =>
      for c in ((w3c.field? "cases").bind Json.asArray?).getD [] do
        let id := (c.getString? "id").getD "?"
        let doc ← IO.FS.readFile (w3cDir / ((c.getString? "file").getD "missing"))
        let r := run L4Wasm.Ops.XmlEnc.decryptWith (.object [("document", .string doc), ("keys", w3cKeys)])
        match c.getString? "outcome" with
        | some "ok" =>
            if c.field? "native" == some (.bool true) then
              let expected ← IO.FS.readFile (w3cDir / ((c.getString? "expected").getD "missing"))
              s := s.ok (sameDoc r expected) s!"W3C {id}: decrypt"
            else if isOk r then s := s.ok false s!"W3C {id}: a host-only case was answered natively"
            else s := { s with hostOnly := s.hostOnly + 1 }
        | _ =>
            let why := (c.getString? "reason").getD "?"
            s := s.ok (errorHas r why && r.getString? "error" != some decryptionError)
              s!"W3C {id}: refused ({why}); got {(r.getString? "error").getD "ok"}"
  | _, _ => s := s.ok false "W3C cases: cases.json or keys.json is not JSON"
  -- SAML.
  let saml := (fx.field? "saml").getD .null
  let hex (k : String) := (L4Factoidal.VC.Multibase.byteArrayOfHex? ((saml.getString? k).getD "")).getD ByteArray.empty
  let now := match saml.field? "now" with
    | some (.number n) => n.toNat?.getD 0
    | _ => 0
  let policy : L4Factoidal.SAML.Policy :=
    { idps := [{ entityId := "https://idp.example", n := hex "idpN", e := hex "idpE" }],
      audience := "https://as.example", now, decryptKeys := keysOfFixture keys }
  let rs256 := L4Factoidal.Authz.hacl.verifiers.rs256
  let validate (p : L4Factoidal.SAML.Policy) (k : String) :=
    L4Factoidal.SAML.validateWith nativeCipher nativePrims rs256 p ((saml.getString? k).getD "")
  let sub (r : Except L4Factoidal.SAML.Outcome L4Factoidal.SAML.Claims) : String :=
    match r with
    | .ok c => c.nameId
    | .error o => "refused: " ++ o.message
  let r1 := sub (validate policy "encryptedAssertion")
  s := s.ok (r1 == "https://id.example/end-user") s!"saml encryptedAssertion: {r1}"
  let r2 := sub (validate policy "encryptedId")
  s := s.ok (r2 == "https://id.example/hidden-user") s!"saml encryptedId: {r2}"
  let r3 := sub (validate policy "unsignedInside")
  s := s.ok ((r3.splitOn "exactly one ds:Signature").length == 2) s!"saml unsignedInside: {r3}"
  let r4 := sub (validate { policy with decryptKeys := {} } "encryptedAssertion")
  s := s.ok ((r4.splitOn L4Factoidal.SAML.encryptionIssue).length == 2) s!"saml without a key: {r4}"
  let r5 := sub (validate { policy with decryptKeys := {} } "encryptedId")
  s := s.ok ((r5.splitOn L4Factoidal.SAML.encryptionIssue).length == 2) s!"saml EncryptedID without a key: {r5}"
  for f in s.failures do IO.println s!"FAIL {f}"
  IO.println s!"xmlenc-native: {s.pass} pass, {s.fail} fail, {s.hostOnly} host-only (out of {s.pass + s.fail + s.hostOnly})"
  return (if s.fail == 0 then 0 else 1)

end XmlEncProbe

def main (args : List String) : IO UInt32 := XmlEncProbe.main args
