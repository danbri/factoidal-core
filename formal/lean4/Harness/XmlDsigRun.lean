/-
Harness/XmlDsigRun — core validation (XML Signature 1.1 §3.2) by
`L4Factoidal.XML.DSig11` with the HACL* backend, over three groups:

  * `third_party/testing/xmldsig11-interop/oracle/`: the 45 signatures of
    the XML Signature 1.1 Interop Test Report (W3C Note, 2012), provenance
    in its PROVENANCE.md. `hmac-sha1-truncated40` must be refused (report
    §6.2); every other one must validate. The HMAC key is "testkey".
  * `tests/xmldsig/fixtures/`: signatures made by signxml (an independent
    implementation) with RSA-2048, P-256 and HMAC keys, and negative cases
    made from them (`tests/xmldsig/make_fixtures.py`; `manifest.tsv` gives
    the expected outcome and the HMAC key).
  * the SAML 2.0 fixtures of `L4Factoidal.SAML.Fixtures`, verified by the
    profile verifier `XML.DSig.verifyEnveloped` and by `DSig11.validate`
    with the identity provider's key: the two verdicts are compared with
    the table `samlExpected`.

Expected failures name an open issue. The run fails when one passes
(STALE) or fails for a reason that does not name its issue.

Usage: `lake exe l4xmldsig [repo-root]`. Exit 0 when nothing fails.
-/
import L4Factoidal.XML.DSig11Native
import L4Factoidal.SAML.Assertion
import L4Factoidal.SAML.Fixtures
import L4Factoidal.JOSE.Pkcs1

open L4Factoidal.XML
open L4Factoidal.XML.DSig11

def issueUrl (n : Nat) : String := s!"https://github.com/danbri/factoidal/issues/{n}"

/-- The interop vectors that fail today, each with the issue whose URL the
error must name. -/
def oracleXfail : List (String × Nat) :=
  let rsa1024 := ["derencoded-rsa", "keyinforeference-rsa", "rsa-sha224", "rsa-sha256", "rsa_sha384",
    "rsa_sha512", "sha224-rsa_sha256", "sha256-rsa-sha256", "sha384-rsa_sha256", "sha512-rsa_sha256"]
  let ec := ["p256_sha1", "p256_sha1_4050", "p256_sha224", "p256_sha384", "p256_sha384_4050",
    "p256_sha512", "p256_sha512_4050",
    "p384_sha1", "p384_sha1_4050", "p384_sha224", "p384_sha256", "p384_sha256_4050", "p384_sha384",
    "p384_sha384_4050", "p384_sha512", "p384_sha512_4050",
    "p521_sha1", "p521_sha1_4050", "p521_sha224", "p521_sha256", "p521_sha256_4050", "p521_sha384",
    "p521_sha384_4050", "p521_sha512", "p521_sha512_4050"]
  (rsa1024.map fun n => (s!"signature-enveloping-{n}.xml", 1227)) ++
  (ec.map fun n => (s!"signature-enveloping-{n}.xml", 1223)) ++
  [("signature-enveloping-x509digest-rsa.xml", 1226)]

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  xfail : Nat := 0

def outcome (r : Except String Validated) : Except String Unit := r.map fun _ => ()

/-- Record one case: `wantValid` the expected verdict, `xf` an expected
failure's issue. -/
def record (t : Tally) (name : String) (wantValid : Bool) (xf : Option Nat)
    (r : Except String Unit) : IO Tally := do
  match xf, r with
  | some n, .ok () =>
      IO.println s!"FAIL {name}: STALE expected failure (it validates now; remove it and close {issueUrl n})"
      return { t with fail := t.fail + 1 }
  | some n, .error e =>
      if (e.splitOn (issueUrl n)).length > 1 then
        IO.println s!"XFAIL {name}: {e}"; return { t with xfail := t.xfail + 1 }
      else
        IO.println s!"FAIL {name}: expected failure for {issueUrl n}, but: {e}"
        return { t with fail := t.fail + 1 }
  | none, .ok () =>
      if wantValid then IO.println s!"PASS {name}"; return { t with pass := t.pass + 1 }
      else IO.println s!"FAIL {name}: validates, but must be refused"; return { t with fail := t.fail + 1 }
  | none, .error e =>
      if wantValid then IO.println s!"FAIL {name}: {e}"; return { t with fail := t.fail + 1 }
      else IO.println s!"PASS {name} (refused: {e})"; return { t with pass := t.pass + 1 }

def runOracle (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  -- the cases, in the order of the vendored checksum list
  let sums ← IO.FS.readFile s!"{dir}/../SHA256SUMS"
  let names := (sums.splitOn "\n").filterMap (fun l => (l.splitOn "  ")[1]?) |>.filter (·.endsWith ".xml")
  for n in names do
    let src ← IO.FS.readFile s!"{dir}/{n}"
    let cfg : Config := { hmacKey := some "testkey".toUTF8 }
    let want := n != "signature-enveloping-hmac-sha1-truncated40.xml"
    t ← record t s!"xmldsig11-interop {n}" want ((oracleXfail.find? (·.1 == n)).map (·.2))
      (outcome (validateText nativeBackend cfg src))
  return t

def runFixtures (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  for line in (← IO.FS.readFile s!"{dir}/manifest.tsv").splitOn "\n" do
    match line.splitOn "\t" with
    | [file, want, key, _] =>
        let src ← IO.FS.readFile s!"{dir}/{file}"
        let cfg : Config := { hmacKey := if key == "-" then none else some key.toUTF8 }
        t ← record t s!"fixture {file}" (want == "valid") none (outcome (validateText nativeBackend cfg src))
    | _ => pure ()
  return t

def hexBytes (s : String) : ByteArray := Id.run do
  let v (c : Char) : Nat :=
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
    else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0
  let cs := s.toList.toArray
  let mut out : ByteArray := .empty
  for i in [0:cs.size / 2] do
    out := out.push (UInt8.ofNat (v cs[2*i]! * 16 + v cs[2*i+1]!))
  return out

/-- The SAML fixtures, and whether the profile verifier and core
validation accept each. The profile is narrower: it refuses comments and
a signature that does not reference the document element. Core validation
accepts `wrapChild` (the signed assertion, `#_a7`, is inside an unsigned
one): the signature is valid, and the caller reads `Validated.references`
to see that the document element is not what was signed. Both refuse
`wrapObject`, where two elements carry the ID `_a8`. -/
def samlExpected : List (String × String × Bool × Bool) :=
  open L4Factoidal.SAML.Fixtures in
  [("valid", valid, true, true), ("altered", altered, false, false), ("unsigned", unsigned, false, false),
   ("attackerKey", attackerKey, false, false), ("comment", comment, false, true),
   ("inclusive", inclusive, true, true), ("wrapChild", wrapChild, false, true),
   ("wrapObject", wrapObject, false, false)]

def runSaml (t0 : Tally) : IO Tally := do
  let mut t := t0
  let n := hexBytes L4Factoidal.SAML.Fixtures.idpN
  let e := hexBytes L4Factoidal.SAML.Fixtures.idpE
  let rsa : DSig.RsaVerify := fun n e s m => L4Factoidal.JOSE.Pkcs1.rs256Verify L4Factoidal.Crypto.Rsa.rsaPublicOp n e s m
  for (name, tok, wantProfile, wantCore) in samlExpected do
    match L4Factoidal.SAML.decodeToken tok with
    | .error err =>
        IO.println s!"FAIL saml {name}: the token does not decode: {err}"; t := { t with fail := t.fail + 1 }
    | .ok d =>
        let prof := (DSig.verifyEnveloped rsa n e d).isOk
        let cd := C14n.C14nDoc.ofDoc (L4Factoidal.XPath4.Doc.ofDocument d)
        let cfg : Config := { key := some (.rsa n e) }
        let core := match signatures cd with
          | [s] => (validate nativeBackend cfg cd s).isOk
          | _ => false
        if prof == wantProfile && core == wantCore then
          IO.println s!"PASS saml {name}: profile {prof}, core validation {core}"
          t := { t with pass := t.pass + 1 }
        else
          IO.println s!"FAIL saml {name}: profile {prof} (want {wantProfile}), core validation {core} (want {wantCore})"
          t := { t with fail := t.fail + 1 }
  return t

def main (args : List String) : IO UInt32 := do
  let root := args.head? |>.getD "../.."
  let odir := s!"{root}/third_party/testing/xmldsig11-interop/oracle"
  let fdir := s!"{root}/tests/xmldsig/fixtures"
  if !(← System.FilePath.pathExists odir) || !(← System.FilePath.pathExists fdir) then
    IO.println s!"xmldsig runner: suite not found under {root}"
    return 1
  let t ← runOracle {} odir
  IO.println s!"xmldsig11-interop: {t.pass} pass, {t.fail} fail, {t.xfail} expected failures (out of {t.pass + t.fail + t.xfail})"
  let u ← runFixtures {} fdir
  IO.println s!"fixtures: {u.pass} pass, {u.fail} fail (out of {u.pass + u.fail})"
  let v ← runSaml {}
  IO.println s!"saml differential: {v.pass} pass, {v.fail} fail (out of {v.pass + v.fail})"
  return (if t.fail + u.fail + v.fail == 0 then 0 else 1)
