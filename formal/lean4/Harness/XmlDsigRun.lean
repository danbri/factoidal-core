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
  * signature generation (§3.1, `L4Factoidal.XML.DSig11Sign`): the keys
    of `tests/xmldsig/signing-keys.tsv` sign a document in each case of
    `signCases` through the signers of `XML/DSig11Native.lean`; each result
    must pass core validation with the key from its `ds:KeyInfo`, and must
    be refused after one character of the signed content changes. With
    `--sign-out DIR` the signed documents go to DIR, for
    `tests/xmldsig/verify_lean_signed.py` (signxml, an independent
    verifier).
  * the SAML 2.0 fixtures of `L4Factoidal.SAML.Fixtures`, verified by the
    profile verifier `XML.DSig.verifyEnveloped` and by `DSig11.validate`
    with the identity provider's key: the two verdicts are compared with
    the table `samlExpected`.

Expected failures name an open issue. The run fails when one passes
(STALE) or fails for a reason that does not name its issue.

Usage: `lake exe l4xmldsig [repo-root] [--sign-out DIR]`. Exit 0 when nothing fails.
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

/-- The document the generation cases sign (the signxml fixtures' document). -/
def signDoc : String :=
  "<doc xmlns=\"urn:example:doc\" xmlns:x=\"urn:example:x\" ID=\"d1\"><x:item n=\"1\">one</x:item>" ++
  "<!--c--><item n=\"2\">two &amp; &lt;three&gt;</item></doc>"

inductive KeyKind where | rsa | p256 | hmac

/-- The generation cases: name, key, signature method, request. -/
def signCases : List (String × KeyKind × DigestAlg × SignSpec) :=
  let env (m : C14n.Method) (h : DigestAlg := .sha256) : SignSpec :=
    { c14n := m, refs := [{ uri := "", transforms := [.enveloped, .c14n m], digest := h }] }
  let exc : C14n.Method := { version := .exc10 }
  [("rsa-sha256-exc", .rsa, .sha256, env exc),
   ("rsa-sha1-exc", .rsa, .sha1, env exc),
   ("rsa-sha224-exc", .rsa, .sha224, env exc),
   ("rsa-sha384-exc", .rsa, .sha384, env exc .sha384),
   ("rsa-sha512-exc", .rsa, .sha512, env exc .sha512),
   ("rsa-sha256-c14n10", .rsa, .sha256, env { version := .c14n10 }),
   ("rsa-sha256-c14n10c", .rsa, .sha256, env { version := .c14n10, comments := true }),
   ("rsa-sha256-c14n11", .rsa, .sha256, env { version := .c14n11 }),
   ("rsa-sha256-exc-prefixlist", .rsa, .sha256, env { version := .exc10, inclusivePrefixes := ["x"] }),
   ("rsa-sha256-id", .rsa, .sha256,
      { refs := [{ uri := "#d1", transforms := [.enveloped, .c14n exc] }] }),
   ("rsa-sha256-enveloping", .rsa, .sha256,
      { refs := [{ uri := "#obj", transforms := [.c14n exc] }],
        placement := .enveloping "obj" "<x:item xmlns:x=\"urn:example:x\" n=\"1\">one</x:item>" }),
   ("p256-sha256-exc", .p256, .sha256, env exc),
   ("p256-sha256-c14n11", .p256, .sha256, env { version := .c14n11 }),
   ("hmac-sha256-exc", .hmac, .sha256, env exc),
   ("hmac-sha512-exc", .hmac, .sha512, env exc .sha512)]

def keyHex (rows : List (String × String)) (k : String) : ByteArray :=
  hexBytes ((rows.find? (·.1 == k)).map (·.2) |>.getD "")

/-- One character of the signed content changed. -/
def tamper (s : String) : String := s.replace ">one<" ">One<"

def runSign (t0 : Tally) (keysFile : String) (outDir : Option String) : IO Tally := do
  let rows := ((← IO.FS.readFile keysFile).splitOn "\n").filterMap fun l =>
    if l.startsWith "#" then none else match l.splitOn "\t" with
      | [a, b] => some (a, b.trimAscii.toString)
      | _ => none
  let n := keyHex rows "rsa2048-n"
  let e := keyHex rows "rsa2048-e"
  let d := keyHex rows "rsa2048-d"
  let sk := keyHex rows "p256-secret"
  let mk := keyHex rows "hmac"
  if let some o := outDir then IO.FS.createDirAll o
  let mut t := t0
  let mut manifest := ""
  for (name, kind, h, spec) in signCases do
    let sg? := match kind with
      | .rsa => rsaSigner h n e d
      | .p256 => p256Signer sk
      | .hmac => some (hmacSigner h mk)
    let some sg := sg? | IO.println s!"FAIL sign {name}: the signer refused the key"; t := { t with fail := t.fail + 1 }; continue
    let rand ← IO.getRandomBytes 32
    match sign nativeBackend sg spec rand signDoc with
    | .error err => IO.println s!"FAIL sign {name}: {err}"; t := { t with fail := t.fail + 1 }
    | .ok out =>
        let cfg : Config := { hmacKey := some mk }
        let ok := (validateText nativeBackend cfg out).isOk
        let tampered := (tamper out != out) && !(validateText nativeBackend cfg (tamper out)).isOk
        if ok && tampered then
          IO.println s!"PASS sign {name}: validates with its ds:KeyInfo key; refused after a change"
          t := { t with pass := t.pass + 1 }
          if let some o := outDir then
            IO.FS.writeFile s!"{o}/{name}.xml" out
            manifest := manifest ++ s!"{name}.xml\t{match kind with | .hmac => "hmac" | _ => "keyvalue"}\n"
        else
          IO.println s!"FAIL sign {name}: validates {ok}, tampered copy refused {tampered}"
          t := { t with fail := t.fail + 1 }
  if let some o := outDir then IO.FS.writeFile s!"{o}/manifest.tsv" manifest
  return t

def main (args0 : List String) : IO UInt32 := do
  let (args, outDir) := match args0.dropWhile (· != "--sign-out") with
    | _ :: o :: _ => (args0.takeWhile (· != "--sign-out"), some o)
    | _ => (args0, none)
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
  let w ← runSign {} s!"{root}/tests/xmldsig/signing-keys.tsv" outDir
  IO.println s!"signature generation: {w.pass} pass, {w.fail} fail (out of {w.pass + w.fail})"
  return (if t.fail + u.fail + v.fail + w.fail == 0 then 0 else 1)
