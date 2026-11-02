/-
Harness/XmlDsigRun — core validation (XML Signature 1.1 §3.2) by
`L4Factoidal.XML.DSig11` with the HACL* backend, over three groups:

  * `third_party/testing/xmldsig11-interop/oracle/`: the 45 signatures of
    the XML Signature 1.1 Interop Test Report (W3C Note, 2012), provenance
    in its PROVENANCE.md. `hmac-sha1-truncated40` must be refused (report
    §6.2); every other one must validate. The HMAC key is "testkey".
  * `third_party/testing/xmldsig-filter2-interop/`: Merlin Hughes's XPath
    Filter 2.0 vectors (2002). Reference validation: the octets of each
    reference equal the published canonical output and the digests match.
    The signatures are DSA, so core validation is an expected failure
    (https://github.com/danbri/factoidal/issues/1224).
  * `third_party/testing/xmldsig-merlin-2001/`: Merlin Hughes's
    `merlin-xmldsig-twenty-three` (the XML Signature interop vectors of
    2001-2002). Reference validation of every `ds:Reference` (those of
    `ds:Manifest` included; one has the XSLT transform of §6.6.5), then
    core validation; DSA signatures are expected failures
    (https://github.com/danbri/factoidal/issues/1224). The HMAC key is
    "secret". External references resolve to the vendored
    `xml-stylesheet.b64` and its decoded octets, never to the network.
  * the `ds:X509Data` of the six X.509 vectors of the 2001 set: the
    certificate selected (§4.5.4) must be the one whose serial number
    `openssl x509 -serial` gives (`merlinX509`); its DSA key is refused.
  * `tests/xmldsig/x509/`: `ds:X509Data` fixtures made by signxml and
    pyca/cryptography (`tests/xmldsig/make_x509_fixtures.py`; the caller's
    certificates are named in `manifest.tsv`).
  * `tests/xmldsig/retrieval/`: `ds:RetrievalMethod` fixtures (§4.5.3),
    the signxml X.509 fixtures with their unsigned `ds:KeyInfo` rewritten
    (`tests/xmldsig/make_retrieval_fixtures.py`); refusals must contain
    the text that `manifest.tsv` gives.
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
  * Wycheproof `ecdsa_secp256r1_sha256_p1363_test.json` and
    `ecdsa_secp256r1_sha512_p1363_test.json`
    (`third_party/testing/wycheproof`), through `nativeBackend.ecdsaVerify`
    at P-256 with SHA-256 and SHA-512: the path that `ecdsa-sha256` and
    `ecdsa-sha512` signatures take. `valid` must verify, `invalid` must be
    refused; `acceptable` is counted apart.
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
import L4Factoidal.JSON.Parser

open L4Factoidal.XML
open L4Factoidal.XML.DSig11

def issueUrl (n : Nat) : String := s!"https://github.com/danbri/factoidal/issues/{n}"

/-- The interop vectors that fail today, each with the issue whose URL the
error must name. -/
def oracleXfail : List (String × Nat) :=
  let rsa1024 := ["derencoded-rsa", "keyinforeference-rsa", "rsa-sha224", "rsa-sha256", "rsa_sha384",
    "rsa_sha512", "sha224-rsa_sha256", "sha256-rsa-sha256", "sha384-rsa_sha256", "sha512-rsa_sha256"]
  let ec := ["p384_sha1", "p384_sha1_4050", "p384_sha224", "p384_sha256", "p384_sha256_4050", "p384_sha384",
    "p384_sha384_4050", "p384_sha512", "p384_sha512_4050",
    "p521_sha1", "p521_sha1_4050", "p521_sha224", "p521_sha256", "p521_sha256_4050", "p521_sha384",
    "p521_sha384_4050", "p521_sha512", "p521_sha512_4050"]
  (rsa1024.map fun n => (s!"signature-enveloping-{n}.xml", 1227)) ++
  (ec.map fun n => (s!"signature-enveloping-{n}.xml", 1223)) ++
  [("signature-enveloping-x509digest-rsa.xml", 1229)]

/-- Expected failures whose error cannot name the issue, because the
missing piece is data, not code: the text the error must contain. -/
def xfailNeedle : Nat → Option String
  | 1229 => some "of ds:X509Data or of the caller matches every identifier"
  | _ => none

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
      if (e.splitOn (issueUrl n)).length > 1 ||
          (xfailNeedle n).any (fun k => (e.splitOn k).length > 1) then
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

/-- The XPath Filter 2.0 vectors (`merlin-xpath-filter2-three`): the
file, and the number of references. `sign-F-c14n-N.txt` is the octets of
reference N; for `sign-spec` the next N is the canonical `ds:SignedInfo`. -/
def filter2Cases : List (String × Nat × Bool) :=
  [("sign-spec", 2, true), ("sign-xfdl", 1, false)]

/-- Reference validation (§3.2.1) of the XPath Filter 2.0 vectors: each
reference's octets must equal the published canonical output and its
digest must match; the canonical `ds:SignedInfo` likewise. Core validation
of the whole signature is an expected failure (DSA,
https://github.com/danbri/factoidal/issues/1224). -/
def runFilter2 (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  for (f, nrefs, hasSi) in filter2Cases do
    let src ← IO.FS.readFile s!"{dir}/{f}.xml"
    let r : Except String (C14n.C14nDoc × Signature) := do
      let cd ← C14n.C14nDoc.ofString? src
      let some s := (signatures cd).head? | throw "no ds:Signature"
      let sg ← parseSignature cd.doc s
      pure (cd, sg)
    match r with
    | .error e => IO.println s!"FAIL filter2 {f}: {e}"; t := { t with fail := t.fail + 1 }
    | .ok (cd, sg) =>
      for (ref, k) in sg.si.refs.zipIdx do
        if k ≥ nrefs then continue
        let want ← IO.FS.readBinFile s!"{dir}/{f}-c14n-{k}.txt"
        match referenceOctets {} cd sg.node ref with
        | .error e => IO.println s!"FAIL filter2 {f} reference {k}: {e}"; t := { t with fail := t.fail + 1 }
        | .ok o =>
            let dOk := ref.digest.digest o == ref.value
            if o == want && dOk then
              IO.println s!"PASS filter2 {f} reference {k}: {o.size} octets equal {f}-c14n-{k}.txt, digest matches"
              t := { t with pass := t.pass + 1 }
            else
              IO.println s!"FAIL filter2 {f} reference {k}: octets equal {o == want} ({o.size} vs {want.size}), digest matches {dOk}"
              t := { t with fail := t.fail + 1 }
      if hasSi then
        let want ← IO.FS.readBinFile s!"{dir}/{f}-c14n-{nrefs}.txt"
        match signedInfoOctets cd sg with
        | .ok o =>
            if o.toUTF8 == want then
              IO.println s!"PASS filter2 {f} SignedInfo: equals {f}-c14n-{nrefs}.txt"; t := { t with pass := t.pass + 1 }
            else IO.println s!"FAIL filter2 {f} SignedInfo: differs from {f}-c14n-{nrefs}.txt"; t := { t with fail := t.fail + 1 }
        | .error e => IO.println s!"FAIL filter2 {f} SignedInfo: {e}"; t := { t with fail := t.fail + 1 }
      t ← record t s!"filter2 {f} core validation" true (some 1224) (outcome (validateParsed nativeBackend {} cd sg))
  return t

/-- The 2001 interop vectors (`merlin-xmldsig-twenty-three`) whose core
validation fails today, each with the issue whose URL the error must name.
Every other one must validate, except `signature-enveloping-hmac-sha1-40`,
which XML Signature 1.1 §6.3.1 refuses (40 bits is below 80). -/
def merlinXfail : List (String × Nat) :=
  ["signature-enveloped-dsa.xml", "signature-enveloping-b64-dsa.xml", "signature-enveloping-dsa.xml",
   "signature-external-b64-dsa.xml", "signature-external-dsa.xml", "signature-keyname.xml",
   "signature-retrievalmethod-rawx509crt.xml", "signature-x509-crt-crl.xml", "signature-x509-crt.xml",
   "signature-x509-is.xml", "signature-x509-ski.xml", "signature-x509-sn.xml", "signature.xml"].map (·, 1224) ++
  [("signature-enveloping-rsa.xml", 1227)]

/-- The two external resources of the 2001 vectors, from the vendored
`xml-stylesheet.b64`: the file itself, and its decoded octets, which are
the 1999 text of `http://www.w3.org/TR/xml-stylesheet` that the vectors
signed (SHA-1 `60NvZvtdTB+7UnlLp/H24p7h4bs=`). -/
def merlinResolve (b64 : ByteArray) : String → Option ByteArray := fun u =>
  if u == "http://www.w3.org/Signature/2002/04/xml-stylesheet.b64" then some b64
  else if u == "http://www.w3.org/TR/xml-stylesheet" then (String.fromUTF8? b64).bind b64?
  else none

/-- The 2001 interop vectors: reference validation (§3.2.1) of every
`ds:Reference` of each file, those of `ds:Manifest` included (the XSLT
transform of §6.6.5 is one of them), then core validation of the
signature. The HMAC key is "secret" (`Readme.txt`). -/
def runMerlin (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  let b64 ← IO.FS.readBinFile s!"{dir}/xml-stylesheet.b64"
  let cfg : Config := { hmacKey := some "secret".toUTF8, resolve := merlinResolve b64 }
  let sums ← IO.FS.readFile s!"{dir}/SHA256SUMS"
  let names := (sums.splitOn "\n").filterMap (fun l => (l.splitOn "  ")[1]?)
    |>.filter (fun n => n.endsWith ".xml")
  for path in names do
    let f := (path.splitOn "/").getLast!
    let src ← IO.FS.readFile s!"{dir}/{path}"
    let r : Except String (C14n.C14nDoc × Signature) := do
      let cd ← C14n.C14nDoc.ofString? src
      let some s := (signatures cd).head? | throw "no ds:Signature"
      let sg ← parseSignature cd.doc s
      pure (cd, sg)
    match r with
    | .error e => IO.println s!"FAIL merlin-2001 {f}: {e}"; t := { t with fail := t.fail + 1 }
    | .ok (cd, sg) =>
      let refs := (List.range cd.n0).filter fun i => isEl cd.doc i dsNs "Reference"
      for (i, k) in refs.zipIdx do
        let name := s!"merlin-2001 {f} reference {k}"
        match parseReference cd.doc i with
        | .error e => IO.println s!"FAIL {name}: {e}"; t := { t with fail := t.fail + 1 }
        | .ok ref =>
          match referenceOctets cfg cd sg.node ref with
          | .error e => IO.println s!"FAIL {name} ({ref.uri.getD ""}): {e}"; t := { t with fail := t.fail + 1 }
          | .ok o =>
            if ref.digest.digest o == ref.value then
              IO.println s!"PASS {name} ({ref.uri.getD ""}): digest matches"; t := { t with pass := t.pass + 1 }
            else
              IO.println s!"FAIL {name} ({ref.uri.getD ""}): digest does not match ({o.size} octets)"
              t := { t with fail := t.fail + 1 }
      let want := f != "signature-enveloping-hmac-sha1-40.xml"
      t ← record t s!"merlin-2001 {f} core validation" want ((merlinXfail.find? (·.1 == f)).map (·.2))
        (outcome (validateParsed nativeBackend cfg cd sg))
  return t

/-- The key selection of `ds:X509Data` (§4.5.4) in the 2001 vectors:
the file, and the serial number (hexadecimal, from `openssl x509
-serial`) of the certificate it names among its own and those of
`certs/`, through `signingCertificate?`. Two of them reach the
certificate through `ds:RetrievalMethod` (§4.5.3,
https://github.com/danbri/factoidal/issues/1228): `signature.xml` (Type
X509Data, a same-document URI and an XPath transform) and
`signature-retrievalmethod-rawx509crt.xml` (Type rawX509Certificate, the
relative URI `certs/balor.crt`, which the runner resolves to the vendored
file). Each selected key is DSA, so `certKey` must refuse it naming
https://github.com/danbri/factoidal/issues/1224. -/
def merlinX509 : List (String × String) :=
  [("signature-x509-crt.xml", "ECF92151D3"), ("signature-x509-crt-crl.xml", "ECF921DE7F"),
   ("signature-x509-is.xml", "ECF9217BFA"), ("signature-x509-sn.xml", "ECF921674A"),
   ("signature-x509-ski.xml", "ECF92190C7"), ("signature.xml", "ECF8EA0DAC"),
   ("signature-retrievalmethod-rawx509crt.xml", "ECF921AC47")]

def hexOfInt (n : Int) : String :=
  (String.ofList (Nat.toDigits 16 n.toNat)).toUpper

def runMerlinX509 (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  let mut certs : List ByteArray := []
  let mut files : List (String × ByteArray) := []
  for n in ["badb", "balor", "bres", "ca", "lugh", "macha", "morigu", "nemain"] do
    let b ← IO.FS.readBinFile s!"{dir}/certs/{n}.crt"
    certs := certs ++ [b]
    files := files ++ [(s!"certs/{n}.crt", b)]
  let fs := files
  let cfg : Config := { certificates := certs, resolve := fun u => (fs.find? (·.1 == u)).map (·.2) }
  for (f, serial) in merlinX509 do
    let src ← IO.FS.readFile s!"{dir}/{f}"
    let r : Except String L4Factoidal.X509.Cert := do
      let cd ← C14n.C14nDoc.ofString? src
      let some s := (signatures cd).head? | throw "no ds:Signature"
      let sg ← parseSignature cd.doc s
      let some c := signingCertificate? cfg cd sg | throw "no ds:X509Data and no ds:RetrievalMethod that gives a certificate"
      c
    let name := s!"merlin-2001 {f} X509Data selection"
    match r with
    | .error e => IO.println s!"FAIL {name}: {e}"; t := { t with fail := t.fail + 1 }
    | .ok c =>
        if hexOfInt c.serial != serial then
          IO.println s!"FAIL {name}: selected serial {hexOfInt c.serial}, expected {serial}"
          t := { t with fail := t.fail + 1 }
        else
          match certKey c with
          | .error e =>
              if (e.splitOn (issueUrl 1224)).length > 1 then
                IO.println s!"PASS {name}: serial {serial}, DSA key refused"; t := { t with pass := t.pass + 1 }
              else IO.println s!"FAIL {name}: {e}"; t := { t with fail := t.fail + 1 }
          | .ok _ => IO.println s!"FAIL {name}: the key is DSA, but certKey read it"; t := { t with fail := t.fail + 1 }
  return t

/-- The `ds:X509Data` fixtures (`tests/xmldsig/make_x509_fixtures.py`):
`manifest.tsv` gives the expected outcome and the certificates the
caller gives. -/
def runX509Fixtures (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  for line in (← IO.FS.readFile s!"{dir}/manifest.tsv").splitOn "\n" do
    match line.splitOn "\t" with
    | [file, want, given, _] =>
        let src ← IO.FS.readFile s!"{dir}/{file}"
        let mut certs : List ByteArray := []
        if given != "-" then
          for g in given.splitOn "," do
            certs := certs ++ [← IO.FS.readBinFile s!"{dir}/{g}"]
        let cfg : Config := { certificates := certs }
        t ← record t s!"x509 {file}" (want == "valid") none (outcome (validateText nativeBackend cfg src))
    | _ => pure ()
  return t

/-- The `ds:RetrievalMethod` fixtures (§4.5.3,
`tests/xmldsig/make_retrieval_fixtures.py`, made from the signxml
fixtures of `tests/xmldsig/x509/`): `manifest.tsv` gives the expected
outcome and a text that the refusal must contain (`-` for any). The
caller's resolver gives the `.der` files of the directory by their
relative names; nothing else is resolved. -/
def runRetrievalFixtures (t0 : Tally) (dir : String) : IO Tally := do
  let mut t := t0
  let mut files : List (String × ByteArray) := []
  for n in ["leaf-rsa.der", "other.der"] do
    files := files ++ [(n, ← IO.FS.readBinFile s!"{dir}/{n}")]
  let fs := files
  let cfg : Config := { resolve := fun u => (fs.find? (·.1 == u)).map (·.2) }
  for line in (← IO.FS.readFile s!"{dir}/manifest.tsv").splitOn "\n" do
    match line.splitOn "\t" with
    | [file, want, needle, _] =>
        let src ← IO.FS.readFile s!"{dir}/{file}"
        let name := s!"retrieval {file}"
        match want == "valid", outcome (validateText nativeBackend cfg src) with
        | true, .ok () => IO.println s!"PASS {name}: validates"; t := { t with pass := t.pass + 1 }
        | true, .error e => IO.println s!"FAIL {name}: {e}"; t := { t with fail := t.fail + 1 }
        | false, .ok () => IO.println s!"FAIL {name}: validates, but must be refused"; t := { t with fail := t.fail + 1 }
        | false, .error e =>
            if needle == "-" || (e.splitOn needle).length > 1 then
              IO.println s!"PASS {name}: refused: {e}"; t := { t with pass := t.pass + 1 }
            else
              IO.println s!"FAIL {name}: refused, but the message does not contain {repr needle}: {e}"
              t := { t with fail := t.fail + 1 }
    | _ => pure ()
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
   ("p256-sha1-exc", .p256, .sha1, env exc),
   ("p256-sha224-exc", .p256, .sha224, env exc),
   ("p256-sha384-exc", .p256, .sha384, env exc .sha384),
   ("p256-sha512-exc", .p256, .sha512, env exc .sha512),
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
      | .p256 => p256Signer sk h
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


/-! ## Wycheproof ECDSA P-256 through the XML Signature backend -/

def hexBytes? (s : String) : Option ByteArray :=
  if s.length % 2 != 0 || !s.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then none
  else some (hexBytes s)

/-- Left-pad to `n` octets after dropping leading zero octets; `none` when longer. -/
def fixLen (n : Nat) (b : ByteArray) : Option ByteArray :=
  let l := b.data.toList.dropWhile (· == 0)
  if l.length > n then none else some ⟨(List.replicate (n - l.length) (0 : UInt8) ++ l).toArray⟩

structure WyTally where
  pass : Nat := 0
  fail : Nat := 0
  acceptable : Nat := 0

open L4Factoidal.JSON in
def runWycheproof (path : String) (label : String) (h : DigestAlg) : IO WyTally := do
  let some j := parseJson? (← IO.FS.readFile path)
    | IO.println s!"FAIL {label}: cannot read {path}"; return { fail := 1 }
  let mut t : WyTally := {}
  for g in (j.getArray? "testGroups").getD [] do
    let pk := (g.field? "publicKey").getD .null
    let xy? : Option ByteArray := do
      let x ← fixLen 32 (← hexBytes? (← pk.getString? "wx"))
      let y ← fixLen 32 (← hexBytes? (← pk.getString? "wy"))
      pure (x ++ y)
    for tc in (g.getArray? "tests").getD [] do
      let id := match tc.field? "tcId" with | some (.number n) => n | _ => "?"
      let res := (tc.getString? "result").getD ""
      let accepted := match xy?, hexBytes? ((tc.getString? "msg").getD ""),
          hexBytes? ((tc.getString? "sig").getD "") with
        | some xy, some msg, some sig => nativeBackend.ecdsaVerify .p256 h xy msg sig == some true
        | _, _, _ => false
      if res == "acceptable" then t := { t with acceptable := t.acceptable + 1 }
      else if (res == "valid") == accepted then t := { t with pass := t.pass + 1 }
      else
        IO.println s!"FAIL {label} tcId={id}: expected {res}, verifier {if accepted then "accepted" else "refused"}"
        t := { t with fail := t.fail + 1 }
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
  let x2 ← runFilter2 {} s!"{root}/third_party/testing/xmldsig-filter2-interop/merlin-xpath-filter2-three"
  IO.println s!"xmldsig-filter2-interop: {x2.pass} pass, {x2.fail} fail, {x2.xfail} expected failures (out of {x2.pass + x2.fail + x2.xfail})"
  let m ← runMerlin {} s!"{root}/third_party/testing/xmldsig-merlin-2001"
  IO.println s!"xmldsig-merlin-2001: {m.pass} pass, {m.fail} fail, {m.xfail} expected failures (out of {m.pass + m.fail + m.xfail})"
  let mx ← runMerlinX509 {} s!"{root}/third_party/testing/xmldsig-merlin-2001/merlin-xmldsig-twenty-three"
  IO.println s!"xmldsig-merlin-2001 X509Data selection: {mx.pass} pass, {mx.fail} fail (out of {mx.pass + mx.fail})"
  let u ← runFixtures {} fdir
  IO.println s!"fixtures: {u.pass} pass, {u.fail} fail (out of {u.pass + u.fail})"
  let ux ← runX509Fixtures {} s!"{root}/tests/xmldsig/x509"
  IO.println s!"x509 fixtures: {ux.pass} pass, {ux.fail} fail (out of {ux.pass + ux.fail})"
  let ur ← runRetrievalFixtures {} s!"{root}/tests/xmldsig/retrieval"
  IO.println s!"retrieval fixtures: {ur.pass} pass, {ur.fail} fail (out of {ur.pass + ur.fail})"
  let v ← runSaml {}
  IO.println s!"saml differential: {v.pass} pass, {v.fail} fail (out of {v.pass + v.fail})"
  let w ← runSign {} s!"{root}/tests/xmldsig/signing-keys.tsv" outDir
  IO.println s!"signature generation: {w.pass} pass, {w.fail} fail (out of {w.pass + w.fail})"
  let wp := s!"{root}/third_party/testing/wycheproof/testvectors_v1"
  let mut wf := 0
  for (file, label, h) in [("ecdsa_secp256r1_sha256_p1363_test.json", "wycheproof-ecdsa-p256-sha256", DigestAlg.sha256),
                           ("ecdsa_secp256r1_sha512_p1363_test.json", "wycheproof-ecdsa-p256-sha512", .sha512)] do
    let x ← runWycheproof s!"{wp}/{file}" label h
    IO.println s!"{label}: {x.pass} pass, {x.fail} fail, {x.acceptable} acceptable (out of {x.pass + x.fail + x.acceptable})"
    wf := wf + x.fail
  return (if t.fail + x2.fail + m.fail + mx.fail + u.fail + ux.fail + ur.fail + v.fail + w.fail + wf == 0 then 0 else 1)
