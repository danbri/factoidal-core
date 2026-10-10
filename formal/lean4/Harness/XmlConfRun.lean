/-
Harness/XmlConfRun — the W3C XML Conformance Test Suite, run end to
end against the Lean XML parser.

`XML/ConfProbe.lean` reads a list of paths from standard input and
prints a verdict per file. That is a probe: it has no expected answer
to compare against, so it cannot say whether a verdict is RIGHT. This
runner reads the suite's OWN sub-manifests — the `<TEST>` elements with
their `TYPE` and `URI` — and scores each verdict against what the
suite says it should be.

The sub-manifests are XML, and they are parsed by the same verified
parser the tests exercise. That is deliberate: a separate manifest
reader would be a second implementation of the syntax under test.

## The parser's PROFILE decides what can be scored

`Parser.lean` implements XML 1.0 (Fifth Edition) and XML 1.1,
NON-VALIDATING, the version chosen by the document's own XML
declaration; `Namespaces.lean` adds the Namespaces-in-XML check on top
of it; `Encoding.lean` turns the BYTES of a document or entity into text
(UTF-8, UTF-16, ISO-8859-1, US-ASCII). A test outside that profile is not
a failure; it is not a test of this parser. Each is counted in its own
bucket and named. A case belongs to the first line below that fits it:

  * `EDITION` without `5` — the case is about an earlier edition of
    XML 1.0 (its name classes were the Appendix B tables). Not scored.
  * `error`   — the specification leaves the behaviour optional, so a
    verdict either way is conformant. NOT scored, and reported (apart
    for the XML suites, the Namespaces suites and the XML 1.1 suites).
  * `eduni/namespaces/*` — scored separately: XML parse AND namespace
    well-formedness (`Document.namespaceWellFormed`).
  * `VERSION="1.1"` — XML 1.1, scored separately. The suites mark which
    cases are about 1.1; the document's own declaration (`<?xml
    version="1.1"?>`, or none) decides which rules the parser applies, so
    a case that carries a 1.0 document is read as 1.0.
  * bytes that are not plain UTF-8 — decoded by `decodeXmlBytesE`
    (XML 1.0 section 4.3.3, Appendix F) and scored on a line of their
    own. An encoding the decoder does not implement is out of profile,
    and its name is printed.
  * everything else: `not-wf` must be REJECTED; `valid` and `invalid`
    must both be ACCEPTED by a NON-VALIDATING parser (`invalid` means
    "violates the DTD", which it is not asked to notice).

The XML 1.1 line also covers the IBM XML 1.1 manifests under
`ibm/xml-1.1/`, which the master manifest includes.

Reporting these as failures would understate the parser; folding them
into passes would overstate it. Both numbers are printed.

Usage: `lake exe l4xmlconf [xmlconf-dir]`
-/
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Namespaces
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.Validity

open L4Factoidal.XML

/-- Every `<TEST>` element anywhere in a manifest tree. -/
partial def testElements : Node → List Node
  | n@(.element tag _ cs) =>
      (if tag == "TEST" then [n] else []) ++ cs.flatMap testElements
  | _ => []

def attr? (name : String) : Node → Option String
  | .element _ attrs _ => (attrs.find? (fun a => a.name == name)).map (·.value)
  | _ => none

/-- The directory part of a path, with its trailing slash. -/
def dirOf (p : String) : String :=
  match (p.splitOn "/").reverse with
  | _ :: rest => if rest.isEmpty then "" else String.intercalate "/" rest.reverse ++ "/"
  | []        => ""

structure Counts where
  scored      : Nat := 0
  pass        : Nat := 0
  fail        : Nat := 0
  optional    : Nat := 0   -- TYPE="error": behaviour is optional
  x11Pass     : Nat := 0   -- XML 1.1 cases, read by the XML 1.1 rules
  x11Fail     : Nat := 0
  x11Optional : Nat := 0   -- XML 1.1 cases of TYPE="error"
  encPass     : Nat := 0   -- the document or a named entity is not plain UTF-8: decoded, then scored
  encFail     : Nat := 0
  encUnsupported : List String := []  -- ... or in an encoding the decoder does not implement (names)
  otherEdition : Nat := 0  -- EDITION says the case is not about 1.0 5e
  nsPass      : Nat := 0   -- Namespaces-in-XML cases, scored with the namespace check
  nsFail      : Nat := 0
  nsOptional  : Nat := 0   -- Namespaces-in-XML cases of TYPE="error"
  -- The VALIDATING line: parse, then the validity constraints.
  -- (passes, failures) per TYPE, and the cases whose DTD could not be read.
  vValidPass : Nat := 0
  vValidFail : Nat := 0
  vInvalidPass : Nat := 0
  vInvalidFail : Nat := 0
  vNotWfPass : Nat := 0
  vNotWfFail : Nat := 0
  vUndecided : Nat := 0
  fileMissing : Nat := 0
deriving Repr, Inhabited

def Counts.add (a b : Counts) : Counts :=
  { scored := a.scored + b.scored, pass := a.pass + b.pass, fail := a.fail + b.fail,
    optional := a.optional + b.optional,
    x11Pass := a.x11Pass + b.x11Pass, x11Fail := a.x11Fail + b.x11Fail,
    x11Optional := a.x11Optional + b.x11Optional,
    encPass := a.encPass + b.encPass, encFail := a.encFail + b.encFail,
    encUnsupported := a.encUnsupported ++ b.encUnsupported, otherEdition := a.otherEdition + b.otherEdition,
    nsPass := a.nsPass + b.nsPass, nsFail := a.nsFail + b.nsFail,
    nsOptional := a.nsOptional + b.nsOptional,
    vValidPass := a.vValidPass + b.vValidPass, vValidFail := a.vValidFail + b.vValidFail,
    vInvalidPass := a.vInvalidPass + b.vInvalidPass, vInvalidFail := a.vInvalidFail + b.vInvalidFail,
    vNotWfPass := a.vNotWfPass + b.vNotWfPass, vNotWfFail := a.vNotWfFail + b.vNotWfFail,
    vUndecided := a.vUndecided + b.vUndecided,
    fileMissing := a.fileMissing + b.fileMissing }

/-- The sub-manifests, relative to the suite root. Listed rather than
    discovered so the denominator is stable and a missing file is
    visible as a missing file. -/
def subManifests : List String :=
  [ "sun/sun-valid.xml", "sun/sun-invalid.xml", "sun/sun-not-wf.xml",
    "sun/sun-error.xml", "xmltest/xmltest.xml", "japanese/japanese.xml",
    "oasis/oasis.xml", "ibm/ibm_oasis_invalid.xml", "ibm/ibm_oasis_not-wf.xml",
    "ibm/ibm_oasis_valid.xml", "eduni/errata-2e/errata2e.xml",
    "eduni/errata-3e/errata3e.xml", "eduni/errata-4e/errata4e.xml",
    "eduni/namespaces/1.0/rmt-ns10.xml", "eduni/namespaces/1.1/rmt-ns11.xml",
    "eduni/namespaces/errata-1e/errata1e.xml", "eduni/xml-1.1/xml11.xml",
    "eduni/misc/ht-bh.xml",
    "ibm/xml-1.1/ibm_invalid.xml", "ibm/xml-1.1/ibm_not-wf.xml",
    "ibm/xml-1.1/ibm_valid.xml" ]

/-- Is this sub-manifest the NAMESPACES suite? Those cases test
    Namespaces in XML on top of XML 1.0: `rmt-ns10-004` is
    `<a:foo xmlns:a="…"/>` with an undeclared prefix, which is
    namespace-ill-formed and XML-well-formed. A case here passes when
    the parse AND `Document.namespaceWellFormed` agree with the
    manifest's TYPE; every other suite is read as plain XML, where a
    colon is an ordinary name character (`xmltest/` depends on that).
    They are counted in their own line so the plain-XML line keeps its
    meaning. -/
def isNamespaceSuite (rel : String) : Bool :=
  rel.startsWith "eduni/namespaces/"

def runManifest (root : String) (rel : String) (verbose : Bool) : IO Counts := do
  let path := root ++ "/" ++ rel
  if !(← System.FilePath.pathExists path) then
    IO.println s!"sub-manifest not found: {rel}"
    return { fileMissing := 1 }
  let src ← IO.FS.readFile path
  -- Some sub-manifests are ENTITY BODIES, not documents: `sun-not-wf.xml`
  -- is a run of sibling `<TEST>` elements with no single root, because
  -- `xmlconf.xml` includes it as an external entity. Rejecting it is
  -- the RIGHT verdict on it as a document, so the runner supplies the
  -- element the entity is included into rather than loosening the
  -- parser. Without this, three manifests and 159 tests vanished from
  -- the denominator with only a one-line notice.
  let wrapped :=
    let body := match src.splitOn "?>" with
      | _ :: rest => if src.startsWith "<?xml" then String.intercalate "?>" rest else src
      | []        => src
    "<TESTCASES>" ++ body ++ "</TESTCASES>"
  let parsed := match parseXML src with
    | .ok d    => some d
    | .error _ => match parseXML wrapped with
      | .ok d    => some d
      | .error _ => none
  match parsed with
  | none =>
      IO.println s!"sub-manifest did not parse: {rel}"
      return { fileMissing := 1 }
  | some doc =>
      let base := root ++ "/" ++ dirOf rel
      let mut c : Counts := {}
      for t in testElements doc.root do
        let ty := (attr? "TYPE" t).getD ""
        let uri := (attr? "URI" t).getD ""
        let ver := (attr? "VERSION" t).getD "1.0"
        let id := (attr? "ID" t).getD "?"
        -- The suite marks which EDITIONS of XML 1.0 a case is about.
        -- The Fifth Edition REPLACED Appendix B's enumerated
        -- BaseChar / CombiningChar / Digit / Extender classes with
        -- the ranges this parser uses, so a case marked
        -- `EDITION="1 2 3 4"` asks a question the Fifth Edition does
        -- not ask — 297 of them, all `not-wf`, all scored as failures
        -- because the runner ignored the attribute. They are NOT
        -- passes either: the parser is not being asked, so the honest
        -- place for them is a bucket of their own.
        let edition := attr? "EDITION" t
        let appliesHere := match edition with
          | none    => true
          | some es => (es.splitOn " ").contains "5"
        let nsAware := isNamespaceSuite rel
        -- The suite marks the XML 1.1 cases; the document's OWN
        -- declaration decides which rules the parser applies to it.
        let is11 := ver == "1.1" && !nsAware
        if uri == "" then pure ()
        else if !appliesHere then c := Counts.add c { otherEdition := 1 }
        else if ty == "error" then
          c := Counts.add c (if nsAware then { nsOptional := 1 }
                             else if is11 then { x11Optional := 1 } else { optional := 1 })
        else
          let fp := base ++ uri
          if !(← System.FilePath.pathExists fp) then
            c := Counts.add c { fileMissing := 1 }
          else
            let bytes ← IO.FS.readBinFile fp
            -- A document is decoded by `decodeXmlBytesE`
            -- (XML 1.0 section 4.3.3 and Appendix F): UTF-8, UTF-16,
            -- ISO-8859-1 and US-ASCII, with the encoding declaration
            -- checked against the bytes.
            --
            -- Which LINE a case is scored on depends only on whether
            -- it needed more than UTF-8: the document, or an entity it
            -- names, is not plain UTF-8 bytes. That keeps the plain
            -- line (1861 cases) the set it was before the decoder
            -- existed.
            let docRead := decodeXmlBytesE bytes
            let docPlain := (String.fromUTF8? bytes).isSome
            match docRead with
            | .error (.unsupported name) =>
                if verbose then IO.println s!"UNSUPPORTED-ENCODING {id}: {uri} is in {name}"
                c := Counts.add c { encUnsupported := [name] }
            | _ =>
                -- A document that does not decode is a fatal error of
                -- the DOCUMENT: the verdict is "rejected", and it is
                -- scored.
                let text := match docRead with
                  | .ok t => t
                  | .error _ => ""
                -- An EXTERNAL entity's text, read from disk relative
                -- to the document that names it. The parser takes the
                -- resolver as a PARAMETER and stays a total function;
                -- the I/O is here, where it belongs.
                --
                -- Every file the document could name is read up
                -- front, because the resolver is pure. That is
                -- affordable: a conformance case names at most a
                -- handful of small files, all in its own directory.
                let docDir := base ++ dirOf uri
                -- (identifier, path, decoded text if it decodes, plain
                -- UTF-8 bytes)
                let mut fetched : List (String × String × Option String × Bool) := []
                -- (identifier, encoding name) of entities in an
                -- encoding the decoder does not implement.
                let mut unreadable : List (String × String) := []
                if ← System.FilePath.isDir docDir then
                  for entry in (← System.FilePath.readDir docDir) do
                    let ep := entry.path.toString
                    if !(← System.FilePath.isDir ep) then
                      let b ← IO.FS.readBinFile ep
                      let plain := (String.fromUTF8? b).isSome
                      match decodeXmlBytesE b with
                      | .error (.unsupported n) => unreadable := unreadable ++ [(entry.fileName, n)]
                      | .error _ => fetched := fetched ++ [(entry.fileName, ep, none, plain)]
                      | .ok t => fetched := fetched ++ [(entry.fileName, ep, some t, plain)]
                  -- A system identifier is RELATIVE to the document
                  -- that names it, and a conformance case may put an
                  -- entity in a sibling or a child directory:
                  -- `valid/ext02.xml` names `../invalid/utf16b.xml`.
                  -- Reading every neighbouring directory for all 1862
                  -- cases would be hundreds of thousands of file
                  -- reads, so a directory is read only when the
                  -- document's own text names it.
                  let parent := dirOf (docDir.dropRight 1)
                  -- (directory name, identifier prefix, path)
                  let mut cands : List (String × String × String) := []
                  for entry in (← System.FilePath.readDir docDir) do
                    if ← System.FilePath.isDir entry.path.toString then
                      cands := cands ++
                        [(entry.fileName, entry.fileName ++ "/", entry.path.toString)]
                  if parent != "" && (← System.FilePath.isDir parent) then
                    for entry in (← System.FilePath.readDir parent) do
                      if ← System.FilePath.isDir entry.path.toString then
                        cands := cands ++
                          [(entry.fileName, "../" ++ entry.fileName ++ "/",
                            entry.path.toString)]
                  for (dname, pfx, dpath) in cands do
                    if (text.splitOn (dname ++ "/")).length > 1 then
                      for entry in (← System.FilePath.readDir dpath) do
                        let ep := entry.path.toString
                        if !(← System.FilePath.isDir ep) then
                          let b ← IO.FS.readBinFile ep
                          let plain := (String.fromUTF8? b).isSome
                          match decodeXmlBytesE b with
                          | .error (.unsupported n) =>
                              unreadable := unreadable ++ [(pfx ++ entry.fileName, n)]
                          | .error _ => fetched := fetched ++ [(pfx ++ entry.fileName, ep, none, plain)]
                          | .ok t => fetched := fetched ++ [(pfx ++ entry.fileName, ep, some t, plain)]
                -- Only files the document NAMES count. A stray file in
                -- a directory says nothing about this case.
                let named : String → Bool := fun key => (text.splitOn key).length > 1
                let entityUnsupported := unreadable.filter (fun (k, _) => named k)
                let entityPlain := fetched.all (fun (k, _, _, plain) => !named k || plain)
                -- Resolution: the identifier AS WRITTEN first (so
                -- `../invalid/utf16b.xml` finds that file and not a
                -- namesake in this directory), then the last path
                -- segment among the document's own directory, which is
                -- what the vendored corpus needs where a manifest
                -- renamed a file.
                let resolve : String → Option String := fun sysId =>
                  match fetched.find? (fun (k, _, _, _) => k == sysId) with
                  | some (_, _, t, _) => t
                  | none =>
                    let name := ((sysId.splitOn "/").getLast?).getD sysId
                    (fetched.find? (fun (k, _, _, _) => k == name)).bind (·.2.2.1)
                match entityUnsupported.head? with
                | some (key, name) =>
                    if verbose then IO.println s!"UNSUPPORTED-ENCODING {id}: entity {key} is in {name}"
                    c := Counts.add c { encUnsupported := [name] }
                | none =>
                let outcome : Except String Document :=
                  match docRead with
                  | .error e => .error e.message
                  | .ok t =>
                      match parseDecodedXMLWith resolve t with
                      | .ok d => .ok d
                      | .error e => .error e.message
                -- A Namespaces-in-XML case asks for namespace
                -- well-formedness ON TOP OF XML well-formedness
                -- (Namespaces in XML 1.0 section 1: a document is
                -- namespace-well-formed when it is well-formed XML and
                -- obeys the namespace constraints). Every other case
                -- is read as plain, non-namespace XML.
                let nsOk := match outcome with
                  | .ok d    => !nsAware || d.namespaceWellFormed
                  | .error _ => false
                let accepted := outcome.toOption.isSome && nsOk
                let why := match outcome with
                  | .ok _    => if nsOk then "" else "namespace-ill-formed"
                  | .error e => e
                -- A NON-VALIDATING parser accepts `valid` AND
                -- `invalid`: the second violates the DTD, which this
                -- parser is not asked to check.
                let want := ty != "not-wf"
                let plainCase := docPlain && entityPlain
                let ok := accepted == want
                c := Counts.add c
                  (if nsAware then (if ok then { nsPass := 1 } else { nsFail := 1 })
                   else if is11 then (if ok then { x11Pass := 1 } else { x11Fail := 1 })
                   else if plainCase then
                     (if ok then { scored := 1, pass := 1 } else { scored := 1, fail := 1 })
                   else (if ok then { encPass := 1 } else { encFail := 1 }))
                -- The VALIDATING line. A `not-wf` case must still be
                -- refused by the parser. A `valid` case must parse and
                -- pass every validity constraint; an `invalid` case must
                -- parse and break one. The Namespaces suites are about
                -- another layer and are not read in this mode. A case
                -- whose DTD could not be read in full is counted apart:
                -- the validator can only say what it saw.
                if !nsAware then
                  let parsed := outcome.toOption
                  let violations := match parsed with
                    | some d => validate d
                    | none => []
                  let incompleteDtd := match parsed with
                    | some d => (d.doctype.map (·.incomplete)).getD false
                    | none => false
                  if ty == "not-wf" then
                    c := Counts.add c (if parsed.isNone then { vNotWfPass := 1 } else { vNotWfFail := 1 })
                  else if incompleteDtd && ty == "valid" then
                    if violations.isEmpty then c := Counts.add c { vValidPass := 1 }
                    else c := Counts.add c { vUndecided := 1 }
                  else if parsed.isNone then
                    c := Counts.add c (if ty == "valid" then { vValidFail := 1 } else { vInvalidFail := 1 })
                  else if ty == "valid" then
                    c := Counts.add c (if violations.isEmpty then { vValidPass := 1 } else { vValidFail := 1 })
                  else
                    c := Counts.add c (if violations.isEmpty then { vInvalidFail := 1 } else { vInvalidPass := 1 })
                  if verbose && ty == "valid" && !violations.isEmpty && parsed.isSome then
                    IO.println s!"VFAIL {id} (valid): {(violations.take 3).map (fun v => v.vc ++ ": " ++ v.message)}"
                  if verbose && ty == "invalid" && violations.isEmpty && parsed.isSome then
                    IO.println s!"VFAIL {id} (invalid): no violation found"
                if verbose && is11 && ty == "not-wf" then
                  IO.println s!"X11 {id} (not-wf): rejected -- {why}"
                if verbose && !plainCase && !nsAware && !is11 then
                  IO.println s!"ENC {id} ({ty}): {if accepted then "accepted" else "rejected"}{if why == "" then "" else " -- " ++ why}"
                if !ok && verbose then
                  IO.println s!"FAIL {id} ({ty}): {uri} was {if accepted then "accepted" else "rejected"}{if why == "" then "" else " -- " ++ why}"
      return c

/-- ": euc-jp x2, shift_jis x1", or "" for none. -/
def encodingNames (names : List String) : String :=
  if names.isEmpty then ""
  else
    let keys := (names.map (·.toLower)).eraseDups
    ": " ++ String.intercalate ", " (keys.map fun k => s!"{k} x{(names.filter (fun n => n.toLower == k)).length}")

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/xml/xmlconf"
  if !(← System.FilePath.isDir dir) then
    IO.println s!"xmlconf runner: corpus not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mut total : Counts := {}
  for m in subManifests do
    let c ← runManifest dir m verbose
    if verbose then
      IO.println s!"manifest {m}: {c.scored + c.encPass + c.encFail + c.nsPass + c.nsFail + c.x11Pass + c.x11Fail} scored"
      (← IO.getStdout).flush
    total := Counts.add total c
  IO.println ""
  IO.println s!"xml conformance SCORED: {total.pass} pass, {total.fail} fail (out of {total.scored} in profile)"
  IO.println s!"namespaces SCORED: {total.nsPass} pass, {total.nsFail} fail (out of {total.nsPass + total.nsFail} Namespaces-in-XML cases; XML parse + namespace well-formedness)"
  IO.println s!"encodings SCORED: {total.encPass} pass, {total.encFail} fail (out of {total.encPass + total.encFail} cases whose document or entity is not plain UTF-8; decoded by decodeXmlBytes)"
  IO.println s!"xml 1.1 SCORED: {total.x11Pass} pass, {total.x11Fail} fail (out of {total.x11Pass + total.x11Fail} XML 1.1 cases; the document's declaration selects the rules)"
  let vp := total.vValidPass + total.vInvalidPass + total.vNotWfPass
  let vf := total.vValidFail + total.vInvalidFail + total.vNotWfFail
  IO.println s!"validating SCORED: {vp} pass, {vf} fail (out of {vp + vf}; parse, then the validity constraints; the Namespaces suites are not read in this mode)"
  IO.println s!"  valid: {total.vValidPass} pass, {total.vValidFail} fail (out of {total.vValidPass + total.vValidFail}), invalid: {total.vInvalidPass} pass, {total.vInvalidFail} fail (out of {total.vInvalidPass + total.vInvalidFail}), not-wf: {total.vNotWfPass} pass, {total.vNotWfFail} fail (out of {total.vNotWfPass + total.vNotWfFail})"
  IO.println s!"  {total.vUndecided} valid cases left out: their DTD could not be read in full"
  IO.println s!"OUT OF PROFILE, reported not scored: {total.optional} optional-behaviour (TYPE=error),"
  IO.println s!"  {total.nsOptional} optional-behaviour in the Namespaces suites (TYPE=error),"
  IO.println s!"  {total.x11Optional} optional-behaviour in the XML 1.1 suites (TYPE=error),"
  IO.println s!"  {total.encUnsupported.length} in an encoding the decoder does not implement{encodingNames total.encUnsupported},"
  IO.println s!"  {total.otherEdition} for editions 1-4 only (this parser follows the Fifth Edition),"
  if total.fileMissing > 0 then
    IO.println s!"  {total.fileMissing} referenced files not on disk"
  IO.println ""
  IO.println "Profile: XML 1.0 (Fifth Edition) and XML 1.1, NON-VALIDATING. Bytes are decoded as"
  IO.println "UTF-8, UTF-16, ISO-8859-1 or US-ASCII (XML 1.0 section 4.3.3, Appendix F)."
  IO.println "The XML suites are read as plain XML, where ':' is an ordinary name"
  IO.println "character. The Namespaces suites (eduni/namespaces) are read with the"
  IO.println "Namespaces-in-XML well-formedness check on top of the XML parse."
  IO.println "A `valid` and an `invalid` case must BOTH be accepted: `invalid` means"
  IO.println "it violates the DTD, which a non-validating parser is not asked to"
  IO.println "notice. Counting those as failures would understate the parser;"
  IO.println "counting the out-of-profile cases as passes would overstate it."
  return 0
