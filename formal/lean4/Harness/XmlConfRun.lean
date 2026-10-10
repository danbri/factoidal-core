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

## Local overrides

`tests/local-overrides/*.json` with `"suite": "xmlconf"` name a case by its
manifest `ID` (key `test_id`) and the open issue that tracks the dispute
(key `issue`). An overridden case still runs. On every score line it
belongs to it is counted in a `local-override` bucket, never as a pass. If
the case passes on a line, the override is STALE: that is a failure of the
line, and the run says which file to delete. An override that names no case
the runner scored is also a failure. The run exits 1 if any line has a
failure.

Usage: `lake exe l4xmlconf [xmlconf-dir]`
-/
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Namespaces
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.Validity
import L4Factoidal.JSON.Parser

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

/-- The three buckets of one score line. A `local-override` case is a
    disputed fixture (tests/local-overrides): it is never a pass. -/
structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  overridden : Nat := 0
deriving Repr, Inhabited

def Tally.add (a b : Tally) : Tally :=
  { pass := a.pass + b.pass, fail := a.fail + b.fail, overridden := a.overridden + b.overridden }

def Tally.total (t : Tally) : Nat := t.pass + t.fail + t.overridden

/-- "N pass, M fail, K local-override" -/
def Tally.text (t : Tally) : String :=
  s!"{t.pass} pass, {t.fail} fail, {t.overridden} local-override"

/-- Which score line a verdict belongs to. -/
inductive Line where
  | plain | ns | enc | x11 | vValid | vInvalid | vNotWf
deriving Repr, BEq, Inhabited

def Line.name : Line → String
  | .plain => "plain" | .ns => "namespaces" | .enc => "encodings" | .x11 => "xml 1.1"
  | .vValid => "validating (valid)" | .vInvalid => "validating (invalid)"
  | .vNotWf => "validating (not-wf)"

structure Counts where
  plain       : Tally := {}
  ns          : Tally := {}   -- Namespaces-in-XML cases, scored with the namespace check
  enc         : Tally := {}   -- the document or a named entity is not plain UTF-8: decoded, then scored
  x11         : Tally := {}   -- XML 1.1 cases, read by the XML 1.1 rules
  -- The VALIDATING line: parse, then the validity constraints, per TYPE.
  vValid      : Tally := {}
  vInvalid    : Tally := {}
  vNotWf      : Tally := {}
  optional    : Nat := 0   -- TYPE="error": behaviour is optional
  x11Optional : Nat := 0   -- XML 1.1 cases of TYPE="error"
  nsOptional  : Nat := 0   -- Namespaces-in-XML cases of TYPE="error"
  encUnsupported : List String := []  -- ... or in an encoding the decoder does not implement (names)
  otherEdition : Nat := 0  -- EDITION says the case is not about 1.0 5e
  vUndecided : Nat := 0    -- valid cases whose DTD could not be read in full
  fileMissing : Nat := 0
  /-- Failures that are not a verdict: a stale override. -/
  stale : List String := []
  /-- Overrides that took effect: (case id, line name). -/
  applied : List (String × String) := []
deriving Repr, Inhabited

def Counts.add (a b : Counts) : Counts :=
  { plain := a.plain.add b.plain, ns := a.ns.add b.ns, enc := a.enc.add b.enc, x11 := a.x11.add b.x11,
    vValid := a.vValid.add b.vValid, vInvalid := a.vInvalid.add b.vInvalid,
    vNotWf := a.vNotWf.add b.vNotWf,
    optional := a.optional + b.optional,
    x11Optional := a.x11Optional + b.x11Optional,
    nsOptional := a.nsOptional + b.nsOptional,
    encUnsupported := a.encUnsupported ++ b.encUnsupported, otherEdition := a.otherEdition + b.otherEdition,
    vUndecided := a.vUndecided + b.vUndecided,
    fileMissing := a.fileMissing + b.fileMissing,
    stale := a.stale ++ b.stale, applied := a.applied ++ b.applied }

/-- The validating line, all three TYPEs together. -/
def Counts.validating (c : Counts) : Tally := (c.vValid.add c.vInvalid).add c.vNotWf

def Counts.ofTally (line : Line) (t : Tally) : Counts :=
  match line with
  | .plain => { plain := t } | .ns => { ns := t } | .enc => { enc := t } | .x11 => { x11 := t }
  | .vValid => { vValid := t } | .vInvalid => { vInvalid := t } | .vNotWf => { vNotWf := t }

/-- One case on one line. `ov` says an override names the case; `ok` says
    the verdict matched the manifest's TYPE. An overridden case that does
    not match is counted in the `local-override` bucket. One that matches
    is a failure of the line (STALE), never a pass. -/
def Counts.verdict (line : Line) (id : String) (ov ok : Bool) : Counts :=
  if ov then
    if ok then
      { Counts.ofTally line { fail := 1 } with
        stale := [s!"{id}: STALE local override on the {line.name} line: the case now passes; delete its file in tests/local-overrides/ and close its issue"],
        applied := [(id, line.name)] }
    else { Counts.ofTally line { overridden := 1 } with applied := [(id, line.name)] }
  else Counts.ofTally line (if ok then { pass := 1 } else { fail := 1 })

-- The bookkeeping, pinned. A plain pass and a plain failure stay what they
-- are; an overridden failure goes to its own bucket and is never a pass; an
-- overridden PASS is a failure of the line and a STALE note.
#guard (Counts.verdict .x11 "a" false true).x11.pass == 1
#guard (Counts.verdict .x11 "a" false false).x11.fail == 1
#guard (Counts.verdict .x11 "a" true false).x11.overridden == 1
#guard (Counts.verdict .x11 "a" true false).x11.pass == 0
#guard (Counts.verdict .x11 "a" true false).x11.fail == 0
#guard (Counts.verdict .x11 "a" true false).stale.isEmpty
#guard (Counts.verdict .x11 "a" true true).x11.pass == 0
#guard (Counts.verdict .x11 "a" true true).x11.fail == 1
#guard (Counts.verdict .x11 "a" true true).stale.length == 1
#guard (Counts.verdict .vValid "a" true false).validating.overridden == 1
#guard (Counts.verdict .vNotWf "a" true true).validating.fail == 1
#guard ((Counts.verdict .plain "a" true false).add (Counts.verdict .plain "b" false true)).plain.total == 2

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

def runManifest (root : String) (rel : String) (verbose : Bool)
    (overrides : List String) : IO Counts := do
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
                  -- A named directory may hold entities that name
                  -- another one (`eduni/errata-2e/E18.xml` names
                  -- `subdir1/E18-pe`, which names `../subdir2/`), so the
                  -- texts read so far are searched for further
                  -- directory names, a few rounds.
                  let mut loadedDirs : List String := []
                  let mut frontier : List String := [text]
                  for _round in [0:3] do
                    let mut next : List String := []
                    if !frontier.isEmpty then
                      for (dname, pfx, dpath) in cands do
                        if !(loadedDirs.contains pfx) &&
                           frontier.any (fun t => (t.splitOn (dname ++ "/")).length > 1) then
                          loadedDirs := loadedDirs ++ [pfx]
                          for entry in (← System.FilePath.readDir dpath) do
                            let ep := entry.path.toString
                            if !(← System.FilePath.isDir ep) then
                              let b ← IO.FS.readBinFile ep
                              let plain := (String.fromUTF8? b).isSome
                              match decodeXmlBytesE b with
                              | .error (.unsupported n) =>
                                  unreadable := unreadable ++ [(pfx ++ entry.fileName, n)]
                              | .error _ => fetched := fetched ++ [(pfx ++ entry.fileName, ep, none, plain)]
                              | .ok t =>
                                  fetched := fetched ++ [(pfx ++ entry.fileName, ep, some t, plain)]
                                  next := next ++ [t]
                    frontier := next
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
                    match fetched.find? (fun (k, _, _, _) => k == name) with
                    | some (_, _, t, _) => t
                    | none =>
                      -- A relative identifier whose `../` climbs out of
                      -- the directory the declaring entity lives in:
                      -- `subdir1/E18-pe` names `../subdir2/E18-extpe`.
                      -- The pure resolver is not told which entity the
                      -- declaration is in, so match what is left of the
                      -- identifier against the end of a path read.
                      let rest := (sysId.splitOn "/").filter (fun seg => seg != ".." && seg != ".")
                      let tail := String.intercalate "/" rest
                      (fetched.find? (fun (k, _, _, _) => k == tail || k.endsWith ("/" ++ tail))).bind (·.2.2.1)
                match entityUnsupported.head? with
                | some (key, name) =>
                    if verbose then IO.println s!"UNSUPPORTED-ENCODING {id}: entity {key} is in {name}"
                    c := Counts.add c { encUnsupported := [name] }
                | none =>
                let withNotes : Except String (Document × Notes) :=
                  match docRead with
                  | .error e => .error e.message
                  | .ok t =>
                      match parseXMLNotes resolve true t with
                      | .ok r => .ok r
                      | .error e => .error e.message
                let outcome : Except String Document :=
                  match withNotes with
                  | .ok (d, _) => .ok d
                  | .error m => .error m
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
                let ov := overrides.contains id
                c := Counts.add c
                  (if nsAware then Counts.verdict .ns id ov ok
                   else if is11 then Counts.verdict .x11 id ov ok
                   else if plainCase then Counts.verdict .plain id ov ok
                   else Counts.verdict .enc id ov ok)
                -- The VALIDATING line. A `not-wf` case must still be
                -- refused by the parser. A `valid` case must parse and
                -- pass every validity constraint; an `invalid` case must
                -- parse and break one. The Namespaces suites are about
                -- another layer and are not read in this mode. A case
                -- whose DTD could not be read in full is counted apart:
                -- the validator can only say what it saw.
                if !nsAware then
                  let parsed := outcome.toOption
                  let violations := match withNotes with
                    | .ok (d, ns) => validateWithNotes d ns
                    | .error _ => []
                  let incompleteDtd := match parsed with
                    | some d => (d.doctype.map (·.incomplete)).getD false
                    | none => false
                  if ty == "not-wf" then
                    c := Counts.add c (Counts.verdict .vNotWf id ov parsed.isNone)
                  else if incompleteDtd && ty == "valid" then
                    if violations.isEmpty then c := Counts.add c (Counts.verdict .vValid id ov true)
                    else c := Counts.add c { vUndecided := 1 }
                  else if parsed.isNone then
                    c := Counts.add c (if ty == "valid" then Counts.verdict .vValid id ov false
                                       else Counts.verdict .vInvalid id ov false)
                  else if ty == "valid" then
                    c := Counts.add c (Counts.verdict .vValid id ov violations.isEmpty)
                  else
                    c := Counts.add c (Counts.verdict .vInvalid id ov !violations.isEmpty)
                  if verbose && ty == "valid" && !violations.isEmpty && parsed.isSome then
                    IO.println s!"VFAIL {id} (valid): {(violations.take 3).map (fun v => v.vc ++ ": " ++ v.message)}"
                  if verbose && ty == "invalid" && violations.isEmpty && parsed.isSome then
                    IO.println s!"VFAIL {id} (invalid): no violation found"
                  if verbose && ty == "invalid" && !violations.isEmpty && parsed.isSome then
                    IO.println s!"VINVALID {id}: {(violations.map (·.vc)).eraseDups}"
                if verbose && is11 && ty == "not-wf" then
                  IO.println s!"X11 {id} (not-wf): rejected -- {why}"
                if verbose && !plainCase && !nsAware && !is11 then
                  IO.println s!"ENC {id} ({ty}): {if accepted then "accepted" else "rejected"}{if why == "" then "" else " -- " ++ why}"
                if !ok && verbose then
                  IO.println s!"{if ov then "OVERRIDDEN" else "FAIL"} {id} ({ty}): {uri} was {if accepted then "accepted" else "rejected"}{if why == "" then "" else " -- " ++ why}"
      return c

/-- ": euc-jp x2, shift_jis x1", or "" for none. -/
def encodingNames (names : List String) : String :=
  if names.isEmpty then ""
  else
    let keys := (names.map (·.toLower)).eraseDups
    ": " ++ String.intercalate ", " (keys.map fun k => s!"{k} x{(names.filter (fun n => n.toLower == k)).length}")

/-- Read `tests/local-overrides/*.json` (relative to the current directory,
    the repository root) and return `(test_id, issue)` for the files whose
    `suite` is `suite`. An absent directory means no overrides. Same files
    and keys `Harness/JsonLdFrameRun.lean` reads. -/
def loadLocalOverrides (suite : String) : IO (List (String × String)) := do
  let dir : System.FilePath := "tests" / "local-overrides"
  let entries ← try dir.readDir catch _ => pure #[]
  let mut out : List (String × String) := []
  for f in entries do
    if !f.fileName.endsWith ".json" then continue
    let txt ← try IO.FS.readFile (dir / f.fileName) catch _ => pure ""
    match L4Factoidal.JSON.parseJson txt with
    | .error _ => pure ()
    | .ok j =>
      if (j.getString? "suite").getD "" == suite then
        match j.getString? "test_id" with
        | some i => out := (i, (j.getString? "issue").getD "(no issue named)") :: out
        | none   => pure ()
  pure out

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let dir := (args.filter (fun a => !a.startsWith "--")).head?
    |>.getD "third_party/testing/xml/xmlconf"
  if !(← System.FilePath.isDir dir) then
    IO.println s!"xmlconf runner: corpus not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let overrideList ← loadLocalOverrides "xmlconf"
  let overrideIds := overrideList.map (·.1)
  let mut total : Counts := {}
  for m in subManifests do
    let c ← runManifest dir m verbose overrideIds
    if verbose then
      IO.println s!"manifest {m}: {c.plain.total + c.enc.total + c.ns.total + c.x11.total} scored"
      (← IO.getStdout).flush
    total := Counts.add total c
  -- An override that took effect on no line names no scored case.
  let unmatched := overrideList.filter (fun (i, _) => !(total.applied.any (fun (a, _) => a == i)))
  IO.println ""
  IO.println s!"xml conformance SCORED: {total.plain.text} (out of {total.plain.total} in profile)"
  IO.println s!"namespaces SCORED: {total.ns.text} (out of {total.ns.total} Namespaces-in-XML cases; XML parse + namespace well-formedness)"
  IO.println s!"encodings SCORED: {total.enc.text} (out of {total.enc.total} cases whose document or entity is not plain UTF-8; decoded by decodeXmlBytes)"
  IO.println s!"xml 1.1 SCORED: {total.x11.text} (out of {total.x11.total} XML 1.1 cases; the document's declaration selects the rules)"
  let v := total.validating
  IO.println s!"validating SCORED: {v.text} (out of {v.total}; parse, then the validity constraints; the Namespaces suites are not read in this mode)"
  IO.println s!"  valid: {total.vValid.text} (out of {total.vValid.total}), invalid: {total.vInvalid.text} (out of {total.vInvalid.total}), not-wf: {total.vNotWf.text} (out of {total.vNotWf.total})"
  IO.println s!"  {total.vUndecided} valid cases left out: their DTD could not be read in full"
  IO.println s!"OUT OF PROFILE, reported not scored: {total.optional} optional-behaviour (TYPE=error),"
  IO.println s!"  {total.nsOptional} optional-behaviour in the Namespaces suites (TYPE=error),"
  IO.println s!"  {total.x11Optional} optional-behaviour in the XML 1.1 suites (TYPE=error),"
  IO.println s!"  {total.encUnsupported.length} in an encoding the decoder does not implement{encodingNames total.encUnsupported},"
  IO.println s!"  {total.otherEdition} for editions 1-4 only (this parser follows the Fifth Edition),"
  if total.fileMissing > 0 then
    IO.println s!"  {total.fileMissing} referenced files not on disk"
  IO.println ""
  if !overrideList.isEmpty then
    IO.println "LOCAL OVERRIDES (tests/local-overrides, suite xmlconf): a disputed case is counted in"
    IO.println "the local-override bucket of each line it belongs to, never as a pass."
    for (i, issue) in overrideList.reverse do
      let lines := (total.applied.filter (fun (a, _) => a == i)).map (·.2)
      IO.println s!"  {i}: {issue} ({String.intercalate ", " lines})"
    IO.println ""
  for m in total.stale do IO.println s!"FAILURE: {m}"
  for (i, issue) in unmatched do
    IO.println s!"FAILURE: local override {i} ({issue}) matches no scored case"
  IO.println "Profile: XML 1.0 (Fifth Edition) and XML 1.1. The parser is NON-VALIDATING;"
  IO.println "validity is a separate layer. Bytes are decoded as UTF-8, UTF-16,"
  IO.println "ISO-8859-1 or US-ASCII (XML 1.0 section 4.3.3, Appendix F)."
  IO.println "The XML suites are read as plain XML, where ':' is an ordinary name"
  IO.println "character. The Namespaces suites (eduni/namespaces) are read with the"
  IO.println "Namespaces-in-XML well-formedness check on top of the XML parse."
  IO.println "In the plain, namespaces, encodings and XML 1.1 lines a `valid` and an"
  IO.println "`invalid` case must BOTH be accepted: `invalid` means the document"
  IO.println "violates its DTD, which a non-validating parser is not asked to notice."
  IO.println "The validating line parses, then checks the validity constraints"
  IO.println "(XML/Validity.lean): `valid` must pass them, `invalid` must break one,"
  IO.println "`not-wf` must still be refused by the parser."
  IO.println "Counting out-of-profile cases as failures would understate the parser;"
  IO.println "counting them as passes would overstate it."
  let anyFail := total.plain.fail + total.ns.fail + total.enc.fail + total.x11.fail
    + total.validating.fail + total.stale.length + unmatched.length
  return (if anyFail > 0 then 1 else 0)
