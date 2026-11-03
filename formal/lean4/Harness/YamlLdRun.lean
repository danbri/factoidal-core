/-
Harness/YamlLdRun — run `L4Factoidal.YAMLLD` against the YAML-LD test suite
(`third_party/testing/yaml-ld/tests/manifest.jsonld`, provenance in
`third_party/testing/yaml-ld-PROVENANCE.md`).

A HARNESS: file I/O and score lines only. Every decision (encoding, YAML
loading, stream processing, HTML script selection, the JSON-LD algorithms)
is in `L4Factoidal.YAMLLD.Api`.

Comparison, from the suite's README ("YAML-LD object comparison"): the
expected `.yamlld` or `.jsonld` document is loaded and compared with the
output as JSON values, with array order significant only under `@list`;
an `.nq` expectation is compared as an RDF dataset (isomorphism). A negative
test passes when the processor fails with the manifest's `expectErrorCode`;
a failure with another code is counted as a fail, because the YAML-LD codes
(`invalid encoding`, `mapping-key-error`) are what those tests check.

The manifest marks the Extended Profile cases `normative: false`; they run
with `Options.extended` and are counted, and also reported apart.

Usage, from the repository root:
  formal/lean4/.lake/build/bin/l4yamlld [tests-dir]
  formal/lean4/.lake/build/bin/l4yamlld --json-superset [json-ld-tests-dir]
The second form loads every `.jsonld` file of the JSON-LD 1.1 test suite
through the YAML loader and checks that it gives the value `parseJson`
gives (YAML 1.2.2 §1.3, JSON is a subset of YAML).
-/
import L4Factoidal.YAMLLD.Api
import L4Factoidal.YAMLLD.Theorems
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical
-- `parseNQuads_eq_fast` (@[csimp]): the calls of `parseNQuads` here run `parseNQuadsFast`
-- (https://github.com/danbri/factoidal/issues/868; `tools/lean-csimp-reach.py`, not-imported).
import L4Factoidal.Syntax.NQuadsFastTheorems

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.YAMLLD
open L4Factoidal.RDF
open L4Factoidal.Syntax

namespace YamlLdRun

def readFileOpt (p : System.FilePath) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

def readBytesOpt (p : System.FilePath) : IO (Option ByteArray) := do
  try pure (some (← IO.FS.readBinFile p)) catch _ => pure none

def walkDir : Nat → System.FilePath → String → IO (List String)
  | 0, _, _ => pure []
  | depth + 1, root, rel => do
    let dir := if rel.isEmpty then root else root / rel
    let entries ← try dir.readDir catch _ => pure #[]
    let mut out : List String := []
    for e in entries do
      let childRel := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      if ← (dir / e.fileName).isDir then
        out := out ++ (← walkDir depth root childRel)
      else
        out := childRel :: out
    pure out

/-- JSON values with arrays in a canonical order except under `@list`. -/
def unorderedNorm : Nat → Bool → Json → Json
  | 0, _, j => j
  | f + 1, isList, .array xs =>
    let ys := xs.map (unorderedNorm f false)
    if isList then .array ys
    else .array ((ys.map (fun y => (jcsDocument y, y))).mergeSort (fun a b => decide (a.1 ≤ b.1))
                  |>.map (·.2))
  | f + 1, _, .object fs => .object (fs.map (fun kv => (kv.1, unorderedNorm f (kv.1 == "@list") kv.2)))
  | _, _, j => j

def sameJson (a b : Json) : Bool :=
  expandedEqual a b ||
    jcsDocument (unorderedNorm (Json.size a + 1) false a) ==
      jcsDocument (unorderedNorm (Json.size b + 1) false b)

def parseNQuadsLenient (txt : String) : Dataset := Id.run do
  let mut ds : Dataset := Dataset.empty
  for line in txt.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "#" then continue
    match parseNQuads t .rdf11 with
    | .error _ => pure ()
    | .ok one =>
      ds := { default := ds.default ++ one.default,
              named := one.named.foldl (fun acc ng =>
                match acc.find? (fun x => x.name == ng.name) with
                | some existing =>
                  acc.map (fun x => if x.name == ng.name
                                    then { name := x.name, graph := existing.graph ++ ng.graph }
                                    else x)
                | none => acc ++ [ng]) ds.named }
  pure ds

structure Entry where
  id : String
  name : String
  negative : Bool
  algo : String
  input : String
  expect : Option String
  context : Option String
  frame : Option String
  errorCode : Option String
  extractAll : Bool
  extended : Bool
  normative : Bool
  compactArrays : Bool

def entryOf (j : Json) : Option Entry := do
  let input ← j.getString? "input"
  let types := match j.field? "@type" with
    | some (.array xs) => xs.filterMap Json.asString?
    | some (.string s) => [s]
    | _ => []
  let opt := j.field? "option"
  let optBool (k : String) (d : Bool) : Bool := (opt.bind (fun o => o.getBool? k)).getD d
  let algo :=
    if types.contains "jld:ToRDFTest" then "toRdf"
    else if types.contains "jld:CompactTest" then "compact"
    else if types.contains "jld:FlattenTest" then "flatten"
    else if types.contains "jld:FrameTest" then "frame"
    else "expand"
  pure { id := (j.getString? "@id").getD "?", name := (j.getString? "name").getD "",
         negative := types.contains "jld:NegativeEvaluationTest", algo := algo, input := input,
         expect := j.getString? "expect", context := j.getString? "context",
         frame := j.getString? "frame", errorCode := j.getString? "expectErrorCode",
         extractAll := optBool "extractAllScripts" false, extended := optBool "extendedYAML" false,
         normative := optBool "normative" true, compactArrays := optBool "compactArrays" true }

def isYamlPath (p : String) : Bool := p.endsWith ".yamlld" || p.endsWith ".yaml"

/-- The expected document as a JSON value. -/
def loadExpected (dir : System.FilePath) (rel : String) : IO (Option Json) := do
  match ← readFileOpt (dir / rel) with
  | none => pure none
  | some txt =>
    if isYamlPath rel then pure (load txt { extended := true }).toOption
    else pure (parseJson txt).toOption

inductive Outcome where
  | pass
  | fail (why : String)

def truncate (n : Nat) (s : String) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.take n) ++ " …"

/-- Produce the output of an entry: a JSON value or a dataset. -/
def runAlgo (loader : Loader) (dir : System.FilePath) (baseIri : String) (e : Entry)
    : IO (Except YamlLdError (Json ⊕ Dataset)) := do
  let opts : Options := { extractAllScripts := e.extractAll, extended := e.extended }
  let base := some (baseIri ++ e.input)
  match ← readBytesOpt (dir / e.input) with
  | none => pure (.error (.loadingDocumentFailed s!"input file not found: {e.input}"))
  | some bytes =>
    match decodeUtf8 bytes with
    | .error err => pure (.error err)
    | .ok text =>
      if e.input.endsWith ".html" then
        let base := match Html.extractHtmlBase text with
          | some hb => some (resolveIri (baseIri ++ e.input) hb)
          | none => base
        match loadHtml text none opts with
        | .error err => pure (.error err)
        | .ok none => pure (.error (.jsonLd .loadingDocumentFailed))
        | .ok (some root) =>
          if e.algo == "toRdf" then
            pure ((liftJsonLd (parseJsonLdRoot loader root base none none none)).map .inr)
          else pure ((liftJsonLd (expandRoot loader root base none none)).map .inl)
      else
        match e.algo with
        | "toRdf" => pure ((toRdfYamlLd loader text base none none none opts).map .inr)
        | "compact" =>
          match e.context with
          | none => pure (.error (.loadingDocumentFailed "no context"))
          | some c =>
            match ← readFileOpt (dir / c) with
            | none => pure (.error (.loadingDocumentFailed s!"context not found: {c}"))
            | some ctx =>
              pure ((compactYamlLd loader text ctx (isYamlPath c) base (some (baseIri ++ c))
                      e.compactArrays true none opts).map .inl)
        | "flatten" =>
          let ctx ← match e.context with
            | none => pure none
            | some c => pure ((← readFileOpt (dir / c)).map (fun t => (t, isYamlPath c)))
          pure ((flattenYamlLd loader text ctx base (e.context.map (baseIri ++ ·))
                  e.compactArrays none opts).map .inl)
        | "frame" =>
          match e.frame with
          | none => pure (.error (.loadingDocumentFailed "no frame"))
          | some f =>
            match ← readFileOpt (dir / f) with
            | none => pure (.error (.loadingDocumentFailed s!"frame not found: {f}"))
            | some fr => pure ((frameYamlLd loader text fr (isYamlPath f) base none opts).map .inl)
        | _ => pure ((expandYamlLd loader text base none none opts).map .inl)

def runEntry (loader : Loader) (dir : System.FilePath) (baseIri : String) (e : Entry) : IO Outcome := do
  let got ← runAlgo loader dir baseIri e
  if e.negative then
    match got with
    | .error err =>
      if e.errorCode == some err.code then pure .pass
      else pure (.fail s!"failed with \"{err.code}\" ({err.detail}); the manifest expects \"{e.errorCode.getD "?"}\"")
    | .ok _ => pure (.fail s!"succeeded; the manifest expects the error \"{e.errorCode.getD "?"}\"")
  else
    match e.expect with
    | none => pure (.fail "no expect file")
    | some x =>
      match got with
      | .error err => pure (.fail s!"failed with \"{err.code}\": {err.detail}")
      | .ok (.inr ds) =>
        match ← readFileOpt (dir / x) with
        | none => pure (.fail s!"expected file not found: {x}")
        | some nq =>
          let exp := parseNQuadsLenient nq
          if ds.isomorphic? exp || ds.canonicalNQuads == exp.canonicalNQuads then pure .pass
          else pure (.fail s!"dataset differs\n      expected:\n{truncate 500 exp.canonicalNQuads}\n      got:\n{truncate 500 ds.canonicalNQuads}")
      | .ok (.inl j) =>
        match ← loadExpected dir x with
        | none => pure (.fail s!"expected file does not load: {x}")
        | some exp =>
          if sameJson j exp then pure .pass
          else pure (.fail s!"output differs\n      expected: {truncate 500 (jcsDocument exp)}\n      got:      {truncate 500 (jcsDocument j)}")

/-- Cases with defective test data (skills/test-suites § Defective test data),
evidence in https://github.com/danbri/factoidal/issues/1182. -/
def defectiveIssue : String := "https://github.com/danbri/factoidal/issues/1182"

def defective : List String :=
  ["#cir-scalar-other-2-positive",
   "#core-bool-true", "#core-bool-false", "#core-bool-true-title", "#core-bool-false-upper",
   "#core-null-null", "#core-null-tilde", "#core-null-upper",
   "#core-int-decimal", "#core-int-octal", "#core-int-hex",
   "#core-float-basic", "#core-float-scientific", "#core-date-ymd",
   "#core-yaml11-yes", "#core-yaml11-no", "#core-yaml11-on", "#core-yaml11-off",
   "#core-yaml11-yes-title", "#core-yaml11-yes-upper"]

/-- The `core-*` context file with its body under an `@context` entry, as
JSON-LD 1.1 API §4.1.2 step 5.2.5 requires (a measurement only, not a score). -/
def repairContext (inner : Loader) : Loader := fun url =>
  match inner url with
  | some body =>
    if url.endsWith "yaml-schema/context.yamlld" then
      some ("\"@context\":\n" ++ String.intercalate "\n" ((body.splitOn "\n").map ("  " ++ ·)))
    else some body
  | none => none

def buildLoader (dir cacheDir : System.FilePath) (baseIri : String) (repair : Bool := false) : IO Loader := do
  let rels ← walkDir 5 dir ""
  let mut files : List (String × String) := []
  for r in rels.filter (fun r => r.endsWith ".jsonld" || r.endsWith ".json" || isYamlPath r) do
    match ← readFileOpt (dir / r) with
    | some body => files := (r, body) :: files
    | none => pure ()
  let mut cache : List (String × String) := []
  match ← readFileOpt (cacheDir / "index.json") with
  | some idxTxt =>
    match parseJson idxTxt with
    | .ok idx =>
      for ce in cacheTableOfIndex idx do
        match ← readFileOpt (cacheDir / ce.path) with
        | some body => cache := (ce.url, body) :: cache
        | none => pure ()
    | .error _ => pure ()
  | none => pure ()
  let base := Loader.orElse (prefixLoader baseIri files) (tableLoader cache)
  pure (yamlAwareLoader (if repair then repairContext base else base))

/-- `--json-superset`: every JSON-LD 1.1 suite input through the YAML loader. -/
def jsonSuperset (dir : System.FilePath) : IO UInt32 := do
  let rels := (← walkDir 4 dir "").filter (·.endsWith ".jsonld")
  if rels.isEmpty then
    IO.eprintln s!"l4yamlld: no .jsonld files under {dir}; run tools/ensure-test-env.sh"
    return 2
  let mut same := 0
  let mut differ : List String := []
  let mut notJson := 0
  for r in rels do
    match ← readFileOpt (dir / r) with
    | none => pure ()
    | some txt =>
      match parseJson txt with
      | .error _ => notJson := notJson + 1
      | .ok j =>
        match L4Factoidal.YAML.loadStream txt with
        | .ok [y] => if y == j then same := same + 1 else differ := s!"{r}: another value" :: differ
        | .ok l => differ := s!"{r}: {l.length} documents" :: differ
        | .error err => differ := s!"{r}: {err.message}" :: differ
  IO.println s!"json-superset: {same} same, {differ.length} differ (out of {same + differ.length} JSON texts; {notJson} files are not JSON and were skipped)"
  for d in differ.reverse do IO.println s!"  {d}"
  return (if differ.isEmpty then 0 else 1)

/-- `--scale n`: a block mapping, a block sequence and a flow sequence of
`n`, `2n` and `4n` entries, and a double-quoted scalar of as many
characters, each loads with the right size. The loops over entries and
characters are tail calls, so the stack does not grow with `n`
(skills/danbri-function-precrime-checkers). -/
def scaleCase (kind : String) (n : Nat) : String × (Json → Bool) :=
  let ks := (List.range n).map toString
  match kind with
  | "map" => (String.join (ks.map (fun k => s!"k{k}: v\n")),
              fun j => match j with | .object fs => fs.length == n | _ => false)
  | "seq" => (String.join (ks.map (fun k => s!"- {k}\n")),
              fun j => match j with | .array xs => xs.length == n | _ => false)
  | "flow" => ("[" ++ String.intercalate ", " ks ++ "]\n",
               fun j => match j with | .array xs => xs.length == n | _ => false)
  | _ => ("\"" ++ String.ofList (List.replicate n 'x') ++ "\"\n",
          fun j => match j with | .string t => t.length == n | _ => false)

def scale (n : Nat) : IO UInt32 := do
  let mut bad := 0
  for kind in ["map", "seq", "flow", "quoted"] do
    for m in [n, 2 * n, 4 * n] do
      let (txt, ok) := scaleCase kind m
      let t0 ← IO.monoMsNow
      let r := L4Factoidal.YAML.loadStream txt
      let good := match r with | .ok [j] => ok j | _ => false
      let t1 ← IO.monoMsNow
      IO.println s!"scale {kind} {m}: {if good then "ok" else "FAIL"} {t1 - t0} ms"
      if !good then bad := bad + 1
  IO.println s!"scale: {12 - bad} pass, {bad} fail (out of 12)"
  return (if bad == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--scale" then
    return ← scale ((args.tail.head?.bind String.toNat?).getD 100000)
  if args.head? == some "--json-superset" then
    return ← jsonSuperset (args.tail.head?.getD "third_party/testing/json-ld/tests")
  let dir : System.FilePath := args.head?.getD "third_party/testing/yaml-ld/tests"
  let cacheDir : System.FilePath := "third_party/jsonld-context-cache"
  match ← readFileOpt (dir / "manifest.jsonld") with
  | none =>
    IO.eprintln s!"l4yamlld: manifest not found under {dir}"
    return 2
  | some raw =>
    match parseJson raw with
    | .error _ =>
      IO.eprintln "l4yamlld: manifest is not JSON"
      return 2
    | .ok m =>
      let baseIri := (m.getString? "baseIri").getD "https://w3c.github.io/yaml-ld/tests/"
      let entries := ((m.getArray? "sequence").getD []).filterMap entryOf
      let loader ← buildLoader dir cacheDir baseIri
      let mut pass := 0
      let mut fails : List String := []
      let mut excluded : List String := []
      let mut infPass := 0
      let mut infTotal := 0
      for e in entries do
        let o ← runEntry loader dir baseIri e
        if defective.contains e.id then
          match o with
          | .pass => fails := s!"{e.id}: STALE exclusion, the case passes; remove it from `defective` and close {defectiveIssue}" :: fails
          | .fail _ => excluded := e.id :: excluded
          continue
        if !e.normative then infTotal := infTotal + 1
        match o with
        | .pass =>
          pass := pass + 1
          if !e.normative then infPass := infPass + 1
        | .fail why => fails := s!"{e.id} [{e.algo}] {e.name}: {why}" :: fails
      let total := entries.length - excluded.length
      IO.println s!"yaml-ld: {pass} pass, {fails.length} fail (out of {total}); {excluded.length} excluded (defective test data)"
      IO.println s!"  of these, Extended Profile (normative: false): {infPass} pass, {infTotal - infPass} fail (out of {infTotal})"
      for x in excluded.reverse do IO.println s!"  EXCLUDED {x}: defective test data, {defectiveIssue}"
      -- the core-* cases with their context file repaired
      let repaired ← buildLoader dir cacheDir baseIri (repair := true)
      let core := entries.filter (fun e => e.id.startsWith "#core-" && !e.negative && defective.contains e.id)
      let mut corePass := 0
      for e in core do
        -- core-null-*: the expected `{"@id": ...}` is itself contrary to JSON-LD 1.1
        -- API §5.1.2 step 19.2 (a top-level map whose only entry is @id is dropped),
        -- so the check expects the empty array there (same issue).
        if e.id.startsWith "#core-null-" then
          match ← runAlgo repaired dir baseIri e with
          | .ok (.inl (.array [])) => corePass := corePass + 1
          | _ => IO.println s!"  repaired-context check fails: {e.id}: expected []"
        else
          match ← runEntry repaired dir baseIri e with
          | .pass => corePass := corePass + 1
          | .fail why => IO.println s!"  repaired-context check fails: {e.id}: {why}"
      IO.println s!"  check, core-* with context.yamlld under \"@context\": {corePass} pass, {core.length - corePass} fail (out of {core.length})"
      if !fails.isEmpty then
        IO.println "  failures:"
        for f in fails.reverse do IO.println s!"    {f}"
      return (if fails.isEmpty && corePass == core.length then 0 else 1)

end YamlLdRun

def main (args : List String) : IO UInt32 := YamlLdRun.main args
