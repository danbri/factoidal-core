/-
Wasm.Cli — `l4factoidal`, a real command-line interface to the Lean 4
engine, so a person or a script can use it without knowing the
dispatch ABI (`Wasm/Dispatch.lean`).

This module is thin argument parsing and JSON-envelope decoding ONLY
(`parse` without `--out` asks `Ops.parseTextToDataset` for the dataset and
prints the size of its RDF 1.1 Concepts normal form, see `parseCountOutput`).
Every verb below calls one of the `Wasm/Ops/*.lean` functions the wasm
build and `l4wasm-cli` also call — the same `parseToDatasetJson`,
`queryDataset`, `owlClosure`, `clParse`, … — and prints the field a
person wants from the envelope those functions already return. No RDF,
SPARQL, OWL or CL semantics live here.

The verbs that read RDF (`query`, `update`, `canonicalize`, `closure`,
`owl-consistent`, `owl-entails`) give the op the PARSED dataset through the
`*Of` forms (`Ops.queryDatasetOf`, ...). Until 2026-10-10 they wrote the
dataset as canonical N-Quads and the op parsed the text again
(https://github.com/danbri/factoidal/issues/724). Each `*Of` op is proved to
answer the envelope the text op answers on that text (`queryDatasetOf_eq`,
`canonicalizeOf_eq`, ...; `RDF/DatasetNormalize.lean`), so the printed
output, row order included, is unchanged.

  l4factoidal parse data.ttl --out nquads
  l4factoidal query data.ttl --query-string 'SELECT * WHERE { ?s ?p ?o }'
  l4factoidal help          -- full verb list

`l4wasm-cli` (`Wasm/Main.lean`) stays as it is — the ABI smoke driver
`Wasm/native-smoke.sh` pins — and is unaffected by this module.
-/
import Wasm.Abi
import Wasm.Dispatch
import L4Factoidal.Syntax.LenientFeed
import L4Factoidal.Syntax.FileIri

namespace L4Wasm.Cli

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON
open L4Wasm.Ops

/-! ## Argument scanning

A minimal flag scanner shared by every verb: `--flag value` pairs
(`valueFlags`), bare boolean flags (`boolFlags`), everything else
positional, in the order given. No logic beyond bucketing strings. -/

structure Scanned where
  positional : List String := []
  values     : List (String × String) := []
  bools      : List String := []

/-- Bucket `args` into positionals / `--flag value` pairs / bare
boolean flags. An unrecognised `--…` token, or a value flag with
nothing after it, is a usage error. Structurally recursive on the
remaining argument list. -/
def scanArgs (valueFlags boolFlags : List String) :
    List String → Except String Scanned
  | [] => .ok {}
  | a :: rest =>
      if boolFlags.contains a then
        (scanArgs valueFlags boolFlags rest).map fun s =>
          { s with bools := a :: s.bools }
      else if valueFlags.contains a then
        match rest with
        | [] => .error s!"{a}: missing value"
        | v :: rest' =>
            (scanArgs valueFlags boolFlags rest').map fun s =>
              { s with values := (a, v) :: s.values }
      else if a.take 2 == "--" then
        .error s!"unknown flag '{a}'"
      else
        (scanArgs valueFlags boolFlags rest).map fun s =>
          { s with positional := a :: s.positional }

def Scanned.value? (s : Scanned) (flag : String) : Option String :=
  (s.values.find? (fun kv => kv.1 == flag)).map Prod.snd

def Scanned.hasBool (s : Scanned) (flag : String) : Bool :=
  s.bools.contains flag

/-! ## Input reading

Every read goes through here so a missing file or an unreadable stdin
reports as ONE clean stderr line and exit 1, never a raw Lean
exception trace. -/

/-- Read `pathOpt` — a file, or `none` / `some "-"` for stdin. -/
def readInput (pathOpt : Option String) : IO (Except String String) := do
  match pathOpt with
  | none | some "-" =>
      try
        let t ← (← IO.getStdin).readToEnd
        pure (.ok t)
      catch e =>
        pure (.error s!"stdin: {e}")
  | some path =>
      try
        let t ← IO.FS.readFile path
        pure (.ok t)
      catch e =>
        pure (.error s!"{path}: {e}")

/-- Read `pathOpt` under `formatTag`/`baseIri` via the SAME
`parseTextToDataset` the dispatch ops use — the input path every
RDF-consuming verb below shares (`query`, `update`, `canonicalize`,
`closure`, `owl-consistent`, `owl-entails`). The verb hands the dataset to
an `Ops.*Of` function, which gives the op what the N-Quads text round trip
would have given it (`Wasm/Ops/FromDataset.lean`). -/
def readDataset (pathOpt : Option String) (formatTag baseIri : String) :
    IO (Except String Dataset) := do
  match ← readInput pathOpt with
  | .error e => pure (.error e)
  | .ok text => pure (Ops.parseTextToDataset text formatTag baseIri)

/-- Resolve a `--foo FILE` / `--foo-string TEXT` pair (exactly one of
the two) into the text it names — shared by `query` and `update`.
The `Except UInt32` error already carries the exit code
the caller should return (2 for a usage mistake). -/
def resolveTextArg (verb fileFlag strFlag what : String) (s : Scanned) :
    IO (Except UInt32 String) := do
  match s.value? fileFlag, s.value? strFlag with
  | some _, some _ =>
      IO.eprintln s!"l4factoidal {verb}: pass only one of {fileFlag} / {strFlag}"
      pure (.error 2)
  | some f, none =>
      match ← readInput (some f) with
      | .error e => IO.eprintln e; pure (.error 1)
      | .ok t => pure (.ok t)
  | none, some txt => pure (.ok txt)
  | none, none =>
      IO.eprintln s!"l4factoidal {verb}: need {fileFlag} FILE or {strFlag} {what}"
      pure (.error 2)

/-- The base IRI of the query or update text that `--foo FILE` /
`--foo-string TEXT` names (SPARQL 1.1 §4.1.1.2 resolves a relative IRI in it
with RFC 3986 §5.1; https://github.com/danbri/factoidal/issues/741). A text
read from FILE has the file's IRI (§5.1.3, the retrieval URI;
`fileIriOfPath` of the real path). A text given on the command line, or read
from stdin (`-`), has `--base` (an empty value means no base). A `BASE` in the
text comes before either (§5.1.1); the parser applies it. -/
def textBaseArg (fileFlag : String) (s : Scanned) : IO (Except String (Option String)) := do
  let cliBase := (s.value? "--base").bind fun b => if b.isEmpty then none else some b
  match s.value? fileFlag with
  | none | some "-" => pure (.ok cliBase)
  | some f =>
      try
        let abs ← IO.FS.realPath f
        pure (.ok (some (fileIriOfPath abs.toString)))
      catch e =>
        pure (.error s!"{f}: {e}")

/-! ## JSON envelope decoding

Every op answers `{"ok":true,…}` or `{"ok":false,"error":"…"}`
(`Wasm/Ops/Support.lean`). Decode once, print the error and hand back
`none` on failure, so every verb below shares one error path. -/

/-- Decode an op's JSON envelope. `none` means the error is already
printed to stderr; the caller returns exit 1. -/
def parseEnvelope (raw : String) : IO (Option Json) := do
  match parseJson raw with
  | .error e =>
      IO.eprintln s!"internal: op result was not JSON ({toString e})"
      pure none
  | .ok j =>
      if j.getBool? "ok" == some true then
        pure (some j)
      else
        IO.eprintln ((j.getString? "error").getD "unknown error")
        pure none

/-- A JSON NUMBER field (RFC 8259 §6 lexeme, kept verbatim by
`L4Factoidal.JSON` — see `JSON/Value.lean`'s module header), e.g.
`parseToDatasetJson`'s `"count"`. `Json.getString?` does not see this
field: it matches `.string` only, never `.number`. -/
def numberField? (j : Json) (key : String) : Option String :=
  match j.field? key with
  | some (.number s) => some s
  | _ => none

/-- `{"fuel":"<n>"}` or `""` — the `optsJson` argument `owlIsConsistent`
/ `owlEntails` take (`Wasm/Ops/Reason.lean`'s `owlRefuteFuelOfOpts`). -/
def optsJsonOfFuel : Option String → String
  | none => ""
  | some fuel => (Json.object [("fuel", Json.string fuel)]).toString

/-- Print a three-valued verdict field (`consistent` / `entailed`):
`true`/`false`/`unknown` to stdout, the `reason` (present on
`false`/`null`) to stderr. Exit 0 for `true`, 1 for `false` or
`unknown` — a verdict this CLI cannot tell apart from a plain failure
by exit code alone, so a script that must distinguish "refuted" from
"budget-out, raise --fuel" reads stdout, not just `$?`. -/
def printVerdict (j : Json) (key : String) : IO UInt32 := do
  let printReason : IO Unit :=
    match j.getString? "reason" with
    | some r => IO.eprintln r
    | none => pure ()
  match j.field? key with
  | some (.bool true) => IO.println "true"; pure 0
  | some (.bool false) => IO.println "false"; printReason; pure 1
  | some .null => IO.println "unknown"; printReason; pure 1
  | _ =>
      IO.eprintln s!"internal: '{key}' verdict missing or malformed"
      pure 1

/-! ## SELECT results: SPARQL Results JSON, or `--table` -/

def bindingValue? (row : Json) (v : String) : Option String :=
  (row.field? v).bind (fun t => t.getString? "value")

/-- Tab-separated: a header row of variable names, then one row per
binding (unbound = empty cell). Not a replacement for the JSON form —
a quick-look shortcut for a terminal or a shell pipeline. -/
def printSelectTable (srj : Json) : IO Unit := do
  let vars := ((srj.field? "head").bind (fun h => h.getStringArray? "vars")).getD []
  IO.println (String.intercalate "\t" vars)
  let rows := ((srj.field? "results").bind (fun r => r.getArray? "bindings")).getD []
  for row in rows do
    IO.println (String.intercalate "\t" (vars.map fun v => (bindingValue? row v).getD ""))

/-- Print the `queryDataset` envelope family
(select/ask/construct/describe; an error envelope is handled by
`parseEnvelope`). -/
def printQueryResult (j : Json) (table : Bool) : IO UInt32 := do
  match j.getString? "kind" with
  | some "ask" =>
      match j.getBool? "boolean" with
      | some true => IO.println "true"; pure 0
      | some false => IO.println "false"; pure 1
      | none => IO.eprintln "internal: ask result missing boolean"; pure 1
  | some "construct" | some "describe" =>
      IO.println ((j.getString? "nquads").getD "")
      pure 0
  | some "select" =>
      match j.field? "srj" with
      | none => IO.eprintln "internal: select result missing srj"; pure 1
      | some srj =>
          if table then printSelectTable srj else IO.println srj.toStringPretty
          pure 0
  | _ =>
      IO.eprintln "internal: unrecognised query result kind"
      pure 1

/-! ## Verbs -/

def versionCmd : IO UInt32 := do
  IO.println L4Wasm.version
  IO.println s!"dispatch ABI: {L4Wasm.dispatchAbiVersion}"
  pure 0

def opsCmd : IO UInt32 := do
  let raw ← L4Wasm.callIO "ops" "[]"
  match parseJson raw with
  | .ok j => IO.println j.toStringPretty
  | .error _ => IO.println raw
  pure 0

/-! ## `parse --lenient`: streaming recovery mode (issue 716)

The library does the parsing (`Syntax/LenientFeed.lean`); this section reads
the file in 65,536-byte chunks, writes each chunk's diagnostics to stderr as
JSON lines (`Ops.diagnosticJson`, the `parseDocument` shape) and its kept
quads to stdout (with `--out nquads`) before reading the next chunk. -/

def lenientChunkBytes : USize := 65536

/-- Read `h` chunk by chunk, at most `fuel` chunks, stopping early when
`stop` holds. The `Bool` is `true` when the end of the file was reached (or
`stop` held). Structural recursion on `fuel`. -/
def forChunks {α : Type} (h : IO.FS.Handle) (stop : α → Bool)
    (f : α → ByteArray → IO (Except String α)) : Nat → α → IO (Except String (α × Bool))
  | 0, a => pure (.ok (a, false))
  | n + 1, a => do
      if stop a then return .ok (a, true)
      let bytes ← h.read lenientChunkBytes
      if bytes.isEmpty then return .ok (a, true)
      match ← f a bytes with
      | .error e => pure (.error e)
      | .ok a' => forChunks h stop f n a'

def printDiagnostics (ds : List Diagnostic) : IO Unit := do
  let err ← IO.getStderr
  for d in ds do err.putStrLn (Ops.diagnosticJson d).toString
  err.flush

def printLines (ls : List String) : IO Unit := do
  let out ← IO.getStdout
  for l in ls do out.putStr l
  out.flush

/-- `parse --lenient`, streaming a FILE. `none` when the format has no
streaming execution (TriG) — the caller then reads the file whole. -/
def streamLenientFile (path : String) (mode : Mode) (tag base : String) (emit : Bool)
    (opts : LenientOptions) : IO (Option (Except String (Nat × Nat))) := do
  let size := (← System.FilePath.metadata path).byteSize.toNat
  let fuel := size / lenientChunkBytes.toNat + 2
  let baseOpt : Option String := if base == "" then none else some base
  let feed? : Option (IO (Except String LenientFeed)) :=
    match tag with
    | "ntriples" | "nt" | "n-triples" =>
        some (pure (.ok (LenientFeed.initLines mode true emit opts)))
    | "nquads" | "nq" | "n-quads" =>
        some (pure (.ok (LenientFeed.initLines mode false emit opts)))
    | "" | "turtle" | "ttl" =>
        some (do
          let pre ← IO.FS.withFile path .read fun h =>
            forChunks h (fun (_ : LenientPrepass) => false)
              (fun (p : LenientPrepass) b => pure (p.feed b)) fuel ({} : LenientPrepass)
          match pre with
          | .error e => pure (.error e)
          | .ok (_, false) => pure (.error "the file grew while it was read")
          | .ok (p, true) =>
              pure ((LenientPrepass.finish p).map fun pfx =>
                LenientFeed.initTurtle pfx baseOpt mode emit opts))
    | _ => none
  match feed? with
  | none => pure none
  | some mk =>
    match ← mk with
    | .error e => pure (some (.error e))
    | .ok feed0 =>
      let walked ← IO.FS.withFile path .read fun h =>
        forChunks h (fun (fd : LenientFeed × Nat) => fd.1.stopped)
          (fun (fd : LenientFeed × Nat) bytes => do
            match fd.1.feed bytes with
            | .error e => pure (.error e)
            | .ok (f', out) =>
                printDiagnostics out.diags
                printLines out.lines
                pure (.ok (f', fd.2 + out.diags.length)))
          fuel (feed0, 0)
      match walked with
      | .error e => pure (some (.error e))
      | .ok (_, false) => pure (some (.error "the file grew while it was read"))
      | .ok ((f, n), true) =>
          match f.finish with
          | .error e => pure (some (.error e))
          | .ok (out, count, _) =>
              printDiagnostics out.diags
              printLines out.lines
              pure (some (.ok (count, n + out.diags.length)))

/-- `parse --lenient`. Exit 1 when any diagnostic was written. The count it
prints is the number of statements read: a repeated triple counts each time.
Strict `parse` counts the normalised dataset (`parseCountOutput`, issue 724);
removing repeats here would need memory that grows with the input, which the
streaming recovery mode must not use (issue 716). -/
def parseLenientCmd (s : Scanned) : IO UInt32 := do
  let format := (s.value? "--format").getD "turtle"
  let base := (s.value? "--base").getD ""
  let emit ← match s.value? "--out" with
    | none => pure (some false)
    | some "nquads" => pure (some true)
    | some other =>
        IO.eprintln s!"l4factoidal parse --lenient: --out '{other}' is not available (nquads)"
        pure none
  match emit with
  | none => pure 2
  | some emit =>
  let maxErrors ← match s.value? "--max-errors" with
    | none => pure (some none)
    | some n => match n.toNat? with
      | some m => pure (some (some m))
      | none => IO.eprintln s!"l4factoidal parse: --max-errors '{n}' is not a number"; pure none
  match maxErrors with
  | none => pure 2
  | some maxErrors =>
  let opts : LenientOptions := { maxErrors }
  let (mode, tag) := Ops.resolveModeAndTag format
  if !["", "turtle", "ttl", "ntriples", "nt", "n-triples", "nquads", "nq", "n-quads", "trig"].contains tag then
    IO.eprintln s!"l4factoidal parse --lenient: format '{format}' has no lenient mode (turtle | trig | ntriples | nquads)"
    return 2
  let streamed ← match s.positional[0]? with
    | none | some "-" => pure none
    | some path =>
        try streamLenientFile path mode tag base emit opts
        catch e => pure (some (.error s!"{path}: {e}"))
  let result ← match streamed with
    | some r => pure r
    | none => do
        -- stdin, or TriG: the whole text through the reference walk.
        match ← readInput s.positional[0]? with
        | .error e => pure (.error e)
        | .ok text =>
            match Ops.lenientDocumentOutcome text format base opts with
            | .error f => pure (.error f.message)
            | .ok (o, ds) =>
                printDiagnostics ds
                if emit then printLines [Dataset.toCanonicalNQuads o.ds]
                pure (.ok (Ops.datasetQuadCount o.ds, ds.length))
  match result with
  | .error e => IO.eprintln s!"l4factoidal parse: {e}"; pure 1
  | .ok (count, nDiags) =>
      if !emit then IO.println (toString count)
      pure (if nDiags > 0 then 1 else 0)

/-- The text `parse` prints when `--out` is absent: the number of quads of
the parsed dataset in its RDF 1.1 Concepts normal form (`normalizeDataset`:
§3, "An RDF graph is a set of RDF triples", so a repeated triple counts once;
§3.3, language tags in lower case), or the parser's error text. It is the
dataset `query` and the other verbs evaluate on (issue 724), so `parse` and a
`COUNT(*)` query over the default graph agree. -/
def parseCountOutput (text format base : String) : Except String String :=
  match Ops.parseTextToDataset text format base with
  | .error msg => .error msg
  | .ok ds => .ok (toString (Ops.datasetQuadCount (normalizeDataset ds)))

/-- The same text read back out of the envelope: what `parse` printed before
2026-10-10, kept so the guards below can compare the two. -/
private def parseCountViaEnvelope (text format base : String) : Except String String :=
  match parseJson (Ops.parseToDatasetJson text format base) with
  | .error e => .error s!"internal: op result was not JSON ({toString e})"
  | .ok j =>
      if j.getBool? "ok" == some true then .ok ((numberField? j "count").getD "0")
      else .error ((j.getString? "error").getD "unknown error")

private def sameOutput : Except String String → Except String String → Bool
  | .ok a,    .ok b    => a == b
  | .error a, .error b => a == b
  | _,        _        => false

private def sampleNt : String :=
  "<http://e/a> <http://e/p> <http://e/b> .\n<http://e/a> <http://e/p> \"x\"@en .\n"
private def sampleTtl : String :=
  "@prefix e: <http://e/> . e:a e:p e:b, e:c ; e:q [ e:r 1 ] ."

-- The direct count is the count in the envelope, for each format and for errors.
#guard sameOutput (parseCountOutput sampleNt "ntriples" "") (parseCountViaEnvelope sampleNt "ntriples" "")
#guard sameOutput (parseCountOutput sampleTtl "turtle" "") (parseCountViaEnvelope sampleTtl "turtle" "")
#guard sameOutput (parseCountOutput "<http://e/g> { <http://e/a> <http://e/p> <http://e/b> }" "trig" "")
  (parseCountViaEnvelope "<http://e/g> { <http://e/a> <http://e/p> <http://e/b> }" "trig" "")
#guard sameOutput (parseCountOutput "<http://e/a> <http://e/p> <http://e/b> <http://e/g> ." "nquads" "")
  (parseCountViaEnvelope "<http://e/a> <http://e/p> <http://e/b> <http://e/g> ." "nquads" "")
#guard sameOutput (parseCountOutput "" "ntriples" "") (parseCountViaEnvelope "" "ntriples" "")
#guard sameOutput (parseCountOutput "<http://e/a> <http://e/p>" "ntriples" "")
  (parseCountViaEnvelope "<http://e/a> <http://e/p>" "ntriples" "")
#guard sameOutput (parseCountOutput sampleNt "bogus" "") (parseCountViaEnvelope sampleNt "bogus" "")
-- Teeth: the values are the expected ones, so two functions that both returned
-- "0", or both failed, would not pass.
#guard parseCountOutput sampleNt "ntriples" "" matches .ok "2"
#guard parseCountOutput sampleTtl "turtle" "" matches .ok "4"
#guard parseCountOutput "" "ntriples" "" matches .ok "0"
#guard parseCountOutput "<http://e/a> <http://e/p>" "ntriples" "" matches .error _
#guard parseCountOutput sampleNt "bogus" "" matches .error _
#guard !sameOutput (.ok "2") (.ok "3")
#guard !sameOutput (.ok "2") (.error "2")

/-- Issue 724's example: one triple written twice, a tag in upper case. -/
private def sampleRepeat : String :=
  "@prefix e: <http://e/> .\ne:a e:p e:b .\ne:a e:p e:b .\ne:a e:q \"x\"@EN ."

/-- The count a `COUNT(*)` query over the parsed text answers, through the
command line's own path. -/
private def queryCountOf (text : String) : Option String :=
  match Ops.parseTextToDataset text "turtle" "" with
  | .error _ => none
  | .ok ds =>
      match parseJson (Ops.queryDatasetOf ds "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }") with
      | .error _ => none
      | .ok j =>
          ((j.field? "srj").bind (fun srj => (srj.field? "results").bind
            (fun r => r.getArray? "bindings"))).bind fun rows =>
              rows.head?.bind (fun row => bindingValue? row "c")

-- `parse` counts the set: 2, where the envelope of the parser's list said 3.
#guard parseCountOutput sampleRepeat "turtle" "" matches .ok "2"
#guard parseCountViaEnvelope sampleRepeat "turtle" "" matches .ok "3"
-- And `query` COUNT(*) on the same text says 2 as well.
#guard queryCountOf sampleRepeat == some "2"
#guard queryCountOf sampleTtl == some "4"

def parseCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--out", "--max-errors"] ["--lenient"] args with
  | .error e => IO.eprintln s!"l4factoidal parse: {e}"; pure 2
  | .ok s =>
    if s.hasBool "--lenient" then parseLenientCmd s else
    let format := (s.value? "--format").getD "turtle"
    let base := (s.value? "--base").getD ""
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match s.value? "--out" with
      | none =>
          -- Count only. `parseToDatasetJson` also writes the whole dataset as
          -- N-Quads text inside a JSON string, and this verb would then parse
          -- that JSON again to read one number: about half of the instructions
          -- of `parse` on a 20,000-triple N-Triples file (survey of 2026-10-10,
          -- docs/designissues/2026-10-10-lean-vs-fstar-performance.md). The
          -- printed number and the error text are the ones the envelope carried.
          match parseCountOutput text format base with
          | .error msg => IO.eprintln msg; pure 1
          | .ok n => IO.println n; pure 0
      | some out =>
        -- The text is printed as the op computes it, without the JSON
        -- envelope `parseToDatasetJson` / `serializeTurtle` wrap it in and
        -- this verb used to decode again (issue 724). `--out nquads` is the
        -- envelope's `nquads` member, `Dataset.toCanonicalNQuads`;
        -- `--out turtle` is `serializeTurtle` on that text
        -- (`Ops.serializeTurtleTextOf_eq`).
        match Ops.parseTextToDataset text format base with
        | .error msg => IO.eprintln msg; pure 1
        | .ok ds =>
          match out with
          | "nquads" =>
              IO.println (Dataset.toCanonicalNQuads ds)
              pure 0
          | "turtle" =>
              match Ops.serializeTurtleTextOf ds with
              | .error e => IO.eprintln e; pure 1
              | .ok t => IO.println t; pure 0
          | other =>
              IO.eprintln s!"l4factoidal parse: unknown --out '{other}' (nquads | turtle)"
              pure 2

def queryCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--query", "--query-string"] ["--table"] args with
  | .error e => IO.eprintln s!"l4factoidal query: {e}"; pure 2
  | .ok s =>
    match ← resolveTextArg "query" "--query" "--query-string" "SPARQL" s with
    | .error code => pure code
    | .ok sparql =>
    match ← textBaseArg "--query" s with
    | .error e => IO.eprintln e; pure 1
    | .ok queryBase =>
      let format := (s.value? "--format").getD "turtle"
      let base := (s.value? "--base").getD ""
      match ← readDataset s.positional[0]? format base with
      | .error e => IO.eprintln e; pure 1
      | .ok ds =>
        match ← parseEnvelope (Ops.queryDatasetOf ds sparql queryBase) with
        | none => pure 1
        | some j => printQueryResult j (s.hasBool "--table")

def updateCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--update", "--update-string"] [] args with
  | .error e => IO.eprintln s!"l4factoidal update: {e}"; pure 2
  | .ok s =>
    match ← resolveTextArg "update" "--update" "--update-string" "SPARQL-UPDATE" s with
    | .error code => pure code
    | .ok upd =>
    match ← textBaseArg "--update" s with
    | .error e => IO.eprintln e; pure 1
    | .ok updateBase =>
      let format := (s.value? "--format").getD "turtle"
      let base := (s.value? "--base").getD ""
      match ← readDataset s.positional[0]? format base with
      | .error e => IO.eprintln e; pure 1
      | .ok ds =>
        match ← parseEnvelope (Ops.updateDatasetOf ds upd updateBase) with
        | none => pure 1
        | some j => IO.println ((j.getString? "nquads").getD ""); pure 0

def canonicalizeCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base"] [] args with
  | .error e => IO.eprintln s!"l4factoidal canonicalize: {e}"; pure 2
  | .ok s =>
    let format := (s.value? "--format").getD "nquads"
    let base := (s.value? "--base").getD ""
    match ← readDataset s.positional[0]? format base with
    | .error e => IO.eprintln e; pure 1
    | .ok ds =>
      match ← parseEnvelope (Ops.canonicalizeOf ds) with
      | none => pure 1
      | some j => IO.println ((j.getString? "nquads").getD ""); pure 0

def closureCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--regime"] [] args with
  | .error e => IO.eprintln s!"l4factoidal closure: {e}"; pure 2
  | .ok s =>
    match s.value? "--regime" with
    | none =>
        IO.eprintln "l4factoidal closure: need --regime rdfs|rho-df|rdfs-plus|owl-rl"
        pure 2
    | some regime =>
      if !(["rdfs", "owl-rl", "rho-df", "rdfs-plus"].contains regime) then
        IO.eprintln s!"l4factoidal closure: unknown --regime '{regime}' (rdfs | rho-df | rdfs-plus | owl-rl)"
        pure 2
      else
        let format := (s.value? "--format").getD "turtle"
        let base := (s.value? "--base").getD ""
        match ← readDataset s.positional[0]? format base with
        | .error e => IO.eprintln e; pure 1
        | .ok ds =>
          let raw :=
            match regime with
            | "rdfs"      => Ops.owlClosureOf ds "RDFS"
            | "owl-rl"    => Ops.owlClosureOf ds "OWL-RL"
            | "rho-df"    => Ops.rhoDfClosureOf ds
            | _           => Ops.rdfsPlusClosureOf ds
          match ← parseEnvelope raw with
          | none => pure 1
          | some j =>
              let out := (j.getString? "nquads") <|> (j.getString? "ntriples")
              IO.println (out.getD "")
              pure 0

def owlConsistentCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--fuel"] [] args with
  | .error e => IO.eprintln s!"l4factoidal owl-consistent: {e}"; pure 2
  | .ok s =>
    let format := (s.value? "--format").getD "turtle"
    let base := (s.value? "--base").getD ""
    let opts := optsJsonOfFuel (s.value? "--fuel")
    match ← readDataset s.positional[0]? format base with
    | .error e => IO.eprintln e; pure 1
    | .ok ds =>
      match ← parseEnvelope (Ops.owlIsConsistentOf ds opts) with
      | none => pure 1
      | some j => printVerdict j "consistent"

def owlEntailsCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--fuel"] [] args with
  | .error e => IO.eprintln s!"l4factoidal owl-entails: {e}"; pure 2
  | .ok s =>
    match s.positional[0]?, s.positional[1]? with
    | some premiseFile, some conclFile =>
        let format := (s.value? "--format").getD "turtle"
        let base := (s.value? "--base").getD ""
        let opts := optsJsonOfFuel (s.value? "--fuel")
        match ← readDataset (some premiseFile) format base with
        | .error e => IO.eprintln e; pure 1
        | .ok premiseDs =>
          match ← readDataset (some conclFile) format base with
          | .error e => IO.eprintln e; pure 1
          | .ok conclDs =>
            match ← parseEnvelope (Ops.owlEntailsOf premiseDs conclDs opts) with
            | none => pure 1
            | some j => printVerdict j "entailed"
    | _, _ =>
        IO.eprintln "l4factoidal owl-entails: need PREMISE_FILE CONCLUSION_FILE"
        pure 2

/-! ## `cl` — Common Logic / IKL -/

def clParseCmd (args : List String) : IO UInt32 := do
  match scanArgs [] [] args with
  | .error e => IO.eprintln s!"l4factoidal cl parse: {e}"; pure 2
  | .ok s =>
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match ← parseEnvelope (Ops.clParse text) with
      | none => pure 1
      | some j => IO.println j.toStringPretty; pure 0

/-- The three text-shaped CL ops share `cl parse`'s shape: read one
CLIF text, print one envelope. `label` is only for the error line. -/
def clTextCmd (label : String) (op : String → String) (args : List String) :
    IO UInt32 := do
  match scanArgs [] [] args with
  | .error e => IO.eprintln s!"l4factoidal cl {label}: {e}"; pure 2
  | .ok s =>
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match ← parseEnvelope (op text) with
      | none => pure 1
      | some j => IO.println j.toStringPretty; pure 0

/-- `cl finite-sat INTERP.json [FILE]` — the one CL op taking two
arguments. The interpretation is a FILE rather than a flag value: it is
a JSON document (see `Wasm/Ops/CL.lean`'s wire-format note), and a
shell quoting it inline is how a domain label acquires a stray quote. -/
def clFiniteSatCmd (args : List String) : IO UInt32 := do
  match scanArgs [] [] args with
  | .error e => IO.eprintln s!"l4factoidal cl finite-sat: {e}"; pure 2
  | .ok s =>
    match s.positional[0]? with
    | none =>
        IO.eprintln "l4factoidal cl finite-sat: need INTERP.json [FILE]"
        pure 2
    | some interpFile =>
      match ← readInput (some interpFile) with
      | .error e => IO.eprintln e; pure 1
      | .ok interpJson =>
        match ← readInput s.positional[1]? with
        | .error e => IO.eprintln e; pure 1
        | .ok text =>
          match ← parseEnvelope (Ops.clFiniteSat interpJson text) with
          | none => pure 1
          | some j => IO.println j.toStringPretty; pure 0

def clCmd (sub : String) (args : List String) : IO UInt32 :=
  match sub with
  | "parse"      => clParseCmd args
  | "serialize"  => clTextCmd "serialize" Ops.clSerialize args
  | "alpha-norm" => clTextCmd "alpha-norm" Ops.clAlphaNorm args
  | "normalize"  => clTextCmd "normalize" Ops.clNormalize args
  | "finite-sat" => clFiniteSatCmd args
  | other => do
      IO.eprintln s!"l4factoidal cl: unknown subcommand '{other}' \
(parse | serialize | alpha-norm | normalize | finite-sat)"
      pure 2

/-! ## Help + dispatch -/

def usageLines : List String :=
  [ "l4factoidal — Lean 4 RDF/SPARQL/OWL/CL engine, command line"
  , ""
  , "Usage: l4factoidal VERB [options] [FILE...]"
  , ""
  , "Verbs:"
  , "  parse [FILE] [--format FMT] [--base IRI] [--out nquads|turtle]"
  , "      Parse RDF and print the quad count, or (with --out) N-Quads"
  , "      or Turtle. FILE omitted or \"-\" reads stdin. FMT: turtle |"
  , "      ntriples | nquads | trig | rdfxml (default turtle)."
  , "  parse --lenient [FILE] [--format FMT] [--base IRI] [--max-errors N]"
  , "        [--out nquads]"
  , "      Recovery mode (turtle | trig | ntriples | nquads): skip each bad"
  , "      statement, write one JSON diagnostic per line to stderr"
  , "      ({message, offset, line, column, class}), keep the good ones."
  , "      A FILE is streamed in 64 KiB chunks (TriG and stdin are read"
  , "      whole). Prints the quad count, or with --out nquads the kept"
  , "      quads as they are read. Exit 1 when any diagnostic was written."
  , "  query [FILE] (--query FILE.rq | --query-string SPARQL)"
  , "        [--format FMT] [--base IRI] [--table]"
  , "      Run a SPARQL query. SELECT prints SPARQL Results JSON (or a"
  , "      tab-separated table with --table); ASK prints true/false,"
  , "      exit 0 for true and 1 for false; CONSTRUCT prints N-Triples."
  , "      --base IRI is the base of the data FILE and of a --query-string"
  , "      text; a --query FILE.rq resolves its relative IRIs against the"
  , "      file's own IRI (file:///...), and a BASE in the query comes first."
  , "  update [FILE] (--update FILE.ru | --update-string SPARQL-UPDATE)"
  , "        [--format FMT] [--base IRI]"
  , "      Apply a SPARQL Update and print the resulting N-Quads. The base"
  , "      of the update text is chosen as for query."
  , "  canonicalize [FILE] [--format FMT]"
  , "      RDFC-1.0 canonical N-Quads (default input format: nquads)."
  , "  closure [FILE] --regime rdfs|rho-df|rdfs-plus|owl-rl [--format FMT]"
  , "      Print the entailment closure (N-Quads, or N-Triples for"
  , "      rho-df / rdfs-plus)."
  , "  owl-consistent [FILE] [--format FMT] [--fuel N]"
  , "      Three-valued OWL DL consistency check: prints true, false,"
  , "      or unknown (budget-out; raise --fuel). Exit 0 for true,"
  , "      1 for false or unknown — read stdout to tell those apart."
  , "  owl-entails PREMISE_FILE CONCLUSION_FILE [--format FMT] [--fuel N]"
  , "      Three-valued OWL DL entailment check, same convention."
  , "  cl parse [FILE]"
  , "      Parse a Common Logic / IKL text; print sentence count,"
  , "      whether it is pure CL, and the canonical re-serialisation."
  , "  cl serialize [FILE]"
  , "      Re-serialise a CLIF text in canonical spacing. Reports"
  , "      roundTripProved:false — clif_roundTrip is an open lemma."
  , "  cl alpha-norm [FILE]"
  , "      Canonical representative of each sentence's"
  , "      alpha-equivalence class (bound names become v1, v2, …), so"
  , "      alpha-variants serialise byte-identically."
  , "  cl normalize [FILE]"
  , "      Hayes's reduction of IKL to Common Logic: a head text and a"
  , "      shared tail. Preserves SATISFIABILITY, not equivalence."
  , "      Reports noIntrusion — the proof hypothesis, decided; when it"
  , "      is false the output is outside what is proved."
  , "  cl finite-sat INTERP.json [FILE]"
  , "      Decide satisfaction of a CLIF text against the finite"
  , "      interpretation in INTERP.json. Refuses a text that"
  , "      quantifies a sequence marker, naming the condition."
  , "  version"
  , "      Print the engine version and the dispatch ABI version."
  , "  ops"
  , "      List every dispatch ABI operation (the l4wasm-cli / wasm"
  , "      surface this CLI is built on)."
  , ""
  , "Exit codes: 0 success/true, 1 failure/false/error, 2 usage error."
  ]

def usageText : String := String.intercalate "\n" usageLines

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "l4factoidal: missing verb (try 'l4factoidal help')"
      pure 2
  | "help" :: _ | "--help" :: _ | "-h" :: _ =>
      IO.println usageText
      pure 0
  | "version" :: _ => versionCmd
  | "ops" :: _ => opsCmd
  | "parse" :: rest => parseCmd rest
  | "query" :: rest => queryCmd rest
  | "update" :: rest => updateCmd rest
  | "canonicalize" :: rest => canonicalizeCmd rest
  | "closure" :: rest => closureCmd rest
  | "owl-consistent" :: rest => owlConsistentCmd rest
  | "owl-entails" :: rest => owlEntailsCmd rest
  | "cl" :: sub :: rest => clCmd sub rest
  | "cl" :: [] =>
      IO.eprintln "l4factoidal cl: need a subcommand \
(parse | serialize | alpha-norm | normalize | finite-sat)"
      pure 2
  | cmd :: _ =>
      IO.eprintln s!"l4factoidal: unknown verb '{cmd}' (try 'l4factoidal help')"
      pure 2

end L4Wasm.Cli

/-- Lake's executable entry point: `lean_exe l4factoidal` needs a
top-level `main`, matching `Harness/Main.lean`'s convention for a
namespaced implementation. -/
def main (args : List String) : IO UInt32 := L4Wasm.Cli.main args
