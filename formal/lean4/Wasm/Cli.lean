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
  l4factoidal parse data.nt --format ntriples --out jsonld
  l4factoidal query data.ttl --query-string 'SELECT * WHERE { ?s ?p ?o }'
  l4factoidal help          -- full verb list

`parse --out F` writes the dataset in any of the six syntaxes of `RDF.RdfFormat`
(`outDocument`, https://github.com/danbri/factoidal/issues/853): `nquads` and
`turtle` as they have always been written, the others by the serialiser layer
(`L4Factoidal/RDF/Sink.lean`).

`l4wasm-cli` (`Wasm/Main.lean`) stays as it is — the ABI smoke driver
`Wasm/native-smoke.sh` pins — and is unaffected by this module.
-/
import Wasm.Abi
import Wasm.Dispatch
import L4Factoidal.RDF.Source
import L4Factoidal.RDF.StreamSet
import L4Factoidal.RDF.SinkJsonLd
import L4Factoidal.Syntax.LenientFeed
import L4Factoidal.Syntax.StrictFeed
import L4Factoidal.Syntax.FileIri
import L4Factoidal.Tdb2.Read

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
  -- `--format tdb2`: the path is an Apache Jena TDB2 database directory, read
  -- with the Lean decoder (https://github.com/danbri/factoidal/issues/834).
  if formatTag == "tdb2" then
    match pathOpt with
    | none | some "-" => return .error "--format tdb2 needs a database directory"
    | some dir =>
      match ← L4Factoidal.Tdb2.readDatabaseNQuads dir with
      | .error e => return .error e
      | .ok text => return Ops.parseTextToDataset text "nquads" baseIri
  match ← readInput pathOpt with
  | .error e => pure (.error e)
  | .ok text => pure (Ops.parseTextToDataset text formatTag baseIri)

/-- `readDataset`, with the proof that the dataset is a set of quads
(`Ops.parseTextToDatasetSet`): the verbs that hand the dataset to an `Ops.*OfSet`
function use it, and the operation does not index the triples a second time. -/
def readDatasetSet (pathOpt : Option String) (formatTag baseIri : String) :
    IO (Except String { ds : Dataset // ds.IsSet }) := do
  if formatTag == "tdb2" then
    match pathOpt with
    | none | some "-" => return .error "--format tdb2 needs a database directory"
    | some dir =>
      match ← L4Factoidal.Tdb2.readDatabaseNQuads dir with
      | .error e => return .error e
      | .ok text => return Ops.parseTextToDatasetSet text "nquads" baseIri
  match ← readInput pathOpt with
  | .error e => pure (.error e)
  | .ok text => pure (Ops.parseTextToDatasetSet text formatTag baseIri)

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

/-- The chunk size of the streamed lenient parse: 65,536 bytes, or the environment
variable `L4_LENIENT_CHUNK_BYTES` when it is a positive number.
`tools/strict-parse-differential.sh` sets it to 1 and to 7 so that every line of the W3C
files falls across a chunk boundary (https://github.com/danbri/factoidal/issues/949). -/
def lenientChunkBytesIO : IO USize := do
  match (← IO.getEnv "L4_LENIENT_CHUNK_BYTES").bind String.toNat? with
  | some n => pure (if n > 0 then n.toUSize else lenientChunkBytes)
  | none => pure lenientChunkBytes

/-- Read `h` chunk by chunk, at most `fuel` chunks, stopping early when
`stop` holds. The `Bool` is `true` when the end of the file was reached (or
`stop` held). Structural recursion on `fuel`. -/
def forChunksOf {α : Type} (chunk : USize) (h : IO.FS.Handle) (stop : α → Bool)
    (f : α → ByteArray → IO (Except String α)) : Nat → α → IO (Except String (α × Bool))
  | 0, a => pure (.ok (a, false))
  | n + 1, a => do
      if stop a then return .ok (a, true)
      let bytes ← h.read chunk
      if bytes.isEmpty then return .ok (a, true)
      match ← f a bytes with
      | .error e => pure (.error e)
      | .ok a' => forChunksOf chunk h stop f n a'

def forChunks {α : Type} (h : IO.FS.Handle) (stop : α → Bool)
    (f : α → ByteArray → IO (Except String α)) : Nat → α → IO (Except String (α × Bool)) :=
  forChunksOf lenientChunkBytes h stop f

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
  let chunk ← lenientChunkBytesIO
  let fuel := size / chunk.toNat + 2
  let baseOpt : Option String := if base == "" then none else some base
  let feed? : Option (IO (Except String LenientFeed)) :=
    match Ops.formatOfTag tag with
    | some .nt =>
        some (pure (.ok (LenientFeed.initLines mode true emit opts)))
    | some .nquads =>
        some (pure (.ok (LenientFeed.initLines mode false emit opts)))
    | some .turtle =>
        some (do
          let pre ← IO.FS.withFile path .read fun h =>
            forChunksOf chunk h (fun (_ : LenientPrepass) => false)
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
        forChunksOf chunk h (fun (fd : LenientFeed × Nat) => fd.1.stopped)
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
  if !([some RdfFormat.turtle, some .nt, some .nquads, some .trig].contains (Ops.formatOfTag tag)) then
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

-- `parse` counts the set: 2. The envelope counts the set as well: the source
-- layer gives a set of quads (`Source.parseDocument`, `Dataset.toSet`). Before
-- 2026-10-23 the envelope counted the parser's list, 3.
#guard parseCountOutput sampleRepeat "turtle" "" matches .ok "2"
#guard parseCountViaEnvelope sampleRepeat "turtle" "" matches .ok "2"
-- And `query` COUNT(*) on the same text says 2 as well.
#guard queryCountOf sampleRepeat == some "2"
#guard queryCountOf sampleTtl == some "4"

/-! ## Strict `parse` of a FILE, streamed (issue 813)

`l4factoidal parse FILE [--out nquads]` for N-Triples, N-Quads and Turtle
reads FILE in 65,536-byte chunks instead of reading it whole
(https://github.com/danbri/factoidal/issues/813). The chunks go through the
source layer (`L4Factoidal/RDF/Source.lean`, `Source.ByteReader`), the reader
the shard packers and `l4sbm11-pack` read through
(https://github.com/danbri/factoidal/issues/837). The format of the file is an
`RdfFormat` (`Ops.formatOfTag`, the labels of `RDF.formatOfLabel`); this
module keeps no table of format names. Each chunk's canonical N-Quads lines
are written before the next chunk is read (N-Triples, Turtle); N-Quads keeps the
set `parseNQuadsFast` keeps (`FastDataset`) and writes it at the end, because
the canonical form groups the quads by graph; the count keeps the set of
distinct triples only. TriG, RDF/XML and JSON-LD are read whole through
`Source.parseDocument` (`Ops.parseTextToDataset`): the canonical form of a
dataset with named graphs groups the quads by graph, which a stream in document
order cannot give.

The output and the count are those of the whole-file path below
(`Ops.parseTextToDataset`); see `StrictFeed.lean` for the theorems and the
design record (section 3b) for the byte comparison. Errors:

* N-Triples and N-Quads: the error of the chunk's line walk, with the
  absolute offset (`fmtParseError`), and the lines of the chunks before it
  already written;
* Turtle: when the walk refuses a document (or the document contains `<<`,
  `Source.Prepass.hasDoubleLt`), the file is read whole and given to
  `Ops.parseTextToDataset`, as `parseTurtleText` gives it to `parseTurtle`, so
  every Turtle error is the reference parser's;
* bytes that are not UTF-8: the file is read whole by `readInput`, which
  reports them as before. -/

/-- The chunk size of the streamed strict parse: 65,536 bytes, or the
environment variable `L4_STRICT_CHUNK_BYTES` when it is a positive number.
`tools/strict-parse-differential.sh` sets it to 1 and to 7 so that every line
and statement boundary of the W3C files falls across a chunk boundary. -/
def strictChunkBytes : IO USize := do
  match (← IO.getEnv "L4_STRICT_CHUNK_BYTES").bind String.toNat? with
  | some n => pure (if n > 0 then n.toUSize else lenientChunkBytes)
  | none => pure lenientChunkBytes

/-- What a streamed strict parse needs from the whole-file path. -/
inductive StrictOutcome where
  /-- Finished: exit status. -/
  | done (code : UInt32)
  /-- Read the file whole; `printed` triples are written (`turtle`: in the
  order of the Turtle walk). -/
  | whole (printed : Nat) (turtle : Bool)

/-- Write the text of one chunk's triples (newest first in `accRev`). -/
def writeTriples (accRev : List Triple) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (StrictFeed.chunkText accRev)
  out.flush

/-- Why a streamed read stopped before the end of the file. -/
inductive StrictStop where
  /-- Read the file whole; the triples already written are counted in the
  caller's reference. -/
  | whole
  /-- The error is printed; exit status 1. -/
  | failed

/-- Read `path` in chunks through `Source.ByteReader` with the consumer `step`
from `init`. After each chunk `hook` may take work out of the reader (the
triples to write). A parse error is printed and stops the read when
`reportParse` holds (N-Triples and N-Quads: the error of the line walk); else
it hands the file to the whole-file path (Turtle: the reference parser words
the error). Bytes that are not UTF-8 hand it over in both cases. -/
def driveSource {α : Type} (path : String) (fmt : RdfFormat) (mode : Mode) (baseOpt : Option String)
    (bnodePrefix : String) (reportParse : Bool) (step : Source.Step α) (init : α)
    (hook : Source.ByteReader α → IO (Source.ByteReader α)) : IO (Except StrictStop α) := do
  let size := (← System.FilePath.metadata path).byteSize.toNat
  let chunk ← strictChunkBytes
  let fuel := size / chunk.toNat + 2
  let rd0 ← match Source.ByteReader.init Source.withJsonLd fmt mode baseOpt bnodePrefix init with
    | .ok r => pure r
    | .error m => throw (IO.userError s!"{path}: {m}")
  let failParse (e : ParseError) : IO StrictStop := do
    if reportParse then
      IO.eprintln (fmtParseError e)
      pure .failed
    else pure .whole
  let walked ← IO.FS.withFile path .read fun h =>
    forChunksOf chunk h (fun (st : Option (Source.ByteReader α) × Option StrictStop) => st.2.isSome)
      (fun st bytes => do
        -- No branch below names the reader again after `feed`: the walk must
        -- hold the only reference to the accumulator, or `addQuadFast` copies
        -- its hash map at the first quad of every chunk (measured: 400,000
        -- N-Triples counted in 8.6 s of CPU, 100,000 in 1.25 s).
        match st.1 with
        | none => pure (.ok (none, some .failed))
        | some rd =>
          match rd.feed step bytes with
          | .error (.utf8 _) => pure (.ok (none, some .whole))
          | .error (.parse e) => pure (.ok (none, some (← failParse e)))
          | .ok rd' => pure (.ok (some (← hook rd'), none)))
      fuel (some rd0, none)
  match walked with
  | .error e => IO.eprintln s!"{path}: {e}"; pure (.error .failed)
  | .ok ((_, some stop), _) => pure (.error stop)
  | .ok (_, false) => IO.eprintln s!"{path}: the file grew while it was read"; pure (.error .failed)
  | .ok ((none, none), true) => pure (.error .failed)
  | .ok ((some rd, none), true) =>
    match rd.endBytes with
    | .error _ => pure (.error .whole)
    | .ok reader =>
      match reader.finish step with
      | .error e => pure (.error (← failParse e))
      | .ok acc => pure (.ok acc)

/-- Write the triples a chunk completed that no earlier triple repeats (newest
first in `fresh`, `StreamSet.lean`) and empty `fresh`, keeping the seen graph;
`printed` counts the triples written. RDF 1.1 Concepts section 3: the output
is a set, as the whole-file output is. -/
def writeChunk (printed : IO.Ref Nat) (rd : Source.ByteReader DedupAcc) :
    IO (Source.ByteReader DedupAcc) := do
  let (rd', accRev) := rd.withAcc DedupAcc.drain
  writeTriples accRev
  printed.modify (· + accRev.length)
  pure rd'

/-- N-Triples and N-Quads. `emit`: write canonical N-Quads; otherwise print the
count. -/
def streamStrictLines (path : String) (fmt : RdfFormat) (mode : Mode) (emit : Bool) : IO StrictOutcome := do
  let printed ← IO.mkRef 0
  if fmt == .nt && emit then
    -- The triples of each chunk that no earlier triple repeats are written and
    -- dropped; the seen graph stays (`dedupStep`).
    match ← driveSource path .nt mode none "" true dedupStep ({} : DedupAcc) (writeChunk printed) with
    | .error .failed => pure (.done 1)
    | .error .whole => pure (.whole (← printed.get) false)
    | .ok st =>
        writeTriples st.fresh
        IO.println ""
        pure (.done 0)
  else
    -- The set: `countQuad` for the N-Triples count, `addQuadFast` for N-Quads
    -- (the accumulator of `parseNQuadsFast`).
    let step : Source.Step FastDataset := if fmt == .nt then StrictFeed.countQuad else addQuadFast
    match ← driveSource path fmt mode none "" true step ({} : FastDataset) pure with
    | .error .failed => pure (.done 1)
    | .error .whole => pure (.whole 0 false)
    | .ok fd =>
        if fmt == .nt then
          IO.println (toString (StrictFeed.FastDataset.quadCount fd))
        else
          let ds := fd.toDataset
          if emit then IO.println (Dataset.toCanonicalNQuads ds)
          else IO.println (toString (datasetQuadCount (normalizeDataset ds)))
        pure (.done 0)

/-- Turtle through the pre-pass (`Source.Prepass`: the generated blank-node
prefix, and whether the document contains `<<`) and the Turtle reader of the
source layer. -/
def streamStrictTurtle (path : String) (mode : Mode) (base : String) (emit : Bool) :
    IO StrictOutcome := do
  let size := (← System.FilePath.metadata path).byteSize.toNat
  let chunk ← strictChunkBytes
  let fuel := size / chunk.toNat + 2
  let baseOpt : Option String := if base == "" then none else some base
  let pre ← IO.FS.withFile path .read fun h =>
    forChunksOf chunk h (fun (_ : Source.Prepass) => false)
      (fun p b => pure (p.feed b)) fuel ({} : Source.Prepass)
  match pre with
  | .error _ => pure (.whole 0 true)
  | .ok (_, false) => IO.eprintln s!"{path}: the file grew while it was read"; pure (.done 1)
  | .ok (p, true) =>
  match p.finish with
  | .error _ => pure (.whole 0 true)
  | .ok pfx =>
  if p.hasDoubleLt then pure (.whole 0 true) else
  let printed ← IO.mkRef 0
  if emit then
    match ← driveSource path .turtle mode baseOpt pfx false dedupStep ({} : DedupAcc) (writeChunk printed) with
    | .error .failed => pure (.done 1)
    | .error .whole => pure (.whole (← printed.get) true)
    | .ok st =>
        writeTriples st.fresh
        IO.println ""
        pure (.done 0)
  else
    match ← driveSource path .turtle mode baseOpt pfx false StrictFeed.countQuad ({} : FastDataset) pure with
    | .error .failed => pure (.done 1)
    | .error .whole => pure (.whole 0 true)
    | .ok fd =>
        IO.println (toString (StrictFeed.FastDataset.quadCount fd))
        pure (.done 0)

/-- The whole-file path after a streamed run handed over: `printed` triples
of the walk are already on standard output. -/
def strictWhole (path format base : String) (emit : Bool) (printed : Nat) (turtle : Bool) :
    IO UInt32 := do
  match ← readInput (some path) with
  | .error e => IO.eprintln e; pure 1
  | .ok text =>
    if !emit then
      match parseCountOutput text format base with
      | .error msg => IO.eprintln msg; pure 1
      | .ok n => IO.println n; pure 0
    else
    match Ops.parseTextToDataset text format base with
    | .error msg => IO.eprintln msg; pure 1
    | .ok ds =>
      if printed == 0 then
        IO.println (Dataset.toCanonicalNQuads ds)
        pure 0
      else
        -- Only the Turtle walk hands over after writing (a document the walk
        -- refuses and `parseTurtle` accepts). The triples written are the
        -- walk's first `printed`; write the rest of the reference graph when
        -- they are its first `printed`.
        let (mode, _) := Ops.resolveModeAndTag format
        let baseOpt : Option String := if base == "" then none else some base
        let walkedRaw := StrictFeed.walkPrefix
          (TurtleChunkFoldState.init (freshBnodePrefixText text) prependReverse [] baseOpt mode) text
        -- The streamed output is a set: the `printed` triples written are the first
        -- `printed` triples of the set of the walk's triples (`StreamSet.lean`).
        let walked := (Dataset.toSet { default := walkedRaw, named := [] }).default
        if turtle && ds.named.isEmpty && printed ≤ walked.length &&
            walked.take printed == ds.default.take printed then
          let out ← IO.getStdout
          out.putStr (String.join ((ds.default.drop printed).map Triple.toCanonicalNTriples))
          IO.println ""
          pure 0
        else
          IO.eprintln s!"l4factoidal parse: internal: the streamed walk and the reference parser disagree within the first {printed} triples; the output is not complete"
          pure 1

/-- `parse FILE [--out nquads]` streamed, or `none` when the format has no
streamed execution (TriG, RDF/XML, JSON-LD). -/
def streamStrictFile (path format base : String) (emit : Bool) : IO (Option UInt32) := do
  let (mode, tag) := Ops.resolveModeAndTag format
  let outcome? ← match Ops.formatOfTag tag with
    | some .nt => some <$> streamStrictLines path .nt mode emit
    | some .nquads => some <$> streamStrictLines path .nquads mode emit
    | some .turtle => some <$> streamStrictTurtle path mode base emit
    | _ => pure none
  match outcome? with
  | none => pure none
  | some (.done code) => pure (some code)
  | some (.whole printed turtle) => some <$> strictWhole path format base emit printed turtle

/-! ## `parse --out F`: the dataset as a document in any of the six syntaxes

Tracking: https://github.com/danbri/factoidal/issues/853 (the known-defects row
`JLD-WSTACK` needs a JSON-LD writer in `l4factoidal`, a program that the CI step
of that suite installs) and https://github.com/danbri/factoidal/issues/837 (a
concrete syntax is named only at the source and serialiser edges).

`--out` takes a label of `RDF.formatOfLabel` (`nquads`, `ntriples`, `turtle`,
`trig`, `rdfxml`, `jsonld`, and the aliases that function reads). This module
keeps no table of format names for it: the label becomes an `RdfFormat` and the
writer decides the text.

* `nquads` and `turtle` print the text they have always printed, byte for byte:
  `nquads` is the canonical form of RDF 1.2 N-Quads (`Dataset.toCanonicalNQuads`:
  language tags in lower case, the escapes of the canonical form), and `turtle`
  is `Ops.serializeTurtleTextOf` (the dataset in its normal form, as the
  `serializeTurtle` op reads the canonical text: RDF 1.2 N-Quads, or RDF 1.1
  N-Quads when the RDF 1.2 reader refuses it; the prefixes derived from the whole
  graph). The batch writers of the serialiser
  layer write other bytes for some datasets (`Term.toNTriples` keeps the case of a
  language tag and escapes fewer control characters), so these two do not go
  through it.
* `ntriples`, `trig`, `rdfxml` and `jsonld` are the batch meaning of the
  serialiser layer, `Sink.serializeDataset` (`L4Factoidal/RDF/Sink.lean`), the
  function `l4source-convert` calls. For JSON-LD it calls `FromRdf.fromRdf`
  (`Sink.jsonLdWriter`), the function `l4sbm11 export --format jsonld` calls; the
  row `jsonld-write-fanout-stack` of `tests/stack/lean_scaling.py` measures its
  stack use through this verb (the known-defects row `JLD-WSTACK` did until the
  repair of issue 853, 2026-10-18).

N-Triples, Turtle and RDF/XML have no place for the name of a graph. The batch
writer of the serialiser layer writes the triples of the default graph and of all
the named graphs as one graph (`Sink.flatten`), and `parse --out turtle` has always
done so. This verb follows it, and says so on standard error when the dataset has a
named graph (`graphNameNotice`); the stream writer's default (`Sink.GraphChoice.refuse`,
an error) belongs to `l4sbm11 export`, which reads a store and has `--graph` to choose. -/

/-- The labels `--out` lists in its usage error: the labels `formatLabel` gives. -/
def outLabels : String := "nquads | ntriples | turtle | trig | rdfxml | jsonld"

/-- The notice `parse --out` writes to standard error when `ds` has a named graph
and the syntax `fmt` has no place for a graph name. -/
def graphNameNotice (fmt : RdfFormat) (ds : Dataset) : Option String :=
  if Source.hasNamedGraphs fmt || ds.named.isEmpty then none
  else
    let n := ds.named.length
    some s!"l4factoidal parse: {formatName fmt} has no graph name; the triples of the default graph and of the {n} named {if n == 1 then "graph" else "graphs"} are written as one graph"

/-- The text `parse --out` prints for `ds` in syntax `fmt`; see the section header. -/
def outDocument (fmt : RdfFormat) (ds : Dataset) : Except String String :=
  match fmt with
  | .nquads => .ok (Dataset.toCanonicalNQuads ds)
  | .turtle => Ops.serializeTurtleTextOf ds
  | _ =>
      ((L4Factoidal.Dataflow.writers Sink.withJsonLd L4Factoidal.RDF.Source.withJsonLd fmt).run .rdf12 {} ds).mapError fun e =>
        s!"l4factoidal parse: cannot write {formatName fmt}: {e}"

/-- Print `ds` in syntax `fmt`: the document and a line break to standard output,
and before them the notice (if any) to standard error. Exit status 0, or 1 when the
writer refuses the dataset: then only the error text is printed, as `--out turtle`
has always done, and no notice. -/
def writeOut (fmt : RdfFormat) (ds : Dataset) : IO UInt32 := do
  match outDocument fmt ds with
  | .error e => IO.eprintln e; pure 1
  | .ok text =>
      if let some notice := graphNameNotice fmt ds then IO.eprintln notice
      IO.println text
      pure 0

/-! ### Build-time checks of `outDocument` and `graphNameNotice`

The checks run the writers on two small datasets and read each document back with
the reader of the same syntax (`Ops.parseTextToDataset`). A document that read back
as an empty dataset would also be "equal" to an empty dataset, so each check first
states the size of the dataset it writes. -/

private def outDataset (text format : String) : Option Dataset :=
  (Ops.parseTextToDataset text format "").toOption

private def outQuads (ds : Dataset) : List (Triple × Option Subject) :=
  ds.default.map (fun t => (t, none)) ++
    ds.named.flatMap fun ng => ng.graph.map fun t => (t, some ng.name)

/-- Equal as sets of quads, graph names included. -/
private def sameQuadSets (a b : List (Triple × Option Subject)) : Bool :=
  a.all (fun q => b.any (· == q)) && b.all (fun q => a.any (· == q))

/-- `ds` written in `fmt` is read back, in the same syntax, as `want`. -/
private def outReadsAs (fmt : RdfFormat) (ds : Dataset) (want : List (Triple × Option Subject)) : Bool :=
  match outDocument fmt ds with
  | .error _ => false
  | .ok text =>
      match outDataset text (formatLabel fmt) with
      | some back => sameQuadSets (outQuads back) want
      | none => false

/-- The quads of `ds` with the graph names removed. -/
private def outUnion (ds : Dataset) : List (Triple × Option Subject) :=
  (outQuads ds).map fun q => (q.1, none)

private def outDefaultOnly : Option Dataset :=
  outDataset ("<http://e/a> <http://e/p> <http://e/b> .\n" ++
    "<http://e/a> <http://e/q> \"x\\ty\"@en .\n" ++
    "<http://e/c> <http://e/p> \"7\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n") "ntriples"

private def outWithNamed : Option Dataset :=
  outDataset ("<http://e/a> <http://e/p> <http://e/b> <http://e/g> .\n" ++
    "<http://e/c> <http://e/p> \"d\"@fr <http://e/g> .\n" ++
    "<http://e/c> <http://e/p> <http://e/d> .\n") "nquads"

private def outTripleTerm : Option Dataset :=
  outDataset "<http://e/a> <http://e/p> <<( <http://e/s> <http://e/p> <http://e/o> )>> .\n" "ntriples12"

-- A dataset with only a default graph is read back, in each of the six syntaxes, as itself.
#guard outDefaultOnly.any fun ds => ds.default.length == 3 && ds.named.isEmpty
#guard outDefaultOnly.any fun ds =>
  [RdfFormat.nquads, .nt, .turtle, .trig, .rdfxml, .jsonld].all fun fmt =>
    outReadsAs fmt ds (outQuads ds)

-- A dataset with a named graph: the syntaxes with a graph name keep it, the others
-- write all the triples as one graph.
#guard outWithNamed.any fun ds => ds.default.length == 1 && ds.named.length == 1
#guard outWithNamed.any fun ds =>
  [RdfFormat.nquads, .trig, .jsonld].all fun fmt => outReadsAs fmt ds (outQuads ds)
#guard outWithNamed.any fun ds =>
  [RdfFormat.nt, .turtle, .rdfxml].all fun fmt => outReadsAs fmt ds (outUnion ds)
-- The union is three triples in one graph (teeth: a writer that dropped the named
-- graph would read back as one).
#guard outWithNamed.any fun ds =>
  match outDocument .nt ds with
  | .ok text => ((text.splitOn "\n").filter (· != "")).length == 3
  | .error _ => false

-- The two syntaxes that have always been written are the canonical N-Quads and
-- `Ops.serializeTurtleTextOf`. A tag read in capitals is held in lower case
-- (issue 1001), so every writer writes it in lower case.
#guard outDefaultOnly.any fun ds =>
  (outDocument .nquads ds).toOption == some (Dataset.toCanonicalNQuads ds) &&
  (outDocument .turtle ds).toOption == (Ops.serializeTurtleTextOf ds).toOption
#guard (outDataset "<http://e/a> <http://e/p> \"x\"@DE-ch .\n" "ntriples").any fun ds =>
  match outDocument .nquads ds, outDocument .nt ds with
  | .ok a, .ok b => (a.splitOn "@de-ch").length == 2 && (b.splitOn "@de-ch").length == 2
  | _, _ => false

-- The notice: a syntax with no graph name and a named graph.
#guard outWithNamed.any fun ds =>
  [RdfFormat.nt, .turtle, .rdfxml].all (fun fmt => (graphNameNotice fmt ds).isSome) &&
  [RdfFormat.nquads, .trig, .jsonld].all (fun fmt => (graphNameNotice fmt ds).isNone)
#guard outDefaultOnly.any fun ds =>
  [RdfFormat.nquads, .nt, .turtle, .trig, .rdfxml, .jsonld].all fun fmt => (graphNameNotice fmt ds).isNone

-- A triple term is written as N-Triples 1.2 and refused by JSON-LD, by name.
#guard outTripleTerm.any fun ds =>
  (match outDocument .nt ds with
   | .ok text => (text.splitOn "<<(").length == 2
   | .error _ => false) &&
  (match outDocument .jsonld ds with
   | .error m => m.startsWith "l4factoidal parse: cannot write JSON-LD 1.1: "
   | .ok _ => false)

def parseCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--out", "--max-errors"] ["--lenient"] args with
  | .error e => IO.eprintln s!"l4factoidal parse: {e}"; pure 2
  | .ok s =>
    if s.hasBool "--lenient" then parseLenientCmd s else
    let format := (s.value? "--format").getD "turtle"
    let base := (s.value? "--base").getD ""
    -- `--out` names a syntax (`RDF.formatOfLabel`). An unknown label is a usage
    -- error, found before any input is read.
    let outLabel? := s.value? "--out"
    let outFmt? : Option RdfFormat := outLabel?.bind formatOfLabel
    if let some label := outLabel? then
      if outFmt?.isNone then
        IO.eprintln s!"l4factoidal parse: unknown --out '{label}' ({outLabels})"
        return 2
    -- An exception of the streamed run (a missing or unreadable file) goes
    -- to the whole-file path, whose `readInput` words the error as before.
    let streamed ← match s.positional[0]?, outFmt? with
      | some path, none =>
          if path == "-" then pure none else
          try streamStrictFile path format base false
          catch _ => pure none
      | some path, some .nquads =>
          if path == "-" then pure none else
          try streamStrictFile path format base true
          catch _ => pure none
      | _, _ => pure none
    match streamed with
    | some code => pure code
    | none =>
    match ← readInput s.positional[0]? with
    | .error e => IO.eprintln e; pure 1
    | .ok text =>
      match outFmt? with
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
      | some fmt =>
        -- The text is printed as the op computes it, without the JSON
        -- envelope `parseToDatasetJson` / `serializeTurtle` wrap it in and
        -- this verb used to decode again (issue 724). `--out nquads` is the
        -- envelope's `nquads` member, `Dataset.toCanonicalNQuads`;
        -- `--out turtle` is `serializeTurtle` on that text
        -- (`Ops.serializeTurtleTextOf_eq`); the other syntaxes are written by
        -- the serialiser layer (`outDocument`).
        match Ops.parseTextToDataset text format base with
        | .error msg => IO.eprintln msg; pure 1
        | .ok ds => writeOut fmt ds

def queryCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--query", "--query-string"] ["--table", "--sparql12"] args with
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
      match ← readDatasetSet s.positional[0]? format base with
      | .error e => IO.eprintln e; pure 1
      | .ok ⟨ds, hds⟩ =>
        -- SPARQL 1.1 §17.4.5.1: `NOW()` is one instant for the whole query
        -- execution. The clock is read here, at the edge, once, and passed to
        -- the pure op (https://github.com/danbri/factoidal/issues/743).
        let now ← Ops.nowDateTime
        -- `--sparql12`: the query is read by the SPARQL 1.2 grammar
        -- (triple-term patterns, TRIPLE, SUBJECT, PREDICATE, OBJECT,
        -- isTRIPLE), as `queryDataset12` reads it; the reference of the SBM11
        -- RDF 1.2 gate (tests/sbm11/run.sh part (m),
        -- https://github.com/danbri/factoidal/issues/792 item 1)
        let answer :=
          if s.hasBool "--sparql12" then
            withOpsSetDataset .rdf12 ds hds (fun d =>
              queryParsedDatasetWith d (some (L4Factoidal.Dataflow.LawfulDataset.ofDataset d)) sparql
                (version := .v12) (base := queryBase) (now := some now))
          else Ops.queryDatasetOfSet ds hds sparql queryBase (some now)
        match ← parseEnvelope answer with
        | none => pure 1
        | some j => printQueryResult j (s.hasBool "--table")

def updateCmd (args : List String) : IO UInt32 := do
  match scanArgs ["--format", "--base", "--update", "--update-string"] ["--sparql12"] args with
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
        -- One clock read per request: `NOW()` in a WHERE clause is the same
        -- instant in every operation of the request (SPARQL 1.1 §17.4.5.1,
        -- https://github.com/danbri/factoidal/issues/743).
        let now ← Ops.nowDateTime
        -- `--sparql12`: the update is read by the SPARQL 1.2 grammar (triple
        -- terms, directional literals); the reference of the SBM11 RDF 1.2
        -- update gate (tests/sbm11/run.sh part (m),
        -- https://github.com/danbri/factoidal/issues/792 item 1)
        let version : L4Factoidal.SPARQL.SparqlVersion := if s.hasBool "--sparql12" then .v12 else .v11
        match ← parseEnvelope (Ops.updateDatasetOf ds upd updateBase (some now) version) with
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

/-- What `closure` printed until 2026-10-13 for a regime: the envelope's
`nquads` (or `ntriples`) member after a JSON round trip, or the error text
(https://github.com/danbri/factoidal/issues/758). Kept for the guards below. -/
private def closureViaEnvelope (ds : Dataset) (regime : String) : Except String String :=
  match parseJson (Ops.closureEnvelopeOf ds regime) with
  | .error e => .error s!"internal: op result was not JSON ({toString e})"
  | .ok j =>
      if j.getBool? "ok" == some true then
        .ok (((j.getString? "nquads") <|> (j.getString? "ntriples")).getD "")
      else .error ((j.getString? "error").getD "unknown error")

/-- What `closure` prints now, before the final newline: the lines of
`Ops.closureStreamOf`, or its error text. -/
private def closureViaStream (ds : Dataset) (regime : String) : Except String String :=
  (Ops.closureStreamOf ds regime).map fun g =>
    String.join (g.map (Triple.toNTriplesLine .rdf12))

private def closureSample : Option Dataset :=
  (Ops.parseTextToDataset ("@prefix e: <http://e/> . @prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> . " ++
    "@prefix owl: <http://www.w3.org/2002/07/owl#> . e:A rdfs:subClassOf e:B . e:x a e:A . " ++
    "e:p a owl:TransitiveProperty . e:x e:p e:y . e:y e:p e:z . e:x e:q \"t\\\"q\"@EN .")
    "turtle" "").toOption

-- The stream gives the envelope's text, for every regime, on a graph with
-- inferences, an escaped literal and a language tag.
#guard closureSample.any fun ds => ["owl-rl", "rdfs", "rho-df", "rdfs-plus"].all fun r =>
  sameOutput (closureViaStream ds r) (closureViaEnvelope ds r)
-- Teeth: the closure holds the inferred triples, so two functions that both
-- returned the input (or nothing) would not pass.
#guard closureSample.any fun ds => match closureViaStream ds "owl-rl" with
  | .ok t => (t.splitOn "<http://e/x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/B> .").length == 2 &&
             (t.splitOn "<http://e/x> <http://e/p> <http://e/z> .").length == 2
  | .error _ => false
#guard closureSample.any fun ds => match closureViaStream ds "rdfs" with
  | .ok t => (t.splitOn "<http://e/x> <http://e/p> <http://e/z> .").length == 1
  | .error _ => false
-- A triple term: until 2026-10-18 the ops read RDF 1.1 and this dataset was
-- the error path (both texts the same error). The ops now read and write
-- RDF 1.2 (https://github.com/danbri/factoidal/issues/873): the stream and
-- the envelope give the same text, for every regime, and it holds the triple.
private def closureTripleTerm : Option Dataset :=
  (Ops.parseTextToDataset "<http://e/a> <http://e/p> <<( <http://e/s> <http://e/p> <http://e/o> )>> ."
    "ntriples12" "").toOption
#guard closureTripleTerm.any fun ds => ["owl-rl", "rdfs", "rho-df", "rdfs-plus"].all fun r =>
  sameOutput (closureViaStream ds r) (closureViaEnvelope ds r) &&
  (match closureViaStream ds r with
   | .ok t => (t.splitOn "<http://e/a> <http://e/p> <<( <http://e/s> <http://e/p> <http://e/o> )>> .").length == 2
   | .error _ => false)

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
          -- One N-Triples line per closure triple, written as it is made
          -- (https://github.com/danbri/factoidal/issues/758). Until
          -- 2026-10-13 this verb took the closure as one string inside the
          -- JSON envelope of `Ops.closureEnvelopeOf`, decoded the envelope
          -- and printed its `nquads` (or `ntriples`) member and a newline.
          -- `Ops.closureEnvelopeOf_stream` proves that member is these lines
          -- in this order, and the error text is the envelope's.
          match Ops.closureStreamOf ds regime with
          | .error m => IO.eprintln m; pure 1
          | .ok g =>
              let out ← IO.getStdout
              for t in g do
                out.putStr (Triple.toNTriplesLine .rdf12 t)
              out.putStr "\n"
              out.flush
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
  , "  parse [FILE] [--format FMT] [--base IRI] [--out OUT]"
  , "      Parse RDF and print the quad count, or (with --out) the dataset"
  , "      as a document. FILE omitted or \"-\" reads stdin. FMT: turtle |"
  , "      ntriples | nquads | trig | rdfxml | jsonld (default turtle)."
  , "      OUT: nquads | ntriples | turtle | trig | rdfxml | jsonld. nquads"
  , "      is the canonical N-Quads form. ntriples, trig, rdfxml and jsonld"
  , "      are written by the serialiser layer (RDF/Sink.lean). ntriples,"
  , "      turtle and rdfxml have no graph name: the triples of the default"
  , "      graph and of the named graphs are written as one graph, and a"
  , "      notice goes to stderr. Every OUT except nquads holds the whole"
  , "      dataset in memory."
  , "  parse --lenient [FILE] [--format FMT] [--base IRI] [--max-errors N]"
  , "        [--out nquads]"
  , "      Recovery mode (turtle | trig | ntriples | nquads): skip each bad"
  , "      statement, write one JSON diagnostic per line to stderr"
  , "      ({message, offset, line, column, class}), keep the good ones."
  , "      A FILE is streamed in 64 KiB chunks (TriG and stdin are read"
  , "      whole). Prints the quad count, or with --out nquads the kept"
  , "      quads as they are read. Exit 1 when any diagnostic was written."
  , "  tdb2-dump DIR      the quads of an Apache Jena TDB2 database, as N-Quads"
  , "                    (also: --format tdb2 DIR for query, parse, update)"
  , "  query [FILE] (--query FILE.rq | --query-string SPARQL)"
  , "        [--format FMT] [--base IRI] [--table] [--sparql12]"
  , "      Run a SPARQL query. SELECT prints SPARQL Results JSON (or a"
  , "      tab-separated table with --table); ASK prints true/false,"
  , "      exit 0 for true and 1 for false; CONSTRUCT prints N-Triples."
  , "      --base IRI is the base of the data FILE and of a --query-string"
  , "      text; a --query FILE.rq resolves its relative IRIs against the"
  , "      file's own IRI (file:///...), and a BASE in the query comes first."
  , "      --sparql12 reads the query with the SPARQL 1.2 grammar (triple-term"
  , "      patterns, TRIPLE, SUBJECT, PREDICATE, OBJECT, isTRIPLE)."
  , "  update [FILE] (--update FILE.ru | --update-string SPARQL-UPDATE) [--sparql12]"
  , "        [--format FMT] [--base IRI]"
  , "      Apply a SPARQL Update and print the resulting N-Quads. The base"
  , "      of the update text is chosen as for query. --sparql12 reads the"
  , "      update with the SPARQL 1.2 grammar (triple terms, directional"
  , "      literals)."
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
  | "tdb2-dump" :: [dir] =>
      match ← L4Factoidal.Tdb2.readDatabaseNQuads dir with
      | .error e => IO.eprintln s!"l4factoidal tdb2-dump: {e}"; pure 1
      | .ok text => IO.print text; pure 0
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
