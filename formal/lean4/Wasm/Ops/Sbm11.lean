/-
Wasm.Ops.Sbm11 — SPARQL over an SBM11 generation in the wasm module
(https://github.com/danbri/factoidal/issues/1009 KR1; stage 1 of
https://github.com/danbri/factoidal/issues/1007).

  sbm11Open(source [, optionsJson])
    -> {"ok":true,"handle":"sbm11-1","generation":G,"terms":N,"artifacts":K,
        "verify":"merkle"|"none","manifestSha256":H,"bytesRead":B}
  sbm11Query(handle, sparql [, optionsJson])
    -> {"ok":true,"path":"path=ids"|"path=reference ...","rows":N,
        "format":"srj"|"ntriples","bytesRead":B,"reads":R,"result":"..."}
    through l4_call_blob_io: "resultBytes":N in place of "result", and the
    result bytes as the out region
  sbm11Close(handle)
    -> {"ok":true}
  sbm11Verify(source)
    -> {"ok":true,"artifacts":K,"files":F,"bytes":B,"quads":Q,"terms":T,
        "manifestSha256":H}
  storeLayout(source)
    -> {"ok":true,"layout":"sbm11"|"ibk","generation":G,"manifest":M}

`source` is the string the host resolves (`Wasm/HostRead.lean`): a directory
for Node and the native CLI, an OPFS directory name in a browser worker. It
names a generation directory, or a collection root whose `CURRENT` file names
one (`G` is then that name, else `""`). Every
byte of the generation comes through the host's positioned read; nothing is
copied in whole. `optionsJson` is an object with the optional members `base`
(the base IRI of the query), `sparql12` (the SPARQL 1.2 grammar) and
`reference` (run the reference evaluator also for the id fragment, the oracle
of the tests).

The `optionsJson` of `sbm11Open` is an object with the optional member
`verify`: `"merkle"` (the default) or `"none"` (`HostVerify.Verify`). Under
`merkle` the open admits the `.merkle` sidecar of every file against the
manifest's Merkle root, and every byte a query decodes is in a 65,536-byte
chunk checked by its proof against that root, with HACL* SHA-256
(`sbm11PackHasher`); a changed byte in any file, sidecar or Merkle reference
of the manifest refuses the open or the query, and the error names the file
(https://github.com/danbri/factoidal/issues/1009). `none` checks the lengths
only, as `l4sbm11 query --verify none`.

The optional member `manifestSha256` of the `optionsJson` of `sbm11Open` is
the trust anchor of the manifest (https://github.com/danbri/factoidal/issues/1105):
the SHA-256 of the bytes of `manifest.sbm11`, as 64 hex digits (either case).
The open computes that digest with HACL* SHA-256 and refuses the open when it
is not the anchor; the error names `manifest.sbm11` and both digests
(`HostVerify.checkAnchor`). The anchor binds the fields of the manifest that
no read binds (the SHA-256 of each file, the source length and SHA-256, the
quad count). With no anchor the open is as before. `H` in the answers of
`sbm11Open` and `sbm11Verify` is the digest, as 64 lowercase hex digits, so
that a caller can pin it. Every open also checks the term count of the
manifest against the GDX1 header (`HostVerify.checkTerms`).

`result` is SPARQL 1.1 Query Results JSON for SELECT and ASK, and N-Triples
lines for CONSTRUCT and DESCRIBE: the bytes `l4sbm11 query` writes for the
same query on the same generation.

The engine: `L4Factoidal.Storage.Sbm11.HostSession`. The handle table is the
only state of this module (the rule of `Wasm/Ops/Handles.lean`).

`sbm11Verify(source)` is the activation check of the generation directory
`source` (it does not read `CURRENT`): `openSession` (the manifest decodes and
is admitted, every artifact has the manifest's length, no delta log, the GDX1
header decodes), then for every artifact the bytes of the whole file and of
its `.merkle` sidecar: the manifest entry that `PackBytes.artifactOf` makes of
the bytes (length, HACL* SHA-256, Merkle root of the 65,536-byte leaves) must
equal the entry in the manifest, and the sidecar must equal those leaves. The
host replaces `CURRENT` only after `"ok":true` (npm `factoidal activate`).
Native `l4sbm11 activate` also runs the decoder checks and the exact
permutation check (`Harness/Sbm11Cli.lean` `verifyGen`); this op does not.
Each file is read whole, so a file must fit in the module's memory.

`storeLayout(source)` says which store a directory holds, so that a host
does not decide it from file names (iron rule 7): it resolves `CURRENT` as
`resolveHost` does, then looks for `manifest.sbm11` (`"sbm11"`) and for the
manifests of the IBK3, IBK4 and IBK5 generations, `manifest.sbm2` and
`manifest.sbm1` (`"ibk"`; the store ops of `Wasm/Ops/Store.lean` then say
which IBK layout). A directory with none of them is an error.
-/
import Std.Data.HashMap
import Wasm.HostRead
import Wasm.Ops.Support
import Wasm.Ops.Clock
import L4Factoidal.SPARQL.Parser
import Wasm.Ops.Sbm11Pack

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.HostSession
open L4Factoidal.Storage.Sbm11.HostVerify (Verify)

/-- The most SBM11 handles open at once. -/
def maxSbm11Handles : Nat := 8

initialize sbm11HandleCounter : IO.Ref Nat ← IO.mkRef 0
initialize sbm11HandleTable : IO.Ref (Std.HashMap String Session) ← IO.mkRef ∅

private def ioMessage (e : IO.Error) : String := toString e

/-- The options of `sbm11Open` (module comment). -/
structure Sbm11OpenOpts where
  verify : Verify := .merkle
  /-- the trust anchor: the SHA-256 of the manifest bytes -/
  manifestSha256 : Option ByteArray := none

/-- The `optionsJson` of `sbm11Open`: the members `verify` and
    `manifestSha256` (module comment). -/
def sbm11OpenOpts (optionsJson : String) : Except String Sbm11OpenOpts := do
  if optionsJson.trimAscii.isEmpty then return {}
  match parseJson optionsJson with
  | .error e => throw s!"optionsJson: {toString e}"
  | .ok (.object members) =>
    let mut o : Sbm11OpenOpts := {}
    for (k, x) in members do
      match k, x with
      | "verify", .string s =>
        match Verify.ofString? s with
        | some w => o := { o with verify := w }
        | none => throw s!"optionsJson: verify is merkle or none, not {s}"
      | "verify", .null => pure ()
      | "manifestSha256", .string s =>
        match L4Factoidal.Storage.Sbm11.HostVerify.sha256OfHex? s with
        | some d => o := { o with manifestSha256 := some d }
        | none => throw s!"optionsJson: manifestSha256 is the SHA-256 of {manifestName} as 64 hex digits, not {s}"
      | "manifestSha256", .null => pure ()
      | k, _ => throw s!"optionsJson: member {k} is not verify (merkle or none) or manifestSha256"
    return o
  | .ok _ => throw "optionsJson must be a JSON object"

/-- `sbm11Open(source, optionsJson)`. -/
def sbm11Open (source : String) (optionsJson : String := "") : IO String := do
  let table ← sbm11HandleTable.get
  if table.size ≥ maxSbm11Handles then
    return errJson s!"sbm11Open: {table.size} handles are open (at most {maxSbm11Handles}); close one with sbm11Close"
  match sbm11OpenOpts optionsJson with
  | .error e => return errJson s!"sbm11Open: {e}"
  | .ok o =>
  let v := o.verify
  try
    let (host, genName) ← resolveHost (hostOf source)
    let ss ← openSession host v sbm11PackHasher o.manifestSha256
    let n ← sbm11HandleCounter.modifyGet fun c => (c + 1, c + 1)
    let h := s!"sbm11-{n}"
    sbm11HandleTable.modify (·.insert h ss)
    return okWith
      [ ("handle", .string h)
      , ("generation", .string genName)
      , ("terms", .number (toString ss.dictHdr.termCount))
      , ("artifacts", .number (toString ss.manifest.artifacts.length))
      , ("verify", .string v.name)
      , ("manifestSha256", .string (L4Factoidal.Storage.Sbm11.HostVerify.hexOf ss.manifestSha256))
      , ("bytesRead", .number (toString (← ss.bytesRead.get))) ]
  catch e => return errJson s!"sbm11Open: {ioMessage e}"

private structure QueryOpts where
  base : Option String := none
  sparql12 : Bool := false
  reference : Bool := false

private def queryOpts (optionsJson : String) : Except String QueryOpts := do
  if optionsJson.trimAscii.isEmpty then return {}
  match parseJson optionsJson with
  | .error e => throw s!"optionsJson: {toString e}"
  | .ok (.object members) =>
    let mut o : QueryOpts := {}
    for (k, v) in members do
      match k, v with
      | "base", .string s => o := { o with base := some s }
      | "base", .null => pure ()
      | "sparql12", .bool b => o := { o with sparql12 := b }
      | "reference", .bool b => o := { o with reference := b }
      | k, _ => throw s!"optionsJson: member {k} is not base (string), sparql12 or reference (boolean)"
    return o
  | .ok _ => throw "optionsJson must be a JSON object"

/-- Run `sbm11Query`: the envelope fields (without the result) and the
    result bytes, or an error message. -/
def sbm11Run (h sparql optionsJson : String) : IO (Except String (List (String × Json) × ByteArray)) := do
  match (← sbm11HandleTable.get)[h]? with
  | none => return .error s!"sbm11Query: no open SBM11 handle {h}"
  | some held =>
  match queryOpts optionsJson with
  | .error e => return .error s!"sbm11Query: {e}"
  | .ok o =>
  match parseSparql sparql o.base (if o.sparql12 then .v12 else .v11) with
  | .error e => return .error s!"sbm11Query: SPARQL parse error at {e.pos}: {e.msg}"
  | .ok q =>
  -- the query runs on references of its own (`Session.localize`: the held
  -- session is reachable from the handle table, a global)
  let ss ← held.localize
  let b0 ← ss.bytesRead.get
  let r0 ← ss.reads.get
  let out ← IO.mkRef (ByteArray.emptyWithCapacity 4096)
  try
    let clockEnv ← emptyEnvNow
    let outcome ← runOne ss clockEnv q (fun b => out.modify (· ++ b)) o.reference
    held.keep ss
    let format := match q.form with
      | .select _ | .ask => "srj"
      | _ => "ntriples"
    return .ok
      ([ ("path", .string outcome.path)
       , ("rows", .number (toString outcome.rows))
       , ("format", .string format)
       , ("bytesRead", .number (toString ((← ss.bytesRead.get) - b0)))
       , ("reads", .number (toString ((← ss.reads.get) - r0))) ], ← out.get)
  catch e => return .error s!"sbm11Query: {ioMessage e}"

/-- `sbm11Query(handle, sparql, optionsJson)` through `callIO`: the result as
    the member `result` of the envelope. -/
def sbm11Query (h sparql optionsJson : String) : IO String := do
  match ← sbm11Run h sparql optionsJson with
  | .error e => return errJson e
  | .ok (fields, bytes) => return okWith (fields ++ [("result", .string (String.fromUTF8! bytes))])

/-- `sbm11Query(handle, sparql, optionsJson)` through `callBlobIO`: the result
    bytes as the out region, not in the envelope. A large answer is then not
    escaped into a JSON string and parsed again (olympics q20: 18.8 MB). -/
def sbm11QueryBlob (h sparql optionsJson : String) : IO (String × ByteArray) := do
  match ← sbm11Run h sparql optionsJson with
  | .error e => return (errJson e, ByteArray.empty)
  | .ok (fields, bytes) => return (okWith (fields ++ [("resultBytes", .number (toString bytes.size))]), bytes)

/-- `sbm11Close(handle)`. -/
def sbm11Close (h : String) : IO String := do
  if (← sbm11HandleTable.get).contains h then
    sbm11HandleTable.modify (·.erase h)
    return okWith []
  return errJson s!"sbm11Close: no open SBM11 handle {h}"

/-- The bytes of the whole file `file` of `n` bytes, through the host. -/
private def readWholeFile (host : Host) (file : String) (n : Nat) : IO ByteArray := do
  if n == 0 then return ByteArray.empty
  let b ← host.readAt file 0 n
  if b.size != n then ioErr s!"{file}: the host returned {b.size} bytes for a read of {n}"
  return b

/-- `sbm11Verify(source)`: the activation check of the generation directory
    `source` (module comment). -/
def sbm11Verify (source : String) : IO String := do
  try
    let host := hostOf source
    let ss ← openSession host .merkle sbm11PackHasher
    let m := ss.manifest
    let mut bytes := 0
    let mut files := 1
    for a in m.artifacts do
      let b ← readWholeFile host a.file a.bytes
      let (entry, leaves) := L4Factoidal.Storage.Sbm11.PackBytes.artifactOf sbm11PackHasher a.role b
      unless entry == a do
        ioErr s!"{a.file}: the manifest entry of these bytes (length, SHA-256, Merkle root) is not the entry in {manifestName}"
      let side := a.file ++ ".merkle"
      let some n ← host.size side | ioErr s!"{side}: not found"
      let sb ← readWholeFile host side n
      unless sb == leaves do ioErr s!"{side}: not the Merkle leaves of {a.file}"
      bytes := bytes + b.size + sb.size
      files := files + 2
    return okWith
      [ ("artifacts", .number (toString m.artifacts.length))
      , ("files", .number (toString files))
      , ("bytes", .number (toString bytes))
      , ("quads", .number (toString m.quads))
      , ("terms", .number (toString m.terms))
      , ("manifestSha256", .string (L4Factoidal.Storage.Sbm11.HostVerify.hexOf ss.manifestSha256)) ]
  catch e => return errJson s!"sbm11Verify: {ioMessage e}"

/-- The manifest names of the IBK3, IBK4 and IBK5 generations, in the order
    `Harness.ShardMerklePread.readManifest` tries them. -/
def ibkManifestNames : List String := ["manifest.sbm2", "manifest.sbm1"]

/-- `storeLayout(source)` (module comment). -/
def storeLayout (source : String) : IO String := do
  try
    let h := hostOf source
    let (g, name) ← do
      match ← h.size currentName with
      | none => pure (h, "")
      | some n =>
        let b ← readWholeFile h currentName n
        let some name := String.fromUTF8? b | ioErr "CURRENT is not valid UTF-8"
        unless safeGenerationName name do ioErr "CURRENT does not name a safe generation directory"
        pure (h.under name, name)
    let answer (layout manifest : String) : String :=
      okWith [("layout", .string layout), ("generation", .string name), ("manifest", .string manifest)]
    if (← g.size manifestName).isSome then return answer "sbm11" manifestName
    for f in ibkManifestNames do
      if (← g.size f).isSome then return answer "ibk" f
    let where_ := if name.isEmpty then source else s!"{source}/{name} (named by CURRENT)"
    return errJson s!"storeLayout: {where_} holds no {manifestName}, {String.intercalate " or " ibkManifestNames}; it is not a generation directory or a collection root"
  catch e => return errJson s!"storeLayout: {ioMessage e}"

/-- The op names of this module, served by `callIO` only. -/
def sbm11OpNames : List String := ["sbm11Open", "sbm11Query", "sbm11Close", "sbm11Verify", "storeLayout"]

end L4Wasm.Ops
