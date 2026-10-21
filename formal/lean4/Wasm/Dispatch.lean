/-
Wasm.Dispatch — the dispatch entries `L4Wasm.call` and `L4Wasm.callIO`.

  L4Wasm.call   (op : String) (argsJson : String) : String
  L4Wasm.callIO (op : String) (argsJson : String) : IO String

`argsJson` is a JSON ARRAY OF STRINGS (positional arguments); the
result is one JSON envelope, `{"ok":true,…}` or
`{"ok":false,"error":"…"}`. Method names and envelopes match the F*
npm entry point (`bin/npm-entry/entry_jsoo.ml`) op for op, so the JS
side can drive either engine through the same result handling
(`api.js`'s `entryResult`).

`call` serves the stateless ops. `callIO` serves those SAME ops
unchanged (it delegates to `call`) PLUS the dataset-handle ops of
https://github.com/danbri/factoidal/issues/585, whose store
(`Wasm/Ops/Handles.lean`) is an `IO.Ref` a pure entry cannot reach.
The wire entry (`l4_call_c` in `Wasm/l4_shim.c`) and the native CLI
(`Wasm/Main.lean`) route through `callIO`; the pure `call` stays
`@[export]`ed as `l4_call` with its signature unchanged.

The op tables below are the whole v1 surface plus a reflection op:

  "ops" -> {"ok":true,"abiVersion":"…","ops":[…names…]}

(through `callIO` the list includes the handle ops; through the pure
`call` it does not, because that entry cannot serve them).

The arms of the ops the core engine also serves are in
`Wasm/CoreDispatch.lean` (`Core.callArgsBy` and `Core.callIOArgsBy`); `call`
and `callIO` below try those first, with `jsonLdReader` as the reader of the
syntaxes outside `Wasm/Ops/Parse.lean`'s table, so each op has one arm and the
two engines answer a core op with the same envelope
(https://github.com/danbri/factoidal/issues/713 stage 4). The name lists below
are the whole full table, core ops included; `Wasm/CoreDispatchTests.lean`
checks them against the core table at build time.

This module owns the tables; the op bodies live in `Wasm/Ops/*.lean`
(split-ready: each imports only the `L4Factoidal.*` modules it needs —
never the umbrella, whose initializer dies under wasm32; see
`Wasm/Abi.lean`'s import note). The phase-1 `bgpQuery`/`version`
exports in `Wasm/Abi.lean` are a separate, pinned surface (hub post
36) and are not routed through this dispatch.
-/
import Wasm.CoreDispatch
import Wasm.Ops.ParseJsonLd
import Wasm.Ops.Parse
import Wasm.Ops.Query
import Wasm.Ops.Reason
import Wasm.Ops.ReasonDl
import Wasm.Ops.Canon
import Wasm.Ops.Block
import Wasm.Ops.Store
import Wasm.Ops.StoreHandles
import Wasm.Ops.StoreServe
import Wasm.Ops.CL
import Wasm.Ops.Proof
import Wasm.Ops.Handles
import Wasm.Ops.DatasetFull
import Wasm.Ops.Pack
import Wasm.Ops.ExtFns
import Wasm.Ops.Lws
import Wasm.Ops.Solid
import Wasm.Ops.Toan
import Wasm.Ops.Xmpp
import Wasm.Ops.Crypto
import Wasm.Ops.Formats
import Wasm.Ops.Reasoning
import Wasm.Ops.QueryExtras
import Wasm.Ops.ServiceReg
import Wasm.Ops.Maths
import Wasm.Ops.Vc
import Wasm.Ops.Lenient
import Wasm.Ops.Validate
import Wasm.Ops.ShExValidate
import Wasm.Ops.QueryHdt

namespace L4Wasm

open L4Wasm.Ops
open L4Factoidal.JSON

/-- Version of the DISPATCH ABI's envelope contract. "1" — the same
value the F* npm entry reports (`entry_jsoo.ml`'s `abi_version`),
because the envelopes are the same contract. Bump when a signature or
JSON shape changes. -/
def dispatchAbiVersion : String := "1"

/-- The stateless op names, in the order they are matched. Served by
both `call` and `callIO`. -/
def opNames : List String :=
  [ "parseToDatasetJson"
  , "queryDataset"
  , "updateDataset"
  , "serializeNQuads"
  , "serializeTurtle"
  , "canonicalizeToNQuads"
  , "scanIBK2Predicate"
  , "scanIBK3Predicate"
  , "queryIBK3BlockSetPreview"
  , "storeManifestInspect"
  , "storeQueryPlan"
  , "storeQuery"
  , "activateVerify"
  , "owlClosure"
  , "owlIsConsistent"
  , "owlEntails"
  , "rhoDfClosure"
  , "rhoDfFragmentCheck"
  , "rdfsPlusClosure"
  , "clParse"
  , "clSerialize"
  , "clAlphaNorm"
  , "clNormalize"
  , "clFiniteSat"
  , "proofCheck"
  , "proofInspect"
  , "toanSummation"
  , "toanProduct"
  , "toanSimplify"
  , "toanDiff"
  , "toanSubst"
  , "xmppJidParse"
  , "xmppJidRender"
  , "xmppStreamHeaderParse"
  , "xmppStreamHeaderRender"
  , "xmppFeaturesFor"
  , "aeadSeal"
  , "aeadOpen"
  , "hpkeSeal"
  , "hpkeOpen"
  , "xmppStanzaParse"
  , "ops" ]

/-- The op names that read a BLOB REGION as well as their string arguments,
served by `callBlob` below.

The dispatch ABI carries strings, so an op that must read megabytes of block
bytes cannot use it: hexadecimal doubles the bytes over the boundary and then
walks every character on the way in. `callBlob` takes one contiguous byte
region the host wrote directly into the wasm heap, and the op's JSON argument
describes windows into it (`Wasm/Ops/Store.lean`). Through the plain `call`
these ops still answer — with an empty region, so a descriptor naming blob
bytes is refused by name rather than silently reading nothing. -/
def blobOpNames : List String := [ "storeQuery", "activateVerify", "queryHdt" ]

/-- The op names that also RETURN a contiguous byte region, served by
`callBlobIO` below (the `l4_call_blob_io` C export, wired to
`l4_call_blob_io_c` in `Wasm/l4_shim.c`).

`blobOpNames` above carries bytes IN. This table carries bytes OUT, for the
same reason and with no encoding: an artifact returned as hexadecimal doubles
the bytes over the boundary, and base64 was refused (owner, 2026-09-03). The
measured cost on the read path was 242,416 bytes and 96 ms for hexadecimal
against 4,893 bytes and 70 ms for the raw region.

`blobEcho` is a self test and nothing else: it builds a region whose byte `i`
is `(i * 7 + 3) mod 256`, so a host can prove the whole path — Lean, the
shim, the Emscripten export, the JavaScript binder — moves every byte without
truncation.

`packFeed` and `packNext` (`Wasm/Ops/Pack.lean`) are the pack operations of
stage C in `docs/designissues/2026-09-03-npm-pack-in-wasm.md`. `packFeed`
reads one chunk of the source from the IN region and builds no OUT region;
`packNext` reads nothing and returns one artifact's bytes. Both are here
because both are served by the one entry which carries a region in either
direction. -/
def blobIoOpNames : List String :=
  [ "blobEcho", "packFeed", "packNext", "storeServeRequest", "storeServeCommit" ]

/-- Largest out region `blobEcho` builds: 67,108,864 bytes. A count above
this is refused by name rather than made into an allocation the module
cannot serve. -/
def blobEchoMaxBytes : Nat := 67108864

/-- Byte `i` of the self-test region: `(i * 7 + 3) mod 256`. The stride is
odd and coprime with 256, so a host that drops, duplicates or reorders a
byte sees it. -/
def blobEchoByte (i : Nat) : UInt8 := UInt8.ofNat ((i * 7 + 3) % 256)

private def blobEchoFill : Nat → Nat → ByteArray → ByteArray
  | 0,          _, acc => acc
  | Nat.succ k, i, acc => blobEchoFill k (i + 1) (acc.push (blobEchoByte i))

/-- The `n`-byte self-test region. -/
def blobEchoRegion (n : Nat) : ByteArray :=
  blobEchoFill n 0 (ByteArray.emptyWithCapacity n)

/-- `blobEcho(lengthHint)`: `{"ok":true,"bytes":N}` plus an `N`-byte out
region. This op has no RDF, SPARQL or storage content — it exists to prove
the byte path, so it deliberately has no `Wasm/Ops/*.lean` module. -/
private def blobEcho (arg : String) : String × ByteArray :=
  match arg.toNat? with
  | none => (errJson s!"blobEcho: '{arg}' is not a decimal byte count",
             ByteArray.empty)
  | some n =>
    if n > blobEchoMaxBytes then
      (errJson s!"blobEcho: {n} bytes is above the {blobEchoMaxBytes}-byte limit",
       ByteArray.empty)
    else
      ((Json.object [("ok", .bool true), ("bytes", .number (toString n))]).toString,
       blobEchoRegion n)

private def arity1 (op : String) (f : String → String) :
    List String → String
  | [a] => f a
  | args => errJson s!"{op} expects 1 argument, got {args.length}"

private def arity2 (op : String) (f : String → String → String) :
    List String → String
  | [a, b] => f a b
  | args => errJson s!"{op} expects 2 arguments, got {args.length}"

private def arity3 (op : String) (f : String → String → String → String) :
    List String → String
  | [a, b, c] => f a b c
  | args => errJson s!"{op} expects 3 arguments, got {args.length}"

private def arity4 (op : String) (f : String → String → String → String → String) :
    List String → String
  | [a, b, c, d] => f a b c d
  | args => errJson s!"{op} expects 4 arguments, got {args.length}"

/-- The dataset-handle op names (`Wasm/Ops/Handles.lean`), served ONLY
by `callIO` — the pure `call` cannot reach the handle store and
answers "unknown op" for these. -/
def handleOpNames : List String :=
  [ "datasetOpen"
  , "datasetQuery"
  , "datasetQuery12"
  , "datasetUpdate"
  , "datasetSerialize"
  , "datasetSerializeWith"
  , "datasetClose"
  , "datasetClone"
  , "datasetCanonicalize"
  , "datasetClosure"
  , "datasetShaclValidate"
  , "datasetQueryRaw"
  , "datasetFormats"
  , "detectFormat"
  , "datasetMatch"
  , "datasetMatchCount"
  , "datasetAddQuads"
  , "datasetDeleteQuads"
  , "datasetFromCsvw"
  , "datasetFromRml"
  , "datasetFromJsonLd"
  , "datasetToJsonLd"
  , "datasetShexValidate"
  , "datasetRifEval" ]

/-- The store-handle op names (`Wasm/Ops/StoreHandles.lean`), served ONLY by
`callIO` and `callBlobIO` — the pure `call` cannot reach the store-handle
table. `storeOpen` also carries a byte region IN; through `callIO`, which
carries none, it still answers, with an empty region, so the diagnostic
`{"key","bytes":"<hex>"}` descriptor form works through the plain entry and
through `Wasm/Main.lean`'s `callseq`. -/
def storeHandleOpNames : List String :=
  [ "storeOpen"
  , "storeHandleQuery"
  , "storeHandleList"
  , "storeHandleClose" ]

/-- The SPARQL 1.1 §17.6 extension-registry op names
(`Wasm/Ops/ExtFns.lean`), served ONLY by `callIO` and `callBlobIO` — the
registry is an `IO.Ref` the pure `call` cannot reach, so that entry keeps
answering with the built-in `geof:` table alone. -/
def extOpNames : List String :=
  [ "extRegister"
  , "extUnregister"
  , "extClear"
  , "extList" ]

/-- The pack op names (`Wasm/Ops/Pack.lean`), served ONLY by `callIO` and
`callBlobIO` — the pure `call` cannot reach the pack table. `packFeed` and
`packNext` also need a byte region and are listed in `blobIoOpNames`; through
`callIO`, which carries none, they answer an error naming the entry they
need rather than feeding nothing. -/
def packOpNames : List String :=
  [ "packBegin"
  , "packFeed"
  , "packEndPass"
  , "packNext"
  , "packFinish"
  , "packClose" ]

/-- The SPARQL endpoint op names over a served generation
(`Wasm/Ops/StoreServe.lean`, https://github.com/danbri/factoidal/issues/669),
served ONLY by `callIO` and `callBlobIO`: the served handles are an `IO.Ref`.
`storeServeRequest` and `storeServeCommit` answer a byte region, so they are
in `blobIoOpNames` too. -/
def storeServeOpNames : List String :=
  [ "storeServeKeys"
  , "storeServeOpen"
  , "storeServeRequest"
  , "storeServeCommit"
  , "storeServeClose"
  , "tdb2ServeKeys"
  , "tdb2ServeOpen" ]

/-- The Linked Web Storage 1.0 and Solid Protocol op names
(`Wasm/Ops/Lws.lean`, `Wasm/Ops/Solid.lean`), served ONLY by `callIO`: the
server operations hold a storage in a handle table, which the pure `call`
cannot reach. The two client operations are pure but are listed here so a
host finds the whole protocol surface under one entry.

The request and response documents are stated in
`docs/lws-solid-conformance.md` § "wasm ABI". -/
def lwsSolidOpNames : List String :=
  [ "lwsOpen"
  , "lwsStep"
  , "lwsClose"
  , "lwsSnapshot"
  , "lwsFetched"
  , "solidOpen"
  , "solidStep"
  , "solidClose"
  , "solidSnapshot"
  , "solidClientRequest"
  , "solidClientResponse" ]

/-- The format, transform and reasoning op names of
`Wasm/Ops/Formats.lean`, `Wasm/Ops/Reasoning.lean` and
`Wasm/Ops/QueryExtras.lean`: the operations of the F* npm entry that the
table did not serve before https://github.com/danbri/factoidal/issues/713
stage 1, and the SHACL and ShEx validation of `Wasm/Ops/Validate.lean`
(stage 3). All are pure and served by both `call` and `callIO`; `queryHdt`
also reads a byte region (it is in `blobOpNames`). -/
def formatOpNames : List String :=
  [ "jsonldToRdf"
  , "jsonldFromRdf"
  , "rmlMap"
  , "csvwToRdf"
  , "xmlWellformed"
  , "xpathEval"
  , "xsltTransform"
  , "schematronValidate"
  , "jsonSchemaValidate"
  , "mathmlEval"
  , "xformsRecalc"
  , "rifEval"
  , "tableauMaterialise"
  , "tableauDlInconsistent"
  , "queryRaw"
  , "queryHdt"
  , "shaclValidate"
  , "shexValidate" ]

/-- `queryDataset12`, the stateless SPARQL 1.2 query op (`Wasm/Ops/Query.lean`),
served ONLY by `callIO` and `callBlobIO`, like `queryDataset`'s IO form: the
caller's §17.6 extension and SERVICE registrations are in scope. -/
def query12OpNames : List String := [ "queryDataset12" ]

/-- The SPARQL SERVICE endpoint registry op names
(`Wasm/Ops/ServiceReg.lean`), served ONLY by `callIO` and `callBlobIO` —
the registry is an `IO.Ref` the pure `call` cannot reach. -/
def serviceOpNames : List String :=
  [ "registerServiceEndpoint"
  , "clearServiceEndpoints" ]

/-- Stage 2 of https://github.com/danbri/factoidal/issues/713: the matrix and
sigmoid ops (`Wasm/Ops/Maths.lean`) and the VC and DID ops (`Wasm/Ops/Vc.lean`).
They are stateless, so `call` serves them and `callIO` reaches them through its
fall-through to `call`. The names are appended to every `ops` reflection by
`opsReflectionFor`; the arms are in the fall-through case of `call`. -/
def stage2OpNames : List String :=
  mathsOpNames ++ vcOpNames ++ parityOpNames ++ lenientOpNames ++ deltaLogOpNames

/-- Serve a stage 2 op of the full table, or answer the unknown-op error.
`serializeTurtleWith` and `parseDocument` (the lenient parse,
https://github.com/danbri/factoidal/issues/716) are core ops and are served
before this by `Core.callArgsBy`. -/
private def callStage2 (op : String) (args : List String) : String :=
  match callMaths op args with
  | some r => r
  | none =>
    match callVc op args with
    | some r => r
    | none => errJson s!"unknown op '{op}'"

/-- `{"ok":true,"abiVersion":"…","ops":[…],"blobOps":[…],"blobIoOps":[…]}`. -/
private def opsReflectionFor (names : List String) : String :=
  (Json.object
    [ ("ok", .bool true)
    , ("abiVersion", .string dispatchAbiVersion)
    , ("engine", .string "full")
    , ("ops", .array ((names ++ stage2OpNames).map Json.string))
    , ("blobOps", .array (blobOpNames.map Json.string))
    , ("blobIoOps", .array (blobIoOpNames.map Json.string)) ]).toString

private def opsReflection : String := opsReflectionFor (opNames ++ formatOpNames)

/-- The `ops` reflection of `callIO`: every op of the full table. -/
def opsReflectionIO : String :=
  opsReflectionFor
    (opNames ++ handleOpNames ++ storeHandleOpNames ++ storeServeOpNames ++ packOpNames
       ++ extOpNames ++ lwsSolidOpNames
       ++ formatOpNames ++ serviceOpNames
       ++ query12OpNames)

/-- The dispatch entry the `l4_call` C export serves. The core ops are
served by `Core.callArgsBy` with the JSON-LD reader; the arms here are the
ops of the full table only.

This entry is pure and has no clock. A `NOW()` in a query (SPARQL 1.1
§17.4.5.1) is bound only when the caller passes the instant: `queryDataset`,
`updateDataset`, `queryRaw`, `storeQuery` and `queryHdt` take an optional last
argument `now`, an `xsd:dateTime` lexical form (after the base IRI where an op
has one), and an empty string means none. A text that is not a dateTime lexical
form is an error envelope (`Core.nowArg`,
https://github.com/danbri/factoidal/issues/748). `callIO` reads the clock once
per execution instead (https://github.com/danbri/factoidal/issues/743). -/
def call (op : String) (argsJson : String) : String :=
  match decodeArgs argsJson with
  | .error e => errJson e
  | .ok args =>
    match (if op == "ops" then none else Core.callArgsBy jsonLdReader op args) with
    | some r => r
    | none =>
    match op with
    | "scanIBK2Predicate"    => arity2 op scanIBK2Predicate args
    | "scanIBK3Predicate"    => arity3 op scanIBK3Predicate args
    | "queryIBK3BlockSetPreview"    => arity3 op queryIBK3BlockSetPreview args
    | "storeManifestInspect" => arity1 op storeManifestInspect args
    | "storeQueryPlan"       => arity2 op storeQueryPlan args
    | "storeQuery"           => Core.arity3Now op (fun a b c n => storeQuery a b c ByteArray.empty [] n) args
    | "activateVerify"       => arity2 op (fun a b => activateVerify a b ByteArray.empty) args
    | "owlIsConsistent"      => arity2 op owlIsConsistent args
    | "owlEntails"           => arity3 op owlEntails args
    | "clParse"              => arity1 op clParse args
    | "clSerialize"          => arity1 op clSerialize args
    | "clAlphaNorm"          => arity1 op clAlphaNorm args
    | "clNormalize"          => arity1 op clNormalize args
    | "clFiniteSat"          => arity2 op clFiniteSat args
    | "proofCheck"           => arity1 op proofCheck args
    | "proofInspect"         => arity1 op proofInspect args
    | "toanSummation"        => arity4 op toanSummation args
    | "toanProduct"          => arity4 op toanProduct args
    | "toanSimplify"         => arity1 op toanSimplify args
    | "toanDiff"             => arity2 op toanDiff args
    | "toanSubst"            => arity3 op toanSubst args
    | "xmppJidParse"         => arity1 op xmppJidParse args
    | "xmppJidRender"        => arity1 op xmppJidRender args
    | "xmppStreamHeaderParse"  => arity1 op xmppStreamHeaderParse args
    | "xmppStreamHeaderRender" => arity1 op xmppStreamHeaderRender args
    | "xmppFeaturesFor"      => arity1 op xmppFeaturesFor args
    | "aeadSeal"             => arity1 op aeadSeal args
    | "aeadOpen"             => arity1 op aeadOpen args
    | "hpkeSeal"             => arity1 op hpkeSeal args
    | "hpkeOpen"             => arity1 op hpkeOpen args
    | "xmppStanzaParse"      => arity1 op xmppStanzaParse args
    -- Format, transform and reasoning ops (`formatOpNames`).
    | "jsonldToRdf"          => arity2 op jsonldToRdf args
    | "jsonldFromRdf"        => arity2 op jsonldFromRdf args
    | "rmlMap"               => arity3 op rmlMap args
    | "csvwToRdf"            => arity3 op csvwToRdf args
    | "xmlWellformed"        => arity1 op xmlWellformed args
    | "xpathEval"            => arity2 op xpathEval args
    | "xsltTransform"        => arity2 op xsltTransform args
    | "schematronValidate"   => arity2 op schematronValidate args
    | "jsonSchemaValidate"   => arity2 op jsonSchemaValidate args
    | "mathmlEval"           => arity2 op mathmlEval args
    | "xformsRecalc"         => arity2 op xformsRecalc args
    | "rifEval"              => arity2 op rifEval args
    | "tableauMaterialise"   => arity1 op tableauMaterialise args
    | "tableauDlInconsistent" => arity1 op tableauDlInconsistent args
    | "queryHdt"             => Core.arity1Now op (fun a n => queryHdt a ByteArray.empty n) args
    | "shexValidate"         => arity4 op shexValidate args
    | "ops"                  => opsReflection
    | _                      => callStage2 op args

/-- The dispatch entry the `l4_call_blob` C export serves: the string
arguments of `call`, plus one byte region. Every other op delegates to `call`,
envelope for envelope, so a host may route everything through this entry.
This entry is pure and has no clock. A `NOW()` in a `storeQuery` or `queryHdt`
query (SPARQL 1.1 §17.4.5.1) is bound only when the caller passes the instant:
both ops take an optional last argument `now`, an `xsd:dateTime` lexical form,
after their other arguments (`storeQuery` fourth, `queryHdt` second), and an
empty string means none (https://github.com/danbri/factoidal/issues/748). The
IO entry `callBlobIO` reads the clock once per query and serves both ops with it
(https://github.com/danbri/factoidal/issues/743). -/
def callBlob (op : String) (argsJson : String) (blob : ByteArray) : String :=
  match op with
  | "storeQuery" =>
      match decodeArgs argsJson with
      | .error e => errJson e
      | .ok args => Core.arity3Now op (fun a b c n => storeQuery a b c blob [] n) args
  | "activateVerify" =>
      match decodeArgs argsJson with
      | .error e => errJson e
      | .ok [a, b] => activateVerify a b blob
      | .ok args => errJson s!"activateVerify expects 2 arguments, got {args.length}"
  | "queryHdt" =>
      match decodeArgs argsJson with
      | .error e => errJson e
      | .ok args => Core.arity1Now op (fun a n => queryHdt a blob n) args
  | _ => call op argsJson

private def arityIO1 (op : String) (f : String → IO String) :
    List String → IO String
  | [a] => f a
  | args => pure (errJson s!"{op} expects 1 argument, got {args.length}")

private def arityIO2 (op : String) (f : String → String → IO String) :
    List String → IO String
  | [a, b] => f a b
  | args => pure (errJson s!"{op} expects 2 arguments, got {args.length}")

private def arityIO3 (op : String) (f : String → String → String → IO String) :
    List String → IO String
  | [a, b, c] => f a b c
  | args => pure (errJson s!"{op} expects 3 arguments, got {args.length}")

/-- The dispatch entry the wire (`l4_call_c` via the `l4_call_io` C
export) and the native CLI serve: the stateful ops, plus every stateless op
via `call`, envelope for envelope. The core ops that need `IO` (dataset
handles, the §17.6 and SERVICE registries, the IO forms of `queryDataset`,
`queryDataset12`, `parseToDatasetJson` and `parseDocument`) are served by
`Core.callIOArgsBy` with the JSON-LD reader; the arms here are the ops of the
full table only.

The ops that evaluate a query or an update read the system clock once per
execution, so `NOW()` is bound (SPARQL 1.1 §17.4.5.1,
https://github.com/danbri/factoidal/issues/743). They take no `now` argument:
the instant is an argument of the pure entries `call` and `callBlob` only
(https://github.com/danbri/factoidal/issues/748). -/
def callIO (op : String) (argsJson : String) : IO String :=
  let withArgs (k : List String → IO String) : IO String :=
    match decodeArgs argsJson with
    | .error e  => pure (errJson e)
    | .ok args  => k args
  let core : Option (IO String) :=
    match decodeArgs argsJson with
    | .ok args => if op == "ops" then none else Core.callIOArgsBy jsonLdReader op args
    | .error _ => none
  match core with
  | some r => r
  | none =>
  match op with
  -- `storeQuery` is served here (rather than by the pure `call`) so a §17.6
  -- registration reaches it, as `Core.callIOArgsBy` does for `queryDataset`.
  | "storeQuery"       => withArgs (arityIO3 op
                            (fun a b c => Ops.storeQueryIO a b c ByteArray.empty))
  -- packBegin takes an optional third argument, the base IRI, and an
  -- optional fourth, the publication batch in source bytes. Fewer arguments
  -- means no base and the default batch, which keeps every host written
  -- against the stage-C contract working and makes a relative IRI a parse
  -- error rather than a silently different term.
  | "packBegin" =>
      withArgs (fun args =>
        match args with
        | [a, b]       => Ops.packBegin a b "" ""
        | [a, b, c]    => Ops.packBegin a b c ""
        | [a, b, c, d] => Ops.packBegin a b c d
        | args => pure (errJson s!"packBegin expects 2, 3 or 4 arguments, got {args.length}"))
  | "packEndPass"      => withArgs (arityIO1 op Ops.packEndPass)
  | "packFinish"       => withArgs (arityIO1 op Ops.packFinish)
  | "packClose"        => withArgs (arityIO1 op Ops.packClose)
  | "packFeed" | "packNext" =>
      pure (errJson s!"{op} carries a byte region; call it through l4_call_blob_io")
  | "storeOpen"        => withArgs (arityIO2 op (fun a b => Ops.storeOpen a b ByteArray.empty))
  | "storeHandleQuery" => withArgs (arityIO2 op Ops.storeHandleQuery)
  -- The dataset-handle ops of the full engine (`Wasm/Ops/DatasetFull.lean`).
  | "datasetFromCsvw"  => withArgs (arityIO3 op Ops.datasetFromCsvw)
  | "datasetFromRml"   => withArgs (arityIO3 op Ops.datasetFromRml)
  | "datasetFromJsonLd" => withArgs (arityIO2 op Ops.datasetFromJsonLd)
  | "datasetToJsonLd"  => withArgs (arityIO2 op Ops.datasetToJsonLd)
  | "datasetShexValidate" => withArgs (fun args =>
      match args with
      | [a, b, c, d] => Ops.datasetShexValidate a b c d
      | _ => pure (errJson s!"{op} expects 4 arguments, got {args.length}"))
  | "datasetRifEval"   => withArgs (arityIO2 op Ops.datasetRifEval)
  | "storeHandleClose" => withArgs (arityIO1 op Ops.storeHandleClose)
  -- The SPARQL endpoint over a served generation (issue 669). The open
  -- carries a byte region; through this entry it takes the hex descriptor
  -- form only, like `storeOpen`.
  | "storeServeKeys"   => withArgs (fun args =>
      match args with
      | [a] => pure (Ops.storeServeKeys a)
      | args => pure (errJson s!"storeServeKeys expects 1 argument, got {args.length}"))
  | "storeServeOpen"   => withArgs (fun args =>
      match args with
      | [a, b, c, d] => Ops.storeServeOpen a b c d ByteArray.empty
      | args => pure (errJson s!"storeServeOpen expects 4 arguments, got {args.length}"))
  | "storeServeClose"  => withArgs (arityIO1 op Ops.storeServeClose)
  | "tdb2ServeKeys"    => withArgs (fun args =>
      match args with
      | [a, b] => pure (Ops.tdb2ServeKeys a b)
      | args => pure (errJson s!"tdb2ServeKeys expects 2 arguments, got {args.length}"))
  | "tdb2ServeOpen"    => withArgs (fun args =>
      match args with
      | [a, b] => Ops.tdb2ServeOpen a b ByteArray.empty
      | args => pure (errJson s!"tdb2ServeOpen expects 2 arguments, got {args.length}"))
  | "storeServeRequest" | "storeServeCommit" =>
      pure (errJson s!"{op} answers a byte region; call it through l4_call_blob_io")
  -- Linked Web Storage 1.0 and the Solid Protocol
  -- (https://github.com/danbri/factoidal/issues/659). `lwsOpen`,
  -- `solidOpen`, `solidClientRequest` and `solidClientResponse` take their
  -- arguments as strings and answer one envelope, like every other op.
  | "lwsOpen"          => withArgs (arityIO1 op Ops.lwsOpen)
  | "lwsStep"          => withArgs (arityIO2 op Ops.lwsStep)
  | "lwsClose"         => withArgs (arityIO1 op Ops.lwsClose)
  | "lwsSnapshot"      => withArgs (arityIO1 op Ops.lwsSnapshot)
  | "lwsFetched"       => withArgs (arityIO2 op Ops.lwsFetched)
  | "solidSnapshot"    => withArgs (arityIO1 op Ops.solidSnapshot)
  | "solidOpen"        => withArgs (arityIO1 op Ops.solidOpen)
  | "solidStep"        => withArgs (arityIO2 op Ops.solidStep)
  | "solidClose"       => withArgs (arityIO1 op Ops.solidClose)
  | "solidClientRequest" =>
      withArgs (fun args =>
        match args with
        | [a, b] => pure (Ops.solidClientRequest a b)
        | args => pure (errJson s!"solidClientRequest expects 2 arguments, got {args.length}"))
  | "solidClientResponse" =>
      withArgs (fun args =>
        match args with
        | [a, b] => pure (Ops.solidClientResponse a b)
        | args => pure (errJson s!"solidClientResponse expects 2 arguments, got {args.length}"))
  | "storeHandleList" =>
      withArgs (fun args =>
        match args with
        | [] => Ops.storeHandleList
        | args => pure (errJson s!"storeHandleList expects 0 arguments, got {args.length}"))
  | "ops"              => pure opsReflectionIO
  | _                  => pure (call op argsJson)

/-- The dispatch entry the `l4_call_blob_io` C export serves: the string
arguments of `callIO`, ONE byte region in, and ONE byte region out.

Only the ops of `blobIoOpNames` build an out region. Every other op answers
exactly as it does today with an EMPTY out region — the blob-in ops of
`blobOpNames` still read their region through `callBlob`, and everything else
goes to `callIO` — so a host may route every call through this entry without
changing any envelope. -/
def callBlobIO (op : String) (argsJson : String) (blob : ByteArray) :
    IO (String × ByteArray) :=
  match op with
  | "blobEcho" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => pure (blobEcho a)
      | .ok args  => pure (errJson s!"blobEcho expects 1 argument, got {args.length}",
                           ByteArray.empty)
  | "packFeed" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => do pure (← Ops.packFeed a blob, ByteArray.empty)
      | .ok args  => pure (errJson s!"packFeed expects 1 argument, got {args.length}",
                           ByteArray.empty)
  | "packNext" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => Ops.packNext a
      | .ok args  => pure (errJson s!"packNext expects 1 argument, got {args.length}",
                           ByteArray.empty)
  -- `storeOpen` is the one op that needs BOTH the incoming region and the
  -- handle table, so neither `callBlob` (pure) nor `callIO` (no region) can
  -- serve it. It builds no out region.
  -- `storeQuery` needs BOTH the incoming region and the §17.6 registry,
  -- so neither `callBlob` (pure) nor `callIO` (no region) can serve it.
  | "storeQuery" =>
      match decodeArgs argsJson with
      | .error e      => pure (errJson e, ByteArray.empty)
      | .ok [a, b, c] => do pure (← Ops.storeQueryIO a b c blob, ByteArray.empty)
      | .ok args      => pure (errJson s!"storeQuery expects 3 arguments, got {args.length}",
                               ByteArray.empty)
  -- `queryHdt` is served here so that `NOW()` is the instant read once for the
  -- query (SPARQL 1.1 §17.4.5.1,
  -- https://github.com/danbri/factoidal/issues/743).
  | "queryHdt" =>
      match decodeArgs argsJson with
      | .error e   => pure (errJson e, ByteArray.empty)
      | .ok [a]    => do pure (← Ops.queryHdtIO a blob, ByteArray.empty)
      | .ok args   => pure (errJson s!"queryHdt expects 1 argument, got {args.length}",
                            ByteArray.empty)
  | "storeServeOpen" =>
      match decodeArgs argsJson with
      | .error e            => pure (errJson e, ByteArray.empty)
      | .ok [a, b, c, d]    => do pure (← Ops.storeServeOpen a b c d blob, ByteArray.empty)
      | .ok args            => pure (errJson s!"storeServeOpen expects 4 arguments, got {args.length}",
                                     ByteArray.empty)
  | "tdb2ServeOpen" =>
      match decodeArgs argsJson with
      | .error e         => pure (errJson e, ByteArray.empty)
      | .ok [a, b]       => do pure (← Ops.tdb2ServeOpen a b blob, ByteArray.empty)
      | .ok args         => pure (errJson s!"tdb2ServeOpen expects 2 arguments, got {args.length}",
                                  ByteArray.empty)
  | "storeServeRequest" =>
      match decodeArgs argsJson with
      | .error e  => pure (errJson e, ByteArray.empty)
      | .ok [a]   => Ops.storeServeRequest a blob
      | .ok args  => pure (errJson s!"storeServeRequest expects 1 argument, got {args.length}",
                           ByteArray.empty)
  | "storeServeCommit" =>
      match decodeArgs argsJson with
      | .error e        => pure (errJson e, ByteArray.empty)
      | .ok [a, b, c]   => Ops.storeServeCommit a b c
      | .ok args        => pure (errJson s!"storeServeCommit expects 3 arguments, got {args.length}",
                                 ByteArray.empty)
  | "storeOpen" =>
      match decodeArgs argsJson with
      | .error e   => pure (errJson e, ByteArray.empty)
      | .ok [a, b] => do pure (← Ops.storeOpen a b blob, ByteArray.empty)
      | .ok args   => pure (errJson s!"storeOpen expects 2 arguments, got {args.length}",
                            ByteArray.empty)
  | _ =>
      if blobOpNames.contains op then
        pure (callBlob op argsJson blob, ByteArray.empty)
      else do
        let envelope ← callIO op argsJson
        pure (envelope, ByteArray.empty)

/-- Decode a `callseq` document — a JSON array of `[op, [arg, …]]`
pairs — into each op paired with its args RE-SERIALISED as the JSON
array-of-strings document `callIO` takes. Handle state lives in the
process, so a sequence of dependent calls (open → query → close) must
run in ONE process; `Wasm/Main.lean`'s `callseq` subcommand drives
this decoder. -/
def decodeCallSeq (seqJson : String) :
    Except String (List (String × String)) :=
  match parseJson seqJson with
  | .error e => .error s!"callseq: {toString e}"
  | .ok (.array items) =>
      items.mapM fun it =>
        match it with
        | .array [.string op, .array argItems] =>
            let argStrs : Except String (List String) :=
              argItems.mapM fun a =>
                match a with
                | Json.string s => .ok s
                | _ => .error "callseq: every argument must be a string"
            argStrs.map fun ss =>
              (op, (Json.array (ss.map Json.string)).toString)
        | _ => .error "callseq: each entry must be [op, [arg, …]]"
  | .ok _ => .error "callseq: document must be a JSON array"


/-! ### The optional base argument of `queryDataset` / `updateDataset` (issue 741) -/

private def dispatchHas (hay needle : String) : Bool := (hay.splitOn needle).length > 1

#guard dispatchHas
  (call "queryDataset" "[\"\",\"SELECT ?x WHERE { BIND(<rel> AS ?x) }\",\"http://e/b/\"]")
  "http://e/b/rel"
-- Two arguments, or an empty third: no base, so the relative IRI is an error.
#guard dispatchHas
  (call "queryDataset" "[\"\",\"SELECT ?x WHERE { BIND(<rel> AS ?x) }\"]") "invalid IRI"
#guard dispatchHas
  (call "queryDataset" "[\"\",\"SELECT ?x WHERE { BIND(<rel> AS ?x) }\",\"\"]") "invalid IRI"
#guard dispatchHas
  (call "updateDataset" "[\"\",\"INSERT DATA { <s> <p> <o> }\",\"http://e/b/\"]")
  "<http://e/b/s> <http://e/b/p> <http://e/b/o> ."
-- A fifth argument, or one argument, is an arity error. (Until issue 748 the
-- fourth argument was one too; it is now the optional instant `now`, below.)
#guard dispatchHas (call "queryDataset" "[\"\",\"ASK {}\",\"\",\"\",\"x\"]") "expects 2, 3 or 4 arguments"
#guard dispatchHas (call "queryDataset" "[\"\"]") "expects 2, 3 or 4 arguments"
#guard dispatchHas (call "updateDataset" "[\"\"]") "expects 2, 3 or 4 arguments"

/-! ### The optional `now` argument of the pure query ops (issue 748)

SPARQL 1.1 §17.4.5.1: `NOW()` is an `xsd:dateTime` for the query execution. The
pure entries `call` and `callBlob` read no clock, so a host that wants `NOW()`
bound passes the instant as the LAST argument: `queryDataset` and
`updateDataset` fourth (after the base IRI), `queryRaw` and `storeQuery` fourth,
`queryHdt` second. An empty string means none, and two- and three-argument hosts
do not change. A text that is not an `xsd:dateTime` lexical form is an error
envelope, never a silent "none". -/

private def pureArgs (xs : List String) : String :=
  (Json.array (xs.map Json.string)).toString

private def nowFixed : String := "2026-10-10T12:34:56.789Z"

-- W3C functions/now01.rq
private def nowAskQ : String :=
  "ASK { BIND(NOW() AS ?n) FILTER(DATATYPE(?n) = <http://www.w3.org/2001/XMLSchema#dateTime>) }"

private def nowSelectQ : String := "SELECT ?n WHERE { BIND(NOW() AS ?n) }"

private def nowInsertQ : String :=
  "INSERT { <http://e/s> <http://e/p> ?n } WHERE { BIND(NOW() AS ?n) }"

private def nowRawData : String := "<http://e/a> <http://e/p> <http://e/b> .\n"

private def nowRawOpts : String := "{\"dataFormat\":\"ntriples\",\"output\":\"csv\"}"

-- Positive: given the instant, NOW() is bound to it, as an xsd:dateTime.
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowAskQ, "", nowFixed])) "\"boolean\":true"
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowSelectQ, "", nowFixed]))
  "\"value\":\"2026-10-10T12:34:56.789Z\""
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowSelectQ, "", nowFixed]))
  "\"datatype\":\"http://www.w3.org/2001/XMLSchema#dateTime\""
-- Positive: the base IRI in the third place still works beside the instant.
#guard dispatchHas (call "queryDataset" (pureArgs
    ["", "SELECT ?x ?n WHERE { BIND(<rel> AS ?x) BIND(NOW() AS ?n) }", "http://e/b/", nowFixed]))
  "\"value\":\"http://e/b/rel\""
#guard dispatchHas (call "queryDataset" (pureArgs
    ["", "SELECT ?x ?n WHERE { BIND(<rel> AS ?x) BIND(NOW() AS ?n) }", "http://e/b/", nowFixed]))
  "\"value\":\"2026-10-10T12:34:56.789Z\""
-- Positive: update, queryRaw, and the blob entry (which delegates to `call`).
#guard dispatchHas (call "updateDataset" (pureArgs ["", nowInsertQ, "", nowFixed]))
  "\\\"2026-10-10T12:34:56.789Z\\\"^^<http://www.w3.org/2001/XMLSchema#dateTime>"
#guard dispatchHas (call "queryRaw" (pureArgs [nowRawData, nowSelectQ, nowRawOpts, nowFixed]))
  "2026-10-10T12:34:56.789Z"
#guard dispatchHas (callBlob "queryDataset" (pureArgs ["", nowAskQ, "", nowFixed]) ByteArray.empty)
  "\"boolean\":true"
-- Positive: the dispatch of the blob ops takes the instant. With the instant
-- given and no HDT bytes, the answer is the missing-bytes error, not an arity
-- or `now` error; likewise a `storeQuery` with a bad manifest names the manifest.
#guard dispatchHas (callBlob "queryHdt" (pureArgs ["ASK {}", nowFixed]) ByteArray.empty) "no HDT bytes"
#guard !dispatchHas (callBlob "queryHdt" (pureArgs ["ASK {}", nowFixed]) ByteArray.empty) "expects"
#guard !dispatchHas (call "storeQuery" (pureArgs ["00", "ASK {}", "[]", nowFixed])) "expects"
#guard !dispatchHas (callBlob "storeQuery" (pureArgs ["00", "ASK {}", "[]", nowFixed]) ByteArray.empty)
  "expects"

-- Negative: with no instant, or an empty one, NOW() is an error (no clock):
-- ASK answers false. A two- or three-argument host sees what it saw before.
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowAskQ])) "\"boolean\":false"
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowAskQ, ""])) "\"boolean\":false"
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowAskQ, "", ""])) "\"boolean\":false"
#guard !dispatchHas (call "updateDataset" (pureArgs ["", nowInsertQ, "", ""])) "dateTime"
#guard !dispatchHas (call "queryRaw" (pureArgs [nowRawData, nowSelectQ, nowRawOpts]))
  "2026-10-10"
-- Negative: the value comes from the argument. A different instant gives a
-- different answer, so a constant or a hard-coded clock fails.
#guard !dispatchHas (call "queryDataset" (pureArgs ["", nowSelectQ, "", "2000-01-01T00:00:00Z"]))
  "2026-10-10"
#guard dispatchHas (call "queryDataset" (pureArgs ["", nowSelectQ, "", "2000-01-01T00:00:00Z"]))
  "\"value\":\"2000-01-01T00:00:00Z\""
-- Negative: an instant that is not an xsd:dateTime lexical form is an error
-- envelope on every op, and no result member appears.
private def badNowAnswers (bad : String) : List String :=
  [ call "queryDataset" (pureArgs ["", nowAskQ, "", bad])
  , call "updateDataset" (pureArgs ["", nowInsertQ, "", bad])
  , call "queryRaw" (pureArgs [nowRawData, nowSelectQ, nowRawOpts, bad])
  , call "storeQuery" (pureArgs ["00", "ASK {}", "[]", bad])
  , callBlob "storeQuery" (pureArgs ["00", "ASK {}", "[]", bad]) ByteArray.empty
  , callBlob "queryHdt" (pureArgs ["ASK {}", bad]) ByteArray.empty ]

private def refusesNow (bad : String) : Bool :=
  (badNowAnswers bad).all (fun r =>
    r.startsWith "{\"ok\":false" && dispatchHas r "not an xsd:dateTime lexical form"
      && !dispatchHas r "\"boolean\"" && !dispatchHas r "\"nquads\"")

#guard refusesNow "x"
#guard refusesNow "now"
#guard refusesNow "yesterday"
#guard refusesNow "2026-10-10"
#guard refusesNow "2026-02-30T00:00:00Z"
#guard refusesNow "2026-13-10T00:00:00Z"
#guard refusesNow " 2026-10-10T12:34:56Z"
#guard refusesNow "2026-10-10T12:34:56Z "
-- Negative: a refusal differs from "no instant": the same text without the
-- bad argument answers.
#guard !(call "queryDataset" (pureArgs ["", nowAskQ])).startsWith "{\"ok\":false"
-- Negative: too many arguments are still an arity error.
#guard dispatchHas (call "queryRaw" (pureArgs [nowRawData, nowSelectQ, nowRawOpts, nowFixed, "x"]))
  "expects 3 or 4 arguments"
#guard dispatchHas (callBlob "queryHdt" (pureArgs ["ASK {}", nowFixed, "x"]) ByteArray.empty)
  "expects 1 or 2 arguments"
#guard dispatchHas (callBlob "storeQuery" (pureArgs ["00", "ASK {}"]) ByteArray.empty)
  "expects 3 or 4 arguments"

end L4Wasm
