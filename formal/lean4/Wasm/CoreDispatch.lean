/-
Wasm.CoreDispatch — the dispatch table of the CORE engine
(`l4factoidal-core.wasm`, https://github.com/danbri/factoidal/issues/713
stage 4), and the arms the full table (`Wasm/Dispatch.lean`) shares with it.

The full wasm (`l4factoidal.wasm`) links every op of `Wasm/Dispatch.lean`, and
that table reaches the whole `L4Factoidal` library, so the linker can drop
nothing. The core wasm links `Wasm/CoreExports.lean`, whose entries are the
four below; this module imports only the op modules of the core subset:

  * parse and serialise every RDF syntax of `Wasm/Ops/Parse.lean`'s table
    (Turtle, TriG, N-Triples, N-Quads, each in RDF 1.1 and 1.2, and RDF/XML),
    and the lenient parse (`Wasm/Ops/Lenient.lean`);
  * SPARQL 1.1 and 1.2 query and update over N-Quads text and over dataset
    handles (`Query`, `Handles`), the §17.6 extension-function registry and
    the SERVICE endpoint registry (`ExtFns`, `ServiceReg`), `queryRaw`;
  * RDFC-1.0 canonicalisation (`Canon`);
  * the RDFS, RDFS-Plus and OWL 2 RL closures (`Reason`);
  * SHACL validation (`Validate`);
  * the durable update log of a browser host (`DeltaLog`).

JSON-LD is outside the core: `Wasm/Ops/Parse.lean` takes the reader of the
syntaxes outside its table as an argument (`ExtraReader`), and this table
passes `coreExtraReader`, which refuses the JSON-LD tags by name. Every other
op of the full table (XML, XPath, XSLT, Schematron, CSVW, JSON-LD, RML,
MathML, ToaN, VC, DID and the HACL* crypto ops, the OWL DL refuter and
tableau, HDT, the Shardborough store and the packer, LWS and Solid, XForms,
RIF, Common Logic, proof checking, XMPP, ShEx, the maths ops) answers the
envelope of `notServed`, which names the full engine. `fullOnlyOpNames`
lists them; `Wasm/CoreDispatchTests.lean` checks at build time that the core
names and that list together are exactly the full table's names.

The full table delegates its core ops here (`callArgsBy jsonLdReader` and
`callIOArgsBy jsonLdReader`), so each of these ops has one arm in the source,
and the two engines answer each core op with the same envelope.

This module must not import the op modules of the full table, nor
`Wasm/Dispatch.lean`: the core wasm is small only because the linker never
sees a reference to them. The size table in
`docs/designissues/2026-10-10-npm-lean-only.md` § 9 is the check.
-/
import Wasm.Ops.Parse
import Wasm.Ops.Query
import Wasm.Ops.Reason
import Wasm.Ops.Canon
import Wasm.Ops.Handles
import Wasm.Ops.ExtFns
import Wasm.Ops.ServiceReg
import Wasm.Ops.QueryExtras
import Wasm.Ops.Lenient
import Wasm.Ops.Validate
import Wasm.Ops.DeltaLog
import Wasm.Ops.Terms
import Wasm.Ops.Collections
import Wasm.Ops.LiteralValue

namespace L4Wasm.Core

open L4Wasm.Ops
open L4Factoidal.JSON

/-- Version of the dispatch ABI's envelope contract; the full table's value
(`L4Wasm.dispatchAbiVersion`). -/
def abiVersion : String := "1"

/-- The reader of the core engine for the syntaxes outside
`Wasm/Ops/Parse.lean`'s table: the JSON-LD tags are refused by name, every
other tag stays unknown. -/
def coreExtraReader : ExtraReader :=
  { refuse := some fun tag =>
      s!"format '{tag}' (JSON-LD 1.1) is not in the core engine (l4factoidal-core.wasm); the full engine (l4factoidal.wasm) reads it" }

/-- The stateless op names of the core engine, served by `call` and `callIO`. -/
def coreOpNames : List String :=
  [ "parseToDatasetJson"
  , "queryDataset"
  , "updateDataset"
  , "serializeNQuads"
  , "serializeTurtle"
  , "canonicalizeToNQuads"
  , "owlClosure"
  , "rhoDfClosure"
  , "rhoDfFragmentCheck"
  , "rdfsPlusClosure"
  , "queryRaw"
  , "shaclValidate" ] ++ parityOpNames ++ lenientOpNames ++ deltaLogOpNames ++ termsOpNames
    ++ literalOpNames

/-- The op names of the core engine that hold state (an `IO.Ref`), served by
`callIO` only: dataset handles, the §17.6 registry, the SERVICE registry, and
the SPARQL 1.2 query over text, which reads both registries. -/
def coreIOOpNames : List String :=
  [ "datasetOpen"
  , "datasetQuery"
  , "datasetQuery12"
  , "datasetQuery12Entail"
  , "datasetUpdate"
  , "datasetSerialize"
  , "datasetSerializeWith"
  , "datasetClose"
  , "datasetClone"
  , "datasetCanonicalize"
  , "datasetCanonicalHash"
  , "datasetClosure"
  , "datasetShaclValidate"
  , "datasetSparqlRlInfer"
  , "datasetQueryRaw"
  , "datasetFormats"
  , "detectFormat"
  , "datasetMatch"
  , "datasetMatchCount"
  , "datasetAddQuads"
  , "datasetDeleteQuads"
  , "datasetQuadsJson"
  , "datasetAddQuadsJson"
  , "datasetDeleteQuadsJson"
  , "datasetFromQuadsJson"
  , "datasetGraphNames"
  , "datasetGraphAsDefault"
  , "datasetIsomorphic"
  , "termsToNTriples"
  , "resolveIri"
  , "queryForm"
  , "engineTables"
  , "apiCheck"
  , "parseQuadsJson"
  , "quadsToNQuads"
  , "extRegister"
  , "extUnregister"
  , "extClear"
  , "extList"
  , "registerServiceEndpoint"
  , "clearServiceEndpoints"
  , "queryDataset12" ] ++ collectionOpNames

/-- The op names the full engine serves and the core engine does not. A
build-time check (`Wasm/CoreDispatchTests.lean`) keeps this list equal to the
full table's names minus the core names. -/
def fullOnlyOpNames : List String :=
  [ "scanIBK2Predicate", "scanIBK3Predicate", "queryIBK3BlockSetPreview"
  , "storeManifestInspect", "storeQueryPlan", "storeQuery", "activateVerify"
  , "owlIsConsistent", "owlEntails"
  , "clParse", "clSerialize", "clAlphaNorm", "clNormalize", "clFiniteSat"
  , "proofCheck", "proofInspect", "explainGraph", "stageList", "pipelineCheck", "pipelineCheckNodes"
  , "toanSummation", "toanProduct", "toanSimplify", "toanDiff", "toanSubst"
  , "xmppJidParse", "xmppJidRender", "xmppStreamHeaderParse"
  , "xmppStreamHeaderRender", "xmppFeaturesFor", "xmppStanzaParse"
  , "xmppOpen", "xmppClose", "xmppSessionOpen", "xmppSessionFeed"
  , "xmppSessionDeliver", "xmppSessionClose", "xmppRosterGet", "xmppRosterSet"
  , "xmppClientOpen", "xmppClientFeed", "xmppClientAnswer", "xmppClientClose"
  , "aeadSeal", "aeadOpen", "hpkeSeal", "hpkeOpen", "jweDecrypt", "jweEncrypt", "xmlDecrypt", "xmlEncrypt"
  , "jsonldToRdf", "jsonldFromRdf", "rmlMap", "csvwToRdf", "xmlWellformed"
  , "xpathEval", "xsltTransform", "schematronValidate", "jsonSchemaValidate"
  , "mathmlEval", "xformsRecalc", "rifEval"
  , "tableauMaterialise", "tableauDlInconsistent", "queryHdt", "shexValidate"
  , "datasetFromCsvw", "datasetFromRml", "datasetFromJsonLd", "datasetToJsonLd"
  , "datasetShexValidate", "datasetRifEval", "datasetQuadsBin"
  , "sbm11Open", "sbm11Query", "sbm11Close", "sbm11Verify", "storeLayout", "sbm11PackFiles"
  , "storeOpen", "storeOpenBytes", "storeManifestInspectBytes", "storeQueryPlanBytes"
  , "storeHandleQuery", "storeHandleList", "storeHandleClose"
  , "storeServeKeys", "storeServeOpen", "storeServeRequest", "storeServeCommit"
  , "storeServeClose", "tdb2ServeKeys", "tdb2ServeOpen"
  , "packBegin", "packFeed", "packEndPass", "packNext", "packFinish", "packClose"
  , "lwsOpen", "lwsStep", "lwsClose", "lwsSnapshot", "lwsFetched", "lwsDelivered", "lwsFlush", "lwsLoad", "lwsPersist", "lwsRead", "solidOpen", "solidStep", "solidClose"
  , "solidSnapshot"
  , "solidFetched"
  , "authzOpen", "authzStep", "authzFetched", "authzKeys", "authzRotate", "authzOwns", "authzClose"
  , "webdavOpen", "webdavLoad", "webdavStep", "webdavResume", "webdavClose", "webdavUser"
  , "solidClientRequest", "solidClientResponse"
  , "lwsClientStart", "lwsClientStep", "lwsClientNewKey"
  , "matrixDeterminant", "matrixScalarProduct", "matrixVectorProduct"
  , "matrixOuterProduct", "sigmoidPoints", "sigmoidFormulaMathml"
  , "vcSha256Hex", "vcEd25519SecretToPublic", "vcEd25519Sign", "vcEd25519Verify"
  , "vcEddsaCreateFromCanonical", "vcEddsaVerifyFromCanonical"
  , "vcCheckCredential", "vcCheckCredentialSubject", "vcCheckNoDataLoss"
  , "vcCheckRelatedResourceDigests", "didKeyResolve"
  , "cidValidate", "cidRetrieve"
  , "blobEcho" ]

def arity1 (op : String) (f : String → String) : List String → String
  | [a] => f a
  | args => errJson s!"{op} expects 1 argument, got {args.length}"

def arity2 (op : String) (f : String → String → String) : List String → String
  | [a, b] => f a b
  | args => errJson s!"{op} expects 2 arguments, got {args.length}"

def arity3 (op : String) (f : String → String → String → String) :
    List String → String
  | [a, b, c] => f a b c
  | args => errJson s!"{op} expects 3 arguments, got {args.length}"

/-- The query and update ops take an optional last argument, the base IRI of
the query or update TEXT (SPARQL 1.1 §4.1.1.2, RFC 3986 §5.1,
https://github.com/danbri/factoidal/issues/741). An empty string, or no
argument, means no base: a relative IRI in the text is then a parse error, as
before. Every host written against the two-argument contract keeps working. -/
def baseArg (s : String) : Option String := if s.isEmpty then none else some s

/-- The pure query and update ops take a second optional last argument, the
instant `NOW()` returns (SPARQL 1.1 §17.4.5.1) as an `xsd:dateTime` lexical
form (XML Schema 1.1 Part 2 §3.3.7). The pure entries (`l4_call`,
`l4_call_blob`) read no clock, so a host that wants `NOW()` bound passes the
instant (https://github.com/danbri/factoidal/issues/748). An empty string, or
no argument, means no instant: `NOW()` is then an error, as before. Any other
text must be a dateTime lexical form (`L4Factoidal.SPARQL.isDateTimeLexical`,
the strict XSD parser); a text it does not read is an error, never a silent
"no instant". -/
def nowArg (s : String) : Except String (Option String) :=
  if s.isEmpty then .ok none
  else if L4Factoidal.SPARQL.isDateTimeLexical s then .ok (some s)
  else .error s!"now '{s}' is not an xsd:dateTime lexical form (XML Schema 1.1 Part 2 section 3.3.7)"

/-- Run `k` with the instant of `nowArg s`, or answer the error envelope. -/
def withNow (op : String) (s : String) (k : Option String → String) : String :=
  match nowArg s with
  | .ok now => k now
  | .error e => errJson s!"{op}: {e}"

/-- Two required arguments, then the optional base IRI, then the optional
instant `now` (`nowArg`). The two- and three-argument forms are the contract
of issue 741 (the base IRI); a host written against them does not change. -/
def arity2BaseNow (op : String)
    (f : String → String → Option String → Option String → String) :
    List String → String
  | [a, b] => f a b none none
  | [a, b, c] => f a b (baseArg c) none
  | [a, b, c, d] => withNow op d (f a b (baseArg c))
  | args => errJson s!"{op} expects 2, 3 or 4 arguments, got {args.length}"

/-- Three required arguments, then the optional instant `now`. -/
def arity3Now (op : String)
    (f : String → String → String → Option String → String) :
    List String → String
  | [a, b, c] => f a b c none
  | [a, b, c, d] => withNow op d (f a b c)
  | args => errJson s!"{op} expects 3 or 4 arguments, got {args.length}"

/-- One required argument, then the optional instant `now`. -/
def arity1Now (op : String)
    (f : String → Option String → String) :
    List String → String
  | [a] => f a none
  | [a, b] => withNow op b (f a)
  | args => errJson s!"{op} expects 1 or 2 arguments, got {args.length}"

def arityIO2Base (op : String) (f : String → String → Option String → IO String) :
    List String → IO String
  | [a, b] => f a b none
  | [a, b, c] => f a b (baseArg c)
  | args => pure (errJson s!"{op} expects 2 or 3 arguments, got {args.length}")

def arityIO0 (op : String) (f : IO String) : List String → IO String
  | [] => f
  | args => pure (errJson s!"{op} expects 0 arguments, got {args.length}")

def arityIO1 (op : String) (f : String → IO String) : List String → IO String
  | [a] => f a
  | args => pure (errJson s!"{op} expects 1 argument, got {args.length}")

def arityIO2 (op : String) (f : String → String → IO String) :
    List String → IO String
  | [a, b] => f a b
  | args => pure (errJson s!"{op} expects 2 arguments, got {args.length}")

def arityIO3 (op : String) (f : String → String → String → IO String) :
    List String → IO String
  | [a, b, c] => f a b c
  | args => pure (errJson s!"{op} expects 3 arguments, got {args.length}")

/-- Two required arguments and an optional third, the options object (an empty
string when it is not given). -/
def arityIO2Opt (op : String) (f : String → String → String → IO String) :
    List String → IO String
  | [a, b] => f a b ""
  | [a, b, c] => f a b c
  | args => pure (errJson s!"{op} expects 2 or 3 arguments, got {args.length}")

/-- The stateless core ops, with `extra` the reader of the syntaxes outside
`Wasm/Ops/Parse.lean`'s table; `none` for any other op (and for `ops`, whose
answer each engine gives itself). -/
def callArgsBy (extra : ExtraReader) (op : String) (args : List String) :
    Option String :=
  match op with
  | "parseToDatasetJson"   => some (arity3 op (parseToDatasetJsonBy extra) args)
  -- The pure form of the query and update ops reads no clock; the optional last
  -- argument is the instant of `NOW()` (`nowArg`, issue 748).
  | "queryDataset"         => some (arity2BaseNow op (fun a b c n => queryDataset a b c n) args)
  | "updateDataset"        => some (arity2BaseNow op (fun a b c n => updateDataset a b c n) args)
  | "serializeNQuads"      => some (arity1 op serializeNQuads args)
  | "serializeTurtle"      => some (arity1 op serializeTurtle args)
  | "canonicalizeToNQuads" => some (arity1 op canonicalizeToNQuads args)
  | "owlClosure"           => some (arity2 op owlClosure args)
  | "rhoDfClosure"         => some (arity1 op rhoDfClosure args)
  | "rhoDfFragmentCheck"   => some (arity1 op rhoDfFragmentCheck args)
  | "rdfsPlusClosure"      => some (arity1 op rdfsPlusClosure args)
  | "queryRaw"             => some (arity3Now op (fun a b c n => queryRawBy extra a b c n) args)
  | "shaclValidate"        => some (arity2 op shaclValidate args)
  -- The durable update log of a browser host (`Wasm/Ops/DeltaLog.lean`,
  -- https://github.com/danbri/factoidal/issues/728).
  | "deltaLogEncode"       => some (arity3 op deltaLogEncode args)
  | "deltaLogDecode"       => some (arity1 op deltaLogDecode args)
  | "deltaLogMerge"        => some (arity2 op deltaLogMerge args)
  | _ =>
      match callParity op args with
      | some r => some r
      | none =>
        -- Terms, IRIs, syntax names and vocabularies (Wasm/Ops/Terms.lean).
        match callTerms op args with
        | some r => some r
        | none =>
          -- Literal values (Wasm/Ops/LiteralValue.lean).
          match callLiteral op args with
          | some r => some r
          | none => callLenientBy extra op args

/-- The core ops that need `IO` (the stateful ones, and the IO forms of
`queryDataset`, `parseToDatasetJson` and `parseDocument`); `none` for any other
op, which the caller serves through its pure table. -/
def callIOArgsBy (extra : ExtraReader) (op : String) (args : List String) :
    Option (IO String) :=
  match op with
  -- §17.6 extension functions. `queryDataset` is served here, not by the
  -- pure table, so a caller registration reaches the stateless query too.
  | "extRegister"      => some (arityIO1 op Ops.extRegister args)
  | "extUnregister"    => some (arityIO1 op Ops.extUnregister args)
  | "extClear"         => some (arityIO0 op Ops.extClear args)
  | "extList"          => some (arityIO0 op Ops.extList args)
  -- The query and update ops take an optional third argument, the base IRI
  -- of the query or update text (`baseArg`).
  | "queryDataset"     => some (arityIO2Base op (fun a b c => Ops.queryDatasetIO a b c) args)
  | "queryDataset12"   => some (arityIO2Base op (fun a b c => Ops.queryDataset12IO a b c) args)
  -- The update and `queryRaw` ops are pure in the table above; their IO forms read
  -- the clock once per request, so `NOW()` in a WHERE clause or a query is the
  -- instant of the call (SPARQL 1.1 §17.4.5.1,
  -- https://github.com/danbri/factoidal/issues/743).
  | "updateDataset"    => some (arityIO2Base op (fun a b c => Ops.updateDatasetIO a b c) args)
  | "queryRaw"         => some (arityIO3 op (Ops.queryRawIOBy extra) args)
  | "datasetOpen"      => some (arityIO3 op (Ops.datasetOpenBy extra) args)
  | "datasetQuery"     => some (arityIO2Base op (fun a b c => Ops.datasetQuery a b c) args)
  | "datasetQuery12"   => some (arityIO2Base op (fun a b c => Ops.datasetQuery12 a b c) args)
  | "datasetUpdate"    => some (arityIO2Base op (fun a b c => Ops.datasetUpdate a b c) args)
  | "datasetSerialize" => some (arityIO2 op Ops.datasetSerialize args)
  | "datasetSerializeWith" => some (arityIO3 op Ops.datasetSerializeWith args)
  | "datasetClose"     => some (arityIO1 op Ops.datasetClose args)
  | "datasetClone"     => some (arityIO1 op Ops.datasetClone args)
  | "datasetCanonicalize" => some (arityIO1 op Ops.datasetCanonicalize args)
  | "datasetCanonicalHash" => some (arityIO1 op Ops.datasetCanonicalHash args)
  | "datasetClosure"   => some (arityIO2 op Ops.datasetClosure args)
  | "datasetShaclValidate" => some (arityIO2 op Ops.datasetShaclValidate args)
  | "datasetSparqlRlInfer" => some (arityIO2 op Ops.datasetSparqlRlInfer args)
  | "datasetQueryRaw"  => some (arityIO3 op Ops.datasetQueryRaw args)
  | "datasetQuery12Entail" => some (arityIO3 op (fun a b c => Ops.datasetQuery12Entail a b c) args)
  | "datasetFormats"   => some (arityIO0 op Ops.datasetFormats args)
  | "detectFormat"     => some (arityIO1 op Ops.detectFormat args)
  -- An optional options object: {"match":"value"} (issue 1052).
  | "datasetMatch"     => some (arityIO2Opt op Ops.datasetMatchWith args)
  | "datasetMatchCount" => some (arityIO2Opt op Ops.datasetMatchCountWith args)
  | "datasetAddQuads"  => some (arityIO2 op Ops.datasetAddQuads args)
  | "datasetDeleteQuads" => some (arityIO2 op Ops.datasetDeleteQuads args)
  | "datasetQuadsJson" => some (arityIO2 op Ops.datasetQuadsJson args)
  | "datasetAddQuadsJson" => some (arityIO2 op Ops.datasetAddQuadsJson args)
  | "datasetDeleteQuadsJson" => some (arityIO2Opt op Ops.datasetDeleteQuadsJsonWith args)
  | "datasetFromQuadsJson" => some (arityIO1 op Ops.datasetFromQuadsJson args)
  | "datasetGraphNames" => some (arityIO1 op Ops.datasetGraphNames args)
  | "datasetGraphAsDefault" => some (arityIO2 op Ops.datasetGraphAsDefault args)
  | "datasetIsomorphic" => some (arityIO2 op Ops.datasetIsomorphic args)
  | "termsToNTriples" => some (arityIO1 op Ops.termsToNTriples args)
  | "resolveIri" => some (arityIO2 op Ops.resolveIriOp args)
  | "queryForm" => some (arityIO1 op Ops.queryForm args)
  | "engineTables" => some (arityIO0 op Ops.engineTables args)
  | "apiCheck" => some (arityIO2 op (fun a b => pure (Ops.apiCheck a b)) args)
  | "parseQuadsJson" => some (arityIO3 op (Ops.parseQuadsJsonBy extra) args)
  | "quadsToNQuads" => some (arityIO1 op Ops.quadsToNQuadsText args)
  -- Each document parsed through the IO entry gets its own blank-node scope
  -- (`d<N>_`), https://github.com/danbri/factoidal/issues/685.
  | "parseToDatasetJson" => some (arityIO3 op (Ops.parseToDatasetJsonScopedBy extra) args)
  | "registerServiceEndpoint" => some (arityIO2 op Ops.registerServiceEndpoint args)
  | "clearServiceEndpoints"   => some (arityIO0 op Ops.clearServiceEndpoints args)
  | _ =>
      match callCollections op args with
      | some r => some r
      | none => callLenientIOBy extra op args

/-- The refusal of an op the core engine does not serve. An op of
`fullOnlyOpNames` names the full engine (`"servedBy":"full"`), so a host can
say which entry point to load; any other name is the unknown-op error the full
table gives. -/
def notServed (op : String) : String :=
  if fullOnlyOpNames.contains op then
    (Json.object
      [ ("ok", .bool false)
      , ("error", .string s!"op '{op}' is not in the core engine (l4factoidal-core.wasm); the full engine (l4factoidal.wasm) serves it")
      , ("engine", .string "core")
      , ("servedBy", .string "full") ]).toString
  else errJson s!"unknown op '{op}'"

/-- `{"ok":true,"abiVersion":"1","engine":"core","ops":[…],"blobOps":[],
"blobIoOps":[],"fullOnlyOps":[…],"fullOnlyFormats":[…]}`. -/
def opsReflectionFor (names : List String) : String :=
  (Json.object
    [ ("ok", .bool true)
    , ("abiVersion", .string abiVersion)
    , ("engine", .string "core")
    , ("ops", .array (names.map Json.string))
    , ("blobOps", .array [])
    , ("blobIoOps", .array [])
    , ("fullOnlyOps", .array (fullOnlyOpNames.map Json.string))
    , ("fullOnlyFormats", .array (jsonLdFormatTags.map Json.string)) ]).toString

/-- The pure entry of the core engine (`l4_call` in `Wasm/CoreExports.lean`). -/
def callUncoded (op : String) (argsJson : String) : String :=
  match decodeArgs argsJson with
  | .error e => errJson e
  | .ok args =>
    if op == "ops" then opsReflectionFor coreOpNames
    else
      match callArgsBy coreExtraReader op args with
      | some r => r
      | none => notServed op

/-- The IO entry of the core engine (`l4_call_io`), which the wire entry of
the shim (`l4_call_c`) serves. -/
def callIOUncoded (op : String) (argsJson : String) : IO String :=
  match decodeArgs argsJson with
  | .error e => pure (errJson e)
  | .ok args =>
    if op == "ops" then pure (opsReflectionFor (coreOpNames ++ coreIOOpNames))
    else
      match callIOArgsBy coreExtraReader op args with
      | some r => r
      | none => pure (callUncoded op argsJson)

/-- The byte-region entry (`l4_call_blob`). The core engine has no op that
reads a byte region, so the region is not read and every op answers as
through `call`. -/
private def argsForCode (argsJson : String) : List String :=
  match decodeArgs argsJson with
  | .ok args => args
  | .error _ => []

/-- `callUncoded` with the error model of `Wasm/Ops/ErrorModel.lean`. -/
def call (op : String) (argsJson : String) : String :=
  attachCodeLazy op (fun _ => argsForCode argsJson) (callUncoded op argsJson)

/-- `callIOUncoded` with the error model of `Wasm/Ops/ErrorModel.lean`. -/
def callIO (op : String) (argsJson : String) : IO String := do
  pure (attachCodeLazy op (fun _ => argsForCode argsJson) (← callIOUncoded op argsJson))

/-- The byte-region entry (`l4_call_blob`). -/
def callBlob (op : String) (argsJson : String) (_blob : ByteArray) : String :=
  call op argsJson

/-- The byte-region-in-and-out entry (`l4_call_blob_io`). The core engine has
no op that builds a byte region: every op answers as through `callIO`, with
an empty out region. -/
def callBlobIO (op : String) (argsJson : String) (_blob : ByteArray) :
    IO (String × ByteArray) := do
  let envelope ← callIO op argsJson
  pure (envelope, ByteArray.empty)

/-! ## Build-time checks (positive and negative) -/

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

private def ntDoc : String := "<http://e/a> <http://e/p> \"v\" .\n"

-- A core op answers; a full-only op is refused naming the full engine; an
-- unknown op is the unknown-op error.
#guard (call "parseToDatasetJson" "[\"<http://e/a> <http://e/p> \\\"v\\\" .\",\"ntriples\",\"\"]").startsWith
         "{\"ok\":true,\"count\":1"
#guard (call "queryDataset" "[\"<http://e/a> <http://e/p> \\\"v\\\" .\\n\",\"ASK { ?s ?p ?o }\"]").startsWith
         "{\"ok\":true"
#guard has (call "xpathEval" "[\"<a/>\",\"/a\"]") "\"servedBy\":\"full\""
#guard has (call "jsonldToRdf" "[\"{}\",\"\"]") "\"servedBy\":\"full\""
#guard (call "noSuchOp" "[]") == "{\"ok\":false,\"error\":\"unknown op 'noSuchOp'\",\"code\":\"op.unknown\"}"
-- JSON-LD is refused by name; Turtle is read.
#guard has (call "parseToDatasetJson" "[\"{}\",\"jsonld\",\"\"]") "not in the core engine"
#guard (parseToDatasetJsonBy coreExtraReader ntDoc "turtle" "").startsWith "{\"ok\":true,\"count\":1"
#guard (parseToDatasetJsonBy coreExtraReader ntDoc "no-such-syntax" "").startsWith
         "{\"ok\":false,\"error\":\"unknown format tag"
-- The reflection names the engine, the core ops, and the full-only ops.
#guard has (call "ops" "[]") "\"engine\":\"core\""
#guard has (call "ops" "[]") "\"shaclValidate\""
#guard !has (call "ops" "[]") "\"datasetOpen\""
#guard has (call "ops" "[]") "\"fullOnlyOps\":[\"scanIBK2Predicate\""
-- No name is both a core op and a full-only op.
#guard (coreOpNames ++ coreIOOpNames).all (fun n => !fullOnlyOpNames.contains n)

end L4Wasm.Core
