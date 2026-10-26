import Lake
open System Lake DSL

/-!
Lake configuration for the Lean 4 port (library `L4Factoidal`).

This file was `lakefile.toml` until the VC Data Integrity stage
(2026-08-22). It became a Lean-DSL lakefile for ONE reason: the TOML
format has no `extern_lib` target, and the Ed25519 signature primitive
must be HACL*'s verified C compiled and linked by Lake itself
(`skills/crypto-policy/SKILL.md`, Lean 4 amendment — signatures via
HACL* FFI only). Everything else below is the mechanical
`lake translate-config lean` output of the former TOML, comments
carried over.
-/

package l4factoidal

/-! ## Native executable-edge externs

`L4Factoidal/Crypto/Ed25519.lean` declares three `opaque`s with
`@[extern "l4_hacl_ed25519_*"]`, and `L4Factoidal/Crypto/SHA2Native.lean`
one more with `@[extern "l4_hacl_sha256"]`. They are realised by
`ffi/hacl_ed25519.c`, a length-checking shim over the vendored,
F*/Low*-verified HACL* extracted C under `third_party/hacl/`
(Apache-2.0; provenance in `third_party/hacl/PROVENANCE.md`). The three
HACL* translation units are compiled UNMODIFIED, exactly as the F*
tree's `build-ocaml.sh` compiles them (`-O2 -fPIC -I include`), and
archived into `libl4hacl.a`, which Lake links into every executable of
this package. `Crypto/SHA2Native.lean` also exposes whole SHA-256 and raw
block compression through the same shim. Differential smoke tests compare
them with pure Lean; a universal native-equivalence proof is not supplied
(https://github.com/danbri/factoidal/issues/777; expected-failure case
NX-1 in `tests/known-defects/run.sh`). -/

/-- `third_party/hacl`, relative to this package (`formal/lean4`). -/
def haclDir (pkg : Package) : FilePath :=
  pkg.dir / ".." / ".." / "third_party" / "hacl"

/-- Compile one C translation unit with the package's HACL* include
path and Lean's include path. -/
def buildHaclO (pkg : Package) (oName : String) (src : FilePath) : SpawnM (Job FilePath) := do
  let oFile := pkg.buildDir / "ffi" / (oName ++ ".o")
  let srcJob ← inputTextFile src
  let weakArgs := #["-I", (← getLeanIncludeDir).toString,
                    "-I", (haclDir pkg / "include").toString]
  buildO oFile srcJob weakArgs #["-O2", "-fPIC"] "cc" getLeanTrace

target hacl_ed25519_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_ed25519_shim" (pkg.dir / "ffi" / "hacl_ed25519.c")

target Hacl_Ed25519.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Ed25519" (haclDir pkg / "src" / "Hacl_Ed25519.c")

target Hacl_Curve25519_51.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Curve25519_51" (haclDir pkg / "src" / "Hacl_Curve25519_51.c")

target Hacl_Hash_SHA2.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Hash_SHA2" (haclDir pkg / "src" / "Hacl_Hash_SHA2.c")

/-! The JOSE additions (2026-09-06). `L4Factoidal/Crypto/P256Native.lean`
declares `@[extern "l4_hacl_p256_*"]` for JWS ES256 and
`L4Factoidal/Crypto/RsaNative.lean` `@[extern "l4_hacl_rsa_public_op"]`
for the RS256 public operation. They are realised by `ffi/hacl_p256.c`
and `ffi/hacl_rsa.c` over the same vendored HACL* C. `Hacl_Bignum.c` is
the generic bignum field `Hacl_Bignum64.c` calls into; `Hacl_P256.c`
already reaches the `Hacl_Hash_SHA2.c` unit above for its digest. -/

target hacl_p256_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_p256_shim" (pkg.dir / "ffi" / "hacl_p256.c")

target hacl_rsa_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_rsa_shim" (pkg.dir / "ffi" / "hacl_rsa.c")

target Hacl_P256.o pkg : FilePath :=
  buildHaclO pkg "Hacl_P256" (haclDir pkg / "src" / "Hacl_P256.c")

target Hacl_Bignum64.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Bignum64" (haclDir pkg / "src" / "Hacl_Bignum64.c")

target Hacl_Bignum.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Bignum" (haclDir pkg / "src" / "Hacl_Bignum.c")

/-! The XMPP client-role and end-to-end-encryption additions (2026-09-07).
`L4Factoidal/Crypto/ChaChaPoly.lean`, `Crypto/Hkdf.lean`, `Crypto/X25519.lean`
and `Crypto/Hpke.lean` declare `@[extern]` opaques realised by
`ffi/hacl_chachapoly.c`, `ffi/hacl_kdf.c` and `ffi/hacl_hpke.c` over the
same vendored HACL* C. `Hacl_Hash_SHA1.c`, `Hacl_Hash_Blake2s.c`,
`Hacl_Hash_Blake2b.c` and `Lib_Memzero0.c` are here as LINK CLOSURE of
`Hacl_HMAC.c`, which is one translation unit covering every HMAC hash; no
Lean code calls them. Portable scalar units only — see
`third_party/hacl/PROVENANCE.md` for why the Simd/Vec variants and AES-GCM
are not vendored. -/

target hacl_chachapoly_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_chachapoly_shim" (pkg.dir / "ffi" / "hacl_chachapoly.c")

target hacl_kdf_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_kdf_shim" (pkg.dir / "ffi" / "hacl_kdf.c")

target hacl_hpke_shim.o pkg : FilePath :=
  buildHaclO pkg "hacl_hpke_shim" (pkg.dir / "ffi" / "hacl_hpke.c")

target Hacl_AEAD_Chacha20Poly1305.o pkg : FilePath :=
  buildHaclO pkg "Hacl_AEAD_Chacha20Poly1305" (haclDir pkg / "src" / "Hacl_AEAD_Chacha20Poly1305.c")

target Hacl_Chacha20.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Chacha20" (haclDir pkg / "src" / "Hacl_Chacha20.c")

target Hacl_MAC_Poly1305.o pkg : FilePath :=
  buildHaclO pkg "Hacl_MAC_Poly1305" (haclDir pkg / "src" / "Hacl_MAC_Poly1305.c")

target Hacl_HKDF.o pkg : FilePath :=
  buildHaclO pkg "Hacl_HKDF" (haclDir pkg / "src" / "Hacl_HKDF.c")

target Hacl_HMAC.o pkg : FilePath :=
  buildHaclO pkg "Hacl_HMAC" (haclDir pkg / "src" / "Hacl_HMAC.c")

target Hacl_Hash_SHA1.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Hash_SHA1" (haclDir pkg / "src" / "Hacl_Hash_SHA1.c")

target Hacl_Hash_Blake2s.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Hash_Blake2s" (haclDir pkg / "src" / "Hacl_Hash_Blake2s.c")

target Hacl_Hash_Blake2b.o pkg : FilePath :=
  buildHaclO pkg "Hacl_Hash_Blake2b" (haclDir pkg / "src" / "Hacl_Hash_Blake2b.c")

target Lib_Memzero0.o pkg : FilePath :=
  buildHaclO pkg "Lib_Memzero0" (haclDir pkg / "src" / "Lib_Memzero0.c")

target Hacl_HPKE_Curve51_CP32_SHA256.o pkg : FilePath :=
  buildHaclO pkg "Hacl_HPKE_Curve51_CP32_SHA256" (haclDir pkg / "src" / "Hacl_HPKE_Curve51_CP32_SHA256.c")

extern_lib libl4hacl pkg := do
  let shim ← hacl_ed25519_shim.o.fetch
  let ed ← Hacl_Ed25519.o.fetch
  let curve ← Hacl_Curve25519_51.o.fetch
  let sha2 ← Hacl_Hash_SHA2.o.fetch
  let p256Shim ← hacl_p256_shim.o.fetch
  let rsaShim ← hacl_rsa_shim.o.fetch
  let p256 ← Hacl_P256.o.fetch
  let bn64 ← Hacl_Bignum64.o.fetch
  let bn ← Hacl_Bignum.o.fetch
  let cpShim ← hacl_chachapoly_shim.o.fetch
  let kdfShim ← hacl_kdf_shim.o.fetch
  let hpkeShim ← hacl_hpke_shim.o.fetch
  let aead ← Hacl_AEAD_Chacha20Poly1305.o.fetch
  let chacha ← Hacl_Chacha20.o.fetch
  let poly ← Hacl_MAC_Poly1305.o.fetch
  let hkdf ← Hacl_HKDF.o.fetch
  let hmac ← Hacl_HMAC.o.fetch
  let sha1 ← Hacl_Hash_SHA1.o.fetch
  let blake2s ← Hacl_Hash_Blake2s.o.fetch
  let blake2b ← Hacl_Hash_Blake2b.o.fetch
  let memzero ← Lib_Memzero0.o.fetch
  let hpke ← Hacl_HPKE_Curve51_CP32_SHA256.o.fetch
  let name := nameToStaticLib "l4hacl"
  buildStaticLib (pkg.staticLibDir / name)
    #[shim, ed, curve, sha2, p256Shim, rsaShim, p256, bn64, bn,
      cpShim, kdfShim, hpkeShim,
      aead, chacha, poly, hkdf, hmac, sha1, blake2s, blake2b, memzero, hpke]

/-- Build the deliberately small POSIX `pread` host adapter used only by the
    native IBK2 range-read probe. The pure planner/decoder remains in Lean;
    this C object is not part of the WASM closure. -/
target block_pread.o pkg : FilePath :=
  buildHaclO pkg "block_pread" (pkg.dir / "ffi" / "block_pread.c")

extern_lib libl4blockhost pkg := do
  let pread ← block_pread.o.fetch
  let name := nameToStaticLib "l4blockhost"
  buildStaticLib (pkg.staticLibDir / name) #[pread]

/-- Optional libzstd call-out for the `l4qlvr` measurements
    (https://github.com/danbri/factoidal/issues/778): `Harness/Qlvr.lean`'s
    `@[extern "l4_zstd_decompress"]`. libzstd is loaded with dlopen at run
    time, so the build needs no zstd headers; the pure Lean decoder
    (`L4Factoidal.Codec.Zstd`) stays the reference and the default. Not part
    of the WASM closure. -/
target qlvr_zstd.o pkg : FilePath :=
  buildHaclO pkg "qlvr_zstd" (pkg.dir / "ffi" / "qlvr_zstd.c")

extern_lib libl4qlvrzstd pkg := do
  let z ← qlvr_zstd.o.fetch
  let name := nameToStaticLib "l4qlvrzstd"
  buildStaticLib (pkg.staticLibDir / name) #[z]

/-- The host call-out for caller-registered SPARQL 1.1 section 17.6
    extension functions (`Wasm/ExtHost.lean`'s `@[extern "l4_ext_call"]`).
    On a native build it has no host and answers the empty string, which
    Lean reads as the section 17.6 error; the Emscripten build compiles the
    same file with an EM_JS body (`Wasm/build-wasm.sh`). -/
target l4_ext.o pkg : FilePath :=
  buildHaclO pkg "l4_ext" (pkg.dir / "ffi" / "l4_ext.c")

extern_lib libl4exthost pkg := do
  let ext ← l4_ext.o.fetch
  let name := nameToStaticLib "l4exthost"
  buildStaticLib (pkg.staticLibDir / name) #[ext]

/-- The positioned reads of a store whose bytes a host supplies
    (`Wasm/HostRead.lean`'s `l4_host_read_at` and `l4_host_size`,
    https://github.com/danbri/factoidal/issues/1009). Native: one `pread` of
    `source/file`; the Emscripten build compiles the same file with EM_JS
    bodies (`Wasm/build-wasm.sh`). -/
target l4_hostread.o pkg : FilePath :=
  buildHaclO pkg "l4_hostread" (pkg.dir / "ffi" / "l4_hostread.c")

extern_lib libl4hostread pkg := do
  let hr ← l4_hostread.o.fetch
  let name := nameToStaticLib "l4hostread"
  buildStaticLib (pkg.staticLibDir / name) #[hr]

@[default_target] lean_lib L4Factoidal

-- Observable cardinality of the dataset handle store: 41 assertions over
-- open / clone / update / add / delete (RDF 1.1 Concepts §3: a graph is a set).
@[default_target] lean_exe «l4dataset-set-regression» where root := `Harness.DatasetSetRegression

-- The W3C harness's shared modules. They live in a lib rather than
-- hanging off an executable root because `Harness.Main` imports them
-- and Lake only builds modules a lib claims. NOT part of the verified
-- library: these do file I/O and print scores. The probes
-- (`Harness.TurtleProbe`, `Harness.CanonProbe`) stay executable roots.
@[default_target] lean_lib Harness where globs :=
  (#[`Harness.Common, `Harness.RifImport, `Harness.Fixtures, `Harness.Manifest, `Harness.Compare, `Harness.ProtocolRun, `Harness.Run, `Harness.HarnessTests,
    `Harness.NativeHasher,
    `Harness.PosixRangeIO, `Harness.CompactedEpoch, `Harness.GenerationPointer, `Harness.ShardMerkleMaterialize, `Harness.ShardMerkleProfile, `Harness.ShardPublish,
    `Harness.IndexedBlockV3Materialize, `Harness.JsonLdScale, `Harness.LenientRun, `Harness.QlvrKernel,
    `Harness.Sbm11Gen, `Harness.RunHeap, `Harness.Sbm11Query, `Harness.Sbm11Delta, `Harness.Sbm11Update, `Harness.Sbm11PackLib, `Harness.Sbm11Compact, `Harness.Sbm11PermCheck,
    `Harness.Sbm11Export, `Harness.Sbm11MemGenCheck, `Harness.Sbm11PackSpecCheck,
    `Harness.PlannerCheck, `Harness.PlannerKinds, `Harness.PlannerSbm11IO,
    `Harness.ProofObligations, `Harness.WorkerPool] : Array Lean.Name).map Glob.one

-- The WebAssembly export surface: the JSON string-in / string-out ABI
-- (Wasm/Abi.lean) and the `@[export]` C symbols (Wasm/Exports.lean).
-- `lake build` compiles it, so the ABI is type-checked on every build
-- even when no wasm toolchain is present.
@[default_target] lean_lib l4wasm where
  srcDir := "."
  roots := #[`Wasm.Abi, `Wasm.Exports, `Wasm.Dispatch,
             `Wasm.ExtHost, `Wasm.Ops.ExtFns, `Wasm.Ops.Clock,
             `Wasm.Ops.ErrorModel, `Wasm.ErrorModelTests,
             `Wasm.Ops.Support, `Wasm.Ops.FromDataset, `Wasm.Ops.Parse, `Wasm.Ops.Query,
             `Wasm.Ops.Reason, `Wasm.Ops.Canon, `Wasm.Ops.CL,
             `Wasm.Ops.Block,
             `Wasm.Ops.Store,
             `Wasm.Ops.StoreHandles, `Wasm.StorePlanGateTests,
             `Wasm.HostRead, `Wasm.Ops.Sbm11, `Wasm.Ops.Sbm11Pack,
             `Wasm.Ops.StoreServe,
             `Wasm.Ops.Proof,
             `Wasm.Ops.Explain,
             `Wasm.Ops.StageList,
             `Wasm.Ops.PipelineNodes,
             `Wasm.Ops.Handles,
             `Wasm.Ops.DatasetFull,
             `Wasm.Ops.Pack,
             `Wasm.Ops.Lws,
             `Wasm.Ops.Solid,
             `Wasm.Ops.LwsClient,
             `Wasm.Ops.Authz,
             `Wasm.Ops.Toan,
             `Wasm.Ops.Xmpp,
             `Wasm.Ops.XmppSession,
             `Wasm.Ops.Crypto,
             `Wasm.Ops.Formats, `Wasm.FormatsBoundaryTests, `Wasm.GraphSetTests,
             `Wasm.Ops.ServiceReg, `Wasm.Ops.Reasoning, `Wasm.Ops.QueryExtras,
             `Wasm.Ops.Maths,
             `Wasm.Ops.Vc,
             `Wasm.Ops.Lenient, `Wasm.Ops.Validate,
             `Wasm.Ops.DeltaLog,
             -- The core wasm (issue 713 stage 4): its dispatch, its C symbols,
             -- the op modules the split moved out of the core closure, and the
             -- build-time agreement checks of the two tables.
             `Wasm.CoreDispatch, `Wasm.CoreExports, `Wasm.CoreDispatchTests,
             `Wasm.Ops.ParseJsonLd, `Wasm.Ops.ReasonDl, `Wasm.Ops.ReasonDlCertified, `Wasm.Ops.ShExValidate,
             `Wasm.Ops.QueryHdt]

-- Runs the XML parser over real W3C XML Conformance Test Suite files:
-- reads paths from stdin, prints WF / NWF per file. See
-- L4Factoidal/XML/ConfProbe.lean for what a verdict does and does not
-- mean.
@[default_target] lean_exe «xmlconf-probe» where root := `L4Factoidal.XML.ConfProbe

-- Real-corpus probe for RDFC-1.0 (the W3C rdf-canon suite). Not part of
-- the verified library: it does file I/O and prints scores.
@[default_target] lean_exe «l4rdfc-probe» where root := `Harness.CanonProbe

-- Real-corpus probe for the Turtle / TriG parsers (Harness/TurtleProbe.lean).
-- Separate from the library so the library stays specification-only, per the
-- spec/pragmatics split recorded in PORT_NOTES.md.
@[default_target] lean_exe «l4turtle-probe» where root := `Harness.TurtleProbe

-- Real-corpus probe for JSON-LD 1.1 expansion + toRdf (the W3C
-- json-ld-api toRdf manifest). Same spec/pragmatics split: it reads the
-- manifest and fixtures from disk and prints scores, so it lives outside
-- the library.
@[default_target] lean_exe «l4jsonld-probe» where root := `Harness.JsonLdProbe

-- Real-corpus probe for the REST of the W3C json-ld-api suite: the
-- expand, compact, flatten, fromRdf and html manifests (Harness/
-- JsonLdApiProbe.lean). Same spec/pragmatics split as l4jsonld-probe,
-- which keeps toRdf and is left alone. Run the built binary from the
-- REPOSITORY ROOT: it resolves the corpus relative to the CWD.
@[default_target] lean_exe «l4jsonld-api» where root := `Harness.JsonLdApiProbe

-- Real-corpus runner for the W3C json-ld-framing suite (Harness/
-- JsonLdFrameRun.lean), the manifest neither probe above covers. Run
-- the built binary from the REPOSITORY ROOT.
@[default_target] lean_exe «l4jsonld-frame» where root := `Harness.JsonLdFrameRun

-- Corpus census for the W3C OWL 2 test catalogs (Harness/OwlProbe.lean):
-- reads the RDF/XML catalogs with the Lean XML parser and reports, with
-- denominators, how many test cases carry a serialisation the Lean tree
-- can turn into triples. Not part of the verified library: file I/O and
-- printed scores.
@[default_target] lean_exe «l4owl-probe» where root := `Harness.OwlProbe

-- Factoidal/qlvr (https://github.com/danbri/factoidal/issues/778): the pure-Lean
-- zstd decoder (L4Factoidal.Codec.Zstd) against libzstd's answers, on the
-- committed vectors and on every column frame of the QLever instance.
@[default_target] lean_exe «l4qlvr-zstd-check» where root := `Harness.QlvrZstdCheck

-- Factoidal/qlvr (https://github.com/danbri/factoidal/issues/778): read a QLever
-- index directory (stats, bound-predicate scan over PSO, full SPO dump, vocabulary).
@[default_target] lean_exe «l4qlvr» where root := `Harness.Qlvr
-- L4Factoidal.Prim.Bytes (https://github.com/danbri/factoidal/issues/797): the
-- differential test of the `@[extern c inline]` store against its Lean reference.
-- tests/prim/run.sh runs it natively and as wasm32 under node.
@[default_target] lean_exe «l4prim-test» where root := `Harness.PrimBytesTest
-- The scan-versus-old-scan differential of Storage/Sbm11/ScanFoldTests (needs compiled code).
@[default_target] lean_exe «l4scanfold-test» where root := `Harness.ScanFoldTest
-- Capability-aware planner, KR 2.2 (https://github.com/danbri/factoidal/issues/801):
-- the structural planner's test set, with its expected-failure bucket.
@[default_target] lean_exe «l4planner-test» where root := `Harness.PlannerTest
-- The q07 kernel timing loop alone (no FFI in its imports), for the native and
-- wasm32 measurements of issue 797 (tools/lean-wasm-exe.sh builds the wasm32 one).
@[default_target] lean_exe «l4qlvr-kernel» where root := `Harness.QlvrKernelBench
-- Start latency of a short job on the Lean task pool and on the per-session
-- worker pool of the SBM11 harness (issue 961, Harness/WorkerPool.lean).
@[default_target] lean_exe «l4pool-bench» where root := `Harness.WorkerPoolBench
-- SBM11 stage 2 (https://github.com/danbri/factoidal/issues/788): packer
-- phases 1 and 2 (global dictionary GDV1/GDX1), its check and lookup bench.
@[default_target] lean_exe «l4sbm11-dict-pack» where root := `Harness.Sbm11DictPack
-- SBM11 stage 3 (https://github.com/danbri/factoidal/issues/789): packer phases
-- 1 to 3 (dictionary, then the PSO/POS/SPO/OSP permutations as PRB1 blocks with
-- PRM1 metadata, the SBM11 manifest), and the reader: stats, scan, count, dump,
-- verify and activate.
@[default_target] lean_exe «l4sbm11-pack» where root := `Harness.Sbm11Pack
@[default_target] lean_exe «l4sbm11» where root := `Harness.Sbm11Cli
-- Read a document in any of the six RDF syntaxes through the source layer and
-- write it in any of the six with the library serialisers (issue 837).
@[default_target] lean_exe «l4source-convert» where root := `Harness.SourceConvert
-- The lists and the comparisons of the W3C round trip through the SBM11 store
-- (tests/sbm11/w3c_roundtrip.sh, issue 837 item 5): the manifests' positive
-- evaluation tests as rows, and the isomorphism of a dump with a result file.
@[default_target] lean_exe «l4sbm11-w3c» where root := `Harness.Sbm11W3c
-- Tests of the producers of RDF quads (L4Factoidal/RDF/QuadSource.lean) and of the
-- packer entry that takes them (tests/sbm11/quad_source.sh, issue 866).
@[default_target] lean_exe «l4sbm11-quad-source» where root := `Harness.Sbm11QuadSource
-- The OWL 2 species verdict (DL or Full) of one ontology document and its
-- imports, read as N-Triples (Harness/OwlSpeciesFile.lean). The verdict is
-- `OWL.SyntaxDL.speciesViolations`, the function `l4owl-probe --species`
-- scores; this executable only reads files and prints JSON. Used by
-- tools/owl-real-bench.sh (https://github.com/danbri/factoidal/issues/651).
@[default_target] lean_exe «l4owl-species» where root := `Harness.OwlSpeciesFile

-- Where the OWL DL tableau refuter spends its work: steps, branch points,
-- state size and the time of each phase of `OWL.Refute.search`, on the OWL
-- RL closure of one N-Triples file (Harness/RefuteProfile.lean). Holds no
-- OWL logic; `--check` compares its verdict with `tableauConsistent`.
-- https://github.com/danbri/factoidal/issues/760
@[default_target] lean_exe «l4refute-profile» where root := `Harness.RefuteProfile

-- Where the OWL 2 RL closure spends its rounds: per round the input size, the
-- conclusions emitted, the new triples and the time; with --rows, per row the
-- emitted, new and delta-driven conclusions and the time
-- (Harness/OwlRlProfile.lean). Holds no OWL logic.
-- https://github.com/danbri/factoidal/issues/756
@[default_target] lean_exe «l4owl-rl-profile» where root := `Harness.OwlRlProfile

-- Native driver for the same ABI, so it can be exercised without wasm.
@[default_target] lean_exe «l4wasm-cli» where
  srcDir := "."
  root := `Wasm.Main

-- `l4factoidal` — the real command-line interface (issue #466 ladder):
-- named verbs and flags over the SAME `Wasm/Ops/*.lean` functions
-- `l4wasm-cli`/the wasm build call, for people and scripts that do not
-- want to know the dispatch ABI. `Wasm/Cli.lean` is thin argument
-- parsing + JSON-envelope decoding; no RDF/SPARQL/OWL/CL logic lives
-- here. `l4wasm-cli` above is unchanged and stays the ABI smoke
-- driver `Wasm/native-smoke.sh` pins.
@[default_target] lean_exe «l4factoidal» where
  srcDir := "."
  root := `Wasm.Cli

-- `l4query-phases` — the phases of `l4factoidal query` (read, parse,
-- normalize, index, eval, output), each followed by the resident memory of
-- the process, with `--stop-after PHASE` (Harness/QueryPhases.lean,
-- https://github.com/danbri/factoidal/issues/729).
-- The phases of the Dataset iteration ops, timed natively
-- (Harness/IterPhases.lean, https://github.com/danbri/factoidal/issues/900).
@[default_target] lean_exe «l4iter-phases» where
  srcDir := "."
  root := `Harness.IterPhases

-- Pack and load time of the store dictionaries of issue 977 (language-tag
-- fold, literal de-duplication) on one N-Quads file (Bench/DictFoldBench.lean).
lean_exe «l4dict-fold-bench» where
  srcDir := "."
  root := `Bench.DictFoldBench

@[default_target] lean_exe «l4query-phases» where
  srcDir := "."
  root := `Harness.QueryPhases

-- Native executable for the first RDF block MVP. It exercises the total
-- `Storage.BlockMvp.scan` path over a small in-memory graph; it does not claim
-- protocol, persistence, or W3C conformance coverage.
@[default_target] lean_exe «l4block-mvp» where root := `Harness.BlockMvp

-- Real-Turtle corpus probe for the indexed block. It is outside the library
-- because file I/O and timing/corpus measurements are executable-edge concerns.
@[default_target] lean_exe «l4block-corpus» where root := `Harness.BlockCorpus

-- Transitional persistent-file vertical: pack supported Turtle as framed BLK0
-- then decode it into the indexed query block without reparsing Turtle.
@[default_target] lean_exe «l4block-pack» where root := `Harness.BlockPack
@[default_target] lean_exe «l4block-file-query» where root := `Harness.BlockFileQuery

-- Direct shared-dictionary/ID-row persistence and query vertical.
@[default_target] lean_exe «l4block-id-pack» where root := `Harness.IndexedBlockPack
@[default_target] lean_exe «l4block-id-file-query» where root := `Harness.IndexedBlockFileQuery
@[default_target] lean_exe «l4block-id-diff» where root := `Harness.IndexedBlockDiff
@[default_target] lean_exe «l4block-id-v2-diff» where root := `Harness.IndexedBlockV2Diff
@[default_target] lean_exe «l4block-id-v2-segment» where root := `Harness.IndexedBlockV2Segment
@[default_target] lean_exe «l4block-id-v2-pack» where root := `Harness.IndexedBlockV2Pack
@[default_target] lean_exe «l4block-id-v2-file-query» where root := `Harness.IndexedBlockV2FileQuery
@[default_target] lean_exe «l4block-id-v2-range-plan» where root := `Harness.IndexedBlockV2RangePlan
@[default_target] lean_exe «l4block-id-v2-pread» where root := `Harness.IndexedBlockV2Pread
@[default_target] lean_exe «l4block-id-v3-convert» where root := `Harness.IndexedBlockV3Convert
@[default_target] lean_exe «l4block-id-v3-merkle-scan» where root := `Harness.IndexedBlockV3MerkleScan
@[default_target] lean_exe «l4block-id-v3-query» where root := `Harness.IndexedBlockV3Query
@[default_target] lean_exe «l4block-paged-dictionary-probe» where root := `Harness.PagedDictionaryProbe
@[default_target] lean_exe «l4termwire-page-decode» where root := `Harness.TermWirePageDecode
@[default_target] lean_exe «l4merkle-range-read» where root := `Harness.MerkleRangeRead
@[default_target] lean_exe «l4block-shard-merkle-pread» where root := `Harness.ShardMerklePread
@[default_target] lean_exe «l4block-shard-merkle-scan» where root := `Harness.ShardMerkleScan
@[default_target] lean_exe «l4block-shard-merkle-query» where root := `Harness.ShardMerkleQuery
@[default_target] lean_exe «l4block-shard-merkle-session» where root := `Harness.ShardMerkleSession
@[default_target] lean_exe «l4block-delta-log» where root := `Harness.DeltaLogTool
@[default_target] lean_exe «l4block-shard-compact» where root := `Harness.ShardDeltaCompact
@[default_target] lean_exe «l4block-shard-activate» where root := `Harness.ShardActivate
@[default_target] lean_exe «l4block-predicate-shards» where root := `Harness.PredicateBlocksProbe
@[default_target] lean_exe «l4block-predicate-query» where root := `Harness.PredicateBlocksQuery
@[default_target] lean_exe «l4block-shard-pack» where root := `Harness.PredicateShardPack
-- SPARQL over an activated SBM7 generation of IBK4 quad blocks: the quad
-- sibling of `l4block-id-v3-query`, which reads IBK3 generations and refuses
-- SBM7 by layout. `GRAPH <iri>`, `GRAPH ?g`, `FROM` / `FROM NAMED` and
-- default-graph patterns all run against the dataset the blocks denote.
@[default_target] lean_exe «l4block-quad-query» where root := `Harness.QuadQuery
-- The W3C SPARQL 1.1 Protocol, Graph Store and Service Description tests
-- replayed against a live `factoidal serve` (issue 669 step 1).
@[default_target] lean_exe «l4protocol-live» where root := `Harness.ProtocolLive
@[default_target] lean_exe «l4block-literal-gram» where root := `Harness.LiteralGramProbe
@[default_target] lean_exe «l4block-geo-bbox» where root := `Harness.GeoBBoxProbe

-- Write an IBK4 generation's quads back out as N-Quads, so the SAME corpus
-- can be packed again under a changed format and the two compared.
@[default_target] lean_exe «l4block-quad-dump» where root := `Harness.QuadDump
-- Native differential smokes for the HACL* SHA-256 entry points and the
-- POSIX range reader, and the prepared-snapshot session driver
-- (`L4Factoidal/SPARQL/PreparedSnapshot.lean`).
@[default_target] lean_exe «l4native-crypto-smoke» where root := `Harness.NativeCryptoSmoke
@[default_target] lean_exe «l4native-range-smoke» where root := `Harness.NativeRangeSmoke
@[default_target] lean_exe «l4block-snapshot-session» where root := `Harness.SnapshotSession

-- The row-identity gate for the LGI3 and LGI4 literal search index, driven through
-- `storeHandleQuery` — the operation a host calls. It opens one handle with
-- the sidecars and one without, and compares the two answer envelopes.
@[default_target] lean_exe «l4block-literal-gate» where
  srcDir := "."
  root := `Harness.LiteralGate

-- The row-identity gate for the GBI1 geometry bounding-box index, through the
-- same operation and with the same with-and-without handle pair.
@[default_target] lean_exe «l4block-geo-gate» where
  srcDir := "."
  root := `Harness.GeoGate
@[default_target] lean_exe «l4block-shard-query» where root := `Harness.ShardManifestQuery
@[default_target] lean_exe «l4block-shard-session» where root := `Harness.ShardManifestSession

-- The MANIFEST-DRIVEN W3C conformance runner (issue #466, ladder rung
-- 3). Reads the real `manifest.ttl` files off disk with the Lean
-- Turtle parser and scores the Lean engine in the same score-line
-- grammar `bin/w3c-runner/w3c_runner.ml` uses, so the two trees'
-- numbers are directly comparable. Design:
-- docs/designissues/2026-08-22-lean4-w3c-harness.md
--   lake exe l4w3c ../../third_party/testing/w3c/rdf/rdf11/rdf-turtle/manifest.ttl
-- `Harness.HarnessTests` is imported so its `#guard`s run in the build.
@[default_target] lean_exe l4w3c where root := `Harness.Main

-- Real-corpus probe for the RDF/XML parser (Harness/RdfXmlProbe.lean).
-- Directory-driven, not manifest-driven, so it does not depend on the
-- Turtle parser. Separate from the library so the library stays
-- specification-only, per the spec/pragmatics split in PORT_NOTES.md.
@[default_target] lean_exe «l4rdfxml-probe» where root := `Harness.RdfXmlProbe

-- The RDF/XML chunk fold of the source layer against the whole-document
-- reader (https://github.com/danbri/factoidal/issues/838).
@[default_target] lean_exe «l4rdfxml-chunk-diff» where root := `Harness.RdfXmlChunkDiff
@[default_target] lean_exe «l4jsonld-chunk-diff» where root := `Harness.JsonLdChunkDiff
-- A Turtle or TriG document read by several range readers against the single reader (issue 842).
@[default_target] lean_exe «l4split-diff» where root := `Harness.SplitReadDiff

-- Reader-level probe over the vendored W3C csvw corpus. Named a
-- PROBE, not a conformance runner, because it measures whether the
-- dialect reader reads each .csv cleanly -- not whether the
-- conversion matches the suite's expected .ttl.
@[default_target] lean_exe «l4csvw-probe» where root := `Harness.CsvwProbe

-- A REAL csv2rdf conformance runner: full pipeline, compared against
-- the suite's expected .ttl by graph isomorphism. Restricted to the
-- no-metadata subset; every skip is reported with its reason.
@[default_target] lean_exe «l4csvw-rdf» where root := `Harness.CsvwRdfRun

@[default_target] lean_exe «l4csvw-json» where root := `Harness.CsvwJsonRun

-- The W3C csvw VALIDATION manifest (Positive / Warning / Negative
-- ValidationTest), run through L4Factoidal.CSVW.Validate. The twin of
-- the F* `csvw_runner --validate` mode, in the same score grammar.
@[default_target] lean_exe «l4csvw-validate» where root := `Harness.CsvwValidateRun

-- The GeoSPARQL v0 slice (WKT parsing, Simple Features topology,
-- geof: distance/envelope) as a scored run, the twin of the F*
-- tests/unit/geosparql_v0_unit.ml pin file.
@[default_target] lean_exe l4geo where root := `Harness.GeoRun

-- The W3C rdf-semantics entailment manifest (RDF 1.2), scored against
-- L4Factoidal.RDFS / L4Factoidal.RDF.Entailment.
@[default_target] lean_exe «l4rdf-semantics» where root := `Harness.RdfSemanticsRun

@[default_target] lean_exe «l4jsonschema» where root := `Harness.JsonSchemaRun

@[default_target] lean_exe «l4mathml» where root := `Harness.MathMLRun

-- The "Think of a Number" parity battery: the checks of the F*
-- consumer test tests/unit/toan_tests.ml, run against the Lean
-- Math/* and MathML/Core functions. Zero arguments.
@[default_target] lean_exe «l4toan» where root := `Harness.ToanRun

@[default_target] lean_exe «l4xmlconf» where root := `Harness.XmlConfRun

-- The W3C XML Schema Test Suite, Part 2 Datatypes slice: suite.xml ->
-- the *Meta/*.testSet manifests -> the datatype-only test groups.
@[default_target] lean_exe «l4xsd-datatypes» where root := `Harness.XsdDatatypesRun

@[default_target] lean_exe «l4shex» where root := `Harness.ShExRun

-- ISO Schematron conformance runner: Schematron/FromXml reads the
-- .sch, XPath/Mini supplies Validate's `select` and `evalTest`.
@[default_target] lean_exe «l4schematron» where root := `Harness.SchematronRun

-- RML-Core test cases: mapping.ttl + source + output.nq, compared by
-- DATASET isomorphism (Harness/RmlRun.lean).
@[default_target] lean_exe «l4rml» where root := `Harness.RmlRun

-- RIF Core conformance: syntax and entailment cases from the W3C
-- suite (Harness/RifRun.lean).
@[default_target] lean_exe «l4rif» where root := `Harness.RifRun

-- XSLT 1.0 conformance over the vendored w3c/xslt30-test subset:
-- XSLT/Transform runs the stylesheet, the result tree is serialised
-- and compared with the suite's own assert-xml file (Harness/XsltRun.lean).
@[default_target] lean_exe «l4xslt» where root := `Harness.XsltRun

-- ShExC differential: every schemas/*.shex read by ShEx/Compact and
-- compared with the ShExJ twin the same directory ships
-- (Harness/ShExCRun.lean).
@[default_target] lean_exe «l4shexc» where root := `Harness.ShExCRun

-- GRDDL conformance over the vendored W3C GRDDL suite: GRDDL/Discovery
-- finds the transformations, XSLT/Transform runs them, RdfXml reads the
-- output, and graphs are compared by isomorphism (Harness/GrddlRun.lean).
@[default_target] lean_exe «l4grddl» where root := `Harness.GrddlRun

-- Real-corpus probe for the SPARQL query parser: walks the W3C sparql11
-- .rq files without a manifest, using the suites' naming convention.
-- See L4Factoidal/SPARQL/Parser.lean and Harness/SparqlSyntaxProbe.lean.
@[default_target] lean_exe «l4sparql-probe» where root := `Harness.SparqlSyntaxProbe

-- Verifiable Credentials Data Integrity (eddsa-rdfc-2022) + did:key
-- probe (Harness/VcProbe.lean): the RFC 8032 Ed25519 vectors through
-- the HACL* extern (which `#guard` cannot evaluate), the did:key
-- vectors `bin/did-runner` reads, the eddsa-rdfc-2022 roundtrip
-- `bin/vc-runner --crypto` runs, and the W3C vc-di-eddsa specification
-- test vectors end to end (JSON-LD -> RDFC-1.0 -> SHA-256 -> Ed25519).
@[default_target] lean_exe «l4vc-probe» where root := `Harness.VcProbe

-- JOSE / Solid-OIDC probe (Harness/JoseProbe.lean, L4Factoidal/JOSE/).
-- The RFC 7515, 7520 and 9449 fixtures and the Wycheproof ECDSA and RSA
-- corpora, through the HACL* P-256 and RSA primitives. Everything the
-- pure JOSE layers decide is a build-time `#guard` in those modules;
-- this binary exists for the part that needs an extern.
@[default_target] lean_exe «l4jose-probe» where root := `Harness.JoseProbe

-- Real-corpus probe for the AEAD, KDF, X25519 and HPKE primitives
-- (Harness/CryptoProbe.lean): RFC 8439 section 2.8.2, RFC 5869 Appendix A,
-- RFC 7748 section 6.1, RFC 9180 Appendix A.2, and the Wycheproof
-- chacha20_poly1305, hkdf_sha256 and x25519 corpora. It also reports the
-- AES-GCM gap as NOT RUN rather than passing over it. Same spec/pragmatics
-- split as the other probes: file I/O and printed scores, and the externs
-- a `#guard` cannot reach. Run the built binary from the REPOSITORY ROOT.
@[default_target] lean_exe «l4crypto-probe» where root := `Harness.CryptoProbe

-- SHACL Core probe over the W3C shacl test suite (Harness/ShaclProbe.lean).
@[default_target] lean_exe «l4shacl» where root := `Harness.ShaclProbe

-- SHACL 1.2 rules suite (Harness/ShaclRulesRun.lean, L4Factoidal/SHACL/Rules.lean).
@[default_target] lean_exe «l4shacl-rules» where root := `Harness.ShaclRulesRun

-- SHACL 1.2 node-expr suite (Harness/ShaclNodeExprRun.lean, L4Factoidal/SHACL/NodeExpr.lean).
@[default_target] lean_exe «l4shacl-nodeexpr» where root := `Harness.ShaclNodeExprRun

-- Property-based probe: seeded generators + algebra/round-trip invariants
-- (Harness/PropProbe.lean, L4Factoidal/Testing/).
@[default_target] lean_exe «l4prop» where root := `Harness.PropProbe

-- Differential harness: the same (data, query) through the F* native
-- binary and the Lean evaluator (Harness/Differential.lean).
@[default_target] lean_exe «l4diff» where root := `Harness.Differential

-- HDT v1 container reader over the vendored hdt-cpp fixtures
-- (Harness/HdtProbe.lean). Directory-driven, not manifest-driven: the
-- HDT format has no W3C test suite, so the corpus is the two files in
-- third_party/testing/hdt/ with their published SHA-256 digests. Run
-- from the REPOSITORY ROOT.
@[default_target] lean_exe «l4hdt» where root := `Harness.HdtProbe

-- Delta (semi-naive) RDFS closure against the naive one: agreement and
-- wall-clock, on the subclass-chain shape issue #340 is about
-- (Harness/RdfsSemiNaive.lean). The module exists for speed, so this
-- measures speed as well as agreement.
@[default_target] lean_exe «l4rdfs-semi» where root := `Harness.RdfsSemiNaive

-- Conformance registry probes for the Linked Web Storage Protocol 1.0 Core
-- and for the Solid Protocol with Web Access Control
-- (https://github.com/danbri/factoidal/issues/659). Neither specification
-- ships a test suite, so the registry IS the conformance record: each row
-- quotes one normative statement verbatim and names the theorem or the
-- `#guard` that decides it. Each probe evaluates every guard and prints
-- "N pass, M fail (out of T)" with the open rows listed, and exits non-zero
-- if a check fails or a guarded row names no check.
-- See docs/lws-solid-conformance.md.
@[default_target] lean_exe «l4lws-probe» where root := `Harness.LwsProbe
@[default_target] lean_exe «l4solid-probe» where root := `Harness.SolidProbe

-- XPath 1.0 Stage-1 unit battery, ported from the F* corpus
-- tests/unit/xpath_tests.ml (Harness/XPathRun.lean), scored against
-- tests/unit/xpath_cases.json.
@[default_target] lean_exe «l4xpath» where root := `Harness.XPathRun

-- One XMPP client connection on stdin and stdout (RFC 6120 / RFC 6121).
-- The carrier forks one of these per connection and terminates TLS
-- outside it (XEP-0368 direct TLS); see deploy/fly/xmpp/. Every
-- protocol decision is in L4Factoidal/XMPP/Server.lean, not here.
@[default_target] lean_exe «l4xmpp-serve» where root := `Harness.XmppServe
@[default_target] lean_exe «l4xml-namespaces» where root := `Harness.NamespaceRun
