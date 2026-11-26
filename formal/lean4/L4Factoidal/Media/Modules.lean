/-
L4Factoidal.Media.Modules: the decoder modules that Lean's WasmVM may run, pinned by SHA-256
(record: docs/designissues/2026-11-26-foafnaut-audio-plan.md, sections 3 and 4; issue
https://github.com/danbri/factoidal-core/issues/1169).

The modules, their build chain, provenance and licences are in `danbri/factoidal-builds`,
`third_party/media-decoders` (owner, 2026-11-26: "vendor them into factoidal-builds/ repo
third_party/ with provenance version and license info. Include wasm and build chain."). A module
is loaded only when its bytes have the pinned size and SHA-256, and its `mw_abi` export gives the
pinned interface version: a rebuilt module with other bytes is a change this file must take on
purpose. `tools/fetch-media-decoders.sh` fetches the modules and checks the same hashes.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Media.Modules

/-- A pinned module: its file name, the SHA-256 of its bytes (lower-case hex), its size in bytes,
and the interface version that its `mw_abi` export returns. -/
structure Pin where
  file : String
  sha256 : String
  bytes : Nat
  abi : Nat
  deriving Repr, BEq

/-- The commit of `danbri/factoidal-builds` whose `third_party/media-decoders/wasm` holds the
pinned modules (`PROVENANCE.md` there: sources, licences, Emscripten 6.0.8, the checks). -/
def source : String :=
  "danbri/factoidal-builds 67701b16ef285969e1a4a7ec7692cafad94b63e8 third_party/media-decoders/wasm"

def pins : List Pin := [
  { file := "opus-wasmvm.wasm", bytes := 126600, abi := 2,
    sha256 := "0397d9f0daf0f85034626f7ce7ac44455ded2d92a120cabb303ed433f9e87daa" },
  { file := "vorbis-wasmvm.wasm", bytes := 152839, abi := 2,
    sha256 := "fcc4c90eaae4dbf44854a227d891ae7a5ae466c8d5c016c715cfac9296a9d367" },
  { file := "vp8-wasmvm.wasm", bytes := 98853, abi := 2,
    sha256 := "3a536c007f6e1dd446c74b46cc003860f51e9a59567aa98dd286f82666f9236b" },
  { file := "mp3-wasmvm.wasm", bytes := 36337, abi := 2,
    sha256 := "d27a97544d98d70ad1a3625f3d5b3db6a6271dd5ef96dc2a601afbd69f7f0efd" } ]

def pinOf? (file : String) : Option Pin := pins.find? (·.file == file)

/-- The check made on a module's bytes before it is instantiated.

Says: `.ok p` only when a pin `p` names the file and the bytes have its size and SHA-256.
Does not say: anything about what the module computes; that is tested (record section 4: the
same C built natively, FFmpeg, and the float exports against the int16 exports). -/
def check (file : String) (b : ByteArray) : Except String Pin := do
  let some p := pinOf? file | throw s!"{file}: not a pinned media module ({source})"
  if b.size != p.bytes then throw s!"{file}: {b.size} bytes, pinned {p.bytes} ({source})"
  let got := Crypto.bytesToHex (Crypto.sha256 b)
  if got != p.sha256 then throw s!"{file}: SHA-256 {got}, pinned {p.sha256} ({source})"
  pure p

/-- Every pin names a different file, so `pinOf?` has one answer for each module. -/
theorem pins_files_nodup : (pins.map (·.file)).Nodup := by decide

#guard (check "other.wasm" ByteArray.empty).toOption.isNone
#guard (check "mp3-wasmvm.wasm" (ByteArray.mk #[0, 1, 2])).toOption.isNone
#guard pins.all (fun p => p.sha256.length == 64 && p.abi == 2)

end L4Factoidal.Media.Modules
