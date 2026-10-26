/-
Wasm.Ops.Support — envelope helpers shared by the op modules.

The dispatch ABI (`Wasm/Dispatch.lean`) speaks the SAME method names and
JSON envelopes as the F* npm entry point (`bin/npm-entry/entry_jsoo.ml`):
every op returns `{"ok":true,…}` or `{"ok":false,"error":"…"}`, so the
JS side (`api.js`'s `entryResult`) can treat the two engines alike.

JSON parsing and serialisation delegate to `L4Factoidal.JSON` (the
ported `Parser.JSON.fst` / `SPARQL.JSON.Escape.fst`), NOT to the
phase-1 `L4Wasm.Json` shim in `Wasm/Abi.lean` — that shim is pinned by
hub post 36 and is not extended (see its own banner).

Targeted imports, not the L4Factoidal umbrella: the wasm module
initializes every module its root imports, so the umbrella pays init
cost (and init RISK) for all modules when an op needs a fraction of
them (same rule as `Wasm/Abi.lean`).
-/
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.Lexing
import Wasm.Ops.ErrorModel

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.RDF

/-- `{"ok":false,"error":"…"}` — the error envelope every op shares
with the F* npm entry. -/
def errJson (msg : String) : String :=
  (Json.object [("ok", .bool false), ("error", .string msg)]).toString

/-- `{"ok":true,…fields…}` — the success envelope, fields in the given
order (`L4Factoidal.JSON.Json.object` preserves member order). -/
def okWith (fields : List (String × Json)) : String :=
  (Json.object (("ok", Json.bool true) :: fields)).toString

/-- The harness's error rendering (`Harness/Run.lean`'s
`fmtParseError`): message plus codepoint offset. -/
def fmtParseError (e : L4Factoidal.Syntax.ParseError) : String :=
  s!"{e.msg} (offset {e.pos})"

/-- The general decoder of the dispatch argument envelope: `parseJson`, then a
check that the value is an array of strings. `decodeArgs` falls back to it on
every input its fast path does not read. -/
def decodeArgsSpec (argsJson : String) : Except String (List String) :=
  match parseJson argsJson with
  | .error e => .error s!"argsJson: {toString e}"
  | .ok (.array items) =>
      items.mapM fun it =>
        match it with
        | .string s => .ok s
        | _ => .error "argsJson must be a JSON array of strings"
  | .ok _ => .error "argsJson must be a JSON array of strings"

/-- The byte a short JSON escape `\c` stands for (RFC 8259 section 7,
`escapePiece` of `L4Factoidal/JSON/Parser.lean`). `none` for `\u` and for
every byte that is not an escape, so that the caller falls back. -/
@[inline] private def argsShortEscape? (c : UInt8) : Option UInt8 :=
  if c == 0x22 then some 0x22        -- \"
  else if c == 0x5C then some 0x5C   -- \\
  else if c == 0x2F then some 0x2F   -- \/
  else if c == 0x62 then some 0x08   -- \b
  else if c == 0x66 then some 0x0C   -- \f
  else if c == 0x6E then some 0x0A   -- \n
  else if c == 0x72 then some 0x0D   -- \r
  else if c == 0x74 then some 0x09   -- \t
  else none

/-- One JSON string at byte `i` of `src` (just after its opening quote): its
UTF-8 bytes with the short escapes decoded, and the position of the closing
quote. `none` at a `\u` escape, a control character or the end of the
input, so that the caller falls back. -/
private def argsStringGo? (src : ByteArray) (i : Nat) (out : ByteArray) :
    Option (ByteArray × Nat) :=
  if h : i < src.size then
    let b := src[i]
    if b == 0x22 then some (out, i)
    else if b < 0x20 then none
    else if b == 0x5C then
      if h2 : i + 1 < src.size then
        match argsShortEscape? src[i + 1] with
        | some e => argsStringGo? src (i + 2) (out.push e)
        | none => none
      else none
    else argsStringGo? src (i + 1) (out.push b)
  else none
termination_by src.size - i

/-- The fast path of `decodeArgs`: the form `JSON.stringify` gives an array
of strings, `["…","…"]` with no whitespace, where every escape is a short one.
`none` on anything else. -/
private def argsArrayGo? (src : ByteArray) (i : Nat) (acc : Array String) :
    Option (List String) :=
  if h : i < src.size then
    if src[i] != 0x22 then none
    else match argsStringGo? src (i + 1) .empty with
      | none => none
      | some (bytes, stop) =>
        match String.fromUTF8? bytes with
        | none => none
        | some text =>
          let acc := acc.push text
          if h2 : stop + 1 < src.size then
            let next := src[stop + 1]
            if next == 0x5D then
              if stop + 2 == src.size then some acc.toList else none
            else if next == 0x2C then
              if h3 : i < stop ∧ stop + 2 < src.size then
                argsArrayGo? src (stop + 2) acc
              else none
            else none
          else none
  else none
termination_by src.size - i
decreasing_by omega

/-- Decode the dispatch argument envelope: a JSON ARRAY OF STRINGS
(positional arguments). Anything else is a caller error.

An argument can be a whole document or a store manifest as hexadecimal (1.5
million characters for the londat store of
https://github.com/danbri/factoidal/issues/1039), and `parseJson` over it
cost about 0.4 s per call in the wasm module. So the form `JSON.stringify`
gives is read in place when every escape in it is a short one (SPARQL text
has `\n`; the artifact list of `storeOpen` is JSON inside a string, so it
has `\"`). A `\u` escape and every other input go to `decodeArgsSpec`. The `#guard`s below check that the two agree. -/
def decodeArgs (argsJson : String) : Except String (List String) :=
  let src := argsJson.toUTF8
  let fast : Option (List String) :=
    if src.size == 2 && src[0]! == 0x5B && src[1]! == 0x5D then some []
    else if 2 ≤ src.size && src[0]! == 0x5B then argsArrayGo? src 1 #[]
    else none
  match fast with
  | some args => .ok args
  | none => decodeArgsSpec argsJson

#guard ([ "[]", "[\"\"]", "[\"a\"]", "[\"a\",\"bc\"]", "[\"é😀\",\"x\"]",
          "[\"a\\\"b\"]", "[\"a\\nb\",\"c\"]", "[ \"a\" ]", "[\"a\",]", "[\"a\"",
          "[\"a\"]x", "[1]", "[\"a\",1]", "{}", "", "[", "[\"", "\"a\"", "[\"a\" ,\"b\"]",
          "[\"\\u0041\"]", "[\"a\"][\"b\"]",
          "[\"\\/\\b\\f\\r\\t\\\\\"]", "[\"x\\\\\",\"\\\"\"]", "[\"\\x\"]", "[\"a\\",
          "[\"\\ud83d\\ude00\"]", "[\"\\ud83d\"]", "[\"{\\\"key\\\":\\\"k\\\",\\\"len\\\":3}\"]",
          "[\"SELECT ?s\\nWHERE { ?s ?p \\\"é\\\" }\",\"\"]" ].all fun t =>
  match decodeArgs t, decodeArgsSpec t with
  | .ok a, .ok b => a == b
  | .error _, .error _ => true
  | _, _ => false)
#guard decodeArgs "[\"ab\",\"\",\"c\"]" == .ok ["ab", "", "c"]
-- The fast path itself reads the two shapes the store ops send: SPARQL text
-- (newlines) and the artifact list of `storeOpen` (JSON inside a string).
#guard (argsArrayGo? "[\"00ff\",\"SELECT *\\nWHERE { ?s ?p ?o }\"]".toUTF8 1 #[]).isSome
#guard (argsArrayGo? "[\"00ff\",\"[{\\\"key\\\":\\\"p-0.ibk5\\\",\\\"offset\\\":0,\\\"len\\\":9}]\"]".toUTF8 1 #[]) ==
  some ["00ff", "[{\"key\":\"p-0.ibk5\",\"offset\":0,\"len\":9}]"]

/-! ## Hexadecimal byte transport

The dispatch ABI carries strings, so every op that moves BYTES across it
encodes them as lowercase hexadecimal.  Hex is a portable diagnostic
transport, not the eventual high-throughput host boundary: a worker that owns
a buffer ABI should pass validated byte buffers directly.  These helpers are
shared by `Wasm/Ops/Block.lean` and `Wasm/Ops/Store.lean` so both read and
write the same encoding. -/

private def hexDigitValue? (c : Char) : Option Nat :=
  let n := c.toNat
  if 0x30 ≤ n && n ≤ 0x39 then some (n - 0x30)
  else if 0x61 ≤ n && n ≤ 0x66 then some (n - 0x61 + 10)
  else if 0x41 ≤ n && n ≤ 0x46 then some (n - 0x41 + 10)
  else none

private def bytesOfHexCharsGo? : List Char → List UInt8 → Option (List UInt8)
  | [], reversed => some reversed.reverse
  | [_], _ => none
  | hi :: lo :: rest, reversed => do
      let h ← hexDigitValue? hi
      let l ← hexDigitValue? lo
      bytesOfHexCharsGo? rest (UInt8.ofNat (h * 16 + l) :: reversed)

/-- The specification of `bytesOfHex?`: the character-list decoder. It builds
one cons cell per character and one per byte, which for a store manifest
(1.5 million hexadecimal digits) cost about 0.7 s per call in the wasm module
(https://github.com/danbri/factoidal/issues/1039). -/
def bytesOfHexSpec? (s : String) : Option ByteArray :=
  (bytesOfHexCharsGo? s.toList []).map fun bytes => ByteArray.mk bytes.toArray

/-- The value of one hexadecimal digit given as a UTF-8 byte. A byte of a
multi-byte character is 0x80 or more, so it is never a digit. -/
@[inline] private def hexByteValue? (b : UInt8) : Option UInt8 :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b - 0x61 + 10)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b - 0x41 + 10)
  else none

private def bytesOfHexUtf8Go? (src : ByteArray) (i : Nat) (out : ByteArray) :
    Option ByteArray :=
  if h : i + 1 < src.size then
    match hexByteValue? src[i], hexByteValue? src[i + 1] with
    | some hi, some lo => bytesOfHexUtf8Go? src (i + 2) (out.push (hi * 16 + lo))
    | _, _ => none
  else if i < src.size then none
  else some out
termination_by src.size - i

/-- Decode an even-length hexadecimal string.  `none` on an odd length or a
non-hexadecimal character. It reads the UTF-8 bytes in place into a buffer of
the final size; the `#guard`s below check it against `bytesOfHexSpec?`. -/
def bytesOfHex? (s : String) : Option ByteArray :=
  let src := s.toUTF8
  bytesOfHexUtf8Go? src 0 (ByteArray.emptyWithCapacity (src.size / 2))

#guard (["", "00", "ff", "FF", "0aB9", "deadBEEF", "0", "abc", "zz", "0g", "é0", "0é",
         "éé", "00é", "Ab😀", "😀"].all fun t =>
  (bytesOfHex? t).map (·.toList) == (bytesOfHexSpec? t).map (·.toList))
#guard (bytesOfHex? "00ff10").map (·.toList) == some [0, 255, 16]

private def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x61 + n - 10)

/-- Lowercase hexadecimal, two digits per byte. -/
def hexOfBytes (bytes : ByteArray) : String :=
  let reversed := bytes.data.toList.foldl (fun out byte =>
    hexChar (byte.toNat % 16) :: hexChar (byte.toNat / 16) :: out) []
  String.ofList reversed.reverse

/-- The members of a JSON object WITHOUT its enclosing braces, so a caller can
splice a pre-serialised JSON document in beside them (the `srj` member of the
`queryDataset` envelope is such a document).  `[]` gives the empty string. -/
def jsonMembers (fields : List (String × Json)) : String :=
  String.intercalate "," (fields.map fun (name, value) =>
    (Json.string name).toString ++ ":" ++ value.toString)

/-- Telemetry only — NOT part of a closure answer (the mirror of
`entry_jsoo.ml`'s `rho_df_rounds_to_fixpoint` /
`rdfs_plus_rounds_to_fixpoint`): count rounds to fixpoint by re-driving
the step function and comparing graph length round over round, capped
so a pathological input cannot spin. The graph this loop touches is
discarded once the round count is known; the closure answer always
comes from the closure function itself. -/
def roundsToFixpoint (stepF : Graph → Graph) : Nat → Graph → Nat
  | 0, _ => 0
  | cap + 1, g =>
      let g' := stepF g
      if g'.length != g.length then roundsToFixpoint stepF cap g' + 1 else 0

end L4Wasm.Ops
