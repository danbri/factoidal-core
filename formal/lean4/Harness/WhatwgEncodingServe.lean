/-
Harness.WhatwgEncodingServe — `l4whatwg-encoding`: the Lean WHATWG Encoding
Standard engine behind the web-platform-tests runner
`tests/whatwg-encoding/run.mjs` (https://github.com/danbri/factoidal/issues/1167,
milestone 2).

  l4whatwg-encoding serve REQ RESP   read requests from the file REQ (a FIFO),
                                     one per line, and write one answer line
                                     per request to RESP
  l4whatwg-encoding selftest         decode and encode checks that need no
                                     fixtures (exit 0 when all pass)

The runner is a JavaScript host for the WPT test files: it gives them a
`TextDecoder`, a `TextEncoder` and the few browser surfaces the encoding tests
read. Every answer about bytes and code points comes from this program.

Request lines (fields separated by one space; `H(x)` is lower-case hex of the
bytes of x, `-` for no bytes; `U(x)` is UTF-16 code units, 4 hex digits each):

  label H(label)                          → ok NAME | fail
  tdnew ID H(label) FATAL IGNOREBOM       → ok ENCODING | range
  tddec ID STREAM HASINPUT H(bytes)       → ok U(output) | type
  te U(input)                             → ok H(bytes)
  teinto U(input) DESTLEN                 → ok READ WRITTEN H(bytes)
  pe H(label) SET PLUS U(input)           → ok H(ascii)
  decode H(label) H(bytes)                → ok U(output) | fail
  tdschunk ID H(bytes)                    → ok U(output) | type   (TextDecoderStream;
  tdsflush ID                             → ok U(output) | type    ID made by tdnew)
  tesnew ID                               → ok
  teschunk ID U(input)                    → ok H(bytes)            (TextEncoderStream)
  tesflush ID                             → ok H(bytes)
  xhrtext H(label)|- H(utf8 of a data: URL body)
                                          → ok U(output)
  quit
-/
import L4Factoidal.WHATWG.Encoding.Core
import L4Factoidal.WHATWG.URL.PercentEncode

open L4Factoidal.WHATWG.Encoding
open L4Factoidal.WHATWG.URL

namespace Harness.WhatwgEncodingServe

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexOfBytes (bs : ByteArray) : String :=
  if bs.size == 0 then "-"
  else bs.foldl (fun s b => (s.push (hexDigit (b.toNat / 16))).push (hexDigit (b.toNat % 16))) ""

def hexOfUnits (us : Array UInt16) : String :=
  if us.size == 0 then "-"
  else us.foldl (fun s u =>
    let n := u.toNat
    (((s.push (hexDigit (n / 4096))).push (hexDigit (n / 256 % 16))).push
      (hexDigit (n / 16 % 16))).push (hexDigit (n % 16))) ""

def digitVal (c : Char) : Nat :=
  if c ≤ '9' then c.toNat - 48 else if c ≤ 'F' then c.toNat - 55 else c.toNat - 87

def bytesOfHex (s : String) : ByteArray :=
  if s == "-" then ByteArray.empty
  else
    let cs := s.toList.toArray
    (List.range (cs.size / 2)).foldl (fun out i =>
      out.push (digitVal cs[2 * i]! * 16 + digitVal cs[2 * i + 1]!).toUInt8) ByteArray.empty

def unitsOfHex (s : String) : Array UInt16 :=
  if s == "-" then #[]
  else
    let cs := s.toList.toArray
    (List.range (cs.size / 4)).foldl (fun out i =>
      out.push (digitVal cs[4 * i]! * 4096 + digitVal cs[4 * i + 1]! * 256
        + digitVal cs[4 * i + 2]! * 16 + digitVal cs[4 * i + 3]!).toUInt16) #[]

def stringOfHex (s : String) : String :=
  String.fromUTF8! (bytesOfHex s)

def answer (decoders : IO.Ref (Std.HashMap String TextDecoder))
    (encoders : IO.Ref (Std.HashMap String TextEncoderStream)) (line : String) : IO String := do
  match line.splitOn " " with
  | ["label", l] =>
    return match getEncoding (stringOfHex l) with
      | some e => s!"ok {e.name}"
      | none => "fail"
  | ["tdnew", id, l, fatal, ign] =>
    match TextDecoder.new? (stringOfHex l) (fatal == "1") (ign == "1") with
    | some td =>
      decoders.modify (·.insert id td)
      return s!"ok {td.encodingName}"
    | none => return "range"
  | ["tddec", id, stream, hasInput, h] =>
    match (← decoders.get)[id]? with
    | none => return "error unknown decoder"
    | some td =>
      let input := if hasInput == "1" then some (bytesOfHex h) else none
      let (td', out) := td.decode input (stream == "1")
      decoders.modify (·.insert id td')
      return match out with
        | some cps => s!"ok {hexOfUnits (cpsToUtf16 cps)}"
        | none => "type"
  | ["tdschunk", id, h] =>
    match (← decoders.get)[id]? with
    | none => return "error unknown decoder"
    | some td =>
      let (td', out) := td.streamChunk (bytesOfHex h)
      decoders.modify (·.insert id td')
      return match out with
        | some cps => s!"ok {hexOfUnits (cpsToUtf16 cps)}"
        | none => "type"
  | ["tdsflush", id] =>
    match (← decoders.get)[id]? with
    | none => return "error unknown decoder"
    | some td =>
      let (td', out) := td.streamFlush
      decoders.modify (·.insert id td')
      return match out with
        | some cps => s!"ok {hexOfUnits (cpsToUtf16 cps)}"
        | none => "type"
  | ["tesnew", id] =>
    encoders.modify (·.insert id {})
    return "ok"
  | ["teschunk", id, u] =>
    let s := (← encoders.get)[id]?.getD {}
    let (s', out) := s.chunk (unitsOfHex u)
    encoders.modify (·.insert id s')
    return s!"ok {hexOfBytes out}"
  | ["tesflush", id] =>
    let s := (← encoders.get)[id]?.getD {}
    return s!"ok {hexOfBytes s.flush}"
  | ["te", u] => return s!"ok {hexOfBytes (textEncoderEncode (unitsOfHex u))}"
  | ["teinto", u, n] =>
    let (r, w, bs) := textEncoderEncodeInto (unitsOfHex u) n.toNat!
    return s!"ok {r} {w} {hexOfBytes bs}"
  | ["pe", l, set, plus, u] =>
    let enc := getOutputEncoding ((getEncoding (stringOfHex l)).getD .utf_8)
    match PercentEncodeSet.ofName? set with
    | none => return "error unknown set"
    | some s =>
      let cps := (usvFromUtf16 (unitsOfHex u)).map (·.1)
      let out := percentEncodeAfterEncoding enc cps s (plus == "1")
      return s!"ok {hexOfBytes out.toUTF8}"
  | ["decode", l, h] =>
    match getEncoding (stringOfHex l) with
    | some e => return s!"ok {hexOfUnits (cpsToUtf16 (decodeCps (bytesOfHex h) e))}"
    | none => return "fail"
  | ["xhrtext", l, h] =>
    -- XMLHttpRequest "text response" for a data: URL: the body is
    -- percent-decoded (URL Standard), the final encoding is the override
    -- charset label, or UTF-8 when there is none or it is not a label
    -- (XMLHttpRequest Standard, "get a final encoding"), then decode.
    let enc := if l == "-" then Encoding.utf_8 else (getEncoding (stringOfHex l)).getD .utf_8
    let bytes := percentDecode (bytesOfHex h)
    return s!"ok {hexOfUnits (cpsToUtf16 (decodeCps bytes enc))}"
  | _ => return s!"error bad request"

/-- The request loop. It ends at `quit` or at the end of the request file,
an outside event, so it is a `repeat` loop (CLAUDE.md, 2026-10-23). -/
def serve (req resp : String) : IO Unit := do
  let hin ← IO.FS.Handle.mk req .read
  let hout ← IO.FS.Handle.mk resp .write
  let decoders ← IO.mkRef ({} : Std.HashMap String TextDecoder)
  let encoders ← IO.mkRef ({} : Std.HashMap String TextEncoderStream)
  repeat
    let line ← hin.getLine
    if line.isEmpty then break
    let line := String.ofList (line.toList.filter (fun c => c != '\n' && c != '\r'))
    if line == "quit" then break
    let a ← answer decoders encoders line
    hout.putStrLn a
    hout.flush

def check (name : String) (ok : Bool) (fails : IO.Ref Nat) : IO Unit := do
  unless ok do
    IO.eprintln s!"selftest FAIL: {name}"
    fails.modify (· + 1)

def selftest : IO UInt32 := do
  let fails ← IO.mkRef 0
  let bytes (l : List Nat) : ByteArray := ByteArray.mk (l.map (·.toUInt8)).toArray
  check "label utf8" (getEncoding " UTF8\n" == some .utf_8) fails
  check "label latin1" (getEncoding "latin1" == some .windows_1252) fails
  check "label bogus" (getEncoding "utf-7" == none) fails
  check "utf-8 snowman" (utf8Decode (bytes [0xE2, 0x98, 0x83]) == "☃") fails
  check "utf-8 bom" (utf8Decode (bytes [0xEF, 0xBB, 0xBF, 0x41]) == "A") fails
  check "utf-8 maximal subpart" (utf8DecodeWithoutBOM (bytes [0xF0, 0x80, 0x41]) == "��A") fails
  check "utf-8 fail" (utf8DecodeWithoutBOMOrFail (bytes [0xC0]) == none) fails
  check "windows-1252 0x80" (decode (bytes [0x80]) .windows_1252 == "€") fails
  check "shift_jis" (decode (bytes [0x82, 0xA0]) .shift_jis == "あ") fails
  check "euc-kr" (decode (bytes [0xB0, 0xA1]) .euc_kr == "가") fails
  check "big5 pair" (decode (bytes [0x88, 0x62]) .big5 == "Ê̄") fails
  check "gb18030 4-byte" (decode (bytes [0x81, 0x30, 0x81, 0x30]) .gb18030 == "\u0080") fails
  check "gb18030 restore" (decode (bytes [0x81, 0x30, 0x81, 0x20]) .gb18030 == "�0� ") fails
  check "iso-2022-jp" (decode (bytes [0x1B, 0x24, 0x42, 0x24, 0x22, 0x1B, 0x28, 0x42]) .iso_2022_jp == "あ") fails
  check "utf-16le bom" (decode (bytes [0xFF, 0xFE, 0x41, 0x00]) .windows_1252 == "A") fails
  check "encode sjis" (encode #[0x3042] .shift_jis == some (bytes [0x82, 0xA0])) fails
  check "encode html mode" (encode #[0x2603] .windows_1252 == some "&#9731;".toUTF8) fails
  check "encode gb18030 4-byte" (encode #[0x80] .gb18030 == some (bytes [0x81, 0x30, 0x81, 0x30])) fails
  check "percent-encode" (percentEncodeAfterEncoding .windows_1252 #[0x2603] .specialQuery == "%26%239731%3B") fails
  -- Scale: 4,000,000 bytes that make the gb18030 decoder restore three bytes
  -- every four; the loop is a tail call, so this runs under a 1 MB stack
  -- (run.sh sets ulimit -s 1024).
  let big := (List.range 1000000).foldl (fun (b : ByteArray) _ =>
    ((b.push 0x81).push 0x30 |>.push 0x81).push 0x20) ByteArray.empty
  let out := decodeCps big .gb18030
  check "gb18030 scale (4,000,000 bytes)" (out.size == 4000000) fails
  let n ← fails.get
  IO.println s!"l4whatwg-encoding selftest: {20 - n} pass, {n} fail (out of 20)"
  return if n == 0 then 0 else 1

/-- Decode throughput on generated input, for the design record. -/
def bench : IO UInt32 := do
  let mk (unit : List UInt8) (n : Nat) : ByteArray :=
    (List.range n).foldl (fun (b : ByteArray) _ => unit.foldl (·.push ·) b) ByteArray.empty
  let cases : List (String × Encoding × ByteArray) :=
    [("UTF-8 ASCII", .utf_8, mk [0x61] 8000000),
     ("UTF-8 3-byte (U+3042)", .utf_8, mk [0xE3, 0x81, 0x82] 2666667),
     ("windows-1252", .windows_1252, mk [0xE9] 8000000),
     ("Shift_JIS 2-byte", .shift_jis, mk [0x82, 0xA0] 4000000),
     ("gb18030 4-byte", .gb18030, mk [0x81, 0x30, 0x81, 0x30] 2000000)]
  for (name, e, bs) in cases do
    let t0 ← IO.monoNanosNow
    let out ← IO.lazyPure fun _ => decodeCps bs e
    let t1 ← IO.monoNanosNow
    let ms := (t1 - t0) / 1000000
    let mbps := if ms == 0 then 0 else bs.size * 1000 / ms / 1000000
    IO.println s!"decode {name}: {bs.size} bytes, {out.size} code points, {ms} ms, {mbps} MB/s"
  -- Reference on the same input: Lean core's String.fromUTF8? (validation
  -- and copy in C, no replacement).
  let bs := mk [0xE3, 0x81, 0x82] 2666667
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure fun _ => String.fromUTF8? bs
  let t1 ← IO.monoNanosNow
  IO.println s!"reference String.fromUTF8? UTF-8 3-byte: {bs.size} bytes, {(r.map (·.length)).getD 0} chars, {(t1 - t0) / 1000000} ms"
  return 0

end Harness.WhatwgEncodingServe

def main (args : List String) : IO UInt32 := do
  match args with
  | ["bench"] => Harness.WhatwgEncodingServe.bench
  | ["serve", req, resp] => Harness.WhatwgEncodingServe.serve req resp; return 0
  | ["selftest"] => Harness.WhatwgEncodingServe.selftest
  | _ =>
    IO.eprintln "usage: l4whatwg-encoding serve REQ RESP | selftest"
    return 2
