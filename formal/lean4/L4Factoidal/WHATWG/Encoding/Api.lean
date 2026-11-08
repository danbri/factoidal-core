/-
L4Factoidal.WHATWG.Encoding.Api — the Encoding Standard's API (section 7) as the
page serves it: bytes in, bytes out.

The algorithms are `Core.lean`'s: `TextDecoder.decode` (section 7.2), "UTF-8 encode"
and `textEncoderEncodeInto` (section 7.4). This module adds what a page needs on top:

  * `TextDecoder.decodeBytes`: the decoded string as UTF-8 bytes (what the page
    import answers), with one fast path. When the decoder is UTF-8, fresh (initial
    state, empty I/O queue) and the input is valid UTF-8, the output is the input
    itself, less a leading BOM that the decoder would remove. `decodeBytesRef` is the
    specification-level function (`TextDecoder.decode`, then UTF-8 encode); the
    `#guard`s below compare the two on the cases of the fast path's conditions.
  * `encodeUtf8?`: `TextEncoder.encode` of a USVString given as its UTF-8 bytes.
  * `encodeIntoUtf8`: `encodeInto` of a USVString given as a Lean string: `read` in
    UTF-16 code units, `written` in bytes.

Theorems (Encoding Standard section 4.1, "process a queue"):

  * `decodeLoop_replacement_ne_error`: with error mode "replacement" the decoder
    loop never ends in error, whatever the decoder, queue and input.
  * `xUserDefined_roundTrip`: x-user-defined decode then encode gives the byte back,
    for every byte.

No `partial`, no `sorry`.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.WHATWG.Encoding

/-- The specification-level result of `decode(input, {stream})`: the next state and
the output's UTF-8 bytes, `none` for a TypeError. -/
def TextDecoder.decodeBytesRef (td : TextDecoder) (input : ByteArray) (stream : Bool) :
    TextDecoder × Option ByteArray :=
  let (td, r) := td.decode (some input) stream
  (td, r.map utf8Encode)

/-- The decoder is UTF-8's in its initial state with an empty queue, after the reset
that `decode` makes when the last call flushed. -/
def TextDecoder.freshUtf8 (td : TextDecoder) : Bool :=
  td.encoding == .utf_8 &&
  (!td.doNotFlush ||
    (match td.decoder with
     | .utf8 cp seen needed lower upper => cp == 0 && seen == 0 && needed == 0 && lower == 0x80 && upper == 0xBF
     | _ => false) &&
    td.queue.front.isEmpty && td.queue.pos == td.queue.data.size)

/-- `decode(input, {stream})` with the output as UTF-8 bytes. -/
def TextDecoder.decodeBytes (td : TextDecoder) (input : ByteArray) (stream : Bool) :
    TextDecoder × Option ByteArray :=
  if td.freshUtf8 && ByteArray.validateUTF8 input then
    let bomSeen := if !td.doNotFlush then false else td.bomSeen
    let bom := input.size ≥ 3 && input[0]! == 0xEF && input[1]! == 0xBB && input[2]! == 0xBF
    let strip := !td.ignoreBOM && !bomSeen && bom
    let seen := if !td.ignoreBOM && !bomSeen && input.size > 0 then true else bomSeen
    let td' : TextDecoder := { td with decoder := utf8Initial, queue := {}, doNotFlush := stream, bomSeen := seen }
    (td', some (if strip then input.extract 3 input.size else input))
  else td.decodeBytesRef input stream

/-- `TextEncoder.encode` of a USVString given as its UTF-8 bytes: the UTF-8 encode of
its scalar values, which are those bytes. `none` when the bytes are not UTF-8 (the
caller did not give a USVString). -/
def encodeUtf8? (bytes : ByteArray) : Option ByteArray :=
  if ByteArray.validateUTF8 bytes then some bytes else none

/-- `encodeInto(source, destination)` (section 7.4) for a USVString: the code units
read, the bytes written, and those bytes. -/
def encodeIntoUtf8 (s : String) (destLength : Nat) : Nat × Nat × ByteArray :=
  let r := s.foldl (fun (acc : Nat × Nat × ByteArray × Bool) c =>
    let (read, written, out, stopped) := acc
    if stopped then acc else
    let n := c.utf8Size
    if destLength - written ≥ n then
      (read + (if c.toNat > 0xFFFF then 2 else 1), written + n, pushBytes out (utf8EncodeCp c.val), false)
    else (read, written, out, true)) (0, 0, ByteArray.empty, false)
  (r.1, r.2.1, r.2.2.1)

/-! ## Theorems -/

theorem decodeLoop_replacement_ne_error : ∀ (fuel : Nat) (d : Decoder) (q : Queue) (out : Array UInt32)
    (stop : Bool), (decodeLoop fuel d q out .replacement stop).2.2.2 ≠ .error := by
  intro fuel
  induction fuel with
  | zero => intro d q out stop; simp [decodeLoop]
  | succ n ih =>
    intro d q out stop
    unfold decodeLoop
    split
    rename_i item q' _
    split
    · simp
    · generalize d.handle item = s
      rcases s with ⟨d', r, rs⟩
      cases r with
      | finished => simp
      | items cps => exact ih _ _ _ _
      | cont => exact ih _ _ _ _
      | error => exact ih _ _ _ _

/-- x-user-defined: the decoder's code point for byte `b`, encoded again, is `b`. -/
def xUserDefinedRoundTrips (b : UInt8) : Bool :=
  match (Decoder.xUserDefined.handle (some b)).result with
  | .items [cp] => match (Encoder.xUserDefined.handle (some cp)).result with
    | .bytes [b'] => b' == b
    | _ => false
  | _ => false

theorem xUserDefined_roundTrip : ∀ i : Fin 256, xUserDefinedRoundTrips (UInt8.ofNat i) = true := by
  decide +kernel

/-! ## Checks of the fast path against the reference -/

private def td! (label : String) (fatal ignoreBOM : Bool := false) : TextDecoder :=
  (TextDecoder.new? label fatal ignoreBOM).getD default

private def agree (td : TextDecoder) (chunks : List (ByteArray × Bool)) : Bool :=
  let go := fun (f : TextDecoder → ByteArray → Bool → TextDecoder × Option ByteArray) =>
    (chunks.foldl (fun (acc : TextDecoder × List (Option ByteArray)) (b, st) =>
      let (t, r) := f acc.1 b st; (t, acc.2 ++ [r])) (td, [])).2
  go TextDecoder.decodeBytes == go TextDecoder.decodeBytesRef

private def bs (l : List Nat) : ByteArray := ByteArray.mk (l.map (·.toUInt8)).toArray

#guard agree (td! "utf-8") [(bs [0x61, 0x62], false)]
#guard agree (td! "utf-8") [(bs [0xEF, 0xBB, 0xBF, 0x61], false)]
#guard agree (td! "utf-8" false true) [(bs [0xEF, 0xBB, 0xBF, 0x61], false)]
#guard agree (td! "utf-8") [(bs [0xEF, 0xBB, 0xBF], true), (bs [0xEF, 0xBB, 0xBF, 0x61], true), (bs [], false)]
#guard agree (td! "utf-8") [(bs [0xE2, 0x82], true), (bs [0xAC, 0x61], true), (bs [0x61], false)]
#guard agree (td! "utf-8") [(bs [], true), (bs [0xEF, 0xBB], true), (bs [0xBF, 0x62], false)]
#guard agree (td! "utf-8" true) [(bs [0xFF], false), (bs [0x61], false)]
#guard agree (td! "utf-8") [(bs [0xF0, 0x9F, 0x98, 0x80], true), (bs [0xEF, 0xBB, 0xBF], false)]
#guard agree (td! "shift_jis") [(bs [0x82, 0xA0, 0x41], false)]
#guard encodeIntoUtf8 "aé😀" 3 == (2, 3, bs [0x61, 0xC3, 0xA9])
#guard encodeIntoUtf8 "aé😀" 7 == (4, 7, bs [0x61, 0xC3, 0xA9, 0xF0, 0x9F, 0x98, 0x80])
#guard (encodeIntoUtf8 "😀x" 3).1 == 0

end L4Factoidal.WHATWG.Encoding
