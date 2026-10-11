/-
L4Factoidal.Qlvr.Fsst — FSST symbol-table decoding for the QLever vocabulary
(Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

Format record: docs/designissues/2026-10-11-qlever-index-format.md, section 2.
A `fsst_decoder_t` (`fsst.h:80-85` in https://github.com/cwida/fsst) is 2,304
bytes: `u64 version`, `u8 zeroTerminated`, `u8 len[255]`, then at offset 264
`u64 symbol[255]` (the symbol bytes in little-endian order). Decoding
(`fsst.h:209-219`): code byte `c < 255` emits the first `len[c]` bytes of
`symbol[c]`; code 255 (`FSST_ESC`) emits the next input byte unchanged.

## Loop

`decodeLoop` is a tail call with a fuel `Nat` (the code bytes still to read)
as its first argument and the output buffer as an accumulator, so it compiles
to a jump. The symbol bytes are copied with `ByteArray.copySlice` from the
decoder table (a different object) into the unique output buffer, which
appends in place.
-/

namespace L4Factoidal.Qlvr.Fsst

/-- Bytes of one serialized `fsst_decoder_t`. -/
def decoderBytes : Nat := 2304

/-- One FSST decoder: the 255 symbol lengths and the 255 × 8 symbol bytes. -/
structure Decoder where
  zeroTerminated : Bool
  lens : ByteArray
  syms : ByteArray
  deriving Inhabited

/-- Parse a `fsst_decoder_t` at byte `off` of `d`. -/
def Decoder.parse (d : ByteArray) (off : Nat) : Except String Decoder :=
  if off + decoderBytes > d.size then
    .error s!"fsst decoder at {off}: needs {decoderBytes} bytes, {d.size - min off d.size} remain"
  else
    .ok { zeroTerminated := d.get! (off + 8) != 0,
          lens := d.extract (off + 9) (off + 264),
          syms := d.extract (off + 264) (off + 264 + 255 * 8) }

/-- Decode code bytes `[i, stop)` of `src`, appending to `out`. -/
def decodeLoop (dec : Decoder) (src : ByteArray) (stop : Nat) :
    Nat → Nat → ByteArray → Except String ByteArray
  | 0, i, out =>
    if i ≥ stop then .ok out else .error "fsst: fuel exhausted before the end of the input"
  | k+1, i, out =>
    if h : i < stop ∧ i < src.size then
      let c := (src[i]'h.2).toNat
      if c == 255 then
        if h2 : i + 1 < stop ∧ i + 1 < src.size then
          decodeLoop dec src stop k (i + 2) (out.push (src[i+1]'h2.2))
        else .error "fsst: escape code at the end of the input"
      else
        let n := (dec.lens.get! c).toNat
        if n > 8 then .error s!"fsst: symbol {c} has length {n} > 8"
        else decodeLoop dec src stop k (i + 1) (dec.syms.copySlice (8 * c) out out.size n false)
    else if i ≥ stop then .ok out
    else .error "fsst: input range past the end of the buffer"

/-- FSST-decode bytes `[start, stop)` of `src`. -/
def decodeRange (dec : Decoder) (src : ByteArray) (start stop : Nat) : Except String ByteArray :=
  if stop > src.size || start > stop then .error "fsst: input range out of bounds"
  else decodeLoop dec src stop (stop - start + 1) start (ByteArray.emptyWithCapacity (8 * (stop - start)))

/-- FSST-decode all of `src`. -/
def decode (dec : Decoder) (src : ByteArray) : Except String ByteArray :=
  decodeRange dec src 0 src.size

-- A two-symbol table: code 0 = "ab", code 1 = "c".
private def testDecoder : Decoder :=
  { zeroTerminated := false,
    lens := (ByteArray.mk (Array.replicate 255 0)).set! 0 2 |>.set! 1 1,
    syms := (ByteArray.mk (Array.replicate (255 * 8) 0)).set! 0 97 |>.set! 1 98 |>.set! 8 99 }
#guard (decode testDecoder (ByteArray.mk #[0, 1, 255, 120, 0])).toOption.map (·.data) ==
  some #[97, 98, 99, 120, 97, 98]
#guard (decode testDecoder (ByteArray.mk #[0, 255])) matches .error _
#guard (decode testDecoder ByteArray.empty).toOption.map (·.size) == some 0

end L4Factoidal.Qlvr.Fsst
