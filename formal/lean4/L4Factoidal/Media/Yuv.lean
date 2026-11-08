/-
L4Factoidal.Media.Yuv: a decoded picture from packed I420 (8-bit Y plane, then the U
and V planes at half width and half height, rounded up) to RGBA (record:
docs/designissues/2026-11-08-media-wasmvm.md).

ITU-R BT.601 with limited range (Y 16 to 235, U and V 16 to 240), as VP8 states
(RFC 6386 section 9.2, colour space 0), in 16.16 fixed point:

    R = 1.164 (Y - 16) + 1.596 (V - 128)
    G = 1.164 (Y - 16) - 0.392 (U - 128) - 0.813 (V - 128)
    B = 1.164 (Y - 16) + 2.017 (U - 128)

each rounded and clamped to 0..255; opacity 255. The VP8 module's `mw_vp8_rgba` has
the same arithmetic in C; `media-bench video` compares the two. The conversion runs
here, in Lean, and not in the interpreted module: in the interpreter it took about
6.3 million instructions for one 320x180 picture.
-/

namespace L4Factoidal.Media.Yuv

@[inline] def clamp8 (v : Int) : UInt8 :=
  if v < 0 then 0 else if v > 255 then 255 else v.toNat.toUInt8

/-- RGBA of a `w`×`h` picture in packed I420; empty when `yuv` is too short. -/
def toRgba (w h : Nat) (yuv : ByteArray) : ByteArray := Id.run do
  let cw := (w + 1) / 2
  let ch := (h + 1) / 2
  let uOff := w * h
  let vOff := uOff + cw * ch
  if yuv.size < vOff + cw * ch then return .empty
  let mut out := ByteArray.emptyWithCapacity (w * h * 4)
  for y in [0:h] do
    let row := y * w
    let crow := (y / 2) * cw
    for x in [0:w] do
      let c : Int := 76309 * ((yuv[row + x]!.toNat : Int) - 16)
      let d : Int := (yuv[uOff + crow + x / 2]!.toNat : Int) - 128
      let e : Int := (yuv[vOff + crow + x / 2]!.toNat : Int) - 128
      out := out.push (clamp8 ((c + 104597 * e + 32768) >>> 16))
      out := out.push (clamp8 ((c - 25674 * d - 53278 * e + 32768) >>> 16))
      out := out.push (clamp8 ((c + 132201 * d + 32768) >>> 16))
      out := out.push 255
  return out

end L4Factoidal.Media.Yuv
