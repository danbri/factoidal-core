/-
L4Factoidal.PageCanvas.Png: the PNG file of a canvas, for `toDataURL` and `toBlob`
(record: docs/designissues/2026-11-08-canvas-2d.md).

PNG (ISO/IEC 15948, W3C PNG 3rd edition): 8-bit RGBA, no interlace, filter 0 on every row,
the image data in a zlib stream (RFC 1950) of stored DEFLATE blocks (RFC 1951 §3.2.4,
`Codec.deflateStored`), each chunk with its CRC-32 (`Codec.crc32`). Stored blocks do not
compress; the file is correct, and `Tests.lean` decodes it back with `Codec.inflate`.
-/
import L4Factoidal.Codec.Crc32
import L4Factoidal.Codec.Inflate

namespace L4Factoidal.PageCanvas.Png
open L4Factoidal.Codec

def be32 (b : ByteArray) (v : Nat) : ByteArray :=
  (((b.push (v / 16777216 % 256).toUInt8).push (v / 65536 % 256).toUInt8).push (v / 256 % 256).toUInt8).push (v % 256).toUInt8

/-- Adler-32 of RFC 1950 §8. -/
def adler32 (b : ByteArray) : Nat := Id.run do
  let mut a := 1
  let mut s := 0
  for x in b do
    a := (a + x.toNat) % 65521
    s := (s + a) % 65521
  return s * 65536 + a

def chunk (kind : String) (data : ByteArray) : ByteArray :=
  let body := kind.toUTF8 ++ data
  be32 (be32 ByteArray.empty data.size ++ body) (crc32 body).toNat

/-- The PNG file of `w × h` pixels of straight (not premultiplied) RGBA. -/
def encode (w h : Nat) (rgba : ByteArray) : ByteArray := Id.run do
  let mut raw := ByteArray.emptyWithCapacity (h * (w * 4 + 1))
  for y in [0:h] do
    raw := raw.push 0
    raw := raw ++ rgba.extract (y * w * 4) ((y + 1) * w * 4)
  let zlib := (ByteArray.empty.push 0x78 |>.push 0x01) ++ deflateStored raw
  let zlib := be32 zlib (adler32 raw)
  let ihdr := ((((be32 (be32 ByteArray.empty w) h).push 8).push 6).push 0 |>.push 0).push 0
  let sig := ByteArray.mk #[137, 80, 78, 71, 13, 10, 26, 10]
  return sig ++ chunk "IHDR" ihdr ++ chunk "IDAT" zlib ++ chunk "IEND" ByteArray.empty

private def b64 (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n) else if n < 52 then Char.ofNat (71 + n)
  else if n < 62 then Char.ofNat (n - 4) else if n == 62 then '+' else '/'

/-- RFC 4648 §4 Base64 with padding. -/
def base64 (b : ByteArray) : String := Id.run do
  let mut out := ""
  let n := b.size
  let mut i := 0
  while i + 2 < n do
    let v := b[i]!.toNat * 65536 + b[i+1]!.toNat * 256 + b[i+2]!.toNat
    out := ((out.push (b64 (v / 262144))).push (b64 (v / 4096 % 64))).push (b64 (v / 64 % 64)) |>.push (b64 (v % 64))
    i := i + 3
  if n - i == 1 then
    let v := b[i]!.toNat * 65536
    out := out.push (b64 (v / 262144)) |>.push (b64 (v / 4096 % 64)) |>.push '=' |>.push '='
  else if n - i == 2 then
    let v := b[i]!.toNat * 65536 + b[i+1]!.toNat * 256
    out := out.push (b64 (v / 262144)) |>.push (b64 (v / 4096 % 64)) |>.push (b64 (v / 64 % 64)) |>.push '='
  return out

end L4Factoidal.PageCanvas.Png
