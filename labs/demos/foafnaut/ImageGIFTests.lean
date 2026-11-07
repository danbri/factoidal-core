import ImageData

/- The GIF decoder against small files. `still`, `anim` and `big` come from FFmpeg
   (palettegen and paletteuse with no dithering, so the colours are exact): `still` is
   4 by 2 with eight colours; `anim` is two frames of 500 ms, the second a 2 by 2
   rectangle with a transparent index (FFmpeg's frame optimisation); `big` is the first
   frame of FFmpeg's `testsrc` at 64 by 48, with LZW codes of more than 8 bits, checked
   against FFmpeg's own decoding by CRC-32. `inter` is 1 by 10, interlaced, made with a
   literal-code LZW writer; FFmpeg decodes it to the grey levels 0, 16, ..., 144. -/
open NativeImage
open L4Factoidal

private def nibble (c : Char) : Nat := if c.isDigit then c.toNat-48 else c.toNat-87
private def hex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:chars.size/2] do
    out := out.push (nibble chars[i*2]!*16+nibble chars[i*2+1]!).toUInt8
  return out
private def still := hex "47494638396104000200f71f000000000000ff00ff0000ffffff0000ff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff21ff0b4e45545343415045322e30030100000021f9040404001f002c000000000400020000080c000908087000808101050202003b"
private def anim := hex "47494638396104000200f71f000000000000ff00ff0000ffffff0000ff00ffffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff21ff0b4e45545343415045322e30030100000021f9040432001f002c000000000400020000080c0009080870008081010502020021f90405320001002c000000000200020000080700010408702020003b"
private def big := hex "47494638396140003000f71f310000000000ff0006ff000fff0017ff001fff0027ff002fff0037ff003fff0047ff004fff0057ff005fff0067ff006fff0077ff007fff0087ff008fff0097ff009fff00a7ff00afff00b7ff00bfff00c7ff00cfff00d7ff00dfff00e7ff00efff00f7ff00ff0000ff0700ff1000ff1800ff2000ff2800ff3000ff3800ff4000ff4800ff5000ff5800ff7000ff7800ff8000ff8800ff9800ffa000ffa800ffb000ffb800ffc000ffc800ffd000ffd800ffe000fff000fff800ffff01ff6001ff6801ff9001ffe806ff000800ff0fff001000ff17ff001800ff1fff002000ff27ff002800ff2fff003000ff37ff003800ff3fff004000ff47ff004800ff4fff005000ff57ff005800ff5fff006000ff67ff006800ff6fff007000ff77ff007800ff7fff008000ff87ff008800ff8fff009000ff97ff009800ff9fff00a000ffa7ff00a800ffafff00b000ffb7ff00b800ffbfff00c000ffc7ff00c800ffcfff00d000ffd7ff00d800ffdfff00e000ffe7ff00e800ffefff00f000fff7ff00f800ffff0000ff0007ff000fff0017ff001fff0027ff002fff0037ff003fff0047ff004fff0057ff005fff0067ff006fff0077ff007fff0087ff008fff0097ff009fff00a7ff00afff00b7ff00bfff00c7ff00cfff00d7ff00dfff00e7ff00efff00f7ff00ffff0800ff1000ff1800ff2000ff2800ff3000ff3800ff4000ff4800ff5000ff5800ff6000ff6800ff7000ff7800ff8000ff8800ff9000ff9800ffa000ffa800ffb000ffb800ffc000ffc800ffd000ffd800ffe000ffe800fff000fff800ffff00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff21ff0b4e45545343415045322e30030100000021f9040464001f002c00000000400030000008ff0001081c281090c18306438400c5b0618087101f029b4871a2c28b0a41f5d8c87163b08f203f12248810e1c2860e2342ac581123c68e1d43861c39b0a4c11e2851aa5cc9d2a24b853761ca0449b360c98d3953eeece9f3e741a14383150570146952503b2532fd09f429c7a8528b22ec78156b56a6c0b886a8da03ec54af1ccb660d8056ad4d8f51df028289f3eadcba5c6dee752b762f4cb967b706be4b98a6e1c37e13f7b42bb8f148be5693fe55ec543080bc4531f7d52c9925659b9f87160d261af152ce2e050312a89a266bccae5502ee8c3af5cc911f5b477e3d79716fdf2281dfe69b3be2eed89e69ff26181cf770ddb031ca1e2853f972c8a4899bff365e923a51f3dfc95e779efde276eee7e1a78fbb9e6771dee5e587952f3c3cf6fbd01d879c77fde5b41980da45275d72fc59e71f7b08baa7e080e815a853692d9187107afb2d68a152ff8d87df86fa11e8a0811852745a7e0b76e8db870c1d2862802c52d82073f569156157024ee7e189178a97e188077168228e0fda3763823dc6f72392280aa9a28645965821902042b8a4844d32081f8c6649d9148d2422e7626a60ca382499559a69db7c994519e29a4cb2d89d6d69a638669d240e05c828a6a4c2ca2bb2d482cb2ebef881871c6c980186165438818410239890020b2dc020430d3804d183071b605081040f30908001030c91c413556c11c6196dccfe91c71f9e6c824925923cc24822860cf267a083167a68a28b36fa68a493567a69a69b76fa69a8a3967a6aaaabb6fa6aacb3d67a6baebbf6faaba0841a8aa8a28c3a0aa9a4945a8aa9a69c7a0aaaa8a49a8aaaaaacba0aabacb4da8aabaebcfa0a28b8c28e5bacb9c8a6bb2cbbcebe1badbcd4d67b2dbedaeedbadbfc0863b2cb9c69e9bacbaccb6fb2cbcd2ce5badbdd8e6bb2dbfdefe1bacb8c4967b2cbacaaedbacbbd0c63b2dbdd6de9badbedcf6fbedca170ffcf2c607cffcf1c2378ffcf0ce274fac5750710639e794237e059a6363459da5927472f9585b578f74d768726ad9358f50d586f551cd714d35747c594692602795edf69e178906564000003b"
private def inter := hex "47494638396101000a00830000000000101010202020303030404040505050606060707070808080909090a0a0a0b0b0b0c0c0c0d0d0d0e0e0e0f0f0f02c0000000001000a004004081020224c18e5a408003b"

private def pixels (r : Except String Rendering.Bitmap) : List Nat :=
  match r with | .ok b => b.rgba.toList.map (·.toNat) | .error _ => []
private def refused (r : Except String Rendering.Bitmap) (text : String) : Bool :=
  match r with | .ok _ => false | .error m => (m.splitOn text).length > 1
private def solid (colours : List (Nat × Nat × Nat)) : List Nat := colours.flatMap fun (r,g,b) => [r,g,b,255]

#guard pixels (decodeGIF still) == solid [(255,0,0),(0,255,0),(0,0,255),(255,255,255),(0,0,0),(255,255,0),(0,255,255),(255,0,255)]
#guard pixels (decode still) == pixels (decodeGIF still)
-- Two frames, 500 ms each; the second draws two pixels over the first.
#guard match decodeGIFFrames anim with
  | .ok frames => frames.size == 2 && frames.toList.map (·.delayMs) == [500,500] &&
      (frames[1]?.map (pixels <| .ok ·.bitmap)) == some ( solid [(0,0,0),(0,255,0),(0,0,255),(255,255,255),(0,0,0),(255,255,255),(0,255,255),(255,0,255)])
  | .error _ => false
#guard pixels (decodeGIF anim) == pixels (decodeGIF still)
#guard match decodeGIF big with
  | .ok b => b.width == 64 && b.height == 48 && (Codec.crc32 b.rgba).toNat == 3279847762
  | .error _ => false
#guard pixels (decodeGIF inter) == solid ((List.range 10).map fun i => (i*16,i*16,i*16))
#guard interlacedRow 10 0 == 0 && interlacedRow 10 1 == 8 && interlacedRow 10 2 == 4 && interlacedRow 10 3 == 2 && interlacedRow 10 9 == 9
-- Hostile changes: a cut file, no image, a screen past the limit, an unknown block.
#guard refused (decodeGIF (still.extract 0 (still.size-8))) "past the end"
-- A file cut before its trailer shows the frames it has, as in the common browsers.
#guard match decodeGIFFrames (still.extract 0 (still.size-1)) with | .ok frames => frames.size == 1 | .error _ => false
#guard refused (decodeGIF ((still.extract 0 6) ++ ByteArray.mk #[0xff,0xff,0xff,0xff,0,0,0,0x3b])) "exceeds"
private def bare : ByteArray := (still.extract 0 6) ++ ByteArray.mk #[4,0,2,0,0,0,0]
#guard refused (decodeGIF (bare ++ ByteArray.mk #[0x3b])) "no image"
#guard refused (decodeGIF (bare ++ ByteArray.mk #[0x99])) "not an extension"
#guard refused (decodeGIF bare) "no image"
#guard refused (decodeGIF (ByteArray.mk #[71,73,70,56,55])) "truncated"
-- A code past the table is a refusal, not a read out of bounds.
#guard match lzwDecode (ByteArray.mk #[0xff,0xff]) 2 4 with | .error _ => true | .ok _ => false
-- The LZW data may give fewer indices than the image: the rest stays empty.
#guard match lzwDecode (ByteArray.mk #[0x44,0x01]) 2 4 with | .ok out => out.size == 4 | .error _ => false
