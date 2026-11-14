import ImageData

/- Decoders against small files and hostile changes of them. The JPEG files come
   from libjpeg through Pillow: 16 by 16 pixels, left half (200,40,40), right half
   (40,40,200). -/
open NativeImage
open L4Factoidal

private def nibble (c : Char) : Nat := if c.isDigit then c.toNat-48 else c.toNat-87
private def hex (s : String) : ByteArray := Id.run do
  let chars := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [0:chars.size/2] do
    out := out.push (nibble chars[i*2]!*16+nibble chars[i*2+1]!).toUInt8
  return out
private def jpegBaseline := hex "ffd8ffe000104a46494600010100000100010000ffdb0043000302020302020303030304030304050805050404050a070706080c0a0c0c0b0a0b0b0d0e12100d0e110e0b0b1016101113141515150c0f171816141812141514ffdb00430103040405040509050509140d0b0d1414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414ffc00011080010001003011100021101031101ffc4001f0000010501010101010100000000000000000102030405060708090a0bffc400b5100002010303020403050504040000017d01020300041105122131410613516107227114328191a1082342b1c11552d1f02433627282090a161718191a25262728292a3435363738393a434445464748494a535455565758595a636465666768696a737475767778797a838485868788898a92939495969798999aa2a3a4a5a6a7a8a9aab2b3b4b5b6b7b8b9bac2c3c4c5c6c7c8c9cad2d3d4d5d6d7d8d9dae1e2e3e4e5e6e7e8e9eaf1f2f3f4f5f6f7f8f9faffc4001f0100030101010101010101010000000000000102030405060708090a0bffc400b51100020102040403040705040400010277000102031104052131061241510761711322328108144291a1b1c109233352f0156272d10a162434e125f11718191a262728292a35363738393a434445464748494a535455565758595a636465666768696a737475767778797a82838485868788898a92939495969798999aa2a3a4a5a6a7a8a9aab2b3b4b5b6b7b8b9bac2c3c4c5c6c7c8c9cad2d3d4d5d6d7d8d9dae2e3e4e5e6e7e8e9eaf2f3f4f5f6f7f8f9faffda000c03010002110311003f00f14afcdcfed53cbebfd1d3f81cf50aff00388fef83cbebfd1d3f81cfffd9"
private def jpegProgressive := hex "ffd8ffe000104a46494600010100000100010000ffdb0043000302020302020303030304030304050805050404050a070706080c0a0c0c0b0a0b0b0d0e12100d0e110e0b0b1016101113141515150c0f171816141812141514ffdb00430103040405040509050509140d0b0d1414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414141414ffc20011080010001003012200021101031101ffc40014000100000000000000000000000000000006ffc40014010100000000000000000000000000000006ffda000c03010002100310000001125d41746b3fffc40014100100000000000000000000000000000020ffda00080101000105021fffc40018110002030000000000000000000000000000064382c1ffda0008010301013f016a86d87fffc40018110002030000000000000000000000000000064382c2ffda0008010201013f014f9eba3fffc40014100100000000000000000000000000000020ffda0008010100063f021fffc40014100100000000000000000000000000000020ffda0008010100013f211fffda000c03010002000300000010ff00ffc40014110100000000000000000000000000000000ffda0008010301013f102fffc40014110100000000000000000000000000000000ffda0008010201013f1077ffc40014100100000000000000000000000000000020ffda0008010100013f101fffd9"
private def jpegGrey := hex "ffd8ffe000104a46494600010100000100010000ffdb0043000302020302020303030304030304050805050404050a070706080c0a0c0c0b0a0b0b0d0e12100d0e110e0b0b1016101113141515150c0f171816141812141514ffc0000b080010001001011100ffc4001f0000010501010101010100000000000000000102030405060708090a0bffc400b5100002010303020403050504040000017d01020300041105122131410613516107227114328191a1082342b1c11552d1f02433627282090a161718191a25262728292a3435363738393a434445464748494a535455565758595a636465666768696a737475767778797a838485868788898a92939495969798999aa2a3a4a5a6a7a8a9aab2b3b4b5b6b7b8b9bac2c3c4c5c6c7c8c9cad2d3d4d5d6d7d8d9dae1e2e3e4e5e6e7e8e9eaf1f2f3f4f5f6f7f8f9faffda0008010100003f00f14af2faf50af2faffd9"

private def be32 (n : Nat) : ByteArray :=
  ByteArray.empty |>.push (n/16777216).toUInt8 |>.push (n/65536%256).toUInt8 |>.push (n/256%256).toUInt8 |>.push (n%256).toUInt8
private def chunk (kind : String) (body : ByteArray) : ByteArray :=
  let tagged := kind.toUTF8 ++ body
  be32 body.size ++ tagged ++ be32 (Codec.crc32 tagged).toNat
private def signature : ByteArray := ByteArray.mk #[137,80,78,71,13,10,26,10]
private def ihdr (w h depth colour : Nat) (interlace : Nat := 0) : ByteArray :=
  chunk "IHDR" (be32 w ++ be32 h ++ ByteArray.mk #[depth.toUInt8,colour.toUInt8,0,0,interlace.toUInt8])
private def zlib (raw : ByteArray) : ByteArray :=
  ByteArray.mk #[0x78,1] ++ Codec.deflateStored raw ++ be32 (adler32 raw)
private def png (head : ByteArray) (raw : ByteArray) (extra : ByteArray := .empty) : ByteArray :=
  signature ++ head ++ extra ++ chunk "IDAT" (zlib raw) ++ chunk "IEND" .empty
/-- 2 by 1, RGB: red and green. -/
private def rgbRaw : ByteArray := ByteArray.mk #[0,255,0,0,0,255,0]
private def rgbPng := png (ihdr 2 1 8 2) rgbRaw

private def pixels (r : Except String Rendering.Bitmap) : List Nat :=
  match r with | .ok b => b.rgba.toList.map (·.toNat) | .error _ => []
private def refused (r : Except String Rendering.Bitmap) (text : String) : Bool :=
  match r with | .ok _ => false | .error m => (m.splitOn text).length > 1

#guard pixels (decodePNG rgbPng) == [255,0,0,255,0,255,0,255]
-- Each colour type. Palette with tRNS, grey with alpha, RGBA, 1-bit grey, 16-bit grey.
#guard pixels (decodePNG (png (ihdr 2 1 8 3) (ByteArray.mk #[0,1,0])
  (chunk "PLTE" (ByteArray.mk #[1,2,3,4,5,6]) ++ chunk "tRNS" (ByteArray.mk #[9])))) == [4,5,6,255,1,2,3,9]
#guard pixels (decodePNG (png (ihdr 1 1 8 4) (ByteArray.mk #[0,7,9]))) == [7,7,7,9]
#guard pixels (decodePNG (png (ihdr 1 1 8 6) (ByteArray.mk #[0,1,2,3,4]))) == [1,2,3,4]
#guard pixels (decodePNG (png (ihdr 2 1 1 0) (ByteArray.mk #[0,0x80]))) == [255,255,255,255,0,0,0,255]
#guard pixels (decodePNG (png (ihdr 1 1 16 0) (ByteArray.mk #[0,0xAB,0xCD]))) == [0xAB,0xAB,0xAB,255]
-- Colour key: tRNS of an RGB image names one colour.
#guard pixels (decodePNG (png (ihdr 1 1 8 2) (ByteArray.mk #[0,1,2,3])
  (chunk "tRNS" (ByteArray.mk #[0,1,0,2,0,3])))) == [1,2,3,0]
-- Filters: sub, up, average, Paeth.
#guard pixels (decodePNG (png (ihdr 2 1 8 0) (ByteArray.mk #[1,10,5]))) == [10,10,10,255,15,15,15,255]
#guard pixels (decodePNG (png (ihdr 1 2 8 0) (ByteArray.mk #[0,10,2,5]))) == [10,10,10,255,15,15,15,255]
#guard pixels (decodePNG (png (ihdr 2 1 8 0) (ByteArray.mk #[3,10,5]))) == [10,10,10,255,10,10,10,255]
#guard pixels (decodePNG (png (ihdr 1 2 8 0) (ByteArray.mk #[0,10,4,5]))) == [10,10,10,255,15,15,15,255]
-- Adam7: pass 1 gives pixel (0,0), pass 6 gives (1,0) of a 2 by 1 image.
#guard pixels (decodePNG (png (ihdr 2 1 8 0 1) (ByteArray.mk #[0,10,0,20]))) == [10,10,10,255,20,20,20,255]
-- A gamma of 1.0 lifts a middle grey: 128 is about 188 for a display exponent of 2.2.
#guard pixels (decodePNG (png (ihdr 1 1 8 0) (ByteArray.mk #[0,128]) (chunk "gAMA" (be32 100000)))) == [186,186,186,255]

-- Hostile PNG input. Each one is a refusal that names the fault.
#guard refused (decodePNG (rgbPng.set! 20 7)) "CRC"
#guard refused (decodePNG (rgbPng.extract 0 30)) "PNG"
#guard refused (decodePNG (signature ++ ihdr 100000 100000 8 6 ++ chunk "IEND" .empty)) "exceeds"
#guard refused (decodePNG (signature ++ ihdr 4294967295 4294967295 16 6 ++ chunk "IEND" .empty)) "exceeds"
#guard refused (decodePNG (signature ++ ihdr 0 1 8 6)) "no pixels"
#guard refused (decodePNG (signature ++ ihdr 1 1 3 2)) "bit depth"
#guard refused (decodePNG (signature ++ chunk "IEND" .empty)) "IHDR"
#guard refused (decodePNG (signature ++ ihdr 1 1 8 3 ++ chunk "IEND" .empty)) "palette"
#guard refused (decodePNG (signature ++ ihdr 1 1 8 0 ++ chunk "ABCD" .empty)) "critical"
#guard refused (decodePNG (png (ihdr 2 1 8 2) (ByteArray.mk #[5,255,0,0,0,255,0]))) "filter"
-- More data than the header allows stops at the size that the header gives.
#guard refused (decodePNG (png (ihdr 1 1 8 0) (ByteArray.mk #[0,1,2,3,4,5]))) "too large"
#guard refused (decodePNG (png (ihdr 2 2 8 2) rgbRaw)) "wrong size"
private def badAdler : ByteArray :=
  signature ++ ihdr 2 1 8 2 ++ chunk "IDAT" (ByteArray.mk #[0x78,1] ++ Codec.deflateStored rgbRaw ++ be32 1) ++ chunk "IEND" .empty
#guard refused (decodePNG badAdler) "Adler"
-- Inflate stops at its limit, for literals and for stored blocks.
#guard (Codec.inflateAt (Codec.deflateStored (ByteArray.mk #[1,2,3])) 0 2).toOption.isNone
#guard (Codec.inflateAt (Codec.deflateStored (ByteArray.mk #[1,2,3])) 0 3).toOption.isSome

-- JPEG: the mean of the left and right halves, to the tolerance of a lossy format.
private def close (r : Except String Rendering.Bitmap) (x y : Nat) (colour : List Nat) : Bool :=
  match r with
  | .error _ => false
  | .ok b => (List.range 3).all fun k =>
    let got := (b.rgba.get! ((y*b.width+x)*4+k)).toNat
    let want := colour[k]!
    (if got > want then got-want else want-got) <= 12
#guard close (decodeJPEG jpegBaseline) 2 8 [200,40,40]
#guard close (decodeJPEG jpegBaseline) 13 8 [40,40,200]
#guard close (decodeJPEG jpegProgressive) 2 8 [200,40,40]
#guard close (decodeJPEG jpegProgressive) 13 8 [40,40,200]
private def greyOf (r : Except String Rendering.Bitmap) (x : Nat) : Nat :=
  match r with | .ok b => (b.rgba.get! ((8*b.width+x)*4)).toNat | .error _ => 0
#guard greyOf (decodeJPEG jpegGrey) 2 > greyOf (decodeJPEG jpegGrey) 13

-- Hostile JPEG input.
private def sof (width height : Nat) (marker : UInt8 := 0xC0) : ByteArray :=
  ByteArray.mk #[0xFF,0xD8,0xFF,marker,0,17,8,(height/256).toUInt8,(height%256).toUInt8,(width/256).toUInt8,(width%256).toUInt8,
    3,1,0x11,0,2,0x11,0,3,0x11,0,0xFF,0xD9]
#guard refused (decodeJPEG (sof 65535 65535)) "exceeds"
#guard refused (decodeJPEG (sof 0 9)) "no pixels"
#guard refused (decodeJPEG (sof 8 8 0xC9)) "not supported"
#guard refused (decodeJPEG (sof 8 8)) "no scan"
-- Sampling factors pad a narrow, tall image. 1 by 65535 with 4 by 4 sampling is the
-- worst case within the pixel limit, and it is exactly the limit on coefficients.
private def padded : ByteArray :=
  ByteArray.mk #[0xFF,0xD8,0xFF,0xC0,0,17,8,0xFF,0xFF,0,1,3,1,0x44,0,2,0x44,0,3,0x44,0,0xFF,0xD9]
#guard refused (decodeJPEG padded) "no scan"
#guard refused (decodeJPEG (ByteArray.mk #[0xFF,0xD8,0xFF,0xDB,0xFF,0xFF])) "past the end"
#guard refused (decodeJPEG (ByteArray.mk #[0xFF,0xD8,0xFF,0xC4,0,3,0x77])) "past its segment"
-- A file cut anywhere gives a refusal or an image; it never reads outside the data.
private def everyCut (file : ByteArray) : Bool :=
  (List.range file.size).all fun n =>
    match decodeJPEG (file.extract 0 n) with
    | .ok b => b.rgba.size == b.width*b.height*4
    | .error _ => true
#guard everyCut jpegBaseline
#guard everyCut jpegProgressive
-- One byte changed anywhere, in a sample of positions.
private def everyChange (file : ByteArray) : Bool :=
  ((List.range (file.size/7)).map (·*7)).all fun n =>
    match decodeJPEG (file.set! n (file.get! n ^^^ 0x55)) with
    | .ok b => b.rgba.size == b.width*b.height*4
    | .error _ => true
#guard everyChange jpegBaseline
#guard everyChange jpegProgressive

-- Base64 and data URIs.
#guard (base64 "aGk=".toUTF8 0).toOption.map (·.toList) == some [104,105]
#guard (base64 "aG k=\n".toUTF8 0).toOption.map (·.toList) == some [104,105]
#guard (base64 "a!k=".toUTF8 0).toOption.isNone
#guard (base64 "aGk=aGk=".toUTF8 0).toOption.isNone
#guard (dataBytes "data:text/plain,hi").toOption.isNone
#guard (dataBytes "data:image/png;base64,aGk=").toOption.map (·.size) == some 2
#guard (decode "not an image".toUTF8).toOption.isNone
-- Images held reduced (2026-11-14): the size from the file's header, with no decoding.
#guard naturalSize rgbPng == some (2,1)
#guard naturalSize jpegBaseline == some (16,16)
#guard naturalSize jpegProgressive == some (16,16)
#guard naturalSize "not an image".toUTF8 == none
#guard naturalSize (jpegBaseline.extract 0 12) == none
#guard (decodeJPEG jpegBaseline).toOption.map (fun b => (b.width,b.height)) == naturalSize jpegBaseline
-- The factor of a document: 1 while its images fit the budget; the smallest that fits after.
#guard factorFor [(100,100),(200,50)] == 1
#guard factorFor [(1024,1024)] == 1
-- one pixel past the budget: the large image is halved, the small one keeps its size
#guard factorFor [(1024,1024),(10,10)] == 2
#guard heldPixels [(1024,1024),(10,10)] 2 == 512*512 + 100
#guard factorFor [(1024,1024),(1024,1024)] == 2
#guard factorFor [(1687,330),(1200,675),(840,779),(871,209),(821,204),(600,400),(600,400),(600,400)] == 2
#guard heldPixels [(1687,330),(1200,675),(840,779),(871,209),(821,204),(600,400),(600,400),(600,400)] 2 ≤ maxDocumentPixels
#guard factorFor (List.replicate 64 (2000,2000)) == 16
-- A small image keeps its size at every factor; a large one is divided, rounded up.
#guard reducedSize 64 64 8 == (64,64)
#guard reducedSize 1687 330 2 == (844,165)
#guard reducedSize 100 100 1 == (100,100)
-- `reduce`: the mean of each block; the bitmap itself at factor 1 and when it is small.
private def grey (w h : Nat) (v : Nat → UInt8) : L4Factoidal.Rendering.Bitmap :=
  {width := w, height := h, rgba := ByteArray.mk ((Array.range (w*h)).flatMap fun i => #[v i,v i,v i,255])}
#guard (reduce (grey 100 100 fun _ => 7) 1).rgba.size == 100*100*4
#guard (reduce (grey 8 8 fun _ => 7) 4).width == 8
#guard (reduce (grey 100 100 fun i => if i % 2 == 0 then 10 else 30) 2).width == 50
#guard (reduce (grey 100 100 fun i => if i % 2 == 0 then 10 else 30) 2).rgba.size == 50*50*4
#guard (reduce (grey 100 100 fun i => if i % 2 == 0 then 10 else 30) 2).rgba.toList.take 4 == [20,20,20,255]
#guard (reduce (grey 101 99 fun _ => 9) 2).width == 51 && (reduce (grey 101 99 fun _ => 9) 2).height == 50
#guard (reduce (grey 101 99 fun _ => 9) 2).rgba.toList.drop (51*50*4-4) == [9,9,9,255]
-- A store holds a reduced image under its key and the image's own size beside it.
#guard match Store.addBytes ({} : Store) 0 "a" jpegBaseline 1 with
  | (store,used) => used == 256 && store.natural "a" == none
#guard smallPixels ≥ 16*16
-- The budget of a document counts the images before this one.
#guard match Store.addBytes ({} : Store) (maxDocumentPixels-1) "a" rgbPng with
  | (store,used) => used == maxDocumentPixels-1 && (store.get? "a").any (·.toOption.isNone)
#guard match Store.addBytes ({} : Store) (maxDocumentPixels-2) "a" rgbPng with
  | (store,used) => used == maxDocumentPixels && (store.get? "a").any (·.toOption.isSome)
