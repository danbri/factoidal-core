import L4Factoidal.Codec.VP8LPrefix

/-!
An entropy-coded VP8L ARGB plane (RFC 9649 §§3.6, 3.7). Literal, backward
reference and color-cache tokens share one bounded writer. The optional
spatial group image is itself a flat plane, so decoding it does not recurse.
-/
namespace L4Factoidal.Codec.VP8L

structure Plane (size : Nat) where
  pixels : Array UInt32
  exactSize : pixels.size = size

private def color (alpha red green blue : Nat) : UInt32 :=
  UInt32.ofNat (alpha * 16777216 + red * 65536 + green * 256 + blue)

private def prefixValue (symbol : Nat) : BitM Nat := do
  if symbol < 4 then return symbol + 1
  let extra := (symbol - 2) / 2
  return (2 + symbol % 2) * 2 ^ extra + (← readBits extra) + 1

/-- RFC 9649 figure 20, the (column distance, row distance) pairs.
    Indices beyond the table instead denote a linear scan-line distance. -/
private def nearby : Array (Int × Nat) := #[
  (0,1),(1,0),(1,1),(-1,1),(0,2),(2,0),(1,2),(-1,2),(2,1),(-2,1),
  (2,2),(-2,2),(0,3),(3,0),(1,3),(-1,3),(3,1),(-3,1),(2,3),(-2,3),
  (3,2),(-3,2),(0,4),(4,0),(1,4),(-1,4),(4,1),(-4,1),(3,3),(-3,3),
  (2,4),(-2,4),(4,2),(-4,2),(0,5),(3,4),(-3,4),(4,3),(-4,3),(5,0),
  (1,5),(-1,5),(5,1),(-5,1),(2,5),(-2,5),(5,2),(-5,2),(4,4),(-4,4),
  (3,5),(-3,5),(5,3),(-5,3),(0,6),(6,0),(1,6),(-1,6),(6,1),(-6,1),
  (2,6),(-2,6),(6,2),(-6,2),(4,5),(-4,5),(5,4),(-5,4),(3,6),(-3,6),
  (6,3),(-6,3),(0,7),(7,0),(1,7),(-1,7),(5,5),(-5,5),(7,1),(-7,1),
  (4,6),(-4,6),(6,4),(-6,4),(2,7),(-2,7),(7,2),(-7,2),(3,7),(-3,7),
  (7,3),(-7,3),(5,6),(-5,6),(6,5),(-6,5),(8,0),(4,7),(-4,7),(7,4),
  (-7,4),(8,1),(8,2),(6,6),(-6,6),(8,3),(5,7),(-5,7),(7,5),(-7,5),
  (8,4),(6,7),(-6,7),(7,6),(-7,6),(8,5),(7,7),(-7,7),(8,6),(8,7)
]

def scanDistance (width code : Nat) : Nat :=
  if code > 120 then code - 120
  else
    let delta := nearby[code-1]?.getD (1,0)
    max 1 (delta.1 + Int.ofNat (delta.2*width)).toNat

theorem scanDistance_positive (width code : Nat) : 0 < scanDistance width code := by
  unfold scanDistance
  split
  · omega
  · exact Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left _ _)

private def cacheSize (bits : Nat) : Nat := if bits == 0 then 0 else 2 ^ bits

private def readCacheBits : BitM Nat := do
  if (← readBit) == 0 then return 0
  let bits ← readBits 4
  if bits < 1 || bits > 11 then throw "invalid VP8L color cache size"
  return bits

private def cacheInsert (bits : Nat) (pixel : UInt32) (cache : Array UInt32) : Array UInt32 :=
  if bits == 0 then cache
  else
    let slot := ((0x1e35a7bd * pixel) >>> UInt32.ofNat (32-bits)).toNat
    cache.set! slot pixel

private def decodePixels (width size bits : Nat)
    (choose : Nat → Option (Group (cacheSize bits))) : BitM (Plane size) := do
  let mut pixels : Array UInt32 := Array.emptyWithCapacity size
  let mut cache : Array UInt32 := Array.replicate (cacheSize bits) 0
  for _ in [:size] do
    if pixels.size == size then break
    let some group := choose pixels.size | throw "missing VP8L entropy group"
    let green := (← readSymbol group.green).val
    if green < 256 then
      let red := (← readSymbol group.red).val
      let blue := (← readSymbol group.blue).val
      let alpha := (← readSymbol group.alpha).val
      let pixel := color alpha red green blue
      pixels := pixels.push pixel
      cache := cacheInsert bits pixel cache
    else if green < 280 then
      let count ← prefixValue (green-256)
      let distance := scanDistance width (← prefixValue (← readSymbol group.distance).val)
      if distance > pixels.size || pixels.size + count > size then
        throw "VP8L backward reference outside plane"
      -- Reading from the growing output permits overlapping runs.
      for _ in [:count] do
        let some pixel := pixels[pixels.size-distance]? | throw "invalid VP8L backward reference"
        pixels := pixels.push pixel
        cache := cacheInsert bits pixel cache
    else
      let some pixel := cache[green-280]? | throw "VP8L cache token outside color cache"
      pixels := pixels.push pixel
      cache := cacheInsert bits pixel cache
  if h : pixels.size = size then return ⟨pixels, h⟩
  else throw "incomplete VP8L plane"

private def readFlat (width height : Nat) : BitM (Plane (width*height)) := do
  let bits ← readCacheBits
  let group ← readGroup (cacheSize bits)
  decodePixels width (width*height) bits (fun _ => some group)

/-- Read one bounded plane. Only the main image can signal a spatial group map;
    predictor, color transform, palette and entropy images use the flat form. -/
def readPlane (width height : Nat) (spatial : Bool) (maxPixels : Nat := 4194304) :
    BitM (Plane (width*height)) := do
  if width == 0 || height == 0 || width*height > maxPixels then throw "invalid or oversized VP8L plane"
  if !spatial then return ← readFlat width height
  let bits ← readCacheBits
  if (← readBit) == 0 then
    let group ← readGroup (cacheSize bits)
    return ← decodePixels width (width*height) bits (fun _ => some group)
  let tile := 2 ^ (2 + (← readBits 3))
  let tilesX := (width + tile - 1) / tile
  let tilesY := (height + tile - 1) / tile
  let image ← readFlat tilesX tilesY
  let groupIds := image.pixels.map (fun (pixel : UInt32) => ((pixel / 256) % 65536).toNat)
  let highest := groupIds.foldl max 0
  let mut used := Array.replicate (highest+1) false
  for id in groupIds do used := used.set! id true
  let mut groups : Array (Option (Group (cacheSize bits))) := Array.emptyWithCapacity (highest+1)
  for id in [:highest+1] do
    let group ← readGroup (cacheSize bits)
    groups := groups.push (if used[id]! then some group else none)
  decodePixels width (width*height) bits fun pos =>
    let tileIndex := (pos / width / tile) * tilesX + ((pos % width) / tile)
    groupIds[tileIndex]?.bind (fun id => (groups[id]?).getD none)

#guard nearby.size == 120
#guard scanDistance 10 1 == 10
#guard scanDistance 10 2 == 1
#guard scanDistance 10 121 == 1

#print axioms scanDistance_positive

end L4Factoidal.Codec.VP8L
