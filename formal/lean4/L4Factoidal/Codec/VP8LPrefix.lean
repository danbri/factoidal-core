import L4Factoidal.Codec.Inflate

/-!
The lossless WebP prefix-code reader (RFC 9649 §3.7.2.1). It shares the
least-significant-first bit reader and canonical code walk with DEFLATE.
Every alphabet and traversal has a bound before table allocation.
-/

namespace L4Factoidal.Codec.VP8L

inductive Prefix (alphabet : Nat) where
  | single (symbol : Fin alphabet)
  | canonical (table : Huff)

def readSymbol {alphabet : Nat} : Prefix alphabet → BitM (Fin alphabet)
  | .single symbol => pure symbol
  | .canonical table => do
    let symbol ← decodeSym table
    if h : symbol < alphabet then return ⟨symbol, h⟩
    else throw "VP8L prefix symbol outside alphabet"

theorem readSingleton_noBits {alphabet : Nat} (symbol : Fin alphabet) (state : Bits) :
    (readSymbol (.single symbol)).run state = .ok (symbol, state) := rfl

private def fullCodeSpace (lengths : Array Nat) : Bool :=
  lengths.foldl (fun used length =>
    if length == 0 then used else used + 2 ^ (15 - length)) 0 == 2 ^ 15

private def makePrefix (alphabet : Nat) (lengths : Array Nat) :
    Except String (Prefix alphabet) := do
  if lengths.size != alphabet || lengths.any (· > 15) then throw "invalid VP8L code lengths"
  let mut count := 0
  let mut last := 0
  for index in [0:alphabet] do
    if lengths[index]! != 0 then
      count := count + 1
      last := index
  if count == 1 then
    if h : last < alphabet then
      if lengths[last]! == 1 then return .single ⟨last, h⟩
      else throw "VP8L singleton code length must be one"
    else throw "VP8L singleton outside alphabet"
  if fullCodeSpace lengths then return .canonical (buildHuff lengths)
  else throw "incomplete or oversubscribed VP8L prefix code"

private def codeLengthOrder : Array Nat :=
  #[17,18,0,1,2,3,4,5,16,6,7,8,9,10,11,12,13,14,15]

private def readNormal (alphabet : Nat) : BitM (Prefix alphabet) := do
  let count := 4 + (← readBits 4)
  let mut lengthsOfLengths := Array.replicate codeLengthOrder.size 0
  for index in [0:count] do
    lengthsOfLengths := lengthsOfLengths.set! codeLengthOrder[index]! (← readBits 3)
  let codeLengths ← ofExcept (makePrefix codeLengthOrder.size lengthsOfLengths)
  let tokenLimit ← if (← readBit) == 0 then pure alphabet else do
    let width := 2 + 2 * (← readBits 3)
    let limit := 2 + (← readBits width)
    if limit > alphabet then throw "VP8L code length token limit outside alphabet"
    pure limit
  let mut lengths := Array.replicate alphabet 0
  let mut pos := 0
  let mut previous := 8
  -- This limit counts encoded tokens. A single repeat can emit many lengths.
  for _ in [0:tokenLimit] do
    if pos == alphabet then break
    let symbol := (← readSymbol codeLengths).val
    let (length, runLength) ← match symbol with
      | 16 => pure (previous, 3 + (← readBits 2))
      | 17 => pure (0, 3 + (← readBits 3))
      | 18 => pure (0, 11 + (← readBits 7))
      | n => pure (n, 1)
    if pos + runLength > alphabet then throw "VP8L code length repeat outside alphabet"
    if length != 0 then
      previous := length
      for index in [pos:pos+runLength] do
        lengths := lengths.set! index length
    pos := pos + runLength
  ofExcept (makePrefix alphabet lengths)

/-- Read a complete canonical prefix code, including the zero-bit singleton.
    The largest permitted alphabet is green (24 length codes, 256 literals,
    and up to 2048 color-cache entries). -/
def readPrefix (alphabet : Nat) : BitM (Prefix alphabet) := do
  if alphabet == 0 || alphabet > 2328 then throw "invalid VP8L prefix alphabet size"
  if (← readBit) == 0 then return ← readNormal alphabet
  let pair := (← readBit) == 1
  let wideFirst := (← readBit) == 1
  let first ← readBits (if wideFirst then 8 else 1)
  if h : first < alphabet then
    if !pair then return .single ⟨first, h⟩
    let second ← readBits 8
    if second ≥ alphabet then throw "VP8L simple prefix symbol outside alphabet"
    -- RFC 9649 allows both entries to name the same leaf.
    if second == first then return .single ⟨first, h⟩
    let lengths := (Array.replicate alphabet 0).set! first 1 |>.set! second 1
    ofExcept (makePrefix alphabet lengths)
  else throw "VP8L simple prefix symbol outside alphabet"

/-- The five codes used for one entropy group, in their wire order. -/
structure Group (cacheSize : Nat) where
  green : Prefix (280 + cacheSize)
  red : Prefix 256
  blue : Prefix 256
  alpha : Prefix 256
  distance : Prefix 40

def readGroup (cacheSize : Nat) : BitM (Group cacheSize) := do
  let green ← readPrefix (280 + cacheSize)
  let red ← readPrefix 256
  let blue ← readPrefix 256
  let alpha ← readPrefix 256
  let distance ← readPrefix 40
  return {green, red, blue, alpha, distance}

#guard !(makePrefix 3 #[1, 1, 1]).isOk
#guard !(makePrefix 2 #[2, 2]).isOk
#guard !(makePrefix 19 (Array.replicate 19 0)).isOk
#guard (((do readSymbol (← readPrefix 40) : BitM (Fin 40)).run
    {data := ⟨#[0x1b, 0x00]⟩, pos := 0}).toOption.map (fun (symbol,s) => (symbol.val,s.pos))) == some (1,12)
#guard !((readPrefix 40).run {data := ⟨#[0xfd, 0x07]⟩, pos := 0}).isOk
#guard !((readPrefix 40).run {data := ByteArray.empty, pos := 0}).isOk

#print axioms readSingleton_noBits

end L4Factoidal.Codec.VP8L
