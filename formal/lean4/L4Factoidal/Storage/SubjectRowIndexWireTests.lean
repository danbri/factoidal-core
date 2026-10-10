import L4Factoidal.Storage.SubjectRowIndexWire

namespace L4Factoidal.Storage.SubjectRowIndexWire

open L4Factoidal.Storage.IndexedBlock

private def rows : Array IdTriple :=
  #[{ s := 7, p := 2, o := 10 }, { s := 9, p := 2, o := 11 },
    { s := 7, p := 2, o := 12 }]

#guard pairsOfRows rows == [(7, 0), (7, 2), (9, 1)]
#guard (encode? rows).bind decode == some (3, [(7, 0), (7, 2), (9, 1)])
#guard (encode? rows).map (fun bytes => (decode bytes).map (fun value => offsetsFor value.2 7)) == some (some [0, 2])
#guard (encode? rows).map (fun bytes => (decode (bytes.extract 0 (bytes.size - 1))).isNone) == some true

private def framedPairs (rowCount : Nat) (pairs : List (Nat × Nat)) : ByteArray :=
  let encodePair := fun pair : Nat × Nat =>
    writeU32LE (UInt32.ofNat pair.1) ++ writeU32LE (UInt32.ofNat pair.2)
  let body := writeU32LE magic ++ [version] ++ writeU32LE (UInt32.ofNat rowCount) ++
    writeU32LE (UInt32.ofNat pairs.length) ++ pairs.flatMap encodePair
  ByteArray.mk ((body ++ writeU32LE (crc32c body)).toArray)

#guard (decode (framedPairs 1 [(7, 1)])).isNone
#guard (decode (framedPairs 2 [(7, 0), (9, 2)])).isNone
#guard (decode (framedPairs 2 [(7, 0), (9, 0)])).isNone

end L4Factoidal.Storage.SubjectRowIndexWire
