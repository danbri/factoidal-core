import L4Factoidal.SPARQL.StringOrder

namespace L4Factoidal.SPARQL.StringOrderTests

private def agrees (left right : String) : Bool :=
  strCompareFast left right == listCharCompare left.toList right.toList

#guard agrees "" ""
#guard agrees "" "a"
#guard agrees "a" ""
#guard agrees "same" "same"
#guard agrees "prefix" "prefix-longer"
#guard agrees "prefix-longer" "prefix"
#guard agrees "urn:scale:subject:00000000" "urn:scale:subject:00000001"
#guard agrees "Bób" "Bob"
#guard agrees "Ω" "é"
#guard agrees "漢" "😀"
#guard agrees "é" "é"
#guard agrees (String.ofList ['a', '\x00', 'b']) (String.ofList ['a', '\x00', 'c'])
#guard agrees (String.ofList ['\x00']) ""
#guard agrees (String.ofList [Char.ofNat 0xd7ff]) (String.ofList [Char.ofNat 0xe000])
#guard agrees (String.ofList [Char.ofNat 0xffff]) (String.ofList [Char.ofNat 0x10000])
#guard agrees (String.ofList [Char.ofNat 0x10fffe]) (String.ofList [Char.ofNat 0x10ffff])

private def specimens : List String :=
  ["", "a", "ab", "abc", "z", "é", "é", "Ω", "漢", "😀", "urn:example:long-prefix:a",
   "urn:example:long-prefix:b", String.ofList ['\x00'], String.ofList ['a', '\x00', 'b']] ++
  ([0x7f, 0x80, 0x7ff, 0x800, 0xd7ff, 0xe000, 0xffff, 0x10000, 0x10ffff].map
    (fun n => String.ofList [Char.ofNat n]))

#guard specimens.all (fun a => specimens.all (fun b => agrees a b))
#guard specimens.all (fun a => strCompareFast a a == 0)
#guard specimens.all (fun a => specimens.all (fun b =>
  strCompareFast a b == -(strCompareFast b a)))

end L4Factoidal.SPARQL.StringOrderTests
