import L4Factoidal.JSON.Serialize

namespace L4Factoidal.JSON.EscapeTests

private def agrees (text : String) : Bool :=
  escapeStringFast text == (text.toList.map escapeChar).foldl (· ++ ·) ""

#guard agrees ""
#guard agrees "ordinary ASCII and urn:subject:00000001"
#guard agrees "quotation \" and backslash \\"
#guard agrees (String.ofList ['\n', '\r', '\t', Char.ofNat 8])
#guard agrees "Bób é é Ω 漢 😀"
#guard agrees (String.ofList ['a', '\x00', 'b'])
#guard agrees (String.ofList (List.range 32 |>.map Char.ofNat))
#guard (List.range 32).all (fun n => agrees (String.ofList [Char.ofNat n]))
#guard agrees (String.ofList ['\x00', '"', '\\', 'é', '\n', '😀'])
#guard agrees (String.ofList [Char.ofNat 0xd7ff, Char.ofNat 0xe000,
  Char.ofNat 0xffff, Char.ofNat 0x10000, Char.ofNat 0x10ffff])
#guard escapeStringFast (String.ofList ['\x00', '\x01', '\x1f']) == "\\u0000\\u0001\\u001f"
#guard escapeStringFast "\"\\\n\r\t" == "\\\"\\\\\\n\\r\\t"
#guard agrees (String.ofList (List.replicate 1000 'a'))
#guard agrees (String.ofList (List.replicate 100 '"'))

end L4Factoidal.JSON.EscapeTests
