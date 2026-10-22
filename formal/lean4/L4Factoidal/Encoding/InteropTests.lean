/- Authored interoperability guards for the shared hex primitive. -/
import L4Factoidal.Encoding.Hex
import L4Factoidal.JSON.Parser
import L4Factoidal.Syntax.Lexing
import L4Factoidal.ShEx.Compact
import L4Factoidal.HTTP.Server
import L4Factoidal.XSD.Datatypes
import L4Factoidal.VC.Multibase

namespace L4Factoidal.Encoding.InteropTests

-- Independent alphabet oracle, including invalid ASCII and non-ASCII inputs.
private def alphabet := "0123456789abcdef".toList.zip (List.range 16) ++
  "ABCDEF".toList.zip (List.range 6 |>.map (· + 10))
#guard ((List.range 256).map Char.ofNat ++ ['Ａ', '９', 'é', '😀']).all fun c =>
  Hex.digitValue c == (alphabet.find? (fun p => p.1 == c)).map Prod.snd

-- These equations assert delegation for every input, not only the test alphabet.
theorem json_shared (c : Char) : JSON.hexVal c = Hex.digitValue c := rfl
theorem xsd_shared (c : Char) : XSD.hexVal? c = Hex.digitValue c := rfl
theorem vc_shared (c : Char) : VC.Multibase.hexDigitVal? c = Hex.digitValue c := rfl
theorem syntax_shared (c : Char) : Syntax.hexVal c = Hex.digitValue c := rfl
theorem shexc_shared (c : Char) : ShEx.Compact.hexVal c = Hex.digitValue c := rfl

-- Consumer-specific byte representation and canonical case remain independent.
#guard XSD.parseHexBinaryLex "00aF" == some [0, 175]
#guard VC.Multibase.bytesOfHex? "00aF" == some [0, 175]
#guard XSD.parseHexBinaryLex "f" == none
#guard VC.Multibase.bytesOfHex? "f" == none
#guard XSD.hexOfBytes [0, 175] == "00AF"
#guard VC.Multibase.hexOfBytes [0, 175] == "00af"

#print axioms json_shared
#print axioms vc_shared
end L4Factoidal.Encoding.InteropTests
