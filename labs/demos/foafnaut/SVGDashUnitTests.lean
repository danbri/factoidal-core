import SVGDashUnits
namespace NativeSVGDashUnitTests
open NativeSVGDash
private def flags (p : List Length) := (normalizeLengths p).toOption.map (List.map Length.percentage)
private def values (p : List Length) := (normalizeLengths p).toOption.map (List.map Length.value)
#guard flags [⟨1,false⟩,⟨2,true⟩,⟨3,false⟩] == some [false,true,false,false,true,false]
#guard values [⟨1,false⟩,⟨2,true⟩,⟨3,false⟩] == some [1,2,3,1,2,3]
#guard flags [⟨2,false⟩,⟨2,true⟩] == some [false,true]
#guard values [⟨0,false⟩,⟨0,true⟩] == some []
#guard !(normalizeLengths [⟨-1,true⟩]).isOk
#guard Length.calibrated ⟨3,true⟩ 5 == 3
#guard Length.calibrated ⟨3,false⟩ 5 == 15
end NativeSVGDashUnitTests
