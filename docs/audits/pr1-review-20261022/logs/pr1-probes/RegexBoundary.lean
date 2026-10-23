import L4Factoidal.Regex.Profiles
import L4Factoidal.JSONSchema.Validate
open L4Factoidal
-- Record actual results, including controls. These guards characterize bugs;
-- they are not the acceptance criteria for a fixed implementation.
#guard (Regex.Profiles.matchWith .ecma2020 "^a" "" "a").toOption == some true
#guard (Regex.Profiles.matchWith .ecma2020 "^^a" "" "a").toOption == some false
#guard (Regex.Profiles.matchWith .ecma2020 "a$$" "" "a").toOption == some false
#guard JSONSchema.patternMatch "^^a" "a" == .fail
#eval Regex.Profiles.matchWith .ecma2020 "^^a" "" "a"
#eval JSONSchema.patternMatch "^^a" "a"
