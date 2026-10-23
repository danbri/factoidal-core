import L4Factoidal.Regex.Profiles
open L4Factoidal.Regex
private def oldMatch (pattern text : String) : Option Bool :=
  (XSDPattern.parseXsdPattern pattern).map (fun r => Exec.acceptsNorm r (cpsOfString text))
private def admission (pattern : String) : String × Bool × Bool :=
  (pattern, (XSDPattern.parseXsdPattern pattern).isSome,
    (Profiles.compileXsd10 pattern).isOk)
#eval admission "\\d\\d47"
#eval admission "\\c{3,6}://(\\c{1,6}\\.){1,3}\\c{3}"
#eval admission "\\i\\c*"
#eval admission "\\w+"
#eval oldMatch "\\d\\d47" "1247"
#eval oldMatch "\\d" "١"
#eval oldMatch "\\w" "_"
#eval oldMatch "\\i\\c*" "A:b_1"
#eval oldMatch "\\c{3,6}://(\\c{1,6}\\.){1,3}\\c{3}" "http://abc.org"
#guard oldMatch "\\d" "١" == some false
#guard oldMatch "\\w" "_" == some true
#guard oldMatch "\\i\\c*" "A:b_1" == some true
