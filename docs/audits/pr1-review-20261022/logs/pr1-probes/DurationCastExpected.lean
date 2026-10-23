import L4Factoidal.RIF.Builtins
open L4Factoidal.RIF
-- Expected to FAIL at reviewed head: acceptance criterion for repair.
#guard evalFunc "cast-string" [gLit "P0M" (xsdNs ++ "yearMonthDuration")] == some (gStr "P0M")
#guard evalFunc "cast-string" [gLit "P0Y" (xsdNs ++ "yearMonthDuration")] == some (gStr "P0M")
#guard evalFunc "cast-string" [gLit "PT0S" (xsdNs ++ "dayTimeDuration")] == some (gStr "PT0S")
#guard evalFunc "cast-string" [gLit "P0M" (xsdNs ++ "duration")] == some (gStr "PT0S")
