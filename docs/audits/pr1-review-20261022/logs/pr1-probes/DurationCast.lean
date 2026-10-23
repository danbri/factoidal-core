import L4Factoidal.RIF.Builtins
open L4Factoidal.RIF
#eval castXsd "string" (gLit "P0M" (xsdNs ++ "yearMonthDuration"))
#eval castXsd "string" (gLit "P0Y" (xsdNs ++ "yearMonthDuration"))
#eval castXsd "string" (gLit "PT0S" (xsdNs ++ "dayTimeDuration"))
#eval castXsd "string" (gLit "P0M" (xsdNs ++ "duration"))
