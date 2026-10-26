import L4Factoidal.RIF.Saturate

open L4Factoidal L4Factoidal.RIF

private def p (arg : Tm) : Atom := .pos "urn:p" iriSpace [arg]
private def q (arg : Tm) : Atom := .pos "urn:q" iriSpace [arg]
private def one : Tm := .const "1" (xsdNs ++ "integer")
private def decimalOne : GTerm := gLit "1.0" (xsdNs ++ "decimal")
private def joinRule : Rule :=
  { head := q (.var "x"), vars := ["x"]
    body := some (.and [.atom (p (.var "x")), .atom (.equal (.var "x") one)]) }

-- Actual engine paths, beyond individual datatype helper calls.
#guard entails [joinRule] [.pos "urn:p" iriSpace [decimalOne]] (.atom (q one)) 4 == .holds
#guard (match entails [joinRule] [.pos "urn:p" iriSpace [gLit "bad" (xsdNs ++ "decimal")]]
  (.atom (q one)) 4 with | .undecided _ => true | _ => false)
#guard (Saturate.saturateGraph "review" [{ head := .equal one one }] []).blocked
#guard (Saturate.saturateGraph "review" [{ head := .equal one one }] []).completeGraph?.isNone
#guard (Saturate.saturateGraph "review" [] [] 0).completeGraph?.isNone

-- Failed RDF projection must not become a complete empty answer.
private def noProjection : Rule :=
  { head := .frame (.const "urn:s" iriSpace) (.const "urn:p" iriSpace)
      (.fapp "urn:f" iriSpace [one]) }
#guard (Saturate.saturateGraph "review" [noProjection] []).unsupportedOutput
#guard (Saturate.saturateGraph "review" [noProjection] []).completeGraph?.isNone
#eval IO.println "PR1_RIF_BOUNDARY_PROBES: 7 guards passed"
