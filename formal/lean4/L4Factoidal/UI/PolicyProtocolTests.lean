import L4Factoidal.UI.PolicyProtocol

namespace L4Factoidal.UI.PolicyProtocol.Tests
open L4Factoidal.JSON
private def n (x : Int) : Json := .number (toString x)
private def app (lo hi a b : Int) : Json := .object
  [("minOverlapBps",n lo),("maxOverlapBps",n hi),("minCheckHz",n a),("maxCheckHz",n b)]
private def cfg (bps hz : Int) : Json := .object [("overlapBps",n bps),("checkHz",n hz)]
private def fields (a c : Json) : List (String × Json) :=
  [("op",.string "configure"),("application",a),("configuration",c)]
private def normal : List (String × Json) := fields (app 300 500 12 16) (cfg 500 12)
private def wire (fs : List (String × Json)) : String := toStringCompact (.object fs)
private def response (text : String) : Json := (parseJson? (request text)).getD .null
private def ok (text : String) : Bool := (response text).getBool? "ok" == some true
private def checkWire (viewport : Json) (footprints : List Json) : String := wire
  [("op",.string "check"),("application",app 300 500 12 16),("configuration",cfg 500 12),
   ("viewport",viewport),("footprints",.array footprints)]
private def box (l t r b : Int) : Json := .array [n l,n t,n r,n b]
private def view : Json := box 0 0 10 10
private def reports (text : String) : List Json := ((response text).getArray? "reports").getD []
#guard ok "{\"op\":\"defaults\"}"
#guard !ok "{\"op\":\"defaults\",\"ignored\":true}"
#guard (readConfig (configJson LayoutPolicy.defaultConfig)).toOption == some LayoutPolicy.defaultConfig
#guard (readConfigText (toStringCompact (configJson LayoutPolicy.defaultConfig))).toOption == some LayoutPolicy.defaultConfig
#guard !(readConfigText "[[[[[[[[[]]]]]]]]]").isOk
#guard !(readConfigText (String.ofList (List.replicate 32769 ' '))).isOk
#guard ok (wire normal)
#guard (response (wire normal)).getString? "protocol" == some protocol
#guard (response (wire normal)).field? "targetIntervalMs" == some (n 84)
#guard ok (wire (fields (app 300 700 12 24) (cfg 700 24)))
#guard !ok (wire (fields (app 300 500 12 16) (cfg 700 12)))
#guard !ok (wire (fields (app 300 500 12 16) (cfg 500 24)))
#guard !ok (wire (fields (app 500 300 12 16) (cfg 500 12)))
#guard !ok (wire (fields (app 300 701 12 16) (cfg 500 12)))
#guard !ok (wire (fields (app 300 500 0 16) (cfg 500 12)))
#guard !ok (wire (fields (app 300 500 12 16) (cfg 0 12)))
#guard !ok (wire (fields (app 300 500 12 16) (cfg 500 120)))
#guard !ok (wire (("allowOverlap",.bool true)::normal))
#guard !ok (wire (("op",.string "configure")::normal))
#guard !ok (wire (normal.drop 1))
#guard !ok "{\"op\":\"unknown\"}"
#guard !ok (wire (fields (.object [("minOverlapBps",n 300)]) (cfg 500 12)))
#guard !ok (wire (fields (app 300 500 12 16) (.object [("overlapBps",.number "500.0"),("checkHz",n 12)])))
#guard !ok (wire (fields (app 300 500 12 16) (.object [("overlapBps",.string "500"),("checkHz",n 12)])))
#guard !ok (wire (fields (app 300 500 12 16) (.object [("overlapBps",n 500),("checkHz",n 12),("checkHz",n 16)])))
#guard !ok (wire (fields (.object [("minOverlapBps",n 300),("maxOverlapBps",n 500),
  ("minCheckHz",n 12),("minCheckHz",n 16)]) (cfg 500 12)))
#guard !ok (wire (fields (app 300 500 12 16) (.object [("overlapBps",n 500),("allowWeakening",.bool true)])))
#guard (response (wire (fields (app 300 700 12 24) (cfg 700 24)))).field? "targetIntervalMs" == some (n 42)
#guard ok (checkWire view [box 8 0 20 10])
#guard ((reports (checkWire view [box 8 0 20 10])).head?.bind (·.field? "area")) == some (n 20)
#guard ((reports (checkWire view [box 8 0 20 10])).head?.bind (·.field? "footprint")) == some (box 8 0 10 10)
#guard (response (checkWire view [box 8 0 20 10])).getBool? "accepted" == some true
#guard (response (checkWire view [box 20 20 30 30])).getBool? "accepted" == some false
#guard (response (checkWire view [.null])).getBool? "accepted" == some false
#guard (response (checkWire view [box 0 0 10 10,box 0 0 10 10])).getBool? "accepted" == some false
#guard (response (checkWire view [])).getBool? "accepted" == some true
#guard !ok (checkWire (box 0 0 0 10) [])
#guard !ok (checkWire view [box 10 0 0 10])
#guard !ok (checkWire view [box 0 0 1000001 10])
#guard !ok (checkWire view [box (-1000001) 0 0 10])
#guard ok (checkWire view [box (-1000000) 0 1000000 10])
#guard ok (checkWire view (List.replicate 256 .null))
#guard !ok (checkWire view (List.replicate 257 .null))
#guard !ok (String.ofList (List.replicate 32769 ' '))
#guard !ok "[[[[[[[[[]]]]]]]]]"
#guard !ok "{"
#guard !ok (wire normal ++ "false")
end L4Factoidal.UI.PolicyProtocol.Tests
