import L4Factoidal.Rendering.FontRequests
namespace L4Factoidal.Rendering.FontRequestsTests
open FontRequests
private def run (html : String) (css : String := "") : Except String (Array Request) := do
  let dom := DOM.parseHtmlDocument html
  forDOM dom (← CSS.parse ("body{font-family:Ahem;font-size:20px}" ++ css))
private def keys (result : Except String (Array Request)) := result.toOption.map fun requests =>
  requests.toList.map fun r => (r.family,r.pixelSize,r.text)
#guard keys (run "<div>AA BB AA</div>") == some [("Ahem",20," "),("Ahem",20,"AA"),("Ahem",20,"BB")]
#guard keys (run "<div>AA\t\n  BB</div>") == keys (run "<div>AA BB</div>")
#guard keys (run "<div>AA &amp; BB</div>") == some [("Ahem",20," "),("Ahem",20,"&"),("Ahem",20,"AA"),("Ahem",20,"BB")]
#guard keys (run "<div style='display:none'><span style='display:block'>MISSING</span></div><div>AA</div>") == keys (run "<div>AA</div>")
#guard keys (run "<div style='visibility:hidden'>AA</div>") == keys (run "<div>AA</div>")
#guard keys (run "<head><style>ignored-css</style><script>NO</script></head><div>AA</div>") == keys (run "<div>AA</div>")
#guard keys (run "<svg width='10' height='10'><text>SVGWORD</text></svg>") == some [("Ahem",20," ")]
#guard keys (run "<svg style='display:block' width='10' height='10'><text>SVGWORD</text></svg>") == some []
#guard keys (run " \n\t ") == some []
#guard keys (run "<div><br></div>") == some [("Ahem",20," ")]
#guard keys (run "<span style='font-size:10px'>AA</span>") == some [("Ahem",10,"AA"),("Ahem",20," ")]
#guard (run "<div>AA</div>" "body{font-size:20.5px}").toOption.isNone
#guard (run "<div>AA</div>" "body{font-size:513px}").toOption.isNone
#guard (run ("<div>" ++ String.ofList (List.replicate 65537 'A') ++ "</div>")).toOption.isNone
#guard (run ("<div>" ++ String.intercalate " " ((List.range 4096).map fun n => "W" ++ toString n) ++ "</div>")).toOption.isNone
#guard (run "<div>AA</div>" ("body{font-family:'" ++ String.ofList (List.replicate 257 'A') ++ "'}")).toOption.isNone
end L4Factoidal.Rendering.FontRequestsTests
