import WebDocument

/-! Pointer targets inside inline SVG (WebHit) and fractional embedded SVG viewports. -/
open L4Factoidal

private def answer (html : String) (x y : Nat) : Option JSON.Json :=
  match WebDocument.runUncached html (.object [("op",.string "nodeAt"),("x",.number (toString x)),
      ("y",.number (toString y))]) 400 300 with
  | .ok text => (JSON.parseJsonText text).toOption.map (·.1)
  | .error _ => none

/-- The target's local name, and its `id` when it has one. -/
private def target (html : String) (x y : Nat) : String := Id.run do
  let some j := answer html x y | return "error"
  let some (.number n) := j.field? "node" | return "none"
  let some id := n.toNat? | return "none"
  let n := (DOM.parseHtmlDocument html).get id
  let ident := Rendering.CSS.attrValue n "id"
  return if ident.isEmpty then n.lname else n.lname ++ "#" ++ ident

private def page (svg : String) : String :=
  "<!doctype html><html><body style=\"margin:0\">" ++ svg ++ "</body></html>"

-- The repro: a tap on the circle targets the circle, not the svg; outside it, the svg.
private def circle := page "<svg width=\"100\" height=\"100\"><circle id=\"c\" cx=\"50\" cy=\"50\" r=\"40\"/></svg>"
#guard target circle 50 50 == "circle#c"
#guard target circle 3 3 == "svg"

-- Paint order: the later shape is on top; `pointer-events:none` lets the point through.
private def stack (top : String) := page ("<svg width=\"200\" height=\"100\"><rect id=\"under\" width=\"200\" height=\"100\" fill=\"blue\"/>" ++
  "<rect id=\"over\" x=\"50\" y=\"0\" width=\"50\" height=\"100\" fill=\"red\"" ++ top ++ "/></svg>")
#guard target (stack "") 60 50 == "rect#over"
#guard target (stack "") 20 50 == "rect#under"
#guard target (stack " pointer-events=\"none\"") 60 50 == "rect#under"
#guard target (stack " style=\"pointer-events:none\"") 60 50 == "rect#under"
-- Inherited from a group.
#guard target (page "<svg width=\"100\" height=\"100\"><g pointer-events=\"none\"><rect id=\"r\" width=\"100\" height=\"100\"/></g></svg>") 50 50 == "svg"

-- Transforms: of a group, and of the viewBox onto the viewport.
private def moved := page ("<svg width=\"200\" height=\"100\"><g transform=\"translate(100 0)\">" ++
  "<rect id=\"m\" width=\"50\" height=\"50\"/></g></svg>")
#guard target moved 120 20 == "rect#m"
#guard target moved 20 20 == "svg"
private def scaled := page "<svg width=\"200\" height=\"200\" viewBox=\"0 0 20 20\"><rect id=\"s\" x=\"10\" y=\"10\" width=\"10\" height=\"10\"/></svg>"
#guard target scaled 150 150 == "rect#s"
#guard target scaled 50 50 == "svg"

-- visiblePainted (the initial value): no fill paint, no hit inside; the stroke hits.
-- `all` hits the inside of an unpainted fill.
private def ring (events : String) := page ("<svg width=\"100\" height=\"100\"><circle id=\"o\" cx=\"50\" cy=\"50\" r=\"40\" fill=\"none\" stroke=\"black\" stroke-width=\"10\"" ++ events ++ "/></svg>")
#guard target (ring "") 50 50 == "svg"
#guard target (ring "") 50 11 == "circle#o"
#guard target (ring " pointer-events=\"all\"") 50 50 == "circle#o"
#guard target (ring " visibility=\"hidden\"") 50 11 == "svg"

-- A `use` instance targets its `use` element.
#guard target (page ("<svg width=\"100\" height=\"100\"><defs><rect id=\"d\" width=\"40\" height=\"40\"/></defs>" ++
  "<use id=\"u\" href=\"#d\" x=\"50\" y=\"50\"/></svg>")) 60 60 == "use#u"

-- The answer carries the coordinates of the pointer events.
#guard (answer circle 50 50).map (fun j => (j.field? "clientX",j.field? "offsetY")) ==
  some (some (.number "50"),some (.number "50"))

-- A fractional viewport (a percentage width with height:auto) lays out and draws.
private def fractional := "<!doctype html><html><body style=\"margin:0\"><div style=\"width:301px\">" ++
  "<svg style=\"width:100%;height:auto\" width=\"3\" height=\"2\" viewBox=\"0 0 3 2\"><rect id=\"f\" width=\"3\" height=\"2\"/></svg></div></body></html>"
#guard (WebDocument.runUncached fractional (.object [("op",.string "render")]) 400 300).toOption.isSome
#guard target fractional 150 100 == "rect#f"
#guard match WebRender.render fractional 400 300 with
  | .ok (_,boxes) => boxes.any fun b => b.width == 301 && (b.height - 602/3).abs < 0.001
  | .error _ => false
