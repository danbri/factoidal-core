import WebDocument

/-! Embedded SVG in HTML pages: fractional viewports. -/
open L4Factoidal

-- A fractional viewport (a percentage width with height:auto) lays out and draws: the
-- viewBox maps onto the exact size, and the backing raster is the next whole pixel.
private def fractional := "<!doctype html><html><body style=\"margin:0\"><div style=\"width:301px\">" ++
  "<svg style=\"width:100%;height:auto\" width=\"3\" height=\"2\" viewBox=\"0 0 3 2\"><rect id=\"f\" width=\"3\" height=\"2\"/></svg></div></body></html>"
#guard (WebDocument.runUncached fractional (.object [("op",.string "render")]) 400 300).toOption.isSome
#guard match WebRender.render fractional 400 300 with
  | .ok (_,boxes) => boxes.any fun b => b.width == 301 && (b.height - 602/3).abs < 0.001
  | .error _ => false
