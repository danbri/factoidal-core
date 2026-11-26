import WebRender

namespace WebRenderTests
open L4Factoidal
private def pixel (html : String) (x y : Nat) : Except String (Float × Float × Float) := do
  let (scene,_) ← WebRender.render html 128 128
  let native ← WebRenderSVG.toScene scene
  let color := native.samplePixel x y
  return (color.r,color.g,color.b)
private def clipHTML := "<style>body{margin:0}svg{display:block;width:40px;height:30px;background:yellow;color:red}</style><svg viewBox='0 0 20 10' preserveAspectRatio='none'><rect width='10' height='20' fill='currentColor'/></svg>"
#guard (pixel clipHTML 10 10).toOption == some (1,0,0)
#guard (pixel clipHTML 30 10).toOption == some (1,1,0)
#guard (pixel clipHTML 10 35).toOption == some (1,1,1)
#guard (pixel (clipHTML.replace "width:40px" "width:30px") 20 10).toOption == some (1,1,0)
private def cascadeHTML := "<style>body{margin:0}svg{color:green!important}</style><svg color='red' style='color:blue'><rect width='20' height='20' fill='currentColor'/></svg>"
#guard (pixel cascadeHTML 10 10).toOption == some (0,128/255,0)
private def visibilityHTML := "<style>body{margin:0}svg{visibility:visible!important}</style><svg style='visibility:hidden'><rect width='20' height='20' fill='red'/></svg>"
#guard (pixel visibilityHTML 10 10).toOption == some (1,0,0)
#guard (pixel "<style>body{margin:0}</style><svg style='padding-bottom:0px;margin-left:0px'><rect width='20' height='20' fill='red'/></svg>" 10 10).toOption == some (1,0,0)
-- A `background` in the style of an outer svg: the shorthand's longhands (colour and image) go
-- to HTML layout, none to the SVG reader (as in the Solving showcase page).
#guard (pixel "<style>body{margin:0}</style><svg width='40' height='30' style='background:rgb(0,0,255)'><rect width='20' height='20' fill='red'/></svg>" 30 25).toOption == some (0,0,1)
#guard (pixel "<style>body{margin:0}</style><svg width='40' height='30' style='background:rgb(0,0,255)'><rect width='20' height='20' fill='red'/></svg>" 10 10).toOption == some (1,0,0)
private def blockHTML := "<style>body{margin:0}div{width:20px;height:12px;overflow:hidden;background:red}div div{width:40px;height:24px;background:blue}</style><div><div></div></div>"
#guard (pixel blockHTML 10 10).toOption == some (0,0,1)
#guard (pixel blockHTML 21 10).toOption == some (1,1,1)
#guard (pixel blockHTML 10 13).toOption == some (1,1,1)
private def useHTML := "<style>body{margin:0}svg{display:block;width:40px;height:30px}</style><svg viewBox='0 0 40 30'><defs><symbol id='s' viewBox='0 0 10 10'><rect width='20' height='20' fill='green'/></symbol></defs><use href='#s' x='5' y='5' width='10' height='10'/></svg>"
#guard (pixel useHTML 10 10).toOption == some (0,128/255,0)
#guard (pixel useHTML 16 10).toOption == some (1,1,1)
private def posterHTML :=
  "<style>body{margin:0}video{display:block;width:40px;height:20px;background:blue}</style>" ++
  "<video poster='data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNg+M/wHwAEAQH/cetH5QAAAABJRU5ErkJggg=='></video>"
#guard (pixel posterHTML 0 10).toOption == some (0,0,1)
#guard (pixel posterHTML 16 10).toOption == some (0,1,0)
#guard (pixel (posterHTML.replace "background:blue" "object-fit:fill;background:blue") 0 10).toOption == some (0,1,0)
#guard (WebRender.htmlImageKeys
    (DOM.parseHtmlDocument "<video poster=' ../poster.png ' src='movie.mp4'></video><video poster=' '></video>")
    (some "https://example.test/media/index.html")).map (·.2) == ["https://example.test/poster.png"]

private def embedInk := "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNg+M/wHwAEAQH/cetH5QAAAABJRU5ErkJggg=="
private def embedStyle :=
  "<style>body{margin:0} object,embed{display:block;width:20px;height:20px} div{width:20px;height:20px;background:red}</style>"
#guard (pixel (embedStyle ++ "<embed src='" ++ embedInk ++ "'>") 10 10).toOption == some (0,1,0)
#guard (pixel (embedStyle ++ "<object data='" ++ embedInk ++ "'><div></div></object>") 10 10).toOption == some (0,1,0)
#guard (pixel (embedStyle ++ "<object data='data:image/png;base64,AAAA'><div></div></object>") 10 10).toOption == some (1,0,0)
#guard (WebRender.htmlImageKeys
    (DOM.parseHtmlDocument "<object data='../icon.svg#view'></object><embed type='image/jpeg' src='still'><object type='text/html' data='page.png'></object><embed src='file.pdf'>")
    (some "https://example.test/docs/")).map (·.2) ==
  ["https://example.test/icon.svg#view", "https://example.test/docs/still"]

private def inlineSvg :=
  "data:image/svg+xml,%3Csvg%20xmlns=%27http://www.w3.org/2000/svg%27%20width=%2720%27%20height=%2720%27%3E" ++
  "%3Crect%20width=%2720%27%20height=%2720%27%20fill=%27%2300ff00%27/%3E%3C/svg%3E"
private def inlineSvgPage := "<style>body{margin:0}img{display:block;width:20px;height:20px}</style>"
#guard (pixel (inlineSvgPage ++ "<img src='" ++ inlineSvg ++ "'>") 10 10).toOption == some (0,1,0)
#guard (pixel (inlineSvgPage ++ "<img src='" ++ inlineSvg ++ "'>") 25 10).toOption == some (1,1,1)

-- Both elements share the striped 8×4 bitmap. At 2x the complete red/blue
-- stripe is painted across four CSS pixels and the next pixel is outside the image.
private def stripeURL := "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAgAAAAECAIAAAA8r+mnAAAAFElEQVR4nGP4z8AAR0jM/wzUkwAAOn4f4QhCQp4AAAAASUVORK5CYII="
private def densityPage :=
  "<style>body{margin:0}img{display:block}</style><img src='" ++ stripeURL ++
  "'><img srcset='" ++ stripeURL ++ " 2x'>"
#guard (pixel densityPage 6 1).toOption == some (0,0,1)
#guard (pixel densityPage 0 4).toOption == some (1,0,0)
#guard (pixel densityPage 3 4).toOption == some (0,0,1)
#guard (pixel densityPage 4 4).toOption == some (1,1,1)

private def intrinsicAt (srcset sizes : String) : Option (Float × Float) := do
  let dom := DOM.parseHtmlDocument ("<img srcset='" ++ stripeURL ++ " " ++ srcset ++ "' sizes='" ++ sizes ++ "'>")
  let [(id,_,_)] := WebRender.htmlImageRequests dom none | none
  let (_,pictures) ← (WebRender.makeReplaced dom).toOption
  return (← pictures id).size

#guard intrinsicAt "16w" "8px" == some (4,2)
#guard intrinsicAt "10000x" "" == some (0,0)

end WebRenderTests
