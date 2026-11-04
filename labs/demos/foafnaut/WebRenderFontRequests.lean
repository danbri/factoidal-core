import WebRender
import L4Factoidal.Rendering.FontRequests
import L4Factoidal.Unicode.BidiData

/-! Font request ABI. The existing Lean HTML parser, stylesheet reader and
computed styles determine all requests. Hosts receive font data requests only;
they must not parse HTML, compute style, or choose line breaks. -/
namespace WebRenderFontRequests
open L4Factoidal

/-- The current HTML line layout has no bidi paragraph phase. Refuse strong
RTL/Arabic numbers and directional formatting even if the font library guesses
LTR from the first Latin letter of a mixed run. The existing generated Unicode
property table supplies the classes; the host makes no Unicode/layout choice. -/
def collectDOMWithRules (dom : DOM.Dom) (rules : List Rendering.CSS.Rule) :
    Except String (Array Rendering.FontRequests.Request) := do
  let requests ← Rendering.FontRequests.forDOM dom rules
  for request in requests do
    for c in request.text.toList do
      let bidi := Unicode.BidiData.bidiClassTable.getChar c |>.toNat
      -- BidiData indices: R=1, AL=2, AN=6, directional formats=14..22.
      if bidi == 1 || bidi == 2 || bidi == 6 || bidi >= 14 then
        throw "unsupported font text: bidi paragraph layout required"
  let bitmap := fun (request : Rendering.FontRequests.Request) =>
    ["monospace","ascii-bitmap"].contains request.family.toLower
  if requests.all bitmap then return #[]
  if requests.any bitmap then throw "unsupported mixed bitmap and supplied font families"
  return requests

def collectDOM (dom : DOM.Dom) : Except String (Array Rendering.FontRequests.Request) := do
  collectDOMWithRules dom (← WebRender.styleRules dom)

def collect (html : String) : Except String (Array Rendering.FontRequests.Request) := do
  if html.utf8ByteSize > 1048576 then
    throw "font requests: HTML exceeds 1MiB transport bound"
  let dom := DOM.parseHtmlDocument html
  collectDOM dom

private def quote (value : String) := "\"" ++ JSON.escapeString value ++ "\""
private def requestJSON (request : Rendering.FontRequests.Request) : String :=
  "{\"family\":" ++ quote request.family ++ ",\"pixelSize\":" ++ toString request.pixelSize ++
    ",\"text\":" ++ quote request.text ++ "}"

def requestsJSON (requests : Array Rendering.FontRequests.Request) : String :=
  "{\"schema\":\"factoidal-font-requests-v1\",\"requests\":[" ++
    String.intercalate "," (requests.toList.map requestJSON) ++ "]}"

def compileDOM (dom : DOM.Dom) : String :=
  match collectDOM dom with
  | .error message => WebRender.errorJSON message
  | .ok requests => requestsJSON requests

/-- Stable JSON ABI shared by the native CLI and browser module. Empty request
arrays are valid for documents without text; they need no host font data. -/
@[export web_render_font_requests]
def compile (html : String) : String :=
  match collect html with
  | .error message => WebRender.errorJSON message
  | .ok requests => requestsJSON requests
end WebRenderFontRequests
