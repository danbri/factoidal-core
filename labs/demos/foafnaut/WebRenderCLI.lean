import WebRenderRDF
import WebRenderFont
import WebDocument

open L4Factoidal
private def byte (v : Float) : String := toString ((max 0 (min 255 (v*255))).round.toUInt32.toNat)

private def pixels (scene : Rendering.Scene) (w h : Nat) : Except String String := do
  let scene ← WebRenderSVG.toScene scene
  let coordinates := (List.range h).flatMap fun y => (List.range w).map fun x => (x,y)
  let colors := scene.samplePixels coordinates
  let values := colors.flatMap fun c => [byte c.r,byte c.g,byte c.b]
  return "{\"width\":" ++ toString w ++ ",\"height\":" ++ toString h ++ ",\"pixels\":[" ++ String.intercalate "," values ++ "]}"

def main (args : List String) : IO UInt32 := do
  match args with
  | path::width::height::flags =>
    if flags == ["--font-requests"] then
      IO.println (WebRenderFontRequests.compile (← IO.FS.readFile path))
      return 0
    if let ["--document",options] := flags then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      if w > 4096 || h > 4096 then throw (IO.userError "viewport exceeds4096")
      IO.println (WebDocument.compile (← IO.FS.readFile path) (← IO.FS.readFile options) w.toUInt32 h.toUInt32)
      return 0
    let fontPath := match flags with
      | ["--font-data",path] | ["--font-data",path,"--pixels"] | ["--pixels","--font-data",path] => some path
      | _ => none
    if fontPath.isNone && (flags.any (fun flag => flag != "--pixels" && flag != "--rdf") || flags.eraseDups.length != flags.length) then
      IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--rdf | --font-data FONT_JSON] [--pixels]"
      return 2
    let some w := width.toNat? | throw (IO.userError "invalid width")
    let some h := height.toNat? | throw (IO.userError "invalid height")
    if w > 4096 || h > 4096 then
      IO.println (WebRender.errorJSON "unsupported viewport dimensions exceeding 4096")
      return 0
    let source ← IO.FS.readFile path
    -- An XML page names its stylesheet; a local file resolves next to the page.
    let source ← match WebXslt.stylesheetHref source with
      | .error message =>
        IO.println (WebRender.errorJSON message)
        return 0
      | .ok none => pure source
      | .ok (some href) =>
        let stylePath := match (System.FilePath.mk path).parent with
          | some parent => parent / href
          | none => System.FilePath.mk href
        match WebXslt.transform source (← IO.FS.readFile stylePath) path stylePath.toString with
        | .error message =>
          IO.println (WebRender.errorJSON message)
          return 0
        | .ok (html,_) => pure html
    let fontData ← match fontPath with
      | none => pure none
      | some fontPath => some <$> IO.FS.readFile fontPath
    if flags.contains "--pixels" then
      if w*h > 1048576 then
        IO.println (WebRender.errorJSON "unsupported CPU image exceeding 1048576 pixels")
        return 0
      let result : Except String Rendering.Scene := match fontData with
        | some data => (WebRenderFont.render source data w h).map (fun (scene,_,_) => scene)
        | none => if flags.contains "--rdf" then
            (WebRenderRDF.render source w h).map (fun (scene,_,_) => scene)
          else (WebRender.render source w h).map (·.1)
      match result with
      | .error message => IO.println (WebRender.errorJSON message)
      | .ok scene =>
        match pixels scene w h with
        | .error message => IO.println (WebRender.errorJSON message)
        | .ok value => IO.println value
    else
      IO.println (match fontData with
        | some data => WebRenderFont.compile source data w.toUInt32 h.toUInt32
        | none => if flags.contains "--rdf" then WebRenderRDF.compile source w.toUInt32 h.toUInt32
          else WebRender.compile source w.toUInt32 h.toUInt32)
    return 0
  | _ =>
    IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--rdf | --font-data FONT_JSON] [--pixels]"
    return 2
