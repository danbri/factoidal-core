import WebRenderRDF

open L4Factoidal
private def byte (v : Float) : String := toString ((max 0 (min 255 (v*255))).round.toUInt32.toNat)

private def pixels (scene : Rendering.Scene) (w h : Nat) : String := Id.run do
  let scene := WebRenderSVG.toScene scene
  let coordinates := (List.range h).flatMap fun y => (List.range w).map fun x => (x,y)
  let colors := scene.samplePixels coordinates
  let values := colors.flatMap fun c => [byte c.r,byte c.g,byte c.b]
  return "{\"width\":" ++ toString w ++ ",\"height\":" ++ toString h ++ ",\"pixels\":[" ++ String.intercalate "," values ++ "]}"

def main (args : List String) : IO UInt32 := do
  match args with
  | path::width::height::flags =>
    if flags.any (fun flag => flag != "--pixels" && flag != "--rdf") || flags.eraseDups.length != flags.length then
      IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--rdf] [--pixels]"
      return 2
    let some w := width.toNat? | throw (IO.userError "invalid width")
    let some h := height.toNat? | throw (IO.userError "invalid height")
    if w > 4096 || h > 4096 then
      IO.println (WebRender.errorJSON "unsupported viewport dimensions exceeding 4096")
      return 0
    let source ← IO.FS.readFile path
    if flags.contains "--pixels" then
      if w*h > 1048576 then
        IO.println (WebRender.errorJSON "unsupported CPU image exceeding 1048576 pixels")
        return 0
      let result := if flags.contains "--rdf" then
          (WebRenderRDF.render source w h).map (fun (scene,_,_) => scene)
        else (WebRender.render source w h).map (·.1)
      match result with
      | .error message => IO.println (WebRender.errorJSON message)
      | .ok scene => IO.println (pixels scene w h)
    else
      IO.println (if flags.contains "--rdf" then WebRenderRDF.compile source w.toUInt32 h.toUInt32
        else WebRender.compile source w.toUInt32 h.toUInt32)
    return 0
  | _ =>
    IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--rdf] [--pixels]"
    return 2
