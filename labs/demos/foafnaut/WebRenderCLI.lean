import WebRender

open L4Factoidal
private def byte (v : Float) : String := toString ((max 0 (min 255 (v*255))).round.toUInt32.toNat)

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,width,height] =>
    let source ← IO.FS.readFile path
    let some w := width.toNat? | throw (IO.userError "invalid width")
    let some h := height.toNat? | throw (IO.userError "invalid height")
    if w > 4096 || h > 4096 then
      IO.println (WebRender.errorJSON "unsupported viewport dimensions exceeding 4096")
      return 0
    IO.println (WebRender.compile source w.toUInt32 h.toUInt32)
    return 0
  | [path,width,height,"--pixels"] =>
    let source ← IO.FS.readFile path
    let some w := width.toNat? | throw (IO.userError "invalid width")
    let some h := height.toNat? | throw (IO.userError "invalid height")
    if w*h > 1048576 then
      IO.println (WebRender.errorJSON "unsupported CPU image exceeding 1048576 pixels")
      return 0
    match WebRender.render source w h with
    | .error message => IO.println (WebRender.errorJSON message)
    | .ok (scene,_) =>
      let scene := WebRenderSVG.toScene scene
      let coordinates := (List.range h).flatMap fun y => (List.range w).map fun x => (x,y)
      let colors := scene.samplePixels coordinates
      let pixels := colors.flatMap fun c => [byte c.r,byte c.g,byte c.b]
      IO.println ("{\"width\":" ++ toString w ++ ",\"height\":" ++ toString h ++ ",\"pixels\":[" ++ String.intercalate "," pixels ++ "]}")
    return 0
  | _ =>
    IO.eprintln "usage: web-render INPUT.html WIDTH HEIGHT [--pixels]"
    return 2
