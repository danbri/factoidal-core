import WebRenderRDF
import WebRenderFont
import WebDocument
import SVGForgiving

open L4Factoidal
private def byte (v : Float) : String := toString ((max 0 (min 255 (v*255))).round.toUInt32.toNat)

private def pixels (scene : Rendering.Scene) (w h : Nat) : Except String String := do
  let scene ← WebRenderSVG.toScene scene
  let coordinates := (List.range h).flatMap fun y => (List.range w).map fun x => (x,y)
  let colors := scene.samplePixels coordinates
  let values := colors.flatMap fun c => [byte c.r,byte c.g,byte c.b]
  return "{\"width\":" ++ toString w ++ ",\"height\":" ++ toString h ++ ",\"pixels\":[" ++ String.intercalate "," values ++ "]}"

/-- WebGPU artifact of one SVG file, with the log of what the forgiving pass removed. -/
private def svgArtifact (source : String) (w h : Nat) (font : Option String) : String :=
  let quoted := fun (line : String) => "\"" ++ (line.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  let parsed := do
    let font ← font.mapM NativeSVGForgiving.SVGFont.parse
    NativeSVGForgiving.parse source w h font
  match parsed >>= fun (scene,dropped) =>
      (scene.artifact).map (fun artifact => (artifact,scene.compiled.length,dropped)) with
  | .error message => WebRender.errorJSON message
  | .ok (artifact,count,dropped) =>
    "{\"primitiveCount\":" ++ toString count ++ ",\"dropped\":[" ++
      String.intercalate "," (dropped.map quoted) ++ "],\"artifact\":" ++ artifact ++ "}"

def main (args : List String) : IO UInt32 := do
  match args with
  | path::width::height::flags =>
    let svgFont := match flags with | ["--svg","--svg-font",font] => some font | _ => none
    if flags == ["--svg"] || svgFont.isSome then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      if w > 4096 || h > 4096 then throw (IO.userError "viewport exceeds 4096")
      let font ← svgFont.mapM IO.FS.readFile
      IO.println (svgArtifact (← IO.FS.readFile path) w h font)
      return 0
    if flags == ["--svg-profile"] then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      let xml ← IO.FS.readFile path
      let start ← IO.monoNanosNow
      match NativeSVG.parse xml w h with
      | .error message => IO.eprintln message; return 1
      | .ok scene =>
        IO.println s!"parse {((← IO.monoNanosNow)-start)/1000} us"
        for (name,part) in scene.artifactParts do
          let begin_ ← IO.monoNanosNow
          let size := part ()
          -- The test uses the size, so the work happens before the second clock read.
          if size == 0 then IO.println s!"{name} is empty"
          IO.println s!"{name} {((← IO.monoNanosNow)-begin_)/1000} us, size {size}"
        return 0
    if flags == ["--font-requests"] then
      IO.println (WebRenderFontRequests.compile (← IO.FS.readFile path))
      return 0
    -- Repeats one frame, so that a stack sampler has time to see where it goes.
    let (repeat_,fontRequest) := match flags with
      | ["--document-repeat",options,count] => (some (options,count),none)
      | ["--document-repeat",options,count,font] => (some (options,count),some font)
      | _ => (none,none)
    if let some (options,count) := repeat_ then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      let some n := count.toNat? | throw (IO.userError "invalid count")
      let html ← IO.FS.readFile path
      let request ← IO.FS.readFile options
      if let some file := fontRequest then
        IO.println (WebDocument.compile "" (← IO.FS.readFile file) 1 1)
      let start ← IO.monoNanosNow
      let mut bytes := 0
      for i in [0:n] do
        -- The space differs on each pass, so a pass can not be shared with another.
        bytes := bytes+(WebDocument.compile (html ++ String.ofList (List.replicate (i%2) ' ')) request w.toUInt32 h.toUInt32).utf8ByteSize
      IO.println s!"{n} frames, {((← IO.monoNanosNow)-start)/1000000/(max n 1)} ms each, {bytes} bytes"
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
      IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--svg [--svg-font SVG_FONT] | [--rdf | --font-data FONT_JSON] [--pixels]]"
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
    IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--svg [--svg-font SVG_FONT] | [--rdf | --font-data FONT_JSON] [--pixels]]"
    return 2
