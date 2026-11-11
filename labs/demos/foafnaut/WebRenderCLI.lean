import WebRenderRDF
import WebRenderFont
import WebDocument
import SVGForgiving
import L4Factoidal.PageCanvas.Png

open L4Factoidal
private def byte (v : Float) : String := toString ((max 0 (min 255 (v*255))).round.toUInt32.toNat)

private def pixels (scene : Rendering.Scene) (w h : Nat) : Except String String := do
  let scene ← WebRenderSVG.toScene scene
  let coordinates := (List.range h).flatMap fun y => (List.range w).map fun x => (x,y)
  let colors := scene.samplePixels coordinates
  let values := colors.flatMap fun c => [byte c.r,byte c.g,byte c.b]
  return "{\"width\":" ++ toString w ++ ",\"height\":" ++ toString h ++ ",\"pixels\":[" ++ String.intercalate "," values ++ "]}"

/-- WebGPU artifact of one SVG file, with the log of what the forgiving pass removed. -/
private def svgArtifact (source : String) (w h : Nat) (font : Option String)
    (images : List (String × ByteArray)) (documentURL : Option String)
    (sfnt : Array Rendering.SfntProfile.Font := #[]) : String :=
  let quoted := fun (line : String) => "\"" ++ (line.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""
  let parsed := do
    let font ← font.mapM NativeSVGForgiving.SVGFont.parse
    NativeSVGForgiving.parse source w h font images documentURL sfnt
  match parsed >>= fun (scene,dropped) =>
      (scene.artifact).map (fun artifact => (artifact,scene.compiled.length,dropped)) with
  | .error message => WebRender.errorJSON message
  | .ok (artifact,count,dropped) =>
    "{\"primitiveCount\":" ++ toString count ++ ",\"dropped\":[" ++
      String.intercalate "," (dropped.map quoted) ++ "],\"artifact\":" ++ artifact ++ "}"

/-- A file under the resource root has this URL, so that relative references and
    `xml:base` resolve in Lean as they do for an HTTP document. It names no host. -/
private def resourceOrigin := "http://svg-resources.invalid/"

/-- The bytes of a local image reference. The policy is that of the browser's
    resource broker for this host: a reference that resolves outside the resource
    origin is not read, so `file:` and the network stay refused, and the real path
    must be under `root`, so a link can not leave it. -/
private def localImage (root : System.FilePath) (key : String) : IO (Option ByteArray) := do
  if !key.startsWith resourceOrigin then return none
  let path := ((((key.drop resourceOrigin.length).toString).splitOn "#").head!.splitOn "?").head!
  let candidate := root / path
  if !(← candidate.pathExists) then return none
  let real ← IO.FS.realPath candidate
  let base ← IO.FS.realPath root
  if !real.toString.startsWith (base.toString ++ "/") then return none
  if (← real.metadata).byteSize.toNat > NativeImage.maxImageBytes then return none
  return some (← IO.FS.readBinFile real)

/-- URL of the document, and the bytes of each image that policy allows. -/
private def localImages (document root : System.FilePath) (source : String) :
    IO (List (String × ByteArray) × Option String) := do
  let real ← IO.FS.realPath document
  let base ← IO.FS.realPath root
  let prefix_ := base.toString ++ "/"
  if !real.toString.startsWith prefix_ then return ([],none)
  let url := resourceOrigin ++ (real.toString.drop prefix_.length).toString
  let mut found : List (String × ByteArray) := []
  let mut tried : List String := []
  -- A document that a `use` names can name more. Each key is read once.
  for _ in [:8] do
    let keys := (NativeSVGForgiving.imageRequests source (some url) found).toOption.getD []
    let fresh := keys.filter (!tried.contains ·)
    if fresh.isEmpty then break
    tried := tried ++ fresh
    for key in fresh do
      if let some bytes ← localImage root key then found := (key,bytes)::found
  return (found,some url)

def main (args : List String) : IO UInt32 := do
  match args with
  | path::width::height::flags =>
    -- `--cpu-out FILE` last: an SVG scene's CPU pixels (`SVGRaster`) are written there.
    let (flags,cpuOut) := match flags.reverse with
      | file::"--cpu-out"::rest => (rest.reverse,some file)
      | _ => (flags,none)
    -- `--svg-sfnt FILE` last: text that has no SVG font is drawn with this SFNT font.
    let (flags,sfntFile) := match flags.reverse with
      | file::"--svg-sfnt"::rest => (rest.reverse,some file)
      | _ => (flags,none)
    let (svgFont,resources,svgRun) := match flags with
      | ["--svg"] => (none,none,true)
      | ["--svg","--svg-font",font] => (some font,none,true)
      | ["--svg","--svg-resources",root] => (none,some root,true)
      | ["--svg","--svg-font",font,"--svg-resources",root] => (some font,some root,true)
      | _ => (none,none,false)
    -- `FONT PX COUNT --colour-glyph TEXT OUT`: the colour glyphs of TEXT in FONT drawn by
    -- Lean (`ColrRaster`) at PX pixels to the em, each as a PNG file OUT-<n>.png, with
    -- their boxes and draw times; then COUNT more words of TEXT drawn and timed (each
    -- glyph drawn anew: the font is read again, so nothing is kept). For the pixel check
    -- against an independent COLR renderer (emoji_pixels_test.ts) and the cost of emoji.
    if let ["--colour-glyph",text,out] := flags then
      let some px := width.toNat? | throw (IO.userError "invalid size")
      let some count := height.toNat? | throw (IO.userError "invalid count")
      let bytes ← IO.FS.readBinFile path
      let read := fun (_ : Unit) => Rendering.SfntProfile.Font.read bytes "colour" "cli"
      let .ok f := read () | throw (IO.userError "font refused")
      let .ok word := f.word text px | throw (IO.userError "text refused")
      let mut rows : Array String := #[]
      for (g,i) in word.glyphs.zipIdx do
        let some c := g.colour | continue
        let start ← IO.monoNanosNow
        let some image := c.image px ⟨0,0,0⟩ | continue
        let us := ((← IO.monoNanosNow)-start)/1000
        let b := image.bitmap
        IO.FS.writeBinFile s!"{out}-{i}.png" (PageCanvas.Png.encode b.width b.height b.rgba)
        rows := rows.push s!"\{\"glyph\":{g.index},\"width\":{b.width},\"height\":{b.height},\"left\":{image.left},\"top\":{image.top},\"us\":{us}}"
      -- Draw every colour glyph of the text COUNT times with a fresh font (no kept rasters).
      let start ← IO.monoNanosNow
      let mut drawn := 0
      for _ in [0:count] do
        let .ok f := read () | throw (IO.userError "font refused")
        let .ok word := f.word text px | throw (IO.userError "text refused")
        for g in word.glyphs do
          if let some c := g.colour then
            if (c.image px ⟨0,0,0⟩).isSome then drawn := drawn+1
      let total := ((← IO.monoNanosNow)-start)/1000
      IO.println ("{\"glyphs\":[" ++ ",".intercalate rows.toList ++ "],\"drawn\":" ++ toString drawn ++ ",\"us\":" ++ toString total ++ "}")
      return 0
    if svgRun then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      if w > 4096 || h > 4096 then throw (IO.userError "viewport exceeds 4096")
      let font ← svgFont.mapM IO.FS.readFile
      let source ← IO.FS.readFile path
      let (images,documentURL) ← match resources with
        | some root => localImages path root source
        | none => pure ([],none)
      let sfnt ← match sfntFile with
        | none => pure #[]
        | some file =>
          let bytes ← IO.FS.readBinFile file
          match Rendering.SfntProfile.Font.read bytes ((System.FilePath.mk file).fileStem.getD "font") "cli" with
          | .ok f => pure #[f]
          | .error e => throw (IO.userError s!"SFNT font refused: {e}")
      IO.println (svgArtifact source w h font images documentURL sfnt)
      if let some out := cpuOut then
        let parsed := do
          let font ← font.mapM NativeSVGForgiving.SVGFont.parse
          NativeSVGForgiving.parse source w h font images documentURL sfnt
        if let .ok (scene,_) := parsed then IO.FS.writeBinFile out scene.rgba
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
      let mut e : WebDocument.Engine := {}
      if let some file := fontRequest then
        let (e',loaded) ← WebDocument.compile e "" (← IO.FS.readFile file) 1 1
        e := e'
        IO.println loaded
      let start ← IO.monoNanosNow
      let mut bytes := 0
      for i in [0:n] do
        -- The space differs on each pass, so a pass can not be shared with another.
        let (e',answer) ← WebDocument.compile e (html ++ String.ofList (List.replicate (i%2) ' ')) request w.toUInt32 h.toUInt32
        e := e'
        bytes := bytes+answer.utf8ByteSize
      IO.println s!"{n} frames, {((← IO.monoNanosNow)-start)/1000000/(max n 1)} ms each, {bytes} bytes"
      return 0
    -- The packed bytes answer (`WebDocument.compileBin`) written to OUT, after a font file
    -- (TTF or OTF) is loaded as the Hub loads Noto Sans; then COUNT more calls, each timed
    -- (a field `repeat` makes each call its own). With `"cpu":true` in the options each
    -- scene also carries its CPU pixels (cpu_render_diff_check.mjs).
    if let ["--document-bin",options,font,out,count] := flags then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      let some n := count.toNat? | throw (IO.userError "invalid count")
      let mut e : WebDocument.Engine := {}
      if font != "-" then
        let (e',loaded) := WebDocument.fontLoadBin e (← IO.FS.readBinFile font) "Noto Sans" "cli" 0
        e := e'
        if loaded.startsWith "{\"error\"" then IO.println loaded; return 1
      let html ← IO.FS.readFile path
      let .ok (request,_) := JSON.parseJsonText (← IO.FS.readFile options) | throw (IO.userError "invalid options JSON")
      let numbered := fun (i : Nat) => match request with
        | .object fields => (JSON.Json.object (fields ++ [("repeat",.number (toString i))])).toString
        | other => other.toString
      let start ← IO.monoNanosNow
      let (e',first) ← WebDocument.compileBin e html (numbered 0) w.toUInt32 h.toUInt32
      e := e'
      let firstNs := (← IO.monoNanosNow)-start
      IO.FS.writeBinFile out first
      let mut times : Array String := #[]
      for i in [0:n] do
        let at_ ← IO.monoNanosNow
        let (e',bytes) ← WebDocument.compileBin e html (numbered (i+1)) w.toUInt32 h.toUInt32
        e := e'
        if bytes.size == 0 then return 1
        times := times.push (toString (((← IO.monoNanosNow)-at_)/1000))
      IO.println ("{\"bytes\":" ++ toString first.size ++ ",\"firstUs\":" ++ toString (firstNs/1000) ++
        ",\"us\":[" ++ String.intercalate "," times.toList ++ "]}")
      return 0
    -- Scroll frames: the same document each time, with `shell.scroll` 40 pixels further.
    if let ["--document-scroll",options,count,font] := flags then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      let some n := count.toNat? | throw (IO.userError "invalid count")
      let html ← IO.FS.readFile path
      let .ok (request,_) := JSON.parseJsonText (← IO.FS.readFile options) | throw (IO.userError "invalid options JSON")
      let at_ := fun (scroll : Nat) => match request with
        | .object fields => (JSON.Json.object (fields.map fun (key,value) =>
            if key != "shell" then (key,value) else match value with
              | .object shell => (key,.object (shell.map fun (k,v) => if k == "scroll" then (k,.number (toString scroll)) else (k,v)))
              | other => (key,other))).toString
        | other => other.toString
      let (e,loaded) ← WebDocument.compile {} "" (← IO.FS.readFile font) 1 1
      IO.println loaded
      let (e,first) ← WebDocument.compile e html (at_ 0) w.toUInt32 h.toUInt32
      if first.startsWith "{\"error\"" then IO.println first; return 1
      let start ← IO.monoNanosNow
      let mut bytes := 0
      let mut e := e
      for i in [0:n] do
        let (e',answer) ← WebDocument.compile e html (at_ (40*(i+1))) w.toUInt32 h.toUInt32
        e := e'
        bytes := bytes+answer.utf8ByteSize
      IO.println s!"{n} scroll frames, {((← IO.monoNanosNow)-start)/1000/(max n 1)} us each, {bytes} bytes"
      return 0
    -- One frame with a font loaded first: the output bytes, for a before/after check.
    if let ["--document",options,font] := flags then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      let (e,loaded) ← WebDocument.compile {} "" (← IO.FS.readFile font) 1 1
      if loaded.startsWith "{\"error\"" then IO.println loaded; return 1
      IO.println (← WebDocument.compile e (← IO.FS.readFile path) (← IO.FS.readFile options) w.toUInt32 h.toUInt32).2
      return 0
    if let ["--document",options] := flags then
      let some w := width.toNat? | throw (IO.userError "invalid width")
      let some h := height.toNat? | throw (IO.userError "invalid height")
      if w > 4096 || h > 4096 then throw (IO.userError "viewport exceeds4096")
      IO.println (← WebDocument.compile {} (← IO.FS.readFile path) (← IO.FS.readFile options) w.toUInt32 h.toUInt32).2
      return 0
    let fontPath := match flags with
      | ["--font-data",path] | ["--font-data",path,"--pixels"] | ["--pixels","--font-data",path] => some path
      | _ => none
    if fontPath.isNone && (flags.any (fun flag => flag != "--pixels" && flag != "--rdf") || flags.eraseDups.length != flags.length) then
      IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--svg [--svg-font SVG_FONT] [--svg-resources ROOT] | [--rdf | --font-data FONT_JSON] [--pixels]]"
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
    IO.eprintln "usage: web-render INPUT WIDTH HEIGHT [--svg [--svg-font SVG_FONT] [--svg-resources ROOT] | [--rdf | --font-data FONT_JSON] [--pixels]]"
    return 2
