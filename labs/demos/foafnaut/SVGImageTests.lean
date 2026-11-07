import SVGForgiving

/- The `image` element: placement, paint and refusals, on the CPU reference. The
   bitmap is 2 by 2: red, green; blue, transparent. -/
open NativeSVG

private def png := "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAAFElEQVR4nGP4z8DwHwwZGP6DCAYAP9IF+9wCo9QAAAAASUVORK5CYII="
private def jpeg := "data:image/jpeg;base64,/9j/4AAQSkZJRgABAQAAAQABAAD/2wBDAAIBAQEBAQIBAQECAgICAgQDAgICAgUEBAMEBgUGBgYFBgYGBwkIBgcJBwYGCAsICQoKCgoKBggLDAsKDAkKCgr/2wBDAQICAgICAgUDAwUKBwYHCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgoKCgr/wAARCAAIAAgDASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwD5fooor8TP9QD/2Q=="
private def doc (body : String) : String :=
  "<svg xmlns='http://www.w3.org/2000/svg' xmlns:xlink='http://www.w3.org/1999/xlink' viewBox='0 0 40 40'>" ++ body ++ "</svg>"
private def image (attrs : String) (href : String := png) : String :=
  "<image xlink:href='" ++ href ++ "' " ++ attrs ++ "/>"
private def rgb (body : String) (x y : Nat) : List Nat :=
  match NativeSVG.parse (doc body) 40 40 with
  | .ok scene =>
    let c := scene.samplePixel x y
    [c.r,c.g,c.b].map (fun v => (v*255).round.toUInt32.toNat)
  | .error _ => []
private def near (a b : List Nat) : Bool :=
  a.length == b.length && (a.zip b).all fun (p,q) => (if p > q then p-q else q-p) <= 16

-- The middle of each pixel, at a scale of 20. Outside the rectangle nothing is drawn.
#guard near (rgb (image "width='40' height='40'") 10 10) [255,0,0]
#guard near (rgb (image "width='40' height='40'") 30 10) [0,255,0]
#guard near (rgb (image "width='40' height='40'") 10 30) [0,0,255]
#guard near (rgb (image "width='40' height='40'") 30 30) [255,255,255]
#guard near (rgb (image "x='10' y='10' width='20' height='20'") 5 5) [255,255,255]
#guard near (rgb (image "x='10' y='10' width='20' height='20'") 14 14) [255,0,0]
-- Opacity is the element's; fill-opacity does not apply to an image.
#guard near (rgb (image "width='40' height='40' opacity='.5'") 10 10) [255,128,128]
#guard near (rgb (image "width='40' height='40' fill-opacity='0'") 10 10) [255,0,0]
-- A transform moves it, and a clip of the group clips it.
#guard near (rgb (image "width='20' height='20' transform='translate(20,20)'") 24 24) [255,0,0]
#guard near (rgb ("<defs><clipPath id='c'><rect width='10' height='40'/></clipPath></defs><g clip-path='url(#c)'>" ++
  image "width='40' height='40'" ++ "</g>") 30 10) [255,255,255]
-- preserveAspectRatio: `meet` keeps the shape, and the rest of the viewport stays empty.
#guard near (rgb (image "width='40' height='20'") 5 10) [255,255,255]
#guard near (rgb (image "width='40' height='20'") 14 4) [255,0,0]
#guard near (rgb (image "width='40' height='20' preserveAspectRatio='xMinYMin'") 4 4) [255,0,0]
#guard near (rgb (image "width='40' height='20' preserveAspectRatio='xMaxYMax'") 35 5) [0,255,0]
-- `none` stretches. `slice` covers the viewport, and the viewport clips the image.
#guard near (rgb (image "width='40' height='20' preserveAspectRatio='none'") 5 5) [255,0,0]
#guard near (rgb (image "width='40' height='20' preserveAspectRatio='xMidYMid slice'") 9 0) [255,0,0]
#guard near (rgb (image "width='40' height='20' preserveAspectRatio='xMidYMid slice'") 5 25) [255,255,255]
-- JPEG goes the same way.
private def jpegCentre := rgb (image "width='40' height='40'" jpeg) 20 20
#guard jpegCentre.length == 3 && (jpegCentre.zip [200,40,40]).all fun (p,q) => (if p > q then p-q else q-p) <= 12
-- Zero disables rendering; a negative size and a bad reference are named refusals.
#guard near (rgb (image "width='0' height='40'") 10 10) [255,255,255]
private def refusal (body : String) : String :=
  match NativeSVG.parse (doc body) 40 40 with | .ok _ => "" | .error m => m
#guard refusal (image "width='-1' height='40'") == "negative image size"
#guard refusal (image "width='9' height='9'" "x.png") == "image resource not supplied: x.png"
#guard refusal (image "width='9' height='9'" "file:///etc/passwd") == "image resource not supplied: file:///etc/passwd"
#guard refusal (image "width='9' height='9'" "data:image/png;base64,aGk=") == "image is not PNG, JPEG or GIF"
-- Expected failure, https://github.com/danbri/factoidal/issues/1258: an `image` of an SVG
-- document is refused. When it draws, this guard fails.
#guard refusal (image "width='9' height='9'" "data:image/svg+xml;base64,PHN2Zy8+") == "image is not PNG, JPEG or GIF"
-- The forgiving pass removes only that element, and logs it.
private def forgiven (body : String) : Nat × List String :=
  match NativeSVGForgiving.parse (doc body) 40 40 with
  | .ok (scene,log) => (scene.compiled.length,log)
  | .error _ => (999,[])
#guard (forgiven (image "width='9' height='9'" "x.png" ++ "<rect width='9' height='9'/>")).1 == 1
#guard (forgiven (image "width='9' height='9'" "x.png")).2.any (·.startsWith "removed image")
-- Bytes from a host are found by the key that `imageRequests` gives.
#guard (NativeSVGForgiving.imageRequests (doc (image "width='9' height='9'" "a/b.png" ++ image "" png))).toOption == some ["a/b.png"]
private def supplied : Bool :=
  match NativeImage.dataBytes png with
  | .error _ => false
  | .ok bytes =>
    match NativeSVGForgiving.parse (doc (image "width='40' height='40'" "a/b.png")) 40 40 none [("a/b.png",bytes)] with
    | .ok (scene,log) => scene.compiled.length == 1 && log.isEmpty
    | .error _ => false
#guard supplied
-- `use` of an image and the same image twice: the table holds its pixels once.
private def tableSize (body : String) : Nat :=
  match NativeSVG.parse (doc body) 40 40 >>= (·.artifact) with
  | .error _ => 0
  | .ok json =>
    let tail := (json.splitOn "\"tiles\":[")[1]!
    let list := (tail.splitOn "]")[0]!
    (((list.splitOn ",").getLast?.getD "0").toNat?).getD 0
#guard tableSize (image "width='9' height='9'") == 9+4
#guard tableSize (image "width='9' height='9'" ++ image "x='9' width='9' height='9'") == 18+4
#guard tableSize ("<defs>" ++ image "id='i' width='9' height='9'" ++ "</defs><use xlink:href='#i'/><use x='9' xlink:href='#i'/>") == 18+4
