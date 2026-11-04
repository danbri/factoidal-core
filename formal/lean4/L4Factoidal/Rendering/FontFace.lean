import L4Factoidal.Rendering.FontProvider

/-! Bounded single-face dictionary of already-shaped words. The font library
provides shaping and outlines; Lean selects exact text runs and checks that
one face identity supplies consistent glyph resources. No CSS layout here. -/
namespace L4Factoidal.Rendering.FontProvider
def compareWordKey (a b : String × Nat) : Ordering :=
  match compare a.1 b.1 with
  | .eq => compare a.2 b.2
  | order => order
structure Face where
  fontSha256 : String
  faceIndex : Nat
  family : String
  style : String
  unitsPerEm : Float
  ascent : Float
  descent : Float
  lineGap : Float
  words : Std.TreeMap (String × Nat) Word compareWordKey
private def sameCommand : FontData.OutlineCommand → FontData.OutlineCommand → Bool
  | .move x y,.move a b | .line x y,.line a b => x == a && y == b
  | .quadratic x y u v,.quadratic a b c d => x == a && y == b && u == c && v == d
  | .cubic x y u v s t,.cubic a b c d e f =>
    x == a && y == b && u == c && v == d && s == e && t == f
  | .close,.close => true
  | _,_ => false
private def sameOutline (a b : FontData.Outline) : Bool :=
  a.id == b.id && a.commands.size == b.commands.size &&
    ((a.commands.toList.zip b.commands.toList).all fun (x,y) => sameCommand x y)
/-- Budgets apply across the dictionary, including repeated outline payloads.
Callers may deduplicate requests before shaping without deciding layout. -/
def Face.make (inputs : Array FontData.ShapedWord) : Except String Face := do
  if inputs.isEmpty || inputs.size > 4096 then throw "font face: require 1 to 4096 shaped words"
  let some source := inputs[0]? | throw "font face: missing first word"
  let first ← prepare source
  let mut words : Std.TreeMap (String × Nat) Word compareWordKey := {}
  let mut resources : Std.TreeMap Nat FontData.Outline := {}
  let mut glyphCount := 0
  let mut commandCount := 0
  for input in inputs do
    glyphCount := glyphCount+input.glyphs.size
    if glyphCount > 65536 then throw "font face: aggregate glyph bound exceeded"
    for outline in input.outlines do
      commandCount := commandCount+outline.commands.size
      if commandCount > 2097152 then throw "font face: aggregate outline bound exceeded"
      if let some old := resources.get? outline.id then
        if !sameOutline old outline then throw "font face: inconsistent outline for glyph identity"
      else resources := resources.insert outline.id outline
    let word ← prepare input
    if word.fontSha256 != first.fontSha256 || word.faceIndex != first.faceIndex ||
        word.family != first.family || word.style != first.style ||
        word.unitsPerEm != first.unitsPerEm || word.ascent != first.ascent ||
        word.descent != first.descent || word.lineGap != first.lineGap then
      throw "font face: shaped word identity or metrics mismatch"
    let key := (word.text,word.pixelSize)
    if words.contains key then throw "font face: duplicate shaped word text/size"
    words := words.insert key word
  return ⟨first.fontSha256,first.faceIndex,first.family,first.style,first.unitsPerEm,
    first.ascent,first.descent,first.lineGap,words⟩
/-- Missing data is an error, never character substitution or a width estimate. -/
def Face.lookup (face : Face) (text : String) (pixelSize : Nat) : Except String Word :=
  match face.words.get? (text,pixelSize) with
  | some word => .ok word
  | none => .error "font face: missing shaped word data at requested size"

/-- Transport is a JSON array of the unchanged native font-data-v1 records.
The aggregate byte cap applies before parsing, in addition to typed budgets. -/
def Face.decode (source : String) : Except String Face := do
  if source.utf8ByteSize > 16777216 then throw "font face: JSON exceeds16MiB transport bound"
  let value ← (JSON.parseJson source).mapError (fun error => s!"font face JSON: {error}")
  let .array records := value | throw "font face: expected array of shaped word records"
  if records.isEmpty || records.length > 4096 then throw "font face: require 1 to 4096 shaped words"
  let inputs ← records.mapM (fun record => FontData.decodeValue record)
  Face.make inputs.toArray
end L4Factoidal.Rendering.FontProvider
