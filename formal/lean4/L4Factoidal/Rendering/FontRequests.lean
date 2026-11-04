import L4Factoidal.Rendering.Layout

/-! Font-data preflight over the existing Lean DOM and computed styles.
The collector calls Layout.inlineItems on text nodes, hence executes the exact
same textItems scanner as rendering. It does not tokenize HTML or decide any
host layout. This module is not yet imported by the frozen runtime. -/
namespace L4Factoidal.Rendering.FontRequests
open DOM CSS Layout
structure Request where
  family : String
  pixelSize : Nat
  text : String
  deriving Repr, BEq

def compareRequest (a b : Request) : Ordering :=
  match compare a.family.toLower b.family.toLower with
  | .eq => match compare a.pixelSize b.pixelSize with
    | .eq => compare a.text b.text
    | order => order
  | order => order
abbrev Requests := Std.TreeMap Request Request compareRequest
private def add (requests : Requests) (style : Computed) (text : String) : Except String Requests := do
  let size := style.fontSize.toUInt32.toNat
  if !style.fontSize.isFinite || Float.ofNat size != style.fontSize || size == 0 || size > 512 then
    throw "font requests: integer pixel sizes 1 to 512 required"
  if text.utf8ByteSize > 65536 || style.fontFamily.utf8ByteSize > 256 then
    throw "font requests: word or family byte bound exceeded"
  let request : Request := ⟨style.fontFamily,size,text⟩
  let out := requests.insert request request
  if out.size > 4096 then throw "font requests: more than 4096 distinct text/family/size requests"
  return out
private def context (dom : Dom) (styles : Array Computed) : Nat → Nat → Except String Nat
  | 0,_ => throw "font requests: ancestor traversal exceeds DOM arena"
  | fuel+1,id => do
    let some node := dom.nodes[id]? | throw "font requests: invalid DOM node"
    let some style := styles[id]? | throw "font requests: missing computed style"
    if id == 0 || style.display == .block then return id
    match node.parent with
    | none => return id
    | some parent => context dom styles fuel parent
private def noEmbedding : Embedding := fun _ _ _ _ => throw "font requests: unexpected embedding during text scan"

/-- Shaping requests include potential retained spaces and parent strut metrics.
Whitespace-only contexts produce no request. SVG descendants belong to the SVG
producer; display:none subtrees are skipped before visiting their contents. -/
def forDOM (dom : Dom) (rules : List CSS.Rule) : Except String (Array Request) := do
  let styles ← CSS.computeAll dom rules
  let mut requests : Requests := {}
  let mut active : Std.TreeMap Nat Unit := {}
  let mut spaces : Array (Nat × Computed) := #[]
  let mut pending := [0]
  for _ in [:dom.size+1] do
    match pending with
    | [] =>
      for (block,style) in spaces do
        if active.contains block then requests ← add requests style " "
      for (block,_) in active.toList do
        let some style := styles[block]? | throw "font requests: missing strut style"
        requests ← add requests style " "
      let out := (requests.toList.map Prod.snd).toArray
      if out.foldl (fun total request => total+request.text.utf8ByteSize) 0 > 1048576 then
        throw "font requests: aggregate text exceeds1MiB"
      return out
    | id::rest =>
      pending := rest
      let some node := dom.nodes[id]? | throw "font requests: invalid DOM node"
      let some style := styles[id]? | throw "font requests: missing computed style"
      if style.display == .none then continue
      if node.type == .element && ["head","script","style","title","meta","link","template"].contains node.lname then
        throw "font requests: visible metadata/script element outside profile"
      if node.type == .element && node.ns == some DOM.svgNS then
        if style.display == .inlineBlock then throw "unsupported CSS inline-block layout"
        if style.display == .inline then
          let block ← context dom styles (dom.size+1) (node.parent.getD 0)
          active := active.insert block ()
        continue
      if node.type == .element && node.ns != some DOM.htmlNS then
        throw "unsupported foreign namespace in font requests"
      if style.display == .inlineBlock then throw "unsupported CSS inline-block layout"
      if node.type == .text then
        let block ← context dom styles (dom.size+1) id
        let items ← Layout.inlineItems dom styles noEmbedding 0 1 id
        for item in items do
          match item with
          | .word _ s text _ =>
            requests ← add requests s text
            active := active.insert block ()
          | .space _ s => spaces := spaces.push (block,s)
          | _ => throw "font requests: unexpected nontext result from shared scanner"
      else if DOM.Dom.isHtmlElement node "br" && style.display == .inline then
        let block ← context dom styles (dom.size+1) (node.parent.getD 0)
        active := active.insert block ()
        requests ← add requests style " "
      pending := node.kids.toList ++ pending
  throw "font requests: DOM traversal exceeds arena"
end L4Factoidal.Rendering.FontRequests
