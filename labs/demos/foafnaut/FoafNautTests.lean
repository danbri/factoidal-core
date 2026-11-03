import FoafNaut
open NativeFoafNaut L4Factoidal.JSON

namespace NativeFoafNautTests
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def step (m : Model) (kind : Nat) (a b : Int := 0) := (update m kind a b).1
private def roundtrip (m : Model) : IO Unit :=
  check (decide (Model.decode m.encode = some m)) "model roundtrip"
private def replaceField (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .object fs => .object (fs.map fun (k,v) => (k,if k == key then value else v))
  | _ => j

def runTests (args : List String) : IO Unit := do
  let some fixture := args.head? | throw (IO.userError "supply RDF fixture")
  let text ← IO.FS.readFile fixture
  let graph ← match FoafGraph.fromTurtle text none graphLimits with
    | .ok g => pure g | .error e => throw (IO.userError e)
  let m := initial graph 1000 700
  check (m.graph.people.size == 8 && m.graph.links.size == 7) "actual RDF fixture"
  check (m.scene.shapes.length == 393 && m.scene.data.length == 6288) "scene slot layout"
  check (m.scene.sample 0 100 == NativeGraphics.RGB.mk 247 249 252) "light canvas"
  check ((m.scene.shapes.filter fun shape => match shape with
    | .glyph _ size _ _ => size == 2 | _ => false).length == 8*12+12+64) "readable base font size"
  check (m.positions[0]! == Position.mk 500 350) "initial focused radial center"
  roundtrip m
  IO.println "PASS RDF scene and model roundtrip"

  let frame ← match parseJson (initialResponse text 1000 700) with
    | .ok j => pure j | .error _ => throw (IO.userError "invalid initial JSON")
  check (frame.getString? "abi" == some "lean-foafnaut-v1") "frame ABI"
  check (frame.getString? "wgsl" == some m.scene.wgsl) "initial Lean WGSL"
  check (frame.getArray? "commands" == some [.string "render",.string "startClock"]) "startup clock"
  check ((initialResponse "" 1000 700).startsWith "{\"error\":") "empty RDF must fail before GPU"
  IO.println "PASS initial frame and empty input"

  let captured := step m 2 500 350
  check (captured.selection == 1 && captured.dragging) "body hit capture"
  check ((step m 2 570 350).selection == 1) "wide name card hit area"
  let dragged := step captured 3 620 410
  check (dragged.positions[0]! == Position.mk 620 410) "drag geometry"
  let released := step dragged 4
  check (released.selection == 1 && !released.dragging && released.pinned[0]!) "persistent selection/pin/release"
  check (decide ((step released 3 100 100).positions = released.positions)) "move after release moved node"
  check (decide ((step released 7 128).positions = released.positions)) "release pin moved during animation"
  check (decide ((step captured 7 32).positions[0]! = captured.positions[0]!)) "captured node eased"
  check ((List.range m.positions.size).all fun i => i == 0 || released.positions[i]! == m.positions[i]!) "drag moved unrelated node"
  let unsettled := {released with positions:=released.positions.set! 1 ⟨200,200⟩}
  let animated := step unsettled 7 128
  check (animated.positions[0]! == released.positions[0]! && animated.positions[1]! != unsettled.positions[1]!) "pinned node moved while unpinned node eased"
  roundtrip released
  IO.println "PASS drag pins, release and independent animation"

  let focusPoint := m.positions[1]!
  let focused := step m 2 focusPoint.x (focusPoint.y-34)
  check (focused.focus == 1 && focused.selection == 2 && !focused.dragging) "plus-head emphasis"
  check (decide (focused.positions = m.positions) && decide (focused.targets = m.targets)) "head changed layout"
  check (decide ((step focused 7 128).positions = m.positions)) "head reflowed unrelated people"
  let masked := {m with hidden:=(Array.replicate m.hidden.size true).set! 0 false}
  let revealed := step masked 2 500 316
  check ((List.range m.hidden.size).all fun i =>
    let related := i == 0 || m.graph.links.any (fun l => (l.source == 0 && l.target == i) || (l.target == 0 && l.source == i))
    revealed.hidden[i]! == !related) "head did not reveal only loaded direct neighbors"
  check (decide (revealed.positions = masked.positions) && decide (revealed.pinned = masked.pinned)) "reveal changed geometry or pins"
  let eased := step unsettled 7 16
  let one := step unsettled 7 32
  let two := step (step unsettled 7 16) 7 16
  check (decide (one.positions = two.positions) && one.accumulator == two.accumulator) "fixed-step time partition"
  check (decide ((step unsettled 7 1000000).positions = (step unsettled 7 128).positions)) "catchup not bounded"
  IO.println "PASS local reveal, no reflow and bounded easing"

  let hidden := step m 2 500 385
  check (hidden.hidden[0]! && hidden.selection == 0 && !hidden.dragging) "minus-foot hide"
  check (hidden.focus == m.focus) "hide changed unrelated emphasis"
  check (decide (hidden.positions = m.positions) && decide (hidden.targets = m.targets)) "hide changed geometry or targets"
  check (decide ((step hidden 7 128).positions = m.positions)) "hide reflowed unrelated people"
  let hiddenPinned := step released 2 620 445
  check (hiddenPinned.hidden[0]! && hiddenPinned.pinned[0]! && decide (hiddenPinned.positions = released.positions)) "hide changed manual pin"
  roundtrip hidden
  check (hidden.scene.data != m.scene.data) "hidden geometry unchanged"
  check (hidden.scene.wgsl == m.scene.wgsl && hidden.scene.data.length == m.scene.data.length) "hidden node changed pipeline layout"
  IO.println "PASS hide and stable shader slots"

  let paused := step focused 5 49
  check (!paused.animating && decide ((step paused 7 128).positions = paused.positions)) "pause"
  let resized := step released 1 320 240
  check (resized.selection == released.selection && resized.width == 320 && resized.height == 240) "resize selection"
  check (resized.scene.wgsl == m.scene.wgsl && resized.scene.shapes.length == m.scene.shapes.length) "resize changed shader layout"
  check (((resized.scene.shapes.take (graph.links.size*3+graph.people.size*32)).filter fun shape => match shape with
    | .glyph _ _ rows _ => rows.row0 != 0 || rows.row1 != 0 || rows.row2 != 0 || rows.row3 != 0 || rows.row4 != 0 || rows.row5 != 0 || rows.row6 != 0
    | _ => false).length < 8*12) "small viewport labels not padded with blank glyphs"
  let reset := step hiddenPinned 5 15
  check (decide (reset.positions = m.positions) && reset.hidden.all (!·) && reset.pinned.all (!·) && reset.selection == 0 && !reset.dragging) "reset clears pins"
  let closed := step captured 5 53
  check (closed.closed && !closed.dragging && decide (step closed 7 128 = closed)) "close"
  check (Model.decode "{}" == none) "invalid model accepted"
  check (Model.decode (toStringCompact (replaceField m.toJson "pinned" (.array []))) == none) "short pin table accepted"
  check (Model.decode (toStringCompact (replaceField m.toJson "pinned" (.array (List.replicate 8 (.number "1"))))) == none) "nonboolean pin accepted"
  check (Model.decode (toStringCompact (replaceField m.toJson "selection" (.number "9"))) == none) "out of range selection accepted"
  IO.println "PASS pause, resize, reset, close and invalid model"
  for state in [m,captured,dragged,released,focused,eased,hidden,paused,resized,reset,closed,masked,revealed,unsettled,animated,hiddenPinned] do
    roundtrip state
    check (state.scene.wgsl == m.scene.wgsl && state.scene.data.length == m.scene.data.length) "state changed persistent pipeline layout"
  let namesText := "@prefix f: <http://xmlns.com/foaf/0.1/> . " ++
    "<https://example.org/a> a f:Person; f:name \"https://example.org/a\" . " ++
    "<https://example.org/people/carol> a f:Person . <https://example.org/people#dave> a f:Person . " ++
    "_:x a f:Person . <https://example.org/zoe> a f:Person; f:name \"Zo\\u00EB\" . " ++
    "<https://example.org/team/?q=1#> a f:Person . <urn:person:anonymous> a f:Person ."
  let namesGraph ← match FoafGraph.fromTurtle namesText none graphLimits with
    | .ok g => pure g | .error e => throw (IO.userError e)
  let names := initial namesGraph 1000 700
  for i in List.range namesGraph.people.size do
    let some p := namesGraph.people[i]? | throw (IO.userError "missing test person")
    let label := displayName names i
    if p.id == "iri:https://example.org/a" then check (label == "https://example.org/a") "explicit URI-valued literal shortened"
    else if p.id == "iri:https://example.org/people/carol" then check (label == "carol") "IRI last path segment"
    else if p.id == "iri:https://example.org/people#dave" then check (label == "dave") "IRI fragment"
    else if p.id == "iri:https://example.org/zoe" then check (label == "Zoë") "Unicode literal changed"
    else if p.id == "iri:https://example.org/team/?q=1#" then check (label == "team") "query/trailing-fragment fallback"
    else check (label == "PERSON " ++ toString (i+1)) "blank fallback label"
  let selectedFrame ← match parseJson (response released []) with
    | .ok j => pure j | .error _ => throw (IO.userError "invalid frame JSON")
  check (selectedFrame.getString? "selectedId" == (graph.people[0]?.map (·.id))) "selected RDF identity metadata"
  roundtrip names
  IO.println "PASS explicit names, compact fallbacks and full RDF metadata"

  let editing := step m 5 37 2 -- Cmd-L
  check (editing.editing && editing.anchor == 0 && editing.cursor == editing.address.length) "Cmd-L selection"
  let entered := (insertText editing "ab🙂CD").model
  check (entered.address == "ab🙂CD" && entered.cursor == 5) "Unicode scalar insertion"
  let left := step entered 5 123
  let selected := step left 5 123 1
  check (selectedText selected == "C") "shift-arrow selection"
  let copied := transitionModel selected 5 8 2
  check (copied.clipboardWrite == some "C" && copied.model.address == selected.address) "copy selection"
  let cut := transitionModel selected 5 7 2
  check (cut.clipboardWrite == some "C" && cut.model.address == "ab🙂D") "cut selection"
  let pasted := (insertText cut.model "xy").model
  let scalar := step pasted 9 0x1F4A1
  let repeated := ((List.range 3).foldl (fun n _ => step n 9 97) scalar)
  check (repeated.address == "ab🙂xy💡aaaD") "committed key repeat"
  check ((step entered 5 15).address == entered.address) "printable key5 double inserts/resets"
  let request := transitionModel repeated 5 9 2
  check (request.clipboardRead && !((transitionModel request.model 7 16 0).clipboardRead)) "clipboard read is sticky"
  let pasteFrame ← match parseJson (response request.model request.commands false request.clipboardWrite request.clipboardRead) with
    | .ok j => pure j | .error _ => throw (IO.userError "clipboard response JSON")
  check (pasteFrame.getBool? "clipboardRead" == some true) "clipboard request missing"
  let laterFrame ← match parseJson (response request.model []) with
    | .ok j => pure j | .error _ => throw (IO.userError "later response JSON")
  check (laterFrame.field? "clipboardRead" == none && laterFrame.field? "clipboardWrite" == none) "clipboard fields persisted"
  let all := step repeated 5 0 2
  let bounded := (insertText all (String.ofList (List.replicate 600 'x'))).model
  check (bounded.address.length == 512 && bounded.cursor == 512) "address limit"
  check (bounded.message == "Address truncated to 512 Unicode scalars") "address truncation not reported"
  let oversizeFrame ← match parseJson (insertResponse editing.encode (String.ofList (List.replicate 65537 'x'))) with
    | .ok j => pure j | .error _ => throw (IO.userError "oversize clipboard frame JSON")
  check (oversizeFrame.field? "error" == none) "oversize paste is fatal"
  let some oversize := (oversizeFrame.getString? "model").bind Model.decode | throw (IO.userError "oversize paste lost model")
  check (oversize.address == editing.address && oversize.message == "Clipboard too large - limit 65536 Unicode scalars") "oversize paste changed address or omitted status"
  let readFailure := transitionModel editing 10 1 0
  let writeFailure := transitionModel editing 10 2 0
  check (readFailure.model.message == "Clipboard read unavailable" && writeFailure.model.message == "Clipboard write failed") "clipboard transport failure status"
  check (!readFailure.clipboardRead && readFailure.clipboardWrite == none && readFailure.model.address == editing.address) "clipboard failure repeated an effect"
  check ((step bounded 9 0xD800).address == bounded.address) "surrogate accepted"
  check ((step bounded 9 0x110000).address == bounded.address) "invalid scalar accepted"
  check ((insertResponse bounded.encode (String.singleton (Char.ofNat 0))).startsWith "{\"error\":") "NUL clipboard accepted"
  check (Model.decode (toStringCompact (replaceField editing.toJson "cursor" (.number "8192"))) == none) "invalid cursor accepted"
  for state in [editing,entered,left,selected,copied.model,cut.model,pasted,scalar,repeated,request.model,bounded] do
    roundtrip state
    check (state.scene.wgsl == m.scene.wgsl && state.scene.data.length == m.scene.data.length) "editor changed shader layout"
  IO.println "PASS Unicode editing, selection, clipboard effects and repeated keys"

  let localAddress :=  (insertText (step names 5 37 2) "https://example.org/people/carol").model
  let selectedLocal := step {localAddress with hidden:=Array.replicate localAddress.hidden.size true} 5 36
  let some person := names.graph.people[selectedLocal.selection-1]? | throw (IO.userError "local navigation did not select")
  check (person.id == "iri:https://example.org/people/carol" && !selectedLocal.editing && !selectedLocal.hidden[selectedLocal.selection-1]!) "local URI navigation"
  check (decide (selectedLocal.positions = names.positions)) "local URI navigation moved people"
  let unknown := (insertText (step names 5 37 2) "https://not-loaded.example/Person").model
  let notFound := step unknown 5 36
  check (notFound.editing && notFound.message == "Not in loaded graph - no network request" && notFound.selection == names.selection) "unknown URI behavior"
  check (!(step editing 5 53).editing && !(step editing 5 53).closed) "Escape editing closes app"
  check ((step m 2 500 28).editing) "address bar pointer focus"
  check (!(step (step m 2 500 28) 2 500 350).editing) "graph click did not blur address"
  let small := step m 1 192 128
  check (small.width == 192 && small.height == 128) "small physical viewport clamped away"
  check ((step small 2 96 64).selection == 1) "small viewport pointer and person disagree"
  let tiny := step m 1 16 16
  check (tiny.width == 16 && tiny.height == 16) "minimum viewport coordinates"
  -- At this deliberately crowded size, the drawn foot sits over the body.
  -- Picking must follow the foreground control instead of the old body box.
  check ((tiny.pick 8 8).map PaintedPart.target == some (.person 0 2)) "tiny painted foot priority"
  check ((step tiny 2 8 8).hidden[0]!) "tiny painted foot action"
  roundtrip small
  roundtrip tiny
  roundtrip selectedLocal
  roundtrip notFound
  IO.println "PASS local address navigation, focus and cursor validation"
  let alone := {m with hidden:=(Array.replicate m.hidden.size true).set! 0 false}
  let wide := {alone with width:=2000,height:=700}
  check ((wide.pick 1018 316).map PaintedPart.target == some (.person 0 0)) "wide viewport stretched head hit"
  check ((alone.pick 512 385).map PaintedPart.target == some (.person 0 0)) "foot radius exceeds drawing"
  check ((step alone 2 570 330).selection == 0) "blank card corner picked"
  let tall := {alone with width:=1000,height:=1400}
  check ((tall.pick 500 650).map PaintedPart.target != some (.person 0 1)) "tall viewport stretched head hit"
  let overlap := {m with
    hidden:=((Array.replicate m.hidden.size true).set! 0 false).set! 1 false
    positions:=m.positions.set! 1 ⟨500,316⟩}
  check ((overlap.pick 500 316).map PaintedPart.target == some (.person 1 0)) "front person did not occlude rear head"
  let underChrome := {alone with positions:=alone.positions.set! 0 ⟨500,100⟩}
  check ((underChrome.pick 500 55).map PaintedPart.target == some .blocked) "chrome forwarded a click to a hidden-under-header control"
  check ((step underChrome 2 500 55).selection == 0) "blocked chrome selected a person"
  check ((alone.pick (-1) 350).isNone && (alone.pick 1000 350).isNone) "outside canvas picked"
  check (m.parts.all fun part => (NativeGeometry.hit part.shape 0 0).isSome) "unsupported picking geometry introduced"
  check (alone.layoutChecks.length == 1 && alone.layoutChecks.all (fun (_,c) => c.accepted)) "hidden people entered footprint audit"
  check (overlap.layoutChecks.any (fun (_,c) => !c.accepted && c.overlapSum > 0)) "actual drawn overlap not detected"
  check (m.layoutChecks.all fun (_,c) => c.accepted) "default layout budget"
  IO.println "PASS shared drawing/picking geometry, paint order and overlap reports"
  IO.println "10 FOAFNaut native state test groups passed (no GPU)"

#eval runTests ["../../labs/demos/foafnaut/foaf/fixtures/people.ttl"]
end NativeFoafNautTests
