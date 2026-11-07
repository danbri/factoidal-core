import WebRenderScript
open L4Factoidal

private def source := "<!doctype html><p id='message'>before</p><button id='change'>change</button><script>document.getElementById('message').textContent = 'after';</script>"
private def dom := DOM.parseHtmlDocument source
private def target := (dom.getElementById 0 "message").getD 0
private def command (id : Nat) (value : String) : JSON.Json :=
  .object [("op",.string "setTextContent"),("nodeId",.number (toString id)),("value",.string value)]

#guard match WebRenderScript.applyCommands dom (.array [command target "after"]) with
  | .ok result => result.textContent target == some "after"
  | .error _ => false
#guard match WebRenderScript.applyCommands dom (.array [command 1048576 "bad"]) with
  | .error _ => true | _ => false
#guard match WebRenderScript.applyCommands dom (.array [command 0 "bad"]) with
  | .error _ => true | _ => false
#guard match WebRenderScript.applyCommands dom (.array [
    .object [("op",.string "setAttribute"),("nodeId",.number (toString target)),
      ("name",.string "data-value"),("value",.string "yes")]]) with
  | .ok result => ((result.get target).attrs.find? (·.lname == "data-value")).map (·.value) == some "yes"
  | .error _ => false
#guard match WebRenderScript.applyCommands dom (.array [
    .object [("op",.string "setAttribute"),("nodeId",.number (toString target)),
      ("name",.string "has space"),("value",.string "bad")]]) with
  | .error _ => true | _ => false
#guard match (WebRenderScript.snapshot dom).field? "scripts" with
  | some (.array scripts) => scripts.length == 1
  | _ => false
#guard match WebRenderScript.applyCommands dom (.array (List.replicate 4097 (command target "bad"))) with
  | .error _ => true | _ => false

/-! Issue 1271: element creation, tree changes, attributes, classes, styles, queries,
history compaction and the page script setting. -/
private def page := DOM.parseHtmlDocument "<!doctype html><body><ul id='list' class='a b'><li class='item'>one</li></ul><svg id='chart'><rect id='bar'/></svg><p id='out'>x</p></body>"
private def idOf (name : String) : Nat := (page.getElementById 0 name).getD 0
private def obj (fields : List (String × String)) (ids : List (String × Nat)) : JSON.Json :=
  .object (ids.map (fun (k,v) => (k,.number (toString v))) ++ fields.map (fun (k,v) => (k,.string v)))
private def run (commands : List JSON.Json) : Except String DOM.Dom := WebRenderScript.applyCommands page (.array commands)
private def create (id : Nat) (tag space : String) : JSON.Json := obj [("op","createElement"),("tagName",tag),("namespace",space)] [("nodeId",id)]
private def append (parent child : Nat) : JSON.Json := obj [("op","appendChild")] [("nodeId",parent),("child",child)]
private def text (id : Nat) (value : String) : JSON.Json := obj [("op","setTextContent"),("value",value)] [("nodeId",id)]
private def attr (id : Nat) (name value : String) : JSON.Json := obj [("op","setAttribute"),("name",name),("value",value)] [("nodeId",id)]
private def ok (r : Except String DOM.Dom) (f : DOM.Dom → Bool) : Bool := match r with | .ok d => f d | .error _ => false
private def refused (r : Except String DOM.Dom) : Bool := match r with | .error _ => true | .ok _ => false

-- createElement takes the next arena id, and only that id.
#guard ok (run [create page.size "li" "html",text page.size "two",append (idOf "list") page.size]) fun d =>
  d.textContent (idOf "list") == some "onetwo" && (d.get page.size).lname == "li"
#guard refused (run [create (page.size+1) "li" "html"])
#guard refused (run [create page.size "script" "html"]) && refused (run [create page.size "template" "html"])
-- An SVG element keeps the SVG namespace and the case of its name.
#guard ok (run [create page.size "linearGradient" "svg",append (idOf "chart") page.size]) fun d =>
  (d.get page.size).ns == some DOM.svgNS && (d.get page.size).lname == "linearGradient" && (d.get page.size).parent == some (idOf "chart")
-- appendChild moves a connected element; removeChild of a non-child is NotFoundError.
#guard ok (run [append (idOf "out") (idOf "bar")]) fun d => (d.get (idOf "bar")).parent == some (idOf "out")
#guard refused (run [obj [("op","removeChild")] [("nodeId",idOf "list"),("child",idOf "bar")]])
#guard ok (run [obj [("op","removeChild")] [("nodeId",idOf "chart"),("child",idOf "bar")]]) fun d => (d.get (idOf "bar")).parent == none
-- A cycle is HierarchyRequestError.
#guard refused (run [append (idOf "out") 0])
-- removeAttribute, also on an SVG element.
#guard ok (run [attr (idOf "bar") "width" "5",obj [("op","removeAttribute"),("name","width")] [("nodeId",idOf "bar")]]) fun d =>
  WebRenderScript.attributeValue d (idOf "bar") "width" == none
-- classList: an ordered set; toggle twice is the start value; a space in a token is refused.
private def classes (action token : String) : JSON.Json := obj [("op","classList"),("action",action),("token",token)] [("nodeId",idOf "list")]
#guard ok (run [classes "add" "c",classes "add" "a",classes "remove" "b"]) fun d => WebRenderScript.attributeValue d (idOf "list") "class" == some "a c"
#guard ok (run [classes "toggle" "z",classes "toggle" "z"]) fun d => WebRenderScript.attributeValue d (idOf "list") "class" == some "a b"
#guard refused (run [classes "add" "x y"]) && refused (run [classes "add" ""])
-- style: replace in place, append, remove with an empty value.
private def style (property value : String) : JSON.Json := obj [("op","setStyleProperty"),("property",property),("value",value)] [("nodeId",idOf "out")]
#guard ok (run [style "color" "red",style "width" "10px",style "Color" "blue"]) fun d =>
  WebRenderScript.attributeValue d (idOf "out") "style" == some "color: blue; width: 10px"
#guard ok (run [style "color" "red",style "color" ""]) fun d => WebRenderScript.attributeValue d (idOf "out") "style" == none
#guard refused (run [style "color" "red; background: x"])
-- A repeated text write changes the Text node in place: the arena does not grow.
#guard ok (run [text (idOf "out") "1",text (idOf "out") "2",text (idOf "out") "3"]) fun d => d.size == page.size && d.textContent (idOf "out") == some "3"
-- Queries use the cascade's selector matcher, in tree order.
private def ids (q : String) : List Nat := match WebRenderScript.query page 0 q with | .ok v => v | .error _ => [999999]
#guard ids ".item" == [idOf "list" + 1]
#guard ids "#chart rect" == [idOf "bar"]
#guard ids "ul, p" == [idOf "list",idOf "out"]
#guard (match WebRenderScript.query page 0 "ul > li" with | .error _ => true | .ok _ => false)
-- Compaction: an animation of 5000 writes replays to the same arena in a few commands.
private def frames : List JSON.Json := (List.range 5000).flatMap fun i =>
  [attr (idOf "bar") "height" (toString i),text (idOf "out") (toString i),style "width" s!"{i}px"]
#guard match WebRenderScript.compact page (.array ([create page.size "li" "html",append (idOf "list") page.size] ++ frames)) with
  | .ok (.array kept) => kept.length == 5 && (match run kept with
      | .ok d => WebRenderScript.attributeValue d (idOf "bar") "height" == some "4999" && d.textContent (idOf "out") == some "4999"
      | .error _ => false)
  | _ => false
-- The setting: QuickJS-NG is the default; None, a refusal and a stop each say so.
#guard WebRenderScript.defaultEngine == "quickjs" && WebRenderScript.setting? "QuickJS-NG" == some "quickjs" && WebRenderScript.setting? "x" == none
#guard (WebRenderScript.plan "quickjs" 2).run && (WebRenderScript.plan "quickjs" 2).marker == "JS QUICKJS-NG"
#guard !(WebRenderScript.plan "none" 2).run && (WebRenderScript.plan "none" 2).marker == "JS OFF"
#guard (WebRenderScript.plan "verifiedjs" 1 "not built").notice == "Page scripts refused (VerifiedJS): not built"
#guard (WebRenderScript.plan "quickjs" 1 "" "timeout").marker == "JS STOPPED" && (WebRenderScript.plan "quickjs" 0).marker == ""
-- The notice is the body's first element and is created after every script node.
#guard (WebRenderScript.withNotice page "refused").textContent ((page.getElementById 0 "list").getD 0) == some "one" &&
  (WebRenderScript.withNotice page "refused").size > page.size
