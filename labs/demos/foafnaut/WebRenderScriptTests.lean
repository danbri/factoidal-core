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
-- The commands of page scripts in the engine (WebScripts): a replay makes the same nodes.
private def list := (dom.getElementById 0 "change").getD 0
private def made := dom.size
#guard match WebRenderScript.applyCommands dom (.array [
    .object [("op",.string "createElement"),("name",.string "li"),("nodeId",.number (toString made))],
    .object [("op",.string "createNode"),("kind",.number "0"),("data",.string "new item"),("nodeId",.number (toString (made+1)))],
    .object [("op",.string "appendChild"),("parent",.number (toString made)),("nodeId",.number (toString (made+1)))],
    .object [("op",.string "insertBefore"),("parent",.number (toString ((dom.get list).parent.getD 0))),
      ("nodeId",.number (toString made)),("before",.number (toString list))],
    .object [("op",.string "removeAttribute"),("nodeId",.number (toString list)),("name",.string "id")]]) with
  | .ok result => result.textContent made == some "new item" && result.getElementById 0 "change" == none
  | .error _ => false
-- A replay that would make another node number is refused.
#guard match WebRenderScript.applyCommands dom (.array [
    .object [("op",.string "createElement"),("name",.string "li"),("nodeId",.number (toString (made+5)))]]) with
  | .error _ => true | _ => false
-- An unknown field is refused.
#guard match WebRenderScript.applyCommands dom (.array [
    .object [("op",.string "removeChild"),("parent",.number "1"),("nodeId",.number "2"),("extra",.bool true)]]) with
  | .error _ => true | _ => false

-- The page script setting: BubblePopJS by default in a native host, QuickJS-NG on the Hub.
#guard WebRenderScript.defaultEngine "native" == "bubblepop" && WebRenderScript.defaultEngine "hub" == "quickjs"
#guard WebRenderScript.setting? "QuickJS-NG" == some "quickjs" && WebRenderScript.setting? "BubblePopJS" == some "bubblepop"
#guard WebRenderScript.setting? "lean" == none && WebRenderScript.setting? "verifiedjs" == none && WebRenderScript.setting? "x" == none
#guard (WebRenderScript.plan "" 1).marker == "JS BUBBLEPOP" && (WebRenderScript.plan "" 1 "hub").marker == "JS QUICKJS-NG"
#guard (WebRenderScript.plan "none" 1).marker == "JS OFF" && !(WebRenderScript.plan "none" 1).run
#guard (WebRenderScript.plan "bubblepop" 0).marker == "" && !(WebRenderScript.plan "bubblepop" 0).run
#guard (WebRenderScript.plan "quickjs" 1 "native" "no guest module").marker == "JS REFUSED"
#guard ((WebRenderScript.choicesHTML "quickjs").splitOn "class=\"tick\"").length == 2
-- BubblePopJS runs on the Hub and in the Foafnaut Wasm build when chosen; QuickJS-NG stays their default.
#guard (WebRenderScript.plan "bubblepop" 1 "hub").marker == "JS BUBBLEPOP" && (WebRenderScript.plan "bubblepop" 1 "hub").run
#guard (WebRenderScript.plan "bubblepop" 1 "wasm").run && (WebRenderScript.plan "" 1 "wasm").engine == "quickjs"
#guard ((WebRenderScript.choicesHTML "" "hub").splitOn "(default here)").length == 2
