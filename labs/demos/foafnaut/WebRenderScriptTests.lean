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
