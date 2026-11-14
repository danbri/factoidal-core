// Keys of a host on the one input path (WebScripts action `key`, L4Factoidal.WebDriver.HostKeys,
// record docs/designissues/2026-11-14-input-webdriver.md "One key path for every host"):
// - the window's typed text and key codes reach the page as trusted keydown/keypress/keyup at
//   the focused element, as test_driver's keys do;
// - a key in a focused text control edits its value (beforeinput, then input), Backspace deletes;
// - keyDefault: false when the page cancels the keydown or the key edits, true otherwise.
// BubblePopJS sessions (no guest module). Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

const url="file:///keys.html";
const page=`<!doctype html><html><body><input id=i><div id=d tabindex=0>d</div>
<script>
for (const t of ['keydown','keypress','keyup','beforeinput','input'])
  document.addEventListener(t, e => console.log(t + ' ' + e.target.id + ' ' + (e.key ?? e.inputType) + ' ' + e.isTrusted +
    (e.ctrlKey ? ' ctrl' : '') + (e.shiftKey ? ' shift' : '')));
document.getElementById('d').addEventListener('keydown', e => { if (e.key === 'ArrowDown') e.preventDefault(); });
document.getElementById('i').focus();
</script></body></html>`;

Deno.test({name:"Host keys: typed text and key codes on the trusted path, text controls, keyDefault",
  ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  if(!engine.scriptInfo().ops.includes("key")){console.log("this engine has no key action");return;}
  let turn=engine.scriptSession(page,{action:"start",url,resources:[],width:400,height:300,layout:{url},engine:"bubblepop"}) as ScriptTurn;
  assert.deepEqual(turn.errors,[]);
  const key=(request:Record<string,unknown>)=>{
    turn=engine.scriptSession("",{action:"key",session:turn.session,...request}) as ScriptTurn;
    assert.deepEqual(turn.errors,[]);
    return turn;
  };
  // Typed text: the events of Element Send Keys at the focused input, and its value.
  let t=key({text:"a"});
  for(const line of ["keydown i a true","beforeinput i insertText true","input i insertText true","keyup i a true"])
    assert.ok(t.logs.includes(line),t.logs.join("\n"));
  assert.equal(t.keyDefault,false);
  key({text:"B"});
  // Backspace (macOS key code 51) deletes backward.
  t=key({mac:51,modifiers:0});
  assert.ok(t.logs.includes("beforeinput i deleteContentBackward true"),t.logs.join("\n"));
  // Control-A (code 0, bit 8): a shortcut, no text.
  t=key({mac:0,modifiers:8});
  assert.ok(t.logs.includes("keydown i a true ctrl"),t.logs.join("\n"));
  assert.ok(!t.logs.some(l=>l.startsWith("input ")),t.logs.join("\n"));
  // A character key without Command or Control sends nothing: its text follows.
  t=key({mac:0,modifiers:0});
  assert.deepEqual(t.logs,[]);
  // The DOM key value of the Hub.
  t=key({key:"x",modifiers:0});
  assert.ok(t.logs.includes("input i insertText true"),t.logs.join("\n"));
  turn=engine.scriptSession("",{action:"close"}) as ScriptTurn;
}});
