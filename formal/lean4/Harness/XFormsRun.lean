/-
Harness/XFormsRun — the W3C XForms 1.1 Test Suite (vendored unchanged at
`third_party/testing/xforms11`) run against `L4Factoidal.XForms.Model`.

The suite's pass conditions are written for a person. Each case is
classified in `tests/xforms11/classification.json` into one of four
groups, and a case that can be decided by machine has a sidecar
`tests/xforms11/expect/<case>.json` holding the sentence of the test
that states the pass condition (`quote`) and the scripted steps:

  * `do`: `activate` (DOMActivate on the control with this `label` or
    `id`), `setvalue` (the user enters `value`), `dispatch` (`event` to
    the element `id`);
  * `expect`: `control` (`value`, `prefix`, `relevant`, `readonly`,
    `required`, `valid` of the control with this `label` or `id`),
    `values` (the values of all such controls, in order), `no-value`
    (no such control shows a value), `absent` (no such control shows a
    value containing one of `values`), `all-shown` / `none-shown` (the
    controls of `kind` whose label ends with `contains`), `each-value`
    (every shown control of `kind` has a value containing `contains`,
    but for the listed exceptions), `message` /
    `no-message` (`contains`), `exception` (`name`: a fatal error of
    that name, or a message naming it), `no-fatal`, `event` /
    `no-event` (`name`), `focus` (the control with this `label` or `id`
    has the focus), `load` (`contains`); `control` also takes `alert`.
    Message and event checks look at the outputs since the last `do`.
    Values are compared after whitespace normalisation (the conditions
    are prose; instance data carries its indentation).

Groups: (a) model, (b) view model, (c) submission, (d) needs a human
reader. Group (d) is counted and listed, never scored. A case with no
sidecar, or whose run met something the engine reports as unsupported,
is unsupported, never a pass.

Usage (from `formal/lean4/`):
  lake build l4xforms && .lake/build/bin/l4xforms [--verbose] [--case NAME]
      [suite-dir] [tests-dir]
-/
import L4Factoidal.XForms.Model
import L4Factoidal.XForms.Theorems
import L4Factoidal.JSON.Parser

open L4Factoidal.XML
open L4Factoidal.XPath.Full
open L4Factoidal.XForms.Engine
open L4Factoidal.JSON

def readText (path : String) : IO (Option String) := do
  if !(← System.FilePath.pathExists path) then return none
  if ← System.FilePath.isDir path then return none
  let bytes ← try IO.FS.readBinFile path catch _ => return none
  match String.fromUTF8? bytes with
  | some s => return some s
  | none => return some (String.ofList (bytes.toList.map (fun b => Char.ofNat b.toNat)))

def parseDoc (src : String) : Option Document :=
  match parseDecodedXMLWith (fun _ => none) src with
  | .ok d => some d
  | .error _ => none

def normPath (p : String) : String :=
  let out := (p.splitOn "/").foldl (fun (acc : List String) s =>
    if s == ".." then
      (match acc with
       | [] => [".."]
       | ".." :: _ => ".." :: acc
       | _ :: r => r)
    else if s == "." || s == "" then acc else s :: acc) []
  (if p.startsWith "/" then "/" else "") ++ String.intercalate "/" out.reverse

def dirOf (p : String) : String := String.intercalate "/" ((p.splitOn "/").dropLast)

def has (hay needle : String) : Bool :=
  needle == "" || (hay.toLower.splitOn needle.toLower).length > 1

def normLabel (s : String) : String :=
  String.ofList ((normalizeSpaceStr s).toLower.toList.reverse.dropWhile (fun c => c == ':' || c == ' ')).reverse

def findCtls (view : List Ctl) (j : Json) : List Ctl :=
  view.filter (fun c =>
    (match j.getString? "id" with
     | some i => c.id == i
     | none => true) &&
    (match j.getString? "label" with
     | some l => normLabel c.label == normLabel l
     | none => true) &&
    (match j.getString? "kind" with
     | some k => c.kind == k
     | none => true))

def isFatal : Output → Bool
  | .fatal .. => true
  | _ => false

def isUnsupported : Output → Option String
  | .unsupported w => some w
  | _ => none

/-- Check one `expect` step; `none` when it holds. -/
def checkExpect (m : Model) (last all : List Output) (j : Json) : Option String :=
  let kind := (j.getString? "expect").getD ""
  let view := match m.view with
    | .ok v => v
    | .error _ => m.snap
  let needle := (j.getString? "contains").getD ""
  let name := (j.getString? "name").getD ""
  let msgs := last.filterMap (fun o => match o with
    | .message _ t => some t
    | _ => none)
  if kind == "message" then
    if msgs.any (fun t => has t needle) then none
    else some s!"no message containing '{needle}' (messages: {msgs})"
  else if kind == "no-message" then
    if msgs.any (fun t => has t needle) then some s!"a message containing '{needle}' was shown" else none
  else if kind == "exception" then
    if last.any (fun o => match o with
      | .fatal n _ => n == name
      | .message _ t => has t name
      | _ => false) then none
    else some s!"no {name}"
  else if kind == "no-fatal" then
    match all.find? isFatal with
    | some o => some s!"fatal error: {repr o}"
    | none => none
  else if kind == "event" then
    if last.any (fun o => match o with
      | .event n _ => n == name
      | _ => false) then none else some s!"event {name} was not dispatched"
  else if kind == "no-event" then
    if last.any (fun o => match o with
      | .event n _ => n == name
      | _ => false) then some s!"event {name} was dispatched" else none
  else if kind == "focus" then
    if (findCtls view j).any (fun c => m.focus == some c.el) then none
    else some "the focus is not in that control"
  else if kind == "load" then
    if last.any (fun o => match o with
      | .load u _ => has u needle
      | _ => false) then none else some s!"no load of '{needle}'"
  else if kind == "values" then
    let got := ((findCtls view j).filter (·.relevant)).map (fun c => normalizeSpaceStr c.value)
    let want := ((j.getStringArray? "values").getD []).map normalizeSpaceStr
    if got == want then none else some s!"values {got}, expected {want}"
  else if kind == "absent" then
    let bad := (j.getStringArray? "values").getD []
    match ((findCtls view j).filter (·.relevant)).find? (fun c => bad.any (fun w => has c.value w)) with
    | some c => some s!"a control shows '{c.value}'"
    | none => none
  else if kind == "all-shown" then
    -- every control of this kind whose label ends with the text is available, and there is one
    let cs := (view.filter (fun c => (j.getString? "kind").all (· == c.kind))).filter
      (fun c => (normLabel c.label).endsWith needle.toLower)
    if cs.isEmpty then some s!"no control with a label ending in '{needle}'"
    else match cs.find? (fun c => !c.relevant) with
      | some c => some s!"'{c.label}' is not shown"
      | none => none
  else if kind == "none-shown" then
    match ((view.filter (fun c => (j.getString? "kind").all (· == c.kind))).filter
        (fun c => (normLabel c.label).endsWith needle.toLower)).find? (·.relevant) with
    | some c => some s!"'{c.label}' is shown"
    | none => none
  else if kind == "each-value" then
    -- every shown control of this kind has a value containing the text; the values
    -- that do not are empty or name one of the listed exceptions, at most one each
    let exc := (j.getStringArray? "except").getD []
    let cs := (findCtls view j).filter (·.relevant)
    let others := cs.filter (fun c => !has c.value needle)
    if cs.isEmpty then some "no such control is shown"
    else if others.length > exc.length then
      some s!"{others.length} values do not contain '{needle}': {(others.map (·.value)).take 4}"
    else match others.find? (fun c => c.value != "" && !exc.any (fun w => has c.value w)) with
      | some c => some s!"value '{c.value}' does not contain '{needle}'"
      | none => none
  else if kind == "no-value" then
    if ((findCtls view j).filter (·.relevant)).any (fun c => normalizeSpaceStr c.value != "") then
      some "the control shows a value"
    else none
  else if kind == "control" then
    match findCtls view j with
    | [] => some s!"no control matches {(j.getString? "label").getD ((j.getString? "id").getD "?")}"
    | c :: _ =>
      let chk (field : String) (actual : Bool) : Option String :=
        match j.getBool? field with
        | some b => if b == actual then none else some s!"{field} is {actual}, expected {b}"
        | none => none
      let v := match j.getString? "value" with
        | some w => if normalizeSpaceStr c.value == normalizeSpaceStr w then none
                    else some s!"value '{c.value}', expected '{w}'"
        | none => none
      let p := match j.getString? "prefix" with
        | some w => if c.value.startsWith w then none else some s!"value '{c.value}' does not start with '{w}'"
        | none => none
      let al := match j.getString? "alert" with
        | some w => if normalizeSpaceStr c.alert == normalizeSpaceStr w then none
                    else some s!"alert '{c.alert}', expected '{w}'"
        | none => none
      [v, p, al, chk "relevant" c.relevant, chk "readonly" c.readonly, chk "required" c.required,
       chk "valid" c.valid].findSome? id
  else some s!"unknown expectation '{kind}'"

/-- Run one case: ("pass" | "fail" | "unsupported", reason). -/
def runCase (suite file : String) (side : Json) : IO (String × String) := do
  let path := suite ++ "/" ++ file
  let some src ← readText path | return ("unsupported", "cannot read the test document")
  let some doc := parseDoc src
    | return ("unsupported", "the XML parser does not accept the test document")
  let fm := Form.ofNode doc.root
  let uris := (fm.els.toList.flatMap (fun e =>
    (["src", "resource"].filterMap e.attr) ++ (((e.attr "schema").map splitWs).getD []))).eraseDups
  let mut res : List (String × String) := []
  for u in uris do
    if (u.splitOn ":").length == 1 && !u.startsWith "#" then
      match ← readText (normPath (dirOf path ++ "/" ++ u)) with
      | some c => res := res ++ [(u, c)]
      | none => pure ()
  let now := (side.getString? "now").getD "2026-11-14T05:00:00Z"
  let tz : Int := match side.field? "tz" with
    | some (.number s) => (s.toInt?).getD 0
    | _ => 0
  let (m0, out0) := step (Model.ofForm fm res now tz) .init
  let mut m := m0
  let mut last := out0
  let mut all := out0
  let mut failure : Option String := none
  let mut checks := 0
  for s in (side.getArray? "steps").getD [] do
    if failure.isSome then break
    match s.getString? "do" with
    | some act =>
      let view := match m.view with
        | .ok v => v
        | .error _ => m.snap
      if act == "dispatch" then
        match (s.getString? "id").bind m.form.byId with
        | none => failure := some s!"no element for dispatch {repr s}"
        | some el =>
          let (m', o) := step m (.dispatch ((s.getString? "event").getD "") el)
          m := m'; last := o; all := all ++ o
      else
        let cs := findCtls view s
        match (cs.find? (·.relevant)).orElse (fun _ => cs.head?) with
        | none => failure := some s!"no control for step {(s.getString? "label").getD ((s.getString? "id").getD "?")}"
        | some c =>
          let ev := if act == "setvalue" then Event.setValue c.el c.iter ((s.getString? "value").getD "")
                    else Event.activate c.el c.iter
          let (m', o) := step m ev
          m := m'; last := o; all := all ++ o
    | none =>
      checks := checks + 1
      match checkExpect m last all s with
      | some why => failure := some why
      | none => pure ()
  match all.findSome? isUnsupported with
  | some w => return ("unsupported", w)
  | none =>
    match failure with
    | some why => return ("fail", why)
    | none => if checks == 0 then return ("unsupported", "the sidecar has no checks") else return ("pass", "")

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  unsup : Nat := 0
deriving Inhabited

def Tally.show (t : Tally) : String :=
  s!"{t.pass} pass, {t.fail} fail, {t.unsup} unsupported (out of {t.pass + t.fail + t.unsup})"

def Tally.add (t : Tally) (r : String) : Tally :=
  if r == "pass" then { t with pass := t.pass + 1 }
  else if r == "fail" then { t with fail := t.fail + 1 }
  else { t with unsup := t.unsup + 1 }

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let rec optVal : List String → String → Option String
    | k :: v :: rest, key => if k == key then some v else optVal (v :: rest) key
    | _, _ => none
  let only := optVal args "--case"
  let positional := (args.filter (fun a => !a.startsWith "--")).filter (fun a => some a != only)
  let suite := positional.head?.getD "../../third_party/testing/xforms11/Test/XForms1.1/Edition1"
  let tests := (positional.drop 1).head?.getD "../../tests/xforms11"
  let t0 ← IO.monoMsNow
  match (← readText (tests ++ "/classification.json")).bind (fun s => (parseJson s).toOption) with
  | none =>
    IO.println s!"l4xforms: cannot read {tests}/classification.json"
    return 1
  | some cls =>
    let cases := (cls.getArray? "cases").getD []
    let mut chapters : List String := []
    let mut tallies : List ((String × String) × Tally) := []
    let mut human : List (String × String × String) := []
    for c in cases do
      let name := (c.getString? "name").getD "?"
      if only.isSome && only != some name then continue
      let file := (c.getString? "file").getD ""
      let group := (c.getString? "group").getD "?"
      let chapter := (c.getString? "chapter").getD "?"
      if !chapters.contains chapter then chapters := chapters ++ [chapter]
      if group == "d" then
        human := human ++ [(chapter, name, (c.getString? "reason").getD "")]
      else
        let side ← readText (tests ++ "/expect/" ++ name ++ ".json")
        let (r, why) ← match side.bind (fun s => (parseJson s).toOption) with
          | none => pure ("unsupported", "no sidecar expectation")
          | some j => runCase suite file j
        if verbose && r != "pass" then IO.println s!"  {r} [{group}] {name}: {why}"
        if only.isSome then IO.println s!"  {r} [{group}] {name}: {why}"
        let key := (chapter, group)
        let old := ((tallies.find? (·.1 == key)).map (·.2)).getD {}
        tallies := (key, old.add r) :: tallies.filter (·.1 != key)
    let groups := [("a", "model"), ("b", "view model"), ("c", "submission")]
    let sum (g : String) : Tally := (tallies.filter (·.1.2 == g)).foldl
      (fun (acc : Tally) p => { pass := acc.pass + p.2.pass, fail := acc.fail + p.2.fail, unsup := acc.unsup + p.2.unsup }) {}
    for ch in chapters do
      for (g, gname) in groups do
        match tallies.find? (·.1 == (ch, g)) with
        | some (_, t) => IO.println s!"{ch} ({g}) {gname}: {t.show}"
        | none => pure ()
      let n := (human.filter (·.1 == ch)).length
      if n > 0 then IO.println s!"{ch} (d) needs a human reader: {n}"
    for (g, gname) in groups do
      IO.println s!"total ({g}) {gname}: {(sum g).show}"
    IO.println s!"total (d) needs a human reader: {human.length} (not scored)"
    if verbose then
      for (ch, name, why) in human do
        IO.println s!"  human reader: {ch} {name}: {why}"
    let t1 ← IO.monoMsNow
    IO.println s!"elapsed: {t1 - t0} ms"
    return 0
