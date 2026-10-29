import L4Factoidal.XProc31.Atomic
import L4Factoidal.XPath4.Ixml

namespace L4Factoidal.XProc31

/-- Read host metadata without invoking a shell. Environment values stay in
the result document and are never emitted by diagnostic logging. -/
def osInfoStep : IO (Result (List Document)) := do
  if System.Platform.isWindows || System.Platform.isEmscripten then
    return unsupported "os-info host metadata APIs for this platform"
  try
    let uname ← IO.Process.output {cmd := "uname", args := #["-s", "-r", "-m"]}
    let user ← IO.Process.output {cmd := "id", args := #["-un"]}
    let environment ← IO.Process.output {cmd := "env", args := #["-0"]}
    if uname.exitCode != 0 || user.exitCode != 0 || environment.exitCode != 0 then
      return unsupported "os-info host metadata command unavailable"
    let fields := (uname.stdout.trimAscii.toString.splitOn " ").filter (· != "")
    let [osName,osVersion,architecture] := fields
      | return unsupported "os-info unexpected uname response"
    let home ← IO.getEnv "HOME"
    let some home := home | return unsupported "os-info home directory unavailable"
    let cwd ← IO.currentDir
    let variables := (environment.stdout.splitOn (String.singleton '\x00')).filterMap fun pair =>
      if pair.isEmpty then none else
      let parts := pair.splitOn "="
      match parts with
      | [] | [_] => none
      | name::value => some (XML.Node.element "c:environment"
          [⟨"name",name⟩,⟨"value",String.intercalate "=" value⟩] [])
    return .ok [{node := .element "c:result"
      [⟨"xmlns:c","http://www.w3.org/ns/xproc-step"⟩,
       ⟨"file-separator","/"⟩,⟨"path-separator",":"⟩,
       ⟨"os-architecture",architecture⟩,⟨"os-name",osName⟩,⟨"os-version",osVersion⟩,
       ⟨"cwd",cwd.toString⟩,⟨"user-name",user.stdout.trimAscii.toString⟩,⟨"user-home",home⟩] variables}]
  catch _ => return unsupported "os-info host metadata commands unavailable"

def invisibleXmlStep (step : XML.Node) (ports : List (String × List Document))
    (env : XPath4.Env) : Result (List Document) := do
  let [source] := (ports.lookup "source").getD []
    | error "XD0006" "invisible-xml requires one source document"
  if (← classifyMediaType source.contentType) != .text then
    error "XD0038" "invisible-xml source must be text" else pure ()
  let grammars := (ports.lookup "grammar").getD []
  if grammars.length > 1 then error "XC0211" "invisible-xml accepts at most one grammar" else pure ()
  let grammar ← match grammars with
    | [] => XPath4.Ixml.ixmlBNF.mapError (fun message => ({code := "XC0212", message} : ProcError))
    | grammar::_ => do
      let kind ← classifyMediaType grammar.contentType
      let compiled ← if kind == .text then pure (XPath4.Ixml.bnfOfText grammar.node.textContent)
        else if kind == .xml then pure (XPath4.Ixml.grammarOfXml (documentElement grammar) >>= XPath4.Ixml.compile)
        else error "XD0038" "invisible-xml grammar must be XML or text"
      compiled.mapError (fun message => ({code := "XC0212", message} : ProcError))
  let fail := (← option step "fail-on-error" env "true") != "false"
  let input := XPath4.Ixml.toCps source.node.textContent
  match XPath4.Ixml.parseCps grammar input with
  | .ok node _ => pure [{node}]
  | .fail position message =>
    if fail then error "XC0205" s!"invisible-xml input failed at {position}: {message}"
    else pure [{node := XPath4.Ixml.failElem input position message}]

/-- The wrapper uses the shared parser on arbitrary grammar/input text. -/
def invisibleXmlRegression : Bool := Id.run do
  let grammar : Document := {node := .text "word: [\"a\"-\"z\"]+.", contentType := "text/plain"}
  let source : Document := {node := .text "hello", contentType := "text/plain"}
  let step := XML.Node.element "p:invisible-xml" [] []
  let some [parsed] := (invisibleXmlStep step [("grammar",[grammar]),("source",[source])] {}).toOption | return false
  if parsed.node.elementTag != some "word" || parsed.node.textContent != "hello" || parsed.baseUri != "" then return false
  let bad := {source with node := .text "123"}
  let failed := invisibleXmlStep step [("grammar",[grammar]),("source",[bad])] {}
  if (match failed with | .error e => e.code != "XC0205" | _ => true) then return false
  let tolerant := XML.Node.element "p:invisible-xml" [⟨"fail-on-error","false"⟩] []
  let some [failure] := (invisibleXmlStep tolerant [("grammar",[grammar]),("source",[bad])] {}).toOption | return false
  return attr failure.node "ixml:state" == "failed"

end L4Factoidal.XProc31
