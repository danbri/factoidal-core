import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.BinaryDocument
import L4Factoidal.XProc31.Loading

namespace L4Factoidal.XProc31

structure ProcessBytes where
  stdout : ByteArray
  stderr : ByteArray
  exitCode : UInt32

/-- Drain both output pipes while writing the input. No shell interprets the
command or argument strings. The parent runner owns process-group timeouts. -/
def executeProcessBytes (args : IO.Process.SpawnArgs) (input : ByteArray) : IO ProcessBytes := do
  let (stdin,child) ← (← IO.Process.spawn {args with stdin := .piped, stdout := .piped, stderr := .piped}).takeStdin
  let writer ← IO.asTask (do stdin.write input; stdin.flush) Task.Priority.dedicated
  let stdout ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readBinToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  let _ := writer.get -- A child may close its input early; its exit status is authoritative.
  pure {stdout,stderr,exitCode}

def processArguments (step : XML.Node) (env : XPath4.Env) : Result (List String) := do
  match (named step "with-option").find? (fun node => attr node "name" == "args") with
  | some node => pure ((← eval (attr node "select") env).map (fun item => seqString env [item]))
  | none => if XML.hasAttr "args" step.elementAttrs then pure [← option step "args" env] else pure []

def processOutputDocument (bytes : ByteArray) (contentType : String) : IO (Result (List Document)) := do
  if bytes.isEmpty then return .ok []
  let result ← documentFromBytes "" contentType bytes
  match result with
  | .ok doc => return .ok [{doc with baseUri := ""}]
  | .error e =>
    -- Process text decoding follows the replacement-character convention for
    -- malformed UTF-8; explicit character encodings use the existing codecs.
    let media := (parseMediaType contentType).toOption
    if media.any (fun m => m.kind == .text && (m.parameters.lookup "charset").isNone) then
      let text := String.ofList (XPath4.utf8Decode (bytes.size+1) (bytes.toList.map UInt8.toNat))
      return .ok [{node := .text text, contentType}]
    return .error e

def processStep (step : XML.Node) (ports : List (String × List Document)) (env : XPath4.Env) : IO (Result (List (String × List Document))) := do
  let options := do
    let sources := (ports.lookup "source").getD []
    if sources.length > 1 then error "XC0032" "os-exec accepts at most one input document" else pure ()
    let separator ← option step "path-separator" env "/"
    if separator.length != 1 then error "XC0063" "path-separator must contain one character" else pure ()
    let native := if System.Platform.isWindows then "\\" else "/"
    let command := (← option step "command" env).replace separator native
    let args := (← processArguments step env).map (fun arg => arg.replace separator native)
    let cwd := (← option step "cwd" env).replace separator native
    let threshold ← option step "failure-threshold" env
    let threshold ← if threshold == "" then pure none else match threshold.toInt? with
      | some n => pure (some n) | none => error "XD0036" "failure-threshold must be an integer"
    let serialization ← typedOption step "serialization" env "map{}"
    let input ← match sources with | [] => pure ByteArray.empty | doc::_ => documentBytes doc serialization env
    let resultType ← option step "result-content-type" env "text/plain"
    let errorType ← option step "error-content-type" env "text/plain"
    let _ ← parseMediaType resultType
    let _ ← parseMediaType errorType
    pure (command,args,cwd,threshold,input,resultType,errorType)
  let .ok (command,args,cwd,threshold,input,resultType,errorType) := options | return options.map (fun _ => [])
  let cwd : Option System.FilePath := if cwd == "" then none else some ⟨cwd⟩
  if let some directory := cwd then
    if !(← directory.isDir) then return error "XC0034" "os-exec working directory does not exist"
  let output ← try executeProcessBytes {cmd := command, args := args.toArray, cwd} input
    catch _ => return error "XC0033" "os-exec command could not be executed"
  if threshold.any (fun value => Int.ofNat output.exitCode.toNat > value) then
    return error "XC0064" "os-exec exit status exceeds failure threshold"
  let result ← match ← processOutputDocument output.stdout resultType with
    | .ok docs => pure docs | .error e => return .error e
  let errors ← match ← processOutputDocument output.stderr errorType with
    | .ok docs => pure docs | .error e => return .error e
  let status : Document := {node := .element "c:result"
    [⟨"xmlns:c","http://www.w3.org/ns/xproc-step"⟩] [.text (toString output.exitCode)]}
  return .ok [("result",result),("error",errors),("exit-status",[status])]

def processStepsRegression : IO Bool := do
  if System.Platform.isWindows then return true
  let cat := XML.Node.element "p:os-exec" [⟨"command","/bin/cat"⟩] []
  let source : Document := {node := .text "literal $HOME; no shell\n", contentType := "text/plain"}
  let copied ← processStep cat [("source",[source])] {}
  let some copied := copied.toOption | return false
  let [doc] := (copied.lookup "result").getD [] | return false
  if doc.node.textContent != source.node.textContent || doc.baseUri != "" then return false
  let echo := XML.Node.element "p:os-exec" [⟨"command","/bin/echo"⟩,⟨"args","literal;argument"⟩] []
  let echoed ← processStep echo [] {}
  let some echoed := echoed.toOption | return false
  if !((echoed.lookup "result").getD []).any (fun d => d.node.textContent.trimAscii.toString == "literal;argument") then return false
  let invalid := XML.Node.element "p:os-exec" [⟨"command","/bin/cat"⟩,⟨"cwd","/not-present-xproc-regression"⟩] []
  let failed ← processStep invalid [] {}
  return match failed with | .error e => e.code == "XC0034" | .ok _ => false

end L4Factoidal.XProc31
