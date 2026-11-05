import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Loading
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XProc31
open XML

def supportsFile (name : String) : Bool :=
  ["file-create-tempfile", "store", "file-info", "directory-list", "file-mkdir", "file-delete", "file-copy", "file-move"].contains name

def fileUri (path : System.FilePath) : String := "file://" ++ Fn.String.iriToUri path.toString

def canonicalTarget : Nat → System.FilePath → IO System.FilePath
  | 0, _ => throw (IO.userError "filesystem path depth limit")
  | fuel+1, path => do
    if ← path.pathExists then IO.FS.realPath path else
    match path.parent, path.fileName with
    | some parent, some name => do
      let resolved ← canonicalTarget fuel parent
      if name == "." then pure resolved
      else if name == ".." then pure (resolved.parent.getD resolved)
      else pure (resolved / name)
    | _, _ => IO.FS.realPath path

def checkWrite (root : Option String) (path : System.FilePath) : IO (Result Unit) := do
  let some root := root | return unsupported "filesystem mutation requires an authorized write root"
  try
    let root ← IO.FS.realPath root
    let target ← canonicalTarget 512 path
    let r := root.toString
    if target != root && target.toString.startsWith (if r.endsWith "/" then r else r ++ "/") then return .ok ()
    return unsupported "filesystem target is outside the authorized write root"
  catch e => return error "XD0011" e.toString

def fileOptionPath (step : Node) (env : XPath4.Env) (name schemeError : String) : Result (String × System.FilePath) := do
  let lexical ← option step name env
  let uri := Syntax.resolveIri env.baseUri lexical
  if !RDF.isAbsoluteIri uri then error "XD0064" "invalid filesystem URI" else
  if !(uri.startsWith "file:") then error schemeError "filesystem URI scheme not supported" else
  pure (uri, ⟨← documentFilePath uri⟩)

def fileResult (uri : String) : List Document :=
  [{node := .element "c:result" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩] [.text uri]}]

def fileFailure (step : Node) (env : XPath4.Env) (e : ProcError) : Result (List Document) := do
  if e.unsupported || (← option step "fail-on-error" env "true") != "false" then .error e else
  pure [{node := .element "c:error" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩,
    ⟨"code", "{http://www.w3.org/ns/xproc-error}" ++ e.code⟩] [.text e.message]}]

def fileInfoNode (path : System.FilePath) (detailed : Bool := true) : IO Node := do
  let m ← path.metadata
  let kind := if m.type == .dir then "directory" else if m.type == .file then "file" else "other"
  let mut attributes : List XML.Attribute := [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩,
    ⟨"name", path.fileName.getD path.toString⟩, ⟨"xml:base", fileUri path⟩]
  if detailed then
    let readable ← try
      if m.type == .dir then let _ ← path.readDir; pure true else
        let _ ← IO.FS.Handle.mk path .read; pure true
      catch _ => pure false
    let writable ← try
      if System.Platform.isWindows then pure none else
        let result ← IO.Process.output {cmd := "/bin/test", args := #["-w",path.toString]}
        pure (if result.exitCode == 0 then some true else if result.exitCode == 1 then some false else none)
      catch _ => pure none
    let modified := match eval ("string(unix-dateTime(" ++ toString (m.modified.sec * 1000 + m.modified.nsec.toNat / 1000000) ++ "))") {} with
      | .ok value => seqString {} value | .error _ => ""
    attributes := attributes ++ [⟨"size", toString m.byteSize⟩, ⟨"readable", if readable then "true" else "false"⟩,
      ⟨"last-modified", modified⟩, ⟨"content-type", if m.type == .dir || !( [".xml", ".xhtml", ".html", ".htm", ".json", ".txt", ".xq", ".xquery"].any (fun extension => path.toString.endsWith extension)) then "application/octet-stream" else inferredDocumentType path.toString⟩]
    if let some writable := writable then
      attributes := attributes ++ [⟨"writable",if writable then "true" else "false"⟩]
  pure (.element ("c:" ++ kind) attributes [])

def filterPatterns (step : Node) (env : XPath4.Env) (name : String) : Result (List String) :=
  match (named step "with-option").find? (fun n => attr n "name" == name) with
  | some n => do pure ((← eval (attr n "select") env).map (fun item => seqString env [item]))
  | none => match XML.findAttr name step.elementAttrs with
    | some value => do pure [← avt value env]
    | none => pure []

def anyPattern (env : XPath4.Env) (patterns : List String) (name : String) : Result Bool := do
  for pattern in patterns do
    if ← evalBool "matches($name,$pattern)" {env with vars := [(⟨"","name",""⟩,XPath4.sStr name), (⟨"","pattern",""⟩,XPath4.sStr pattern)] ++ env.vars} then return true
  pure false

def fileContentOverrides (step : Node) (env : XPath4.Env) : Result (List (String × String)) := do
  let values ← typedOption step "override-content-types" env "[]"
  match values with
  | [.arr pairs] => pairs.mapM fun (pair : XPath4.Seq) => do
    let [.arr members] := pair | error "XD0036" "override entries must be string arrays"
    let strings ← members.mapM fun member => do
      let [.atom value] := member | error "XD0036" "override members must be single strings"
      if !value.ty.derives (.b .string) then error "XD0036" "override members must be strings"
      else pure value.str
    let [pattern,ct] := strings | error "XC0146" "override entries require exactly two strings"
    let _ ← (anyPattern env [pattern] "").mapError (fun e => {e with code := "XC0147"})
    let _ ← parseMediaType ct
    pure (pattern,ct)
  | _ => error "XD0036" "override-content-types must be an array"

def overrideFileContentType (env : XPath4.Env) (overrides : List (String × String))
    (name : String) (node : Node) : Result Node := do
  let mut attributes := node.elementAttrs
  for (pattern,ct) in overrides do
    if ← anyPattern env [pattern] name then
      attributes := attributes.filter (·.name != "content-type") ++ [⟨"content-type",ct⟩]
  pure (.element (node.elementTag.getD "c:other") attributes (children node))

def listingTree (env : XPath4.Env) (inclusion exclusion : List String) (detailed : Bool)
    (overrides : List (String × String)) : Nat → System.FilePath → String → IO (Result Node)
  | 0, path, _ => return .ok (← fileInfoNode path detailed)
  | depth+1, path, relative => do
    let base ← fileInfoNode path detailed
    if !(← path.isDir) then return .ok base
    let mut output := []
    for entry in (← path.readDir).toList.mergeSort (fun a b => a.fileName ≤ b.fileName) do
      let directory ← entry.path.isDir
      let name := relative ++ entry.fileName ++ (if directory then "/" else "")
      let accepted := do
        let inc ← if inclusion.isEmpty then pure true else anyPattern env inclusion name
        let exc ← anyPattern env exclusion name
        pure (inc && !exc)
      let .ok accepted := accepted | return accepted.map (fun _ => base)
      let child ← listingTree env inclusion exclusion detailed overrides depth entry.path name
      let .ok child := child | return child
      if accepted || !(children child).isEmpty then
        let mut attrs := child.elementAttrs
        if detailed then
          for (pattern,ct) in overrides do
            if (anyPattern env [pattern] name).toOption == some true then
              attrs := attrs.filter (·.name != "content-type") ++ [⟨"content-type",ct⟩]
        output := output ++ [.element (child.elementTag.getD "c:file") attrs (children child)]
    return .ok (.element (base.elementTag.getD "c:directory") base.elementAttrs output)

def copyTree (root : Option String) (overwrite : Bool) : Nat → System.FilePath → System.FilePath → IO (Result Unit)
  | 0, _, _ => return unsupported "filesystem tree depth limit"
  | fuel+1, source, target => do
    if let .error e ← checkWrite root target then return .error e
    if ← source.isDir then
      if (← target.pathExists) && !(← target.isDir) then
        if !overwrite then return .ok ()
        IO.FS.removeFile target
      IO.FS.createDirAll target
      for entry in ← source.readDir do
        let r ← copyTree root overwrite fuel entry.path (target / entry.fileName)
        if let .error e := r then return .error e
      return .ok ()
    else
      if (← target.pathExists) && !overwrite then return .ok ()
      IO.FS.createDirAll (target.parent.getD target)
      IO.FS.writeBinFile target (← IO.FS.readBinFile source)
      return .ok ()

def storeOptions (env : XPath4.Env) (step : Node) (d : Document) : Result XPath4.Seq := do
  let explicit ← typedOption step "serialization" env "map{}"
  let [.map extra] := explicit | error "XD0036" "serialization option must be a map"
  let old := match documentProperty d ⟨"", "serialization", ""⟩ with | [.map entries] => entries | _ => []
  let entries := extra ++ old.filter (fun (k,_) => !extra.any (fun (n,_) => n.str == k.str))
  pure [.map (entries.map (fun (key,value) =>
    (match key.v with | .qn q => if q.uri == "" then XPath4.Atomic.ofStr q.loc else key | _ => key, value)))]

def fileStep (step : Node) (ports : List (String × List Document)) (env : XPath4.Env)
    (writeRoot : Option String := none) : IO (Result (List Document)) := do
  let kind := tag step
  let schemeError := match kind with
    | "file-create-tempfile" => "XC0138" | "file-info" => "XC0134" | "file-delete" => "XC0142" | "file-mkdir" => "XC0140"
    | "file-copy" => "XC0144" | "file-move" => "XC0148" | _ => "XD0011"
  let pathOption := if kind == "file-create-tempfile" && attr step "href" == "" && !(named step "with-option").any (fun n => attr n "name" == "href") then
    match writeRoot with | some root => .ok (fileUri ⟨root⟩, System.FilePath.mk root) | none => unsupported "temporary file creation requires an authorized write root"
    else fileOptionPath step env (if kind == "directory-list" then "path" else "href") schemeError
  let path ← match pathOption with
    | .error e => return fileFailure step env e
    | .ok path => pure path
  let (uri,path) := path
  let failureCode := match kind with
    | "file-create-tempfile" => "XC0116" | "file-mkdir" => "XC0114" | "file-delete" => "XC0113" | "file-copy" => "XC0050"
    | "file-move" => "XC0115" | _ => "XD0011"
  let action : IO (Result (List Document)) := do
    if kind == "file-create-tempfile" then
      if !(← path.isDir) then return error "XD0011" "temporary file destination must be an existing directory"
      let settings := do pure (← option step "prefix" env "", ← option step "suffix" env "")
      let .ok (pfx,suffix) := settings | return settings.map (fun _ => [])
      if [pfx,suffix].any (fun s => s.contains '/' || s.contains '\\') then return error "XC0116" "temporary filename prefix and suffix must not contain separators"
      for _ in [:128] do
        let nonce ← IO.rand 0 18446744073709551615
        let target := path / (pfx ++ "tmp" ++ toString nonce ++ suffix)
        if let .error e ← checkWrite writeRoot target then return .error e
        let handle ← try pure (some (← IO.FS.Handle.mk target .writeNew)) catch e =>
          if ← target.pathExists then pure none else throw e
        if let some handle := handle then
          try
            IO.setAccessRights target {user := {read := true, write := true}}
            handle.flush
            return .ok (fileResult (fileUri target))
          catch e =>
            IO.FS.removeFile target
            throw e
      return error "XC0116" "unable to allocate a unique temporary filename"
    if kind == "store" then
      let serialized := do
        let d ← oneSource ((ports.lookup "source").getD [])
        let options ← storeOptions env step d
        documentBytes d options env
      let .ok bytes := serialized | return serialized.map (fun _ => [])
      if let .error e ← checkWrite writeRoot path then return .error e
      IO.FS.createDirAll (path.parent.getD path)
      IO.FS.writeBinFile path bytes
      return .ok (fileResult uri)
    if kind == "file-mkdir" then
      if let .error e ← checkWrite writeRoot path then return .error e
      IO.FS.createDirAll path
      return .ok (fileResult uri)
    if kind == "file-delete" then
      if let .error e ← checkWrite writeRoot path then return .error e
      if !(← path.pathExists) then return .ok (fileResult uri)
      let recurse := (option step "recursive" env "false").toOption.getD "false" == "true"
      if ← path.isDir then
        if recurse then IO.FS.removeDirAll path else IO.FS.removeDir path
      else IO.FS.removeFile path
      return .ok (fileResult uri)
    if !(← path.pathExists) then return error "XD0011" "filesystem source does not exist"
    if kind == "file-info" then
      let node ← fileInfoNode path
      let result := do
        let overrides ← fileContentOverrides step env
        let node ← overrideFileContentType env overrides path.toString node
        pure [{node}]
      return result
    if kind == "directory-list" then
      if !(← path.isDir) then return error "XC0017" "directory-list requires a directory"
      let opts := do
        let depth ← option step "max-depth" env "1"
        let depth ← if depth == "unbounded" then pure 512 else match depth.toNat? with | some n => pure n | none => error "XD0028" "invalid maximum directory depth"
        let overrides ← fileContentOverrides step env
        pure (depth, ← filterPatterns step env "include-filter", ← filterPatterns step env "exclude-filter", (← option step "detailed" env "false") == "true", overrides)
      let .ok (depth,inclusion,exclusion,detailed,overrides) := opts | return opts.map (fun _ => [])
      let result ← listingTree env inclusion exclusion detailed overrides depth path ""
      return result.map (fun node => [{node, baseUri := uri}])
    if kind == "file-copy" || kind == "file-move" then
      let target := fileOptionPath step env "target" schemeError
      let .ok (targetUri,target) := target | return target.map (fun _ => [])
      let sourceDir ← path.isDir
      if sourceDir && (← target.pathExists) && !(← target.isDir) then
        return error (if kind == "file-copy" then "XC0157" else "XC0158") "cannot copy or move directory onto a file"
      let target := if (← target.isDir) || (kind == "file-copy" && sourceDir) then target / path.fileName.getD "" else target
      let target : System.FilePath := ⟨if target.toString.endsWith "/" then (target.toString.dropEnd 1).toString else target.toString⟩
      if let .error e ← checkWrite writeRoot target then return .error e
      let overwrite := (option step "overwrite" env (if kind == "file-copy" then "true" else "false")).toOption.getD "false" == "true"
      if kind == "file-copy" then
        let result ← copyTree writeRoot overwrite 512 path target
        return result.map (fun _ => fileResult (if targetUri.endsWith "/" && !sourceDir then targetUri else fileUri target))
      else
        if let .error e ← checkWrite writeRoot path then return .error e
        if (← target.pathExists) && !overwrite then return error "XC0115" "move target already exists"
        if (← path.isDir) && (← target.pathExists) && !(← target.isDir) then return error "XC0158" "cannot move directory onto a file"
        IO.FS.createDirAll (target.parent.getD target)
        IO.FS.rename path target
        return .ok (fileResult targetUri)
    return unsupported ("filesystem step " ++ kind)
  let result ← try action catch e => pure (error failureCode e.toString)
  match result with | .ok docs => return .ok docs | .error e => return fileFailure step env e

/-- Real filesystem regression, confined to an automatically cleaned temporary directory. -/
def fileStepsRegression : IO Bool := IO.FS.withTempDir fun root => do
  let env : XPath4.Env := {baseUri := fileUri root ++ "/pipeline.xpl"}
  let step := fun name attrs => XML.Node.element ("p:" ++ name) attrs []
  let source : Document := {node := .element "doc" [] [.text "stored"]}
  let tempStep := step "file-create-tempfile" [⟨"prefix", "probe-"⟩, ⟨"suffix", ".tmp"⟩]
  let first ← fileStep tempStep [] env (some root.toString)
  let second ← fileStep tempStep [] env (some root.toString)
  let some [a] := first.toOption | return false
  let some [b] := second.toOption | return false
  if a.node.textContent == b.node.textContent then return false
  let .ok tempPath := documentFilePath a.node.textContent | return false
  if !(((System.FilePath.mk tempPath).fileName.getD "").startsWith "probe-") then return false
  if !tempPath.endsWith ".tmp" || !(← (System.FilePath.mk tempPath).pathExists) then return false
  let stored ← fileStep (step "store" [⟨"href", "sub/result.xml"⟩]) [("source",[source])] env (some root.toString)
  if !stored.toBool then return false
  if !((← IO.FS.readFile (root / "sub/result.xml")).contains "stored") then return false
  let copied ← fileStep (step "file-copy" [⟨"href", "sub/result.xml"⟩, ⟨"target", "copy.xml"⟩]) [] env (some root.toString)
  if !copied.toBool then return false
  let conflict ← fileStep (step "file-move" [⟨"href", "sub/result.xml"⟩, ⟨"target", "copy.xml"⟩]) [] env (some root.toString)
  if (match conflict with | .error e => e.code != "XC0115" | .ok _ => true) then return false
  if !(← (root / "sub/result.xml").pathExists) then return false
  let info ← fileStep (step "file-info" [⟨"href", "copy.xml"⟩,
    ⟨"override-content-types", "[['[.]xml$', 'application/octet-stream']]"⟩]) [] env (some root.toString)
  let some [info] := info.toOption | return false
  if attr info.node "content-type" != "application/octet-stream" then return false
  IO.FS.createDirAll (root / "destination")
  let moved ← fileStep (step "file-move" [⟨"href", "sub/result.xml"⟩, ⟨"target", "destination"⟩]) [] env (some root.toString)
  let some [moved] := moved.toOption | return false
  if moved.node.textContent != fileUri (root / "destination") then return false
  if !(← (root / "destination/result.xml").pathExists) || (← (root / "sub/result.xml").pathExists) then return false
  let denied ← fileStep (step "store" [⟨"href", "../escape.xml"⟩]) [("source",[source])] env (some root.toString)
  if denied.toBool then return false
  let rootDelete ← fileStep (step "file-delete" [⟨"href", "."⟩, ⟨"recursive", "true"⟩]) [] env (some root.toString)
  if rootDelete.toBool then return false
  let deleted ← fileStep (step "file-delete" [⟨"href", "copy.xml"⟩]) [] env (some root.toString)
  return deleted.toBool && !(← (root / "copy.xml").pathExists)

end L4Factoidal.XProc31
