import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Loading
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XProc31
open XML

def supportsFile (name : String) : Bool :=
  ["store", "file-info", "directory-list", "file-mkdir", "file-delete", "file-copy", "file-move"].contains name

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
  [{node := .element "c:result" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩] [.text uri], baseUri := uri}]

def fileFailure (step : Node) (env : XPath4.Env) (e : ProcError) : Result (List Document) := do
  if e.unsupported || (← option step "fail-on-error" env "true") != "false" then .error e else
  pure [{node := .element "c:error" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩,
    ⟨"code", "{http://www.w3.org/ns/xproc-error}" ++ e.code⟩] [.text e.message]}]

def fileInfoNode (path : System.FilePath) : IO Node := do
  let m ← path.metadata
  let kind := if m.type == .dir then "directory" else if m.type == .file then "file" else "other"
  pure (.element ("c:" ++ kind) [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩,
    ⟨"name", path.fileName.getD path.toString⟩, ⟨"xml:base", fileUri path⟩,
    ⟨"size", toString m.byteSize⟩] [])

def listingTree (env : XPath4.Env) (inclusion exclusion : String) : Nat → System.FilePath → IO (Result Node)
  | 0, path => return .ok (← fileInfoNode path)
  | depth+1, path => do
    let base ← fileInfoNode path
    if !(← path.isDir) then return .ok base
    let mut children := []
    for entry in (← path.readDir).toList.mergeSort (fun a b => a.fileName ≤ b.fileName) do
      let e := {env with vars := (⟨"", "name", ""⟩, XPath4.sStr entry.fileName) :: env.vars}
      let accepted := do
        let inc ← if inclusion == "" then pure true else evalBool ("matches($name, '" ++ inclusion.replace "'" "''" ++ "')") e
        let exc ← if exclusion == "" then pure false else evalBool ("matches($name, '" ++ exclusion.replace "'" "''" ++ "')") e
        pure (inc && !exc)
      let .ok accepted := accepted | return accepted.map (fun _ => base)
      if accepted then
        let child ← listingTree env inclusion exclusion depth entry.path
        let .ok child := child | return child
        children := children ++ [child]
    return .ok (.element (base.elementTag.getD "c:directory") base.elementAttrs children)

def copyTree (root : Option String) (overwrite : Bool) : Nat → System.FilePath → System.FilePath → IO (Result Unit)
  | 0, _, _ => return unsupported "filesystem tree depth limit"
  | fuel+1, source, target => do
    if let .error e ← checkWrite root target then return .error e
    if ← source.isDir then
      if (← target.pathExists) && !(← target.isDir) then return error "XC0157" "cannot copy directory onto a file"
      IO.FS.createDirAll target
      for entry in ← source.readDir do
        let r ← copyTree root overwrite fuel entry.path (target / entry.fileName)
        if let .error e := r then return .error e
      return .ok ()
    else
      if (← target.pathExists) && !overwrite then return error "XC0050" "copy target already exists"
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
    | "file-info" => "XC0134" | "file-delete" => "XC0142" | "file-mkdir" => "XC0140"
    | "file-copy" => "XC0144" | "file-move" => "XC0148" | _ => "XD0011"
  let path ← match fileOptionPath step env (if kind == "directory-list" then "path" else "href") schemeError with
    | .error e => return fileFailure step env e
    | .ok path => pure path
  let (uri,path) := path
  let failureCode := match kind with
    | "file-mkdir" => "XC0114" | "file-delete" => "XC0113" | "file-copy" => "XC0050"
    | "file-move" => "XC0115" | _ => "XD0011"
  let action : IO (Result (List Document)) := do
    if kind == "store" then
      let serialized := do
        let d ← oneSource ((ports.lookup "source").getD [])
        let options ← storeOptions env step d
        let e := xpathEnv (some d) env.vars env.ns
        let params ← fromXPath (XPath4.serParamsOf e options)
        if !["UTF-8", "utf-8"].contains params.encoding then return ← unsupported "store encoding other than UTF-8"
        let suppliedMethod := match options with | [.map entries] => entries.any (fun (key,_) => key.str == "method") | _ => false
        let kind ← classifyMediaType d.contentType
        let method := match kind with | .json => "json" | .text => "text" | .html => "html" | _ => "xml"
        let params := if suppliedMethod then params else {params with method}
        fromXPath (e.serializeWith params (e.ctx.getD []))
      let .ok text := serialized | return serialized.map (fun _ => [])
      if let .error e ← checkWrite writeRoot path then return .error e
      IO.FS.createDirAll (path.parent.getD path)
      IO.FS.writeFile path text
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
    if kind == "file-info" then return .ok [{node := ← fileInfoNode path, baseUri := uri}]
    if kind == "directory-list" then
      if !(← path.isDir) then return error "XC0017" "directory-list requires a directory"
      let opts := do
        let depth ← option step "max-depth" env "1"
        let depth ← if depth == "unbounded" then pure 512 else match depth.toNat? with | some n => pure n | none => error "XD0028" "invalid maximum directory depth"
        pure (depth, ← option step "include-filter" env, ← option step "exclude-filter" env)
      let .ok (depth,inclusion,exclusion) := opts | return opts.map (fun _ => [])
      let result ← listingTree env inclusion exclusion depth path
      return result.map (fun node => [{node, baseUri := uri}])
    if kind == "file-copy" || kind == "file-move" then
      let target := fileOptionPath step env "target" schemeError
      let .ok (_,target) := target | return target.map (fun _ => [])
      let target := if (← target.isDir) then target / path.fileName.getD "" else target
      if let .error e ← checkWrite writeRoot target then return .error e
      let overwrite := (option step "overwrite" env "false").toOption.getD "false" == "true"
      if kind == "file-copy" then
        let result ← copyTree writeRoot overwrite 512 path target
        return result.map (fun _ => fileResult (fileUri target))
      else
        if let .error e ← checkWrite writeRoot path then return .error e
        if (← target.pathExists) && !overwrite then return error "XC0115" "move target already exists"
        if (← path.isDir) && (← target.pathExists) && !(← target.isDir) then return error "XC0158" "cannot move directory onto a file"
        IO.FS.createDirAll (target.parent.getD target)
        IO.FS.rename path target
        return .ok (fileResult (fileUri target))
    return unsupported ("filesystem step " ++ kind)
  let result ← try action catch e => pure (error failureCode e.toString)
  match result with | .ok docs => return .ok docs | .error e => return fileFailure step env e

end L4Factoidal.XProc31
