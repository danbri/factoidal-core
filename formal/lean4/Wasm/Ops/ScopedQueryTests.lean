import Wasm.Ops.ScopedQuery

open L4Factoidal.Dataflow.ExecutionContext
open L4Wasm.Ops
open L4Wasm.Ops.ScopedQuery
open L4Factoidal.JSON

private def containsText (text needle : String) : Bool := (text.splitOn needle).length > 1
private def ok (text : String) : Bool :=
  match parseJson? text with
  | some json => json.field? "ok" == some (.bool true)
  | none => false
private def expect (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

#guard (capture (α := Nat) {} [("urn:hidden", 7)] ["urn:host"]).services == []
#guard (capture (α := Nat) {} [("urn:hidden", 7)] ["urn:host"]).extensions == []
#guard dispatch (capture (α := Nat) { extensions := ["urn:allowed"] } [] ["urn:allowed"] ).extensions
  (fun _ n => some (n + 1)) "urn:allowed" 41 == some 42
#guard dispatch (capture (α := Nat) {} [] ["urn:host"]).extensions
  (fun _ n => some (n + 1)) "urn:host" 41 == none

private def secret := "<urn:s> <urn:value> \"LOCAL_SECRET\" ."
private def replacement := "<urn:s> <urn:value> \"REPLACED_SECRET\" ."
private def query := "SELECT ?v WHERE { SERVICE <urn:private> { ?s <urn:value> ?v } }"
private def variableQuery := "SELECT ?v WHERE { VALUES ?endpoint { <urn:private> } SERVICE ?endpoint { ?s <urn:value> ?v } }"
private def nestedQuery := "SELECT ?v WHERE { SERVICE <urn:outer> { SERVICE <urn:private> { ?s <urn:value> ?v } } }"

private def runtimeTests : IO Unit := do
  let passCount ← IO.mkRef 0
  let check := fun (condition : Bool) (message : String) => do
    expect condition message
    passCount.modify (· + 1)
  let _ ← clearServiceEndpoints
  let _ ← extClear
  try
    let _ ← registerServiceEndpoint "urn:private" secret
    let _ ← registerServiceEndpoint "urn:outer" ""
    let ambient ← queryDatasetIO "" query
    check (ok ambient && containsText ambient "LOCAL_SECRET") "ambient compatibility control"
    let deny ← captureContext {}
    let allow ← captureContext { services := ["urn:private"] }
    let outerOnly ← captureContext { services := ["urn:outer"] }
    let both ← captureContext { services := ["urn:outer", "urn:private"] }
    check (!ok (runCaptured deny "" query)) "ungranted SERVICE must remain unavailable"
    let silent := runCaptured deny "" "SELECT ?v WHERE { SERVICE SILENT <urn:private> { ?s <urn:value> ?v } }"
    check (ok silent && !containsText silent "LOCAL_SECRET") "SILENT preserves success without private value"
    check (ok (runCaptured allow "" query) && containsText (runCaptured allow "" query) "LOCAL_SECRET") "explicit SERVICE grant"
    check (!containsText (runCaptured deny "" variableQuery) "LOCAL_SECRET") "variable SERVICE denial"
    check (ok (runCaptured allow "" variableQuery) &&
      containsText (runCaptured allow "" variableQuery) "LOCAL_SECRET")
      "explicit variable SERVICE grant is a nonvacuous positive control"
    check (!containsText (runCaptured outerOnly "" nestedQuery) "LOCAL_SECRET") "nested SERVICE cannot acquire inner authority"
    check (containsText (runCaptured both "" nestedQuery) "LOCAL_SECRET") "nested SERVICE explicit grants"
    let _ ← registerServiceEndpoint "urn:private" replacement
    let later ← captureContext { services := ["urn:private"] }
    check (containsText (runCaptured allow "" query) "LOCAL_SECRET" && !containsText (runCaptured allow "" query) "REPLACED_SECRET") "captured service data cannot change with registry mutation"
    check (containsText (runCaptured later "" query) "REPLACED_SECRET") "later operation captures replacement"
    let oldTask := Task.spawn fun _ => runCaptured allow "" query
    let newTask := Task.spawn fun _ => runCaptured later "" query
    let oldResult := oldTask.get
    let newResult := newTask.get
    check (containsText oldResult "LOCAL_SECRET" && !containsText oldResult "REPLACED_SECRET" &&
      containsText newResult "REPLACED_SECRET" && !containsText newResult "LOCAL_SECRET")
      "spawned query evaluations keep their separate immutable service snapshots"
    let _ ← extRegister "urn:host"
    let noExtension ← captureContext {}
    let yesExtension ← captureContext { extensions := ["urn:host"] }
    check (noExtension.providers.extensions == []) "ungranted extension excluded at actual host-call gate"
    check (yesExtension.providers.extensions == ["urn:host"]) "explicit extension admission"
    let _ ← extClear
    check (yesExtension.providers.extensions == ["urn:host"]) "captured extension IRIs immutable"
    check (extFnsWith noExtension.providers.extensions "urn:host" [] == none) "denied extension does not reach extern host branch"
    IO.println s!"ScopedQuery runtime: {← passCount.get} pass / 0 unexpected fail / 0 expected failure (not a conformance-suite result)"
  finally
    let _ ← clearServiceEndpoints
    let _ ← extClear

#eval runtimeTests
