/-
Wasm.Ops.ContainerPath — the op `containerPath`: which URL a host may request under one
HTTP(S) container (`L4Factoidal.LWS.ContainerPath`;
https://github.com/danbri/factoidal/issues/1127, row C3 of
`docs/designissues/2026-10-28-feature-combination-safety.md`).

  containerPath(requestJson) with requestJson one of
    {"kind":"target","url":U,"canonical":B}          -> ContainerPath.target
    {"kind":"container","url":U,"canonical":B}       -> ContainerPath.containerOf
    {"kind":"resource","container":C,"path":P}        -> ContainerPath.resourceIn
    {"kind":"segment","root":R,"name":N}              -> ContainerPath.segmentIn
    {"kind":"within","root":R,"url":U,"canonical":B}  -> ContainerPath.within
    {"kind":"parent","root":R,"folder":F}             -> ContainerPath.parentIn
  -> {"ok":true,"allowed":true,"url":"..."}
   | {"ok":true,"allowed":false,"reason":"..."}

A refusal is an answer (`allowed: false`), not an error: the host turns it
into its own exception. A string member that is absent or not a string is a
refusal too (a JavaScript `null` or number as a path). Only a request that is
not a JSON object with a known `kind` is an error (code `call.arguments`).

Pure and stateless: the core and the full engines serve it through `call`.
The hosts are `npm/factoidal/lib/sbm11-lws.mjs` (the LWS reader of an SBM11
generation) and `docs/web/hub/data-compositor/pod-storage.mjs` (the
compositor's pod storage).
-/
import Wasm.Ops.Support
import Wasm.Ops.ErrorModel
import L4Factoidal.LWS.ContainerPath

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.LWS

private def answer : Except String String → String
  | .ok u => okWith [("allowed", .bool true), ("url", .string u)]
  | .error r => okWith [("allowed", .bool false), ("reason", .string r)]

private def str (j : Json) (k : String) (what : String) : Except String String :=
  match j.getString? k with
  | some s => .ok s
  | none => .error s!"the {what} is not a string"

/-- `containerPath(requestJson)`. -/
def containerPathOp (requestJson : String) : String :=
  match parseJson requestJson with
  | .error e => errCoded "call.arguments" s!"containerPath: the request is not JSON ({e})"
  | .ok j =>
    let canonical := (j.getBool? "canonical").getD false
    match j.getString? "kind" with
    | some "target" =>
        answer ((str j "url" "URL").bind (ContainerPath.target · canonical))
    | some "container" =>
        answer ((str j "url" "URL").bind (ContainerPath.containerOf · canonical))
    | some "resource" =>
        answer ((str j "container" "container URL").bind fun c =>
          (str j "path" "path").bind (ContainerPath.resourceIn c))
    | some "segment" =>
        answer ((str j "root" "root URL").bind fun r =>
          (str j "name" "name").bind (ContainerPath.segmentIn r))
    | some "within" =>
        answer ((str j "root" "root URL").bind fun r =>
          (str j "url" "URL").bind (ContainerPath.within r · canonical))
    | some "parent" =>
        answer ((str j "root" "root URL").bind fun r =>
          (str j "folder" "folder URL").bind (ContainerPath.parentIn r))
    | _ => errCoded "call.arguments"
        "containerPath: \"kind\" is one of target, container, resource, segment, within, parent"

/-- The op names of this module. -/
def containerPathOpNames : List String := ["containerPath"]

/-- Serve an op of this module; `none` for any other op. -/
def callContainerPath (op : String) (args : List String) : Option String :=
  match op, args with
  | "containerPath", [a] => some (containerPathOp a)
  | "containerPath", _ => some (errJson s!"containerPath expects 1 argument, got {args.length}")
  | _, _ => none

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

#guard containerPathOp "{\"kind\":\"resource\",\"container\":\"https://s.example/c\",\"path\":\"a b\"}" ==
  "{\"ok\":true,\"allowed\":true,\"url\":\"https://s.example/c/a%20b\"}"
#guard has (containerPathOp "{\"kind\":\"resource\",\"container\":\"https://s.example/c/\",\"path\":\"../x\"}")
  "\"allowed\":false"
#guard has (containerPathOp "{\"kind\":\"resource\",\"container\":\"https://s.example/c/\",\"path\":null}")
  "\"allowed\":false"
#guard has (containerPathOp "{\"kind\":\"within\",\"root\":\"https://s.example/alice/\",\"url\":\"https://s.example/alice-other/\",\"canonical\":true}")
  "\"allowed\":false"
#guard has (containerPathOp "{\"kind\":\"segment\",\"root\":\"https://s.example/alice/\",\"name\":\"p.json\"}")
  "\"url\":\"https://s.example/alice/p.json\""
#guard has (containerPathOp "{\"kind\":\"container\",\"url\":\"https://s.example/alice\",\"canonical\":true}")
  "\"allowed\":false"
#guard has (containerPathOp "{\"kind\":\"nope\"}") "\"code\":\"call.arguments\""
#guard has (containerPathOp "[") "\"code\":\"call.arguments\""
#guard (callContainerPath "containerPath" []).isSome
#guard (callContainerPath "other" []).isNone

end L4Wasm.Ops
