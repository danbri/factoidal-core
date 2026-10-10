/-
Wasm.CoreDispatchTests — build-time checks that the core dispatch
(`Wasm/CoreDispatch.lean`) and the full dispatch (`Wasm/Dispatch.lean`) agree
(https://github.com/danbri/factoidal/issues/713 stage 4).

  * The core op names and `Core.fullOnlyOpNames` together are exactly the
    names the full table serves (its `ops` reflection through `callIO`, and
    `blobEcho`), and the two lists are disjoint. A new op added to the full
    table and to neither list fails this build.
  * A core op answers the same envelope through both tables, for a positive
    and a negative input of each family.
  * The full table reads JSON-LD; the core table refuses it by name.

This module imports both tables. It imports neither `Wasm/Exports.lean` nor
`Wasm/CoreExports.lean`, which define the same C symbols.
-/
import Wasm.Dispatch
import Wasm.CoreDispatch

namespace L4Wasm.CoreDispatchTests

open L4Factoidal.JSON

/-- The op names of an `ops` reflection envelope. -/
def reflectedOps (envelope : String) : List String :=
  match parseJson envelope with
  | .ok j =>
      match j.field? "ops" with
      | some (.array xs) => xs.filterMap fun x => match x with
          | .string s => some s
          | _ => none
      | _ => []
  | .error _ => []

/-- `a` and `b` hold the same names (as sets). -/
def sameNames (a b : List String) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

/-- The full table's names, `ops` itself left out. -/
def fullNames : List String :=
  ((reflectedOps (L4Wasm.opsReflectionIO)) ++ L4Wasm.blobIoOpNames).filter (· != "ops")

/-- The core table's names. -/
def coreNames : List String := Core.coreOpNames ++ Core.coreIOOpNames

#guard !fullNames.isEmpty
#guard sameNames fullNames (coreNames ++ Core.fullOnlyOpNames)
#guard coreNames.all (fun n => !Core.fullOnlyOpNames.contains n)
-- The pure core reflection lists the stateless core ops only.
#guard sameNames (reflectedOps (Core.call "ops" "[]")) Core.coreOpNames

private def nt : String := "<http://e/a> <http://e/p> \"v\" .\n"
private def argsOf (xs : List String) : String := (Json.array (xs.map Json.string)).toString

/-- The pure entries of the two tables give the same envelope. -/
def samePure (op : String) (args : List String) : Bool :=
  L4Wasm.call op (argsOf args) == Core.call op (argsOf args)

#guard samePure "parseToDatasetJson" [nt, "ntriples", ""]
#guard samePure "parseToDatasetJson" ["<a> <b>", "ntriples", ""]
#guard samePure "parseToDatasetJson" [nt, "no-such-syntax", ""]
#guard samePure "queryDataset" [nt, "SELECT ?o WHERE { ?s ?p ?o }"]
#guard samePure "queryDataset" [nt, "SELECT WHERE"]
#guard samePure "updateDataset" [nt, "INSERT DATA { <http://e/b> <http://e/p> 1 }"]
#guard samePure "serializeNQuads" [nt]
#guard samePure "serializeTurtle" [nt]
#guard samePure "canonicalizeToNQuads" ["_:x <http://e/p> _:y .\n"]
#guard samePure "owlClosure" [nt, "OWL-RL"]
#guard samePure "owlClosure" [nt, "no-such-mode"]
#guard samePure "rhoDfClosure" [nt]
#guard samePure "rdfsPlusClosure" [nt]
#guard samePure "rhoDfFragmentCheck" [nt]
#guard samePure "queryRaw" [nt, "ASK { ?s ?p ?o }", "{\"dataFormat\":\"ntriples\"}"]
#guard samePure "shaclValidate" [nt, ""]
#guard samePure "serializeTurtleWith" [nt, "{\"literalShorthand\":false}"]
#guard samePure "parseDocument" [nt, "ntriples", "", "{\"lenient\":true}"]
#guard samePure "queryDataset" [nt]
#guard samePure "noSuchOp" []

-- JSON-LD: read by the full table, refused by name by the core table.
private def jl : String := "{\"@id\":\"http://e/a\",\"http://e/p\":\"v\"}"
#guard (L4Wasm.call "parseToDatasetJson" (argsOf [jl, "jsonld", ""])).startsWith
         "{\"ok\":true,\"count\":1"
#guard ((Core.call "parseToDatasetJson" (argsOf [jl, "jsonld", ""])).splitOn
          "not in the core engine").length > 1
-- A full-only op: answered by the full table, refused by the core table.
#guard (L4Wasm.call "xmlWellformed" (argsOf ["<a/>"])).startsWith "{\"ok\":true"
#guard ((Core.call "xmlWellformed" (argsOf ["<a/>"])).splitOn "\"servedBy\":\"full\"").length > 1

end L4Wasm.CoreDispatchTests
