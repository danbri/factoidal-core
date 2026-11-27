import EVMCleanroom.SparseReplace
import EVMCleanroom.CLIEncoding

/-! Native test probe only; no host implementation or runtime theorem search. -/
namespace EVMCleanroom.SparseReplaceProbe

open CLI (parseBytecode hexBytes)

def readInput (root key old value : String) (proof : List String) :
    Except String (Array UInt8 × Array UInt8 × Array UInt8 × Array UInt8 × Array (Array UInt8)) := do
  if proof.length > MPT.maxProofNodes then throw "proof-count"
  if [root, key, old, value].any (fun s => s.length > 2*MPT.maxNodeBytes) ||
      proof.any (fun s => s.length > 2*MPT.maxNodeBytes) then throw "input-size"
  let r ← parseBytecode root
  let k ← parseBytecode key
  let o ← parseBytecode old
  let v ← parseBytecode value
  let nodes ← proof.mapM parseBytecode
  return (r, k, o, v, nodes.toArray)

def run (args : List String) : IO UInt32 := do
  match args with
  | "--dangerously-enable-unverified-keccak" :: root :: key :: old :: value :: proof =>
    match readInput root key old value proof with
    | .error why => IO.println ("inputError:" ++ why); return 2
    | .ok (r,k,o,v,nodes) =>
      match SparseReplace.replace Keccak.dangerouslyAcceptUnverified r k o v nodes with
      | .error (.witness why) => IO.println ("witness:" ++ why); return 0
      | .error (.unsupported why) => IO.println ("unsupported:" ++ why); return 0
      | .error .resourceLimit => IO.println "resourceLimit"; return 0
      | .error (.internal why) => IO.println ("internal:" ++ why); return 0
      | .ok result =>
        IO.println "projected"
        IO.println (hexBytes result.projection.root)
        for node in result.projection.nodes do IO.println (hexBytes node)
        return 0
  | _ => IO.println "inputError:explicit-experimental-opt-in-required"; return 2

end EVMCleanroom.SparseReplaceProbe

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.SparseReplaceProbe.run args
