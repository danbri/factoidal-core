import EVMCleanroom.MPTPathStore
import EVMCleanroom.CLIEncoding

namespace EVMCleanroom.MPTPathStoreProbe

open CLI (parseBytecode hexBytes)

def run (args : List String) : IO UInt32 := do
  match args with
  | "--dangerously-enable-unverified-keccak" :: root :: key :: proof =>
    if proof.length > MPTPathStore.maxStoreNodes ||
        proof.any (fun s => s.length > 2*MPT.maxNodeBytes) then
      IO.println "resourceLimit"
      return 0
    if root.length != 64 || key.length != 64 then
      IO.println "witness:root-or-key-width"
      return 0
    match (do
      let r ← parseBytecode root
      let k ← parseBytecode key
      let nodes ← proof.mapM parseBytecode
      pure (r,k,nodes.toArray) : Except String (Array UInt8 × Array UInt8 × Array (Array UInt8))) with
    | .error why => IO.println ("inputError:" ++ why); return 2
    | .ok (r,k,nodes) =>
      let a := Keccak.dangerouslyAcceptUnverified
      let result := do
        let s ← MPTPathStore.admit a #[]
        let s ← MPTPathStore.extend a s nodes
        MPTPathStore.select a s r k
      match result with
      | .error .resourceLimit => IO.println "resourceLimit"; return 0
      | .error (.invalidProof why) => IO.println ("witness:" ++ why); return 0
      | .ok out =>
        match out.value with
        | none => IO.println "absent"
        | some value => IO.println ("present:" ++ hexBytes value)
        for node in out.proof do IO.println (hexBytes node)
        return 0
  | _ => IO.println "inputError:explicit-experimental-opt-in-required"; return 2

end EVMCleanroom.MPTPathStoreProbe

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.MPTPathStoreProbe.run args
