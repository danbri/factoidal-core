import EVMCleanroom.MPTPathStore
import EVMCleanroom.CLIEncoding

namespace EVMCleanroom.MPTPathStoreProbe

open CLI (parseBytecode hexBytes)

def readInput (root key : String) (proof : List String) :
    Except String (Array UInt8 × Array UInt8 × Array (Array UInt8)) := do
  let r ← parseBytecode root
  let k ← parseBytecode key
  let nodes ← proof.mapM parseBytecode
  return (r,k,nodes.toArray)

def run (args : List String) : IO UInt32 := do
  match args with
  | "--dangerously-enable-unverified-keccak" :: root :: key :: proof =>
    -- Permit exactly one over-limit node/count in this test probe so the
    -- Lean store admission/extension guards, not just transport, are exercised.
    if proof.length > MPTPathStore.maxStoreNodes + 1 ||
        proof.any (fun s => s.length > 2*(MPT.maxNodeBytes+1)) then
      IO.println "resourceLimit"
      return 0
    if root.length != 64 || key.length != 64 then
      IO.println "witness:root-or-key-width"
      return 0
    match readInput root key proof with
    | .error why => IO.println ("inputError:" ++ why); return 2
    | .ok (r,k,nodes) =>
      let a := Keccak.dangerouslyAcceptUnverified
      let result : Except MPT.Error (MPTPathStore.Selected a r k) := do
        let mid := nodes.size / 2
        let s ← MPTPathStore.admit a (nodes.extract 0 mid)
        let s ← MPTPathStore.extend a s (nodes.extract mid nodes.size)
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
