import EVMCleanroom.CallTransaction

/-!
Direct transaction guards for the identity precompile. The input uses an
ordinary synthetic witness and the public `CallTransaction.run` entry point.
The independent signed transaction corpus also compares full account effects,
receipt bytes and state roots with EthereumJS and Geth. These guards are tests.
-/

namespace EVMCleanroom.CallTransaction

private def identityRequest (gas : Nat) (bytes : Array UInt8) (fuel : Nat := 100) : Request :=
  { fork := .shanghai, fuel
    tx := {
      kind := 2, signedChainId := some 1, sender := 0x1000, to := 4
      nonce := 0, value := 3, gasLimit := gas, gasPriceCap := 2, priorityFeeCap := 1
      data := bytes, accessList := [] }
    block := {
      chainId := 1, coinbase := 0xc4, number := 19000000, timestamp := 1706000000
      gasLimit := 30000000, gasUsedBefore := 0, baseFee := 1, prevRandao := 0, blobBaseFee := 0 }
    witnesses := [
      { address := 0x1000, present := true, balance := 1000000, nonce := 0, code := #[], storage := [] },
      {
        address := 4, present := true, balance := 7, nonce := 0, code := #[0xfe]
        storage := [{ key := 0, value := 77 }] },
      { address := 0xc4, present := false, balance := 0, nonce := 0, code := #[], storage := [] }] }

private def isSuccess (fuel : Nat) : Bool :=
  match run (identityRequest 21022 #[0] fuel) with
  | .executed out =>
    out.receiptStatus && out.charge.used == 21022 && out.charge.refund == 0 &&
    out.output.size == 1 && out.output.readByte 0 == 0 &&
    (out.world.accounts 4).balance == 10 && (out.world.accounts 4).storage 0 == 77 &&
    (out.world.accounts 4).code == #[0xfe] &&
    (out.world.accounts 0x1000).nonce == 1 && (out.world.accounts 0x1000).balance == 957953
  | _ => false

#guard isSuccess 100
#guard isSuccess 0
#guard match run (identityRequest 21021 #[0]) with
  | .executed out =>
    !out.receiptStatus && out.charge.used == 21021 && out.charge.refund == 0 &&
    out.output.size == 0 && (out.world.accounts 4).balance == 7 &&
    (out.world.accounts 4).storage 0 == 77 &&
    (out.world.accounts 0x1000).nonce == 1 && (out.world.accounts 0x1000).balance == 957958 &&
    (match out.frame with | .exceptional .outOfGas => true | _ => false)
  | _ => false
#guard match run (identityRequest 21015 #[]) with
  | .executed out => out.receiptStatus && out.output.size == 0 && out.charge.used == 21015
  | _ => false
#guard match run (identityRequest 21014 #[]) with
  | .executed out => !out.receiptStatus && out.charge.used == 21014 && (out.world.accounts 4).balance == 7
  | _ => false
#guard match run (identityRequest 21000 #[0]) with
  | .rejected "below-intrinsic-gas" => true
  | _ => false
#guard let request := identityRequest 21022 #[0]
  let witnesses := request.witnesses.filter (fun a => a.address != 4)
  match run { request with witnesses } with
  | .indeterminate (.frame (.incompleteState 4 none)) => true
  | _ => false
#guard let request := identityRequest 21022 #[0]
  let witnesses := request.witnesses.map (fun a => if a.address == 4 then { a with address := 1 } else a)
  match run { request with tx := { request.tx with to := 1 }, witnesses } with
  | .indeterminate (.frame .unsupportedFork) => true
  | _ => false
#guard let frame : State := { code := #[], gas := 0, callData := { size := CallOpcode.maxIdentityCallBytes + 1 } }
  match runFrame 0 (World.beginTransaction (fun _ => {})) 4 frame with
  | .indeterminate .resourceLimit => true
  | _ => false
#guard match runFrame 0 (World.beginTransaction (fun _ => {})) 0xc1 { code := #[0], gas := 0 } with
  | .indeterminate .stepLimit => true
  | _ => false

end EVMCleanroom.CallTransaction
