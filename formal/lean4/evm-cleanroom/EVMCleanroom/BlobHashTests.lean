import EVMCleanroom.BlobHashProofs

/-!
# Executable BLOBHASH and nested-context regressions

These are tests of the actual interpreters, separate from the theorem claims.
The two fixture hashes differ in their final byte and retain a nonzero most
significant version byte, so a zero context or byte reversal cannot pass.
-/

namespace EVMCleanroom.BlobHashTests

open World CallOpcode

private def firstHash : Word := word (2 ^ 248 + 0x11)
private def secondHash : Word := word (2 ^ 248 + 0x22)
private def hashes : Array Word := #[firstHash, secondHash]

private def input (index gas : Nat) (profile : Profile := .cancunPlus)
    (readOnly : Bool := false) (context : Array Word := hashes) : State :=
  { code := #[0x49], gas, profile, readOnly, txBlobHashes := context
    stack := ⟨[word index, word 0xdd], by simp⟩ }

private def stepResult (index gas expected : Nat) (profile : Profile := .cancunPlus)
    (readOnly : Bool := false) (context : Array Word := hashes) : Bool :=
  match step (input index gas profile readOnly context) with
  | .ok out =>
    out.stack.items.map (·.val) == [expected, 0xdd] && out.gas + 3 == gas &&
    out.pc == 1 && !out.halted && out.txBlobHashes == context &&
    out.memory.words == 0 && out.storage.current 0 == 0
  | .error _ => false

private def stepError (s : State) (expected : Error) : Bool :=
  match step s with
  | .error e => decide (e = expected)
  | .ok _ => false

#guard stepResult 0 3 firstHash.val
#guard stepResult 1 3 secondHash.val
#guard stepResult 2 3 0
#guard stepResult (modulus - 1) 3 0
#guard stepResult (2 ^ 32) 3 0
#guard stepResult (2 ^ 64) 3 0
#guard stepResult 0 3 0 (context := #[])
#guard stepResult 1 8 secondHash.val .osaka
#guard stepResult 1 3 secondHash.val (readOnly := true)
#guard stepResult 5 3 secondHash.val
  (context := #[firstHash, firstHash, firstHash, firstHash, firstHash, secondHash])
#guard stepResult 6 3 0
  (context := #[firstHash, firstHash, firstHash, firstHash, firstHash, secondHash])
#guard stepError (input 0 2) .outOfGas
#guard stepError (input (modulus - 1) 0) .outOfGas
#guard stepError { input 0 100 with stack := Stack.empty } .stackUnderflow
#guard stepError { input 0 0 with stack := Stack.empty } .stackUnderflow
#guard stepError (input 0 100 .shanghaiPlus) .unsupportedFork
#guard stepError (input 0 100 .preShanghai) .unsupportedFork

private def fullStack : Bool :=
  let s := { input 1 3 with stack :=
    ⟨word 1 :: List.replicate 1023 (word 7), by
      simp only [List.length_cons, List.length_replicate]
      decide⟩ }
  match step s with
  | .ok out => out.stack.items == secondHash :: List.replicate 1023 (word 7) &&
      out.stack.items.length == 1024 && out.gas == 0
  | .error _ => false

#guard fullStack

private def returnHashCode (index : UInt8) (terminal : UInt8 := 0xf3) : Array UInt8 :=
  #[0x60, index, 0x49, 0x60, 0, 0x52, 0x60, 32, 0x60, 0, terminal]

private def expectedBytes (last : UInt8) : List UInt8 :=
  [1] ++ List.replicate 30 0 ++ [last]

private def viewBytes (view : ByteView) : List UInt8 :=
  (List.range view.size).map view.readByte

private def direct (index : UInt8) (gas : Nat := 21) (fuel : Nat := 7)
    (context : Array Word := hashes) (readOnly : Bool := false) : RawOutcome :=
  let w := { beginTransaction (fun _ => ({} : Account)) with txBlobHashes := context }
  let s := { frameInput w 0xc1 gas readOnly .cancunPlus with code := returnHashCode index }
  execute fuel w 0xc1 s

private def returned (outcome : RawOutcome) (bytes : List UInt8) (remaining : Nat)
    (context : Array Word := hashes) : Bool :=
  match outcome with
  | .returned out s =>
    viewBytes s.outputData == bytes && s.outputData.size == 32 &&
    s.gas == remaining && s.stack.items.isEmpty &&
    out.txBlobHashes == context && s.txBlobHashes == context
  | _ => false

#guard returned (direct 0) (expectedBytes 0x11) 0
#guard returned (direct 1) (expectedBytes 0x22) 0
#guard returned (direct 2) (List.replicate 32 0) 0
#guard returned (direct 0 (context := #[])) (List.replicate 32 0) 0 #[]
#guard returned (direct 1 (readOnly := true)) (expectedBytes 0x22) 0
#guard match direct 0 20 with | .exceptional .outOfGas => true | _ => false
#guard match direct 0 21 6 with | .indeterminate .stepLimit => true | _ => false

private def callPrefix (op : UInt8) (target : UInt8 := 0xc3)
    (value : UInt8 := 0) : Array UInt8 :=
  -- Output [0,32), empty input, optional explicit value, target and gas.
  #[0x60, 32, 0x60, 0, 0x60, 0, 0x60, 0] ++
    (if op == 0xf1 || op == 0xf2 then #[0x60, value] else #[]) ++
    #[0x60, target, 0x61, 0x75, 0x30, op]

private def parentCode (op : UInt8) (value : UInt8 := 0) : Array UInt8 :=
  callPrefix op (value := value) ++
    -- Read the child's copied hash, then the parent's own first hash.
    #[0x60, 0, 0x51, 0x60, 0, 0x49, 0x00]

private def fixtureWorld (parent child : Array UInt8)
    (grandchild : Array UInt8 := #[]) : TxWorld :=
  { beginTransaction (fun address =>
      if address == 0xc1 then { code := parent, balance := 1000 }
      else if address == 0xc3 then { code := child }
      else if address == 0xc4 then { code := grandchild }
      else {}) with txBlobHashes := hashes }

private def nested (op : UInt8) (value : UInt8 := 0) (readOnly : Bool := false) : Bool :=
  let w := fixtureWorld (parentCode op value) (returnHashCode 1)
  let s := frameInput w 0xc1 100000 readOnly .cancunPlus
  match execute 64 w 0xc1 s with
  | .stopped out final =>
    final.stack.items.map (·.val) == [firstHash.val, secondHash.val, 1] &&
    viewBytes final.returnData == expectedBytes 0x22 &&
    out.txBlobHashes == hashes && final.txBlobHashes == hashes
  | _ => false

#guard nested 0xf1
#guard nested 0xf2
#guard nested 0xf4
#guard nested 0xfa
#guard nested 0xf1 7
#guard nested 0xf2 7
#guard nested 0xf1 (readOnly := true)
#guard nested 0xf4 (readOnly := true)

private def publicCallStep (value : Nat) : Bool :=
  let w := fixtureWorld #[] (returnHashCode 1)
  let s := { frameInput w 0xc1 100000 false .cancunPlus with
    code := #[0xf1, 0]
    stack := ⟨[word 30000, word 0xc3, word value,
      word 0, word 0, word 0, word 32], by simp⟩ }
  match callStep 7 w 0xc1 s with
  | .committed out final =>
    final.stack.items.map (·.val) == [1] &&
    viewBytes final.returnData == expectedBytes 0x22 &&
    final.memory.readWord 0 == secondHash.val &&
    out.txBlobHashes == hashes && final.txBlobHashes == hashes
  | _ => false

#guard publicCallStep 0
#guard publicCallStep 7

private def twoLevels : Bool :=
  let middle := callPrefix 0xfa 0xc4 ++ #[0x60, 32, 0x60, 0, 0xf3]
  let w := fixtureWorld (parentCode 0xf1) middle (returnHashCode 1)
  match execute 96 w 0xc1 (frameInput w 0xc1 100000 false .cancunPlus) with
  | .stopped out final =>
    final.stack.items.map (·.val) == [firstHash.val, secondHash.val, 1] &&
    viewBytes final.returnData == expectedBytes 0x22 && out.txBlobHashes == hashes
  | _ => false

#guard twoLevels

private def childRevert : Bool :=
  let child := #[0x60, 1, 0x49, 0x60, 0, 0x55] ++ returnHashCode 1 0xfd
  let w := fixtureWorld (parentCode 0xf1) child
  match execute 64 w 0xc1 (frameInput w 0xc1 100000 false .cancunPlus) with
  | .stopped out final =>
    final.stack.items.map (·.val) == [firstHash.val, secondHash.val, 0] &&
    viewBytes final.returnData == expectedBytes 0x22 &&
    (out.accounts 0xc3).storage 0 == 0 && out.txBlobHashes == hashes
  | _ => false

#guard childRevert

private def parentRevert : Bool :=
  let parent := callPrefix 0xf1 (value := 7) ++ #[0x60, 0, 0x60, 0, 0xfd]
  let w := fixtureWorld parent (returnHashCode 1)
  let s := frameInput w 0xc1 100000 false .cancunPlus
  match settle w s (execute 64 w 0xc1 s) with
  | .reverted out final =>
    (out.accounts 0xc1).balance == 1000 && (out.accounts 0xc3).balance == 0 &&
    out.txBlobHashes == hashes && final.txBlobHashes == hashes
  | _ => false

#guard parentRevert

end EVMCleanroom.BlobHashTests
