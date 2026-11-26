import EVMCleanroom.Frame

namespace EVMCleanroom

private def maxWord : Nat := modulus - 1

private def withCopyStack (s : State) (dest source length : Nat) : State :=
  { s with stack := ⟨[word dest, word source, word length, word 0xabc], by simp⟩ }

private def copyError (s : State) (dest source length : Nat) (expected : Error) : Bool :=
  match step (withCopyStack s dest source length) with
  | .error why => why == expected
  | .ok _ => false

private def memoryBytes (m : Memory) (addresses : List Nat) : List UInt8 :=
  addresses.map m.readByte

-- An adapter may have a nonzero backing value beyond its advertised size.
#guard (ByteView.mk 1 (fun _ => 0xff)).readByte 1 == 0

-- A source window on the old memory survives an overlapping destination write.
#guard
  let m := ((Memory.empty.expand 1).writeByte 0 0x10).writeByte 1 0x11
  let copied := m.copyFrom (ByteView.ofMemory m 0 3) 0 1 3
  memoryBytes copied [0, 1, 2, 3] == [0x10, 0x10, 0x11, 0] && copied.words == 1

-- Non-word-aligned destination, zero padding, expansion and pop order.
#guard
  let m := (Memory.empty.expand 1).writeByte 30 0x81
  let s : State := {
    code := #[0x37], gas := 9, memory := m
    callData := ByteView.ofArray #[0xaa, 0xbb] }
  match step (withCopyStack s 31 1 3) with
  | .ok out =>
    memoryBytes out.memory [30, 31, 32, 33, 34] == [0x81, 0xbb, 0, 0, 0] &&
      out.memory.words == 2 && out.stack.items == [word 0xabc] && out.pc == 1 && out.gas == 0
  | .error _ => false

-- The largest source offset overwrites an existing nonzero byte with padding.
#guard
  let m := (Memory.empty.expand 1).writeByte 0 0xff
  let s : State := {
    code := #[0x37], gas := 6, memory := m
    callData := ByteView.ofArray #[0xab] }
  match step (withCopyStack s 0 maxWord 1) with
  | .ok out => out.memory.readByte 0 == 0 && out.memory.words == 1 && out.gas == 0
  | .error _ => false

#guard
  let s : State := { code := #[0x37], gas := 3 }
  match step (withCopyStack s maxWord maxWord 0) with
  | .ok out => out.memory.words == 0 && out.gas == 0
  | .error _ => false

-- A nonempty far destination cannot affect memory with ordinary gas.
#guard copyError { code := #[0x37], gas := 1000000 } maxWord 0 1 .outOfGas

-- Even with synthetic gas sufficient for a huge copy, the range is sparse.
#guard
  let gas := MemoryGas.copyCost 0 maxWord maxWord
  let s : State := { code := #[0x37], gas, callData := ByteView.ofArray #[0xad] }
  match step (withCopyStack s maxWord 0 maxWord) with
  | .ok out => out.gas == 0 && out.memory.readByte maxWord == 0xad &&
      out.memory.readByte (2 * maxWord - 1) == 0 &&
      out.memory.words == MemoryGas.requestedWords maxWord maxWord
  | .error _ => false

#guard
  match step { code := #[0x38, 0x61, 0xda, 0x7a], gas := 2, profile := .preShanghai } with
  | .ok out => out.stack.items == [word 4] && out.gas == 0
  | .error _ => false

#guard
  let s : State := { code := #[0x39, 0xab, 0xcd], gas := 9, profile := .preShanghai }
  match step (withCopyStack s 0 1 4) with
  | .ok out => memoryBytes out.memory [0, 1, 2, 3] == [0xab, 0xcd, 0, 0] && out.gas == 0
  | .error _ => false

-- At 24 allocated words, expansion costs 73, and copying 33 bytes costs 9.
#guard
  let s : State := { code := #[0x39], gas := 82 }
  match step (withCopyStack s 704 0 33) with
  | .ok out => out.memory.words == 24 && memoryBytes out.memory [703, 704, 705, 736] ==
      [0, 0x39, 0, 0] && out.gas == 0
  | .error _ => false

#guard
  match step { code := #[0x3d], gas := 2 } with
  | .ok out => out.stack.items == [word 0] && out.gas == 0
  | .error _ => false

#guard
  let s : State := { code := #[0x3d], gas := 2, returnData := ByteView.ofArray #[1, 2, 3] }
  match step s with
  | .ok out => out.stack.items == [word 3] && out.gas == 0
  | .error _ => false

-- A nonempty read ending exactly at the buffer bound succeeds.
#guard
  let m := ((Memory.empty.expand 1).writeByte 2 0xff).writeByte 5 0xff
  let s : State := {
    code := #[0x3e], gas := 6, memory := m
    returnData := ByteView.ofArray #[0xaa, 0xbb, 0xcc] }
  match step (withCopyStack s 3 1 2) with
  | .ok out => memoryBytes out.memory [2, 3, 4, 5] == [0xff, 0xbb, 0xcc, 0xff] &&
      out.gas == 0 && out.returnData.size == 3 && out.returnData.readByte 0 == 0xaa
  | .error _ => false

-- Zero length at exactly the buffer end succeeds, including a far destination.
#guard
  let s : State := { code := #[0x3e], gas := 3, returnData := ByteView.ofArray #[0xee] }
  match step (withCopyStack s maxWord 1 0) with
  | .ok out => out.gas == 0 && out.memory.words == 0
  | .error _ => false

#guard copyError { code := #[0x3e], gas := 3 } maxWord 1 0 .returnDataOutOfBounds
#guard copyError { code := #[0x3e], gas := 9 } 0 maxWord 1 .returnDataOutOfBounds
#guard copyError { code := #[0x3e], gas := 8 } 0 maxWord 1 .outOfGas

#guard ([0x3d, 0x3e] : List UInt8).all fun op =>
  copyError { code := #[op], gas := 3, profile := .preShanghai } 0 0 0 .unsupportedFork

-- A guarded frame classifies a return-buffer bounds violation as exceptional.
#guard
  let s := withCopyStack { code := #[0x3e], gas := 20, readOnly := true } 0 1 0
  match Frame.runWithPolicy Frame.zeroValueContextFree 1 s with
  | .exceptional out .returnDataOutOfBounds => out.gas == 0 && out.memory.words == 0
  | _ => false

-- A frame's terminal output is separate from the last child output it had read.
#guard
  let s : State := {
    code := #[0x60, 0xab, 0x5f, 0x53, 0x60, 0x01, 0x5f, 0xf3], gas := 16
    returnData := ByteView.ofArray #[0xde, 0xad] }
  match Frame.run 6 s with
  | .returned out 0 1 => out.gas == 0 && out.outputData.size == 1 &&
      out.outputData.readByte 0 == 0xab && out.returnData.size == 2 && out.returnData.readByte 0 == 0xde
  | _ => false

end EVMCleanroom
