import EVMCleanroom.HashLogProofs

namespace EVMCleanroom

private def repeatA (size : Nat) : ByteView := { size, raw := fun _ => 0x61 }
private def byteRamp (size : Nat) : ByteView := { size, raw := UInt8.ofNat }

-- Selected existing XKCP-pinned vectors, including a combined suffix and final
-- bit in each of the first three blocks. The native gate uses all 24 fixtures.
#guard Keccak.digestWord (repeatA 0) ==
  0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
#guard Keccak.digestWord (repeatA 135) ==
  0x34367dc248bbd832f4e3e69dfaac2f92638bd0bbd18f2912ba4ef454919cf446
#guard Keccak.digestWord (repeatA 136) ==
  0xa6c4d403279fe3e0af03729caada8374b5ca54d8065329a3ebcaeb4b60aa386e
#guard Keccak.digestWord (byteRamp 271) ==
  0x7c974895b2a88303ff2dc6b58f438ceb0b298cac91099ac0539cc0f477506191
#guard Keccak.digestWord (byteRamp 272) ==
  0xfdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e
#guard Keccak.digestWord (repeatA 407) ==
  0x73c267c603b2e9c9d572afa045ccd787f5828029ecfa74295c193ba15dacd6c4
#guard Keccak.digestWord (repeatA 408) ==
  0xf763fe56a104e5c3ec0e4f311124923905d7f8e1dd03bdc91f2e6845ea523677
#guard Keccak.digestWord (ByteView.ofArray #[0x61, 0x62, 0x63]) ==
  0x4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45

private def maxWord : Nat := modulus - 1

private def hashInput (memory : Memory) (offset length gas : Nat) : State := {
  code := #[0x20]
  stack := ⟨[word offset, word length, word 0xcafe], by simp⟩
  memory
  gas
  -- Public known-answer fixtures and synthetic inputs in this test module.
  keccakAcceptance := some Keccak.dangerouslyAcceptUnverified
}

private def errorIs (outcome : Except Error State) (expected : Error) : Bool :=
  match outcome with
  | .error e => e == expected
  | .ok _ => false

#guard errorIs (step { hashInput Memory.empty 0 0 30 with keccakAcceptance := none }) .unsupportedFork

-- Zero-length access leaves even an enormous address unallocated.
#guard
  match step (hashInput Memory.empty maxWord 0 30) with
  | .ok out => out.stack.items.map Word.val == [
      0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470, 0xcafe] &&
      out.gas == 0 && out.memory.words == 0
  | .error _ => false

-- Reads span the high-water mark, so bytes in newly paid memory are zero.
#guard
  let memory := (Memory.empty.expand 1).writeByte 31 0xab
  [38, 39, 40].all fun gas =>
    match step (hashInput memory 31 3 gas) with
    | .ok out => gas >= 39 && out.gas == gas - 39 && out.memory.words == 2 &&
        out.stack.items.map Word.val == [Keccak.digestWord (ByteView.ofArray #[0xab, 0, 0]), 0xcafe]
    | .error .outOfGas => gas == 38
    | .error _ => false

#guard
  let length := 17 * 1024 * 1024
  let funded := MemoryGas.keccakCost 0 0 length
  errorIs (step (hashInput Memory.empty 0 length funded)) .resourceLimit

-- Gas checking precedes the experimental work cap, even with a maximal word length.
#guard errorIs (step (hashInput Memory.empty 0 maxWord modulus)) .outOfGas

#guard
  let s := { hashInput Memory.empty 0 0 30 with readOnly := true }
  match Frame.runWithPolicy Frame.zeroValueContextFree 2 s with
  | .stopped out => out.gas == 0 && out.stack.items.length == 2
  | _ => false

-- Exact LOG4 gas with one memory expansion, topic order and address.
#guard
  let memory := (Memory.empty.expand 1).writeByte 31 0xff
  let s : State := {
    code := #[0xa4]
    memory
    stack := ⟨[word 31, word 2, word 0, word 0xbb, word maxWord, word 0x412, word 0x123], by simp⟩
    currentAddress := 0xc1
    gas := 1894 }
  match step s with
  | .ok out =>
    match out.logsRev with
    | [entry] => out.gas == 0 && out.stack.items == [word 0x123] && out.memory.words == 2 &&
      entry.address == 0xc1 && entry.topics.map Word.val == [0, 0xbb, maxWord, 0x412] &&
      entry.data.size == 2 && entry.data.readByte 0 == 0xff && entry.data.readByte 1 == 0
    | _ => false
  | .error _ => false

#guard
  let s : State := {
    code := #[0xa0], gas := 375, stack := ⟨[word maxWord, word 0], by simp⟩ }
  match step s with
  | .ok out => out.gas == 0 && out.memory.words == 0 && out.logsRev.length == 1
  | .error _ => false

#guard
  ([0xa0, 0xa1, 0xa2, 0xa3, 0xa4] : List UInt8).all fun opcode =>
    let s : State := {
      code := #[opcode], gas := 10000, readOnly := true
      stack := ⟨[word 0, word 0, word 1, word 2, word 3, word 4], by simp⟩ }
    errorIs (step s) .writeProtection

#guard
  let s : State := {
    code := #[0xa1], gas := 749, readOnly := true, stack := ⟨[word 0, word 0, word 7], by simp⟩ }
  errorIs (step s) .outOfGas &&
    errorIs (step { s with stack := ⟨[word 0, word 0], by simp⟩ }) .stackUnderflow

-- A later MSTORE8 edits live memory without changing an earlier log's payload.
#guard
  let s : State := {
    code := #[0x60, 0xaa, 0x5f, 0x53, 0x60, 1, 0x5f, 0xa0, 0x60, 0xbb, 0x5f, 0x53, 0]
    gas := 500 }
  match Frame.run 10 s with
  | .stopped out =>
    match out.logsRev with
    | [entry] => entry.data.size == 1 && entry.data.readByte 0 == 0xaa && out.memory.readByte 0 == 0xbb
    | _ => false
  | _ => false

-- REVERT and an exception discard the emitted log but preserve the prior journal.
#guard
  let prior : LogEntry := ⟨7, [], ByteView.ofArray #[0xcc]⟩
  let s : State := { code := #[0x5f, 0x5f, 0xa0, 0x5f, 0x5f, 0xfd], gas := 500, logsRev := [prior] }
  match Frame.run 6 s, Frame.run 4 { s with code := #[0x5f, 0x5f, 0xa0, 0xfe] } with
  | .reverted reverted 0 0, .exceptional failed (.invalidOpcode 0xfe) =>
    (reverted.logsRev.map LogEntry.address == [7]) && (failed.logsRev.map LogEntry.address == [7])
  | _, _ => false

end EVMCleanroom
