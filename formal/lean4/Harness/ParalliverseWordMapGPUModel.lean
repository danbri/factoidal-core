import L4Factoidal.Paralliverse.WordMapGPUChain

/-! Executable checks for the restricted Lean WGSL parser and dispatch model.
The full-buffer oracle below uses independent ordinary word arithmetic. -/

open L4Factoidal.Paralliverse
open WordMapGPU

private def inputWords (n : Nat) : List UInt32 :=
  (List.range n).map fun i => if i % 7 = 0 then 0xFFFFFFFF else UInt32.ofNat (i % 11)

private def completeCase (xs : List UInt32) : Bool :=
  let n := xs.length
  let src := packet 2 xs [0xF1234567, 0x11223344]
  let mid := packet 1 (List.replicate n 0xBAD0) [0xA1, 0xA2]
  let end_ := packet 0xE1234567 (List.replicate n 0xBAD1) [0xB0, 0xB1, 0xB2]
  let lanes := CountTarget.canonicalLanes n
  match runTwo ⟨.multiply, 2⟩ ⟨.add, 1⟩ n src mid end_ lanes.reverse lanes with
  | none => false
  | some (intermediate, final_) =>
    let expectedMid := UInt32.ofNat n :: 1 :: (xs.map (fun x : UInt32 => x * 2) ++ [0xA1, 0xA2])
    let expectedEnd := UInt32.ofNat n :: 0xE1234567 ::
      (xs.map (fun x : UInt32 => x * 2 + 1) ++ [0xB0, 0xB1, 0xB2])
    intermediate.dst.toList == expectedMid && final_.dst.toList == expectedEnd &&
      intermediate.trace.length == lanes.length && final_.trace.length == lanes.length

#guard completeCase []
#guard completeCase [0xFFFFFFFF]
#guard completeCase [0xFFFFFFFF, 3, 3, 0, 3]
#guard completeCase (inputWords 64)
#guard completeCase (inputWords 65)
#guard completeCase (inputWords 129)
#guard completeCase (inputWords 1024)

-- The active read detects a missing payload. The active destination store is checked independently.
#guard (runGrid ⟨.add, 5⟩ 1 #[1, 5] #[10, 11, 12] (CountTarget.canonicalLanes 1)).isNone
#guard (runGrid ⟨.add, 5⟩ 1 (packet 5 [3] []) #[10, 11] (CountTarget.canonicalLanes 1)).isNone

-- Coefficients really come from the storage header. The pass tag only chooses shader bytes.
#guard ((runGrid ⟨.add, 99⟩ 1 (packet 7 [2] []) #[10, 11, 12] (CountTarget.canonicalLanes 1)).map
    (fun out => out.dst.toList)) == some [10, 11, 9]

#guard (select? (Program.fuseMaps (WordProgram.affine 2 1))).isNone

