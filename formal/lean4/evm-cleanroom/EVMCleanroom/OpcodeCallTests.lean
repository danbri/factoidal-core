import EVMCleanroom.OpcodeCall

/-! Executable checks for the actual restricted bytecode 0xF1 path. -/

namespace EVMCleanroom.OpcodeCallTests

open EVMCleanroom.World

private def parentCode : Array UInt8 :=
  #[0x5f,0x5f,0x5f,0x5f,0x5f,0x60,0xc3,0x61,0x75,0x30,0xf1,0x00]

private def parentThenInvalid : Array UInt8 :=
  #[0x5f,0x5f,0x5f,0x5f,0x5f,0x60,0xc3,0x61,0x75,0x30,0xf1,0xfe]

private def accounts (parent child : Array UInt8) (addr : Nat) : Account :=
  if addr == 0xc1 then { code := parent }
  else if addr == 0xc3 then { code := child }
  else {}

private def runPair (parent child : Array UInt8) (gas : Nat := 50000) :
    OpcodeCall.Outcome :=
  OpcodeCall.run 40 40 (beginTransaction (accounts parent child)) 0xc1 gas

private def success := runPair parentCode
  #[0x60,0x01,0x60,0x00,0x55,0x00]

private def reverting := runPair parentCode
  #[0x60,0x01,0x60,0x00,0x55,0x60,0x00,0x60,0x00,0xfd]

private def childInvalid := runPair parentCode
  #[0x60,0x01,0x60,0x00,0x55,0xfe]

private def parentInvalid := runPair parentThenInvalid
  #[0x60,0x01,0x60,0x00,0x55,0x00]

private def gasRemaining (o : OpcodeCall.Outcome) : Option Nat :=
  match o with
  | .stopped _ s => some s.gas
  | _ => none

private def resultWord (o : OpcodeCall.Outcome) : Option Nat :=
  match o with
  | .stopped _ s => s.stack.items.head?.map Word.val
  | _ => none

private def childStorage (o : OpcodeCall.Outcome) : Option Nat :=
  match o with
  | .stopped w _ => some ((w.accounts 0xc3).storage 0)
  | .exceptional w _ => some ((w.accounts 0xc3).storage 0)
  | _ => none

private def targetWarm (o : OpcodeCall.Outcome) : Bool :=
  match o with
  | .stopped w _ => w.warmAddresses 0xc3
  | _ => false

private def childSlotWarm (o : OpcodeCall.Outcome) : Bool :=
  match o with
  | .stopped w _ => w.warmSlots 0xc3 0
  | _ => false

private def isParentExceptional (o : OpcodeCall.Outcome) : Bool :=
  match o with
  | .exceptional _ (.invalidOpcode 0xfe) => true
  | _ => false

-- Parent CALL is a real bytecode opcode and pushes a success flag.
#guard gasRemaining success == some 25278
#guard resultWord success == some 1
#guard childStorage success == some 1
#guard targetWarm success
#guard childSlotWarm success

-- Child REVERT returns failure=0 to parent, refunding unused child gas.
#guard gasRemaining reverting == some 25272
#guard resultWord reverting == some 0
#guard childStorage reverting == some 0
#guard targetWarm reverting
#guard !(childSlotWarm reverting)

-- Exceptional child burns its allotted gas; parent itself does not halt.
#guard gasRemaining childInvalid == some 17384
#guard resultWord childInvalid == some 0
#guard childStorage childInvalid == some 0

-- If the *parent* subsequently fails, it rolls back the already
-- committed child effects too: journal scope matters more than call depth.
#guard isParentExceptional parentInvalid
#guard childStorage parentInvalid == some 0


-- Genuine child RETURN bytes must reach the parent's RETURNDATACOPY,
-- survive a 31-byte offset, be read through MLOAD and reach storage slot 1.
private def returnChild : Array UInt8 :=
  #[0x60,0x2a,0x60,0x00,0x53,0x60,0x01,0x60,0x00,0xf3]

private def parentCopy : Array UInt8 :=
  #[0x5f,0x5f,0x5f,0x5f,0x5f,0x60,0xc3,0x61,0x75,0x30,0xf1,
    0x60,0x01,0x60,0x00,0x60,0x1f,0x3e,
    0x60,0x00,0x51,0x60,0x01,0x55,0x00]

private def returnCopy := runPair parentCopy returnChild

private def parentSlot1 (o : OpcodeCall.Outcome) : Option Nat :=
  match o with
  | .stopped w _ => some ((w.accounts 0xc1).storage 1)
  | _ => none

private def parentMemoryByte (o : OpcodeCall.Outcome) (addr : Nat) : Option Nat :=
  match o with
  | .stopped _ parent => some (parent.memory.readByte addr).toNat
  | _ => none

#guard gasRemaining returnCopy == some 25239
#guard resultWord returnCopy == some 1
#guard parentMemoryByte returnCopy 31 == some 42
#guard parentSlot1 returnCopy == some 42

private def parentReturnSize : Array UInt8 :=
  #[0x5f,0x5f,0x5f,0x5f,0x5f,0x60,0xc3,0x61,0x75,0x30,0xf1,0x3d,0x00]

#guard resultWord (runPair parentReturnSize returnChild) == some 1
#guard gasRemaining (runPair parentReturnSize returnChild) == some 47364

private def parentBadReturnCopy : Array UInt8 :=
  #[0x5f,0x5f,0x5f,0x5f,0x5f,0x60,0xc3,0x61,0x75,0x30,0xf1,
    0x60,0x01,0x60,0x01,0x60,0x00,0x3e,0x00]

private def isBadReturnCopy (o : OpcodeCall.Outcome) : Bool :=
  match o with
  | .exceptional _ .returnDataOutOfBounds => true
  | _ => false

#guard isBadReturnCopy (runPair parentBadReturnCopy returnChild)

end EVMCleanroom.OpcodeCallTests
