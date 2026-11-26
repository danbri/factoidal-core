import Std.Tactic.BVDecide

-- Sample bug: overflow in an unsigned average
def avgBad (a b : BitVec 32) : BitVec 32 := (a + b) >>> 1
def avgGood (a b : BitVec 32) : BitVec 32 := (a &&& b) + ((a ^^^ b) >>> 1)
def avgSpec (a b : BitVec 32) : BitVec 32 :=
  ((a.zeroExtend 33 + b.zeroExtend 33) >>> 1).truncate 32

theorem good_ok (a b : BitVec 32) : avgGood a b = avgSpec a b := by
  unfold avgGood avgSpec; bv_decide

-- Expected to FAIL: bv_decide reports the counterexample a = b = 0xFFFFFFFF
theorem bad_ng (a b : BitVec 32) : avgBad a b = avgSpec a b := by
  unfold avgBad avgSpec; bv_decide

-- Equivalence for performance work: x*8 + x*2 == x*10 ; x%8 == x&&&7
theorem mul10 (x : BitVec 32) : (x <<< 3) + (x <<< 1) = x * 10 := by bv_decide
theorem mod8 (x : BitVec 32) : x % 8 = x &&& 7 := by bv_decide
