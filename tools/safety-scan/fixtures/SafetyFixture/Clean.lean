/-! Expected: io-free. Pure code, a `partial def`, and `ST` with a type variable. -/
namespace SafetyFixture.Clean
def double (n : Nat) : Nat := n + n
partial def countDown (n : Nat) : Nat := if n == 0 then 0 else countDown (n - 1)
def sumST (xs : List Nat) : Nat := runST fun σ => do
  let r : ST.Ref σ Nat ← ST.mkRef 0
  for x in xs do r.modify (· + x)
  r.get
end SafetyFixture.Clean
