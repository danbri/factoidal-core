/-
tests/stack/StackControl.lean -- the control program of the native stack canary
(tests/stack/run.sh --canary). Issue 749.

It holds one function that is non-tail on purpose: `foldNonTail` adds each
element AFTER the recursive call returns, so every element costs one native
stack frame. It exists only to show that the stack budget the canary sets
reaches the process:

  - at the canary budget, a list of n elements must abort with "Stack overflow
    detected" (exit 134);
  - at the default budget, the same list must run and print the sum.

It imports nothing from L4Factoidal, so a repair of a library function cannot
change what it measures. Do not repair it. Do not add it to
tools/lean-tail-recursion-allow.txt: the audit reads library and harness
declarations, not this file.

Compiled by run.sh with `lean -c` and `leanc`, outside Lake.
Usage: stack-control N     prints the sum 0 + 1 + ... + (N-1).
-/

def foldNonTail : List Nat → Nat
  | [] => 0
  | x :: xs => x + foldNonTail xs

def main (args : List String) : IO UInt32 := do
  match args with
  | [text] =>
    match text.toNat? with
    | some n =>
      IO.println (foldNonTail (List.range n))
      return 0
    | none =>
      IO.eprintln "stack-control: N must be a natural number"
      return 2
  | _ =>
    IO.eprintln "usage: stack-control N"
    return 2
