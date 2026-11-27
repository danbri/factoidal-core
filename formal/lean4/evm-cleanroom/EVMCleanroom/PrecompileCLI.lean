import EVMCleanroom.Precompiles

/-!
# `evm-precompile`: run the precompile router natively

A plain-text test and timing entry point for `Precompiles.run`, the function
the CALL family uses. It exists so published vectors and independent oracles
can be compared with the compiled Lean code in CI, and so time per call can
be measured. It imports no `Lean.*` module.

    evm-precompile [--dangerously-enable-unverified-keccak] --run PROFILE ADDRESS GAS HEX
    evm-precompile [--dangerously-enable-unverified-keccak] --batch FILE
    evm-precompile [--dangerously-enable-unverified-keccak] --bench FILE REPEATS

`PROFILE` is `preShanghai`, `shanghaiPlus`, `cancunPlus`, `prague` or `osaka`; `ADDRESS`
and `GAS` are decimal; `HEX` is the input without `0x` (`-` for empty). A
batch file has one `PROFILE ADDRESS GAS HEX` case per line. Each case prints

    ok GAS_USED OUTPUT_HEX      the call succeeds
    fail                        exceptional halt: forwarded gas consumed
    refuse REASON               not an Ethereum result (inactive address,
                                missing opt-in or a local resource bound)

`--bench` prints `ADDRESS INPUT_BYTES GAS_USED MIN P50 P95 MAX` per line, the
times in nanoseconds over `REPEATS` calls in one process.
-/

namespace EVMCleanroom.PrecompileCLI

open EVMCleanroom EVMCleanroom.Precompiles

private def profileOf : String → Option Profile
  | "preShanghai" => some .preShanghai
  | "shanghaiPlus" => some .shanghaiPlus
  | "cancunPlus" => some .cancunPlus
  | "prague" => some .prague
  | "osaka" => some .osaka
  | _ => none

structure Case where
  profile : Profile
  address : Nat
  gas : Nat
  input : ByteArray

private def parseCase (profile address gas hexInput : String) : Except String Case := do
  let some profile := profileOf profile | throw "unknown profile"
  let some address := address.toNat? | throw "address is not a decimal number"
  let some gas := gas.toNat? | throw "gas is not a decimal number"
  let some input := ofHex? (if hexInput == "-" then "" else hexInput) | throw "input is not hexadecimal"
  return ⟨profile, address, gas, input⟩

private def parseLine (line : String) : Except String Case :=
  match (line.splitOn " ").filter (· ≠ "") with
  | [profile, address, gas, hexInput] => parseCase profile address gas hexInput
  | _ => throw "expected: PROFILE ADDRESS GAS HEX"

private def outputBytes (view : ByteView) : ByteArray := materialize view

def execute (keccak : Option Keccak.Acceptance) (c : Case) : Except Error (ByteView × Nat) :=
  Precompiles.run c.profile keccak c.address c.gas (viewOf c.input)

private def render (c : Case) : Except Error (ByteView × Nat) → String
  | .ok (output, left) => s!"ok {c.gas - left} {toHex (outputBytes output)}"
  | .error .outOfGas => "fail"
  | .error .resourceLimit => "refuse resource-limit"
  | .error .unsupportedFork => "refuse unavailable"
  | .error _ => "refuse other"

private def insertSorted (xs : Array Nat) (x : Nat) : Array Nat := Id.run do
  let mut out := xs.push x
  let mut i := out.size - 1
  while i > 0 && out[i - 1]! > out[i]! do
    out := out.swapIfInBounds (i - 1) i
    i := i - 1
  return out

/-- One timed call. Not inlined, so the work happens between the two clock reads. -/
@[noinline] private def gasUsedOnce (keccak : Option Keccak.Acceptance) (c : Case) : IO Nat :=
  match execute keccak c with
  | .ok (output, left) => pure (c.gas - left + (output.readByte 0).toNat * 0)
  | .error _ => pure c.gas

private def benchCase (keccak : Option Keccak.Acceptance) (repeats : Nat) (c : Case) : IO String := do
  let mut times : Array Nat := #[]
  let mut used := 0
  for _ in [0:repeats] do
    let start ← IO.monoNanosNow
    used ← gasUsedOnce keccak c
    let stop ← IO.monoNanosNow
    times := insertSorted times (stop - start)
  let pick (percent : Nat) := times[(times.size - 1) * percent / 100]!
  return s!"{c.address} {c.input.size} {used} {pick 0} {pick 50} {pick 95} {pick 100}"

def main (args : List String) : IO UInt32 := do
  let (keccak, args) := match args with
    | "--dangerously-enable-unverified-keccak" :: rest => (some Keccak.dangerouslyAcceptUnverified, rest)
    | rest => (none, rest)
  match args with
  | ["--run", profile, address, gas, hexInput] =>
    match parseCase profile address gas hexInput with
    | .error message => IO.eprintln s!"input error: {message}"; return 2
    | .ok c => IO.println (render c (execute keccak c)); return 0
  | ["--batch", path] =>
    let lines ← IO.FS.lines path
    let out ← IO.getStdout
    for line in lines do
      match parseLine line with
      | .error message => out.putStrLn s!"input-error {message}"
      | .ok c => out.putStrLn (render c (execute keccak c))
    return 0
  | ["--bench", path, repeats] =>
    let some repeats := repeats.toNat? | IO.eprintln "REPEATS is not a number"; return 2
    if repeats == 0 then IO.eprintln "REPEATS must be positive"; return 2
    let lines ← IO.FS.lines path
    for line in lines do
      match parseLine line with
      | .error message => IO.println s!"input-error {message}"
      | .ok c => IO.println (← benchCase keccak repeats c)
    return 0
  | _ =>
    IO.eprintln "usage: evm-precompile [--dangerously-enable-unverified-keccak] (--run PROFILE ADDRESS GAS HEX | --batch FILE | --bench FILE REPEATS)"
    return 2

end EVMCleanroom.PrecompileCLI

def main (args : List String) : IO UInt32 := EVMCleanroom.PrecompileCLI.main args
