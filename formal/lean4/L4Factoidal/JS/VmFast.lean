import L4Factoidal.JS.Value

/-!
# L4Factoidal.JS.VmFast — the register machine's inner loop for plain instructions

`vmLoop` (`JS/Interp.lean`) is one function with an arm for every instruction, in the monad
of the evaluator. Measured on the Mac (`docs/bubblepopjs-jit.md`, "Stage C spike"): a loop of
number instructions costs about 200 machine instructions for each register-machine
instruction there, against about 90 for the same arms in a small function of their own. The
size of `vmLoop` is the cost: its frame, the spills at the dispatch, the state of the monad.

`vmFast` is that small function. It runs, from a loop head (`Instr.tick`), every following
instruction that needs nothing of the evaluator: moves, constants, number arithmetic and
comparisons on registers that hold numbers (`Value.fl`), jumps, the step of the budget, and
reads of a property or an array element that the heap's pure fast read answers
(`HeapOf.fastGetV`, a dense array element). It stops, with nothing changed for the
instruction it stops at, at the first instruction it does not do or whose operands do not pass
its test (a register that is not a number, a property the fast read does not answer, the step
budget at zero or at a full-heap check), and `vmLoop` runs that instruction as before.

Each arm here is the arm of `vmLoop` for the same instruction, written with the same
expressions (`regs[bp + a]!`, `fregs.set! (bp + dst) ...`), with the call of `vmLoop` replaced
by the call of `vmFast`. `JS/VmFastProofs.lean` states and proves what that gives.

Fuel: `vmFast` takes one unit for each instruction, from the fuel `vmLoop` passes it; `vmLoop`
then takes one unit for the whole run. So a run with the fast loop uses less fuel than the
instruction-by-instruction run, never more: the two agree whenever the latter does not stop for
fuel (fuel is 2^31 - 1 at the start of a script; the step budget, which is kept exactly, is
what stops a script in practice).
-/

namespace L4Factoidal.JS

variable {H : Type}

/-- Where `vmFast` stopped: the instruction to run next, and the registers. -/
structure FastOut where
  pc : Nat
  regs : Array Value
  fregs : FloatArray

/-- One exit for every stop of `vmFast`. Not inlined, so that the loop keeps its registers. -/
@[noinline] def fastStop (pc : Nat) (regs : Array Value) (fregs : FloatArray) (h : HeapOf H) :
    EStateM.Result Abrupt (HeapOf H) FastOut :=
  .ok ⟨pc, regs, fregs⟩ h

/-- A register as a language value (`vmRd` of `JS/Interp.lean`). -/
@[inline] def fastRd (regs : Array Value) (fregs : FloatArray) (i : Nat) : Value :=
  match regs[i]! with
  | .fl => .num (fregs.get! i)
  | v => v

/-- A global name read through the cache: the value, or `Value.hole` when the general path
must look (not a plain writable data property, or a lexical binding may shadow it). -/
def vmGlobalHit (h : HeapOf H) (env : Nat) (x : String) (site : Nat) : Value :=
  match h.findEnv x 100000 env with
  | some _ => .hole
  | none =>
    let g := h.obj h.realm.globalObj
    let slot := h.globalCache[site]!
    match g.props.ks[slot]?, g.props.vs[slot]? with
    | some k, some (.data v ..) => if k == x then v else .hole
    | _, _ => .hole

/-- `vals` with slot `i` set to the number `x` (`vals.set! i (.num x)`, `setNumSlot_eq`). The old
value is taken out of the array first, so when it is a number box that nothing else holds, the
compiler reuses its cell for the new number: a loop that writes a number variable in an
environment allocates nothing. -/
@[inline] def setNumSlot (vals : Array Value) (i : Nat) (x : Float) : Array Value :=
  let old := vals[i]!
  let vals := vals.set! i .undef
  match old with
  | .num _ => vals.set! i (.num x)
  | _ => vals.set! i (.num x)

/-- Slot `idx` of environment `e` becomes the register `r` as a language value (`setSlot` of
`JS/Interp.lean` with `vmRd`, as a function of the heap). -/
@[inline] def fastSetSlot (h : HeapOf H) (e idx : Nat) (regs : Array Value) (fregs : FloatArray) (r : Nat) : HeapOf H :=
  let envs := h.envs
  let h := { h with envs := #[] }
  match regs[r]! with
  | .fl =>
    let x := fregs.get! r
    { h with envs := envs.modify e fun en => { en with vals := setNumSlot en.vals idx x } }
  | v => { h with envs := envs.modify e fun en => { en with vals := en.vals.set! idx v } }

/-- An array element as `vmLoop`'s `.getIndex` arm reads it with no call: a dense element of
an Array object at a whole-number index in range that is not a hole; `.hole` otherwise. -/
@[inline] def fastIndex (h : HeapOf H) (id : Nat) (x : Float) : Value :=
  match (h.obj id).kind with
  | .array es =>
    if x ≥ 0 && x < Float.ofNat es.size && x.floor == x && !(es.getD x.toUInt64.toNat .undef).isHole then
      es.getD x.toUInt64.toNat .undef
    else .hole
  | _ => .hole

/-- The inner loop: run instructions from `pc` while they need nothing of the evaluator (see
the module doc). The heap changes as `vmLoop` changes it: the step budget at `tick`, an
environment slot at `setUp`. -/
def vmFastGo (instrs : @& Array Instr) (env : Nat) : Nat → Nat → Nat → Array Value → FloatArray →
    HeapOf H → EStateM.Result Abrupt (HeapOf H) FastOut
  | 0, pc, _, regs, fregs, h => fastStop pc regs fregs h
  | n + 1, pc, bp, regs, fregs, h =>
    if pc ≥ instrs.size then fastStop pc regs fregs h else
    match instrs[pc]! with
    | .move dst src =>
      match regs[bp + src]! with
      | .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + src))) h
      | v => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) v) fregs h
    | .loadF dst x => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x) h
    | .loadV dst v => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) v) fregs h
    | .setHole r => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + r) .hole) fregs h
    | .add dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) + fregs.get! (bp + b))) h
      | _, _ => fastStop pc regs fregs h
    | .sub dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) - fregs.get! (bp + b))) h
      | _, _ => fastStop pc regs fregs h
    | .mul dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) * fregs.get! (bp + b))) h
      | _, _ => fastStop pc regs fregs h
    | .div dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) / fregs.get! (bp + b))) h
      | _, _ => fastStop pc regs fregs h
    | .lt dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) < fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool true)) fregs h
        else vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool false)) fregs h
      | _, _ => fastStop pc regs fregs h
    | .gt dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) > fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool true)) fregs h
        else vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool false)) fregs h
      | _, _ => fastStop pc regs fregs h
    | .le dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≤ fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool true)) fregs h
        else vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool false)) fregs h
      | _, _ => fastStop pc regs fregs h
    | .ge dst a b =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≥ fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool true)) fregs h
        else vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) (.bool false)) fregs h
      | _, _ => fastStop pc regs fregs h
    | .addK dst a k =>
      match regs[bp + a]! with
      | .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) + k)) h
      | _ => fastStop pc regs fregs h
    | .subK dst a k =>
      match regs[bp + a]! with
      | .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) - k)) h
      | _ => fastStop pc regs fregs h
    | .mulK dst a k =>
      match regs[bp + a]! with
      | .fl => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) (fregs.get! (bp + a) * k)) h
      | _ => fastStop pc regs fregs h
    | .jnltK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) < k then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _ => fastStop pc regs fregs h
    | .jngtK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) > k then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _ => fastStop pc regs fregs h
    | .jnleK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) ≤ k then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _ => fastStop pc regs fregs h
    | .jngeK a k t =>
      match regs[bp + a]! with
      | .fl =>
        if fregs.get! (bp + a) ≥ k then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _ => fastStop pc regs fregs h
    | .jnlt a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) < fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _, _ => fastStop pc regs fregs h
    | .jngt a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) > fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _, _ => fastStop pc regs fregs h
    | .jnle a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≤ fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _, _ => fastStop pc regs fregs h
    | .jnge a b t =>
      match regs[bp + a]!, regs[bp + b]! with
      | .fl, .fl =>
        if fregs.get! (bp + a) ≥ fregs.get! (bp + b) then vmFastGo instrs env n (pc + 1) bp regs fregs h
        else vmFastGo instrs env n t bp regs fregs h
      | _, _ => fastStop pc regs fregs h
    | .inc nw old src up =>
      match regs[bp + src]! with
      | .fl =>
        let x := fregs.get! (bp + src)
        let d := if up then x + 1 else x - 1
        vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + old) .fl |>.set! (bp + nw) .fl) (fregs.set! (bp + old) x |>.set! (bp + nw) d) h
      | _ => fastStop pc regs fregs h
    | .jmp t => vmFastGo instrs env n t bp regs fregs h
    | .jnull a t =>
      match regs[bp + a]! with
      | .undef | .null => vmFastGo instrs env n t bp regs fregs h
      | _ => vmFastGo instrs env n (pc + 1) bp regs fregs h
    | .jnotnull a t =>
      match regs[bp + a]! with
      | .undef | .null => vmFastGo instrs env n (pc + 1) bp regs fregs h
      | _ => vmFastGo instrs env n t bp regs fregs h
    | .tick | .tickF =>
      -- `tick` of `JS/Interp.lean`; where it would throw, `vmLoop` runs it
      if h.steps == 0 then fastStop pc regs fregs h
      else if h.steps % 1024 == 0 && h.full then fastStop pc regs fregs h
      else vmFastGo instrs env n (pc + 1) bp regs fregs { h with steps := h.steps - 1 }
    | .getMember dst o k =>
      match h.fastGetV (fastRd regs fregs (bp + o)) k with
      | .hole => fastStop pc regs fregs h
      | .num x => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x) h
      | v => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) v) fregs h
    | .getIndex dst o i =>
      match regs[bp + o]!, regs[bp + i]! with
      | .obj id, .fl =>
        match fastIndex h id (fregs.get! (bp + i)) with
        | .hole => fastStop pc regs fregs h
        | .num x => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x) h
        | v => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) v) fregs h
      | _, _ => fastStop pc regs fregs h
    | .getUp dst hops idx x =>
      let en := h.envs.getD (h.envUp hops env) default
      if hi : idx < en.names.size ∧ idx < en.vals.size then
        if en.names[idx] == x then
          match en.vals[idx] with
          | .hole => fastStop pc regs fregs h
          | .num x => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) x) h
          | wv => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) wv) fregs h
        else fastStop pc regs fregs h
      else fastStop pc regs fregs h
    | .setUp src hops idx x =>
      let e := h.envUp hops env
      let en := h.envs.getD e default
      if hi : idx < en.names.size ∧ idx < en.vals.size then
        if en.names[idx] == x && en.mutableAt idx then
          match en.vals[idx] with
          | .hole => fastStop pc regs fregs h
          | _ => vmFastGo instrs env n (pc + 1) bp regs fregs (fastSetSlot h e idx regs fregs (bp + src))
        else fastStop pc regs fregs h
      else fastStop pc regs fregs h
    | .getGlobal dst x site =>
      match vmGlobalHit h env x site with
      | .num xf => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) .fl) (fregs.set! (bp + dst) xf) h
      | .hole => fastStop pc regs fregs h
      | v => vmFastGo instrs env n (pc + 1) bp (regs.set! (bp + dst) v) fregs h
    | _ => fastStop pc regs fregs h

/-- The inner loop from `pc`, in the evaluator's monad. Off (`HeapOf.vmFastOn`), it stops at
once. -/
@[inline] def vmFast (instrs : @& Array Instr) (env fuel pc bp : Nat) (regs : Array Value) (fregs : FloatArray) :
    EStateM Abrupt (HeapOf H) FastOut := fun h =>
  if h.vmFastOn then vmFastGo instrs env fuel pc bp regs fregs h
  else .ok ⟨pc, regs, fregs⟩ h

end L4Factoidal.JS
