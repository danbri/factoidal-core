/-
L4Factoidal.WasmVM.Aot.Translate: a validated guest module, translated into a module for
the host's WebAssembly engine (record: docs/designissues/2026-11-08-wasmvm-aot.md).

The translation is close to the identity on code. It does four things:

1. **Imports are routed to Lean.** Every import must be a function import. Import `k`
   keeps its type and gets the module `aot` and the name `importName k`; the host gives
   each such name one function that passes the call, with `k`, to Lean, which serves it
   with the binding the interpreter would use (`Wasi.link`). A table, memory, global or
   tag import is refused, so the guest can reach no state but its own.
2. **Memory is the guest's own, with Lean's page limit.** The module must define exactly
   one memory and import none; its maximum becomes the smaller of its own and `pages`,
   so the host engine's `memory.grow` stops where the interpreter's `pageLimit` would.
   Every access is checked by the host engine's bounds checks against this memory.
3. **Fuel.** One new mutable i64 global (appended, so no global index moves), exported
   as `fuelExport`. Each function body starts with `charge c`, and each `loop` header is
   followed by `charge c`: `c` is the length of the straight line that every entry into
   that region runs (`regionCosts`). `charge` subtracts `c` from the fuel and traps
   (`unreachable`) when the fuel goes below zero. Every way back to earlier code is a
   branch to a loop header, which charges again, and every call charges at the callee's
   start, so the fuel charged is at most the instructions run: a run stopped for fuel
   `F` has run at least `F` instructions, and an endless loop is always stopped.
4. **Exports** are kept, plus the fuel global.

Theorems here: the import map is type-preserving and injective, with the route back to
the original import (`translate_import_desc`, `translate_import_route`; `Proofs/AotNames.lean`: `importName_injective`,
`translate_import_names`); erasing the fuel charges gives back each original body
(`erase_instrument`); the exports are the original ones plus the fuel global
(`translate_exports`).
-/
import L4Factoidal.WasmVM.Syntax

namespace L4Factoidal.WasmVM.Aot

/-- The module name of every translated import. -/
def importModule : String := "aot"

/-- The name of translated import `k`. -/
def importName (k : Nat) : String := "i" ++ Nat.repr k

def fuelExport : String := "aot_fuel"

/-! ## Fuel -/

/-- Take `c` from fuel global `g`; trap when it is below zero. Ten instructions with no
net stack effect, no branch out and one nested `if`. -/
def charge (g c : Nat) : List Instr :=
  [.globalGet g, .i64Const c.toUInt64, .num .i64_sub, .globalSet g,
   .globalGet g, .i64Const 0, .num .i64_lt_s, .if_ .empty, .unreachable, .end_]

theorem charge_length (g c : Nat) : (charge g c).length = 10 := rfl

/-- Is this the ten instructions of a charge to global `g`? -/
def isCharge (g : Nat) : List Instr → Bool
  | [.globalGet a, .i64Const _, .num .i64_sub, .globalSet b, .globalGet d, .i64Const z,
     .num .i64_lt_s, .if_ .empty, .unreachable, .end_] => a == g && b == g && d == g && z == 0
  | _ => false

theorem isCharge_charge (g c : Nat) : isCharge g (charge g c) = true := by
  simp [isCharge, charge]

@[simp] theorem take_charge (g c : Nat) (x : List Instr) : (charge g c ++ x).take 10 = charge g c := by
  simp [charge]

@[simp] theorem drop_charge (g c : Nat) (x : List Instr) : (charge g c ++ x).drop 10 = x := by
  simp [charge]

/-- Instructions after which control may leave the straight line: a branch, a return,
a trap, a throw, a tail call, an `if` (one of two arms), a `loop` (its body may branch
out of the region around it), and the end of a legacy `try` clause. -/
def mayLeave : Instr → Bool
  | .br _ | .brIf _ | .brTable _ _ | .return_ | .unreachable | .if_ _ | .else_ | .loop _
  | .throw _ | .throwRef | .rethrow _ | .delegate _ | .catch_ _ | .catchAll
  | .returnCall _ | .returnCallIndirect _ _ | .returnCallRef _ | .brOnNull _ | .brOnNonNull _
  | .tryTable _ _ => true
  | _ => false

/-- Instructions that only give the code its structure: the engines run them at no
cost (WasmVM compiles them to no op, `Valid.lean`), so they are not counted. -/
def structural : Instr → Bool
  | .block _ | .loop _ | .end_ | .else_ | .try_ _ | .tryTable _ _ | .nop => true
  | _ => false

/-- The region costs of a flat body: index 0 is the function outside its loops, index
`k + 1` the `k`-th `loop` (in order) outside its inner loops. The cost of a region is the
number of its instructions that are not `structural`, from its start up to and
including the first one after which control may leave the straight line (`mayLeave`),
and at least 1. Every entry into the region runs all of them (or traps), so the fuel
charged is at most the instructions run, plus one for an entry that runs none. -/
def regionCosts (body : Array Instr) : Array Nat := Id.run do
  let mut costs : Array Nat := #[0]
  -- Whether each region still counts (no instruction of `mayLeave` seen yet).
  let mut open_ : Array Bool := #[true]
  -- The open blocks: the region each one is in (a loop: its own region).
  let mut stack : Array Nat := #[]
  for i in body do
    let cur := stack.back?.getD 0
    if open_.getD cur false then
      if !structural i then costs := costs.modify cur (· + 1)
      if mayLeave i then open_ := open_.set! cur false
    match i with
    | .loop _ =>
      stack := stack.push costs.size
      costs := costs.push 0
      open_ := open_.push true
    | .block _ | .if_ _ | .try_ _ | .tryTable .. => stack := stack.push cur
    | .end_ | .delegate _ => stack := stack.pop
    | _ => pure ()
  return costs.map (max 1)

/-- The body with a charge after each `loop`, the `k`-th loop charging `cs[k]`. -/
def emit (g : Nat) : List Instr → List Nat → List Instr
  | [], _ => []
  | .loop bt :: is, c :: cs => .loop bt :: (charge g c ++ emit g is cs)
  | .loop bt :: is, [] => .loop bt :: (charge g 0 ++ emit g is [])
  | i :: is, cs => i :: emit g is cs

/-- Remove the charge after each `loop`. -/
def erase (g : Nat) : List Instr → List Instr
  | [] => []
  | .loop bt :: rest =>
    if isCharge g (rest.take 10) then .loop bt :: erase g (rest.drop 10)
    else .loop bt :: erase g rest
  | i :: rest => i :: erase g rest
termination_by l => l.length
decreasing_by all_goals simp_wf <;> omega

/-- `emit` as a loop with an accumulator (the code that runs: `emit` recurses once per
instruction, and a function body can have tens of thousands). -/
def emitAcc (g : Nat) : List Instr → List Nat → Array Instr → Array Instr
  | [], _, acc => acc
  | .loop bt :: is, c :: cs, acc => emitAcc g is cs (acc.push (.loop bt) ++ (charge g c).toArray)
  | .loop bt :: is, [], acc => emitAcc g is [] (acc.push (.loop bt) ++ (charge g 0).toArray)
  | i :: is, cs, acc => emitAcc g is cs (acc.push i)

theorem emitAcc_toList (g : Nat) (is : List Instr) : ∀ (cs : List Nat) (acc : Array Instr),
    (emitAcc g is cs acc).toList = acc.toList ++ emit g is cs := by
  induction is with
  | nil => intro cs acc; simp [emitAcc, emit]
  | cons i is ih =>
    intro cs acc
    cases i <;> cases cs <;> simp [emitAcc, emit, ih]

theorem emitAcc_eq (g : Nat) (is : List Instr) (cs : List Nat) (acc : Array Instr) :
    emitAcc g is cs acc = acc ++ (emit g is cs).toArray := by
  apply Array.toList_inj.mp
  simp [emitAcc_toList]

/-- A function body with its charges. -/
def instrument (g : Nat) (body : Array Instr) : Array Instr :=
  let cs := (regionCosts body).toList
  emitAcc g body.toList cs.tail (charge g (cs.headD 0)).toArray

theorem instrument_eq (g : Nat) (body : Array Instr) :
    instrument g body = (charge g ((regionCosts body).toList.headD 0) ++
      emit g body.toList (regionCosts body).toList.tail).toArray := by
  simp [instrument, emitAcc_eq]

/-- A body with its charges removed. -/
def eraseBody (g : Nat) (body : Array Instr) : Array Instr :=
  if isCharge g (body.toList.take 10) then (erase g (body.toList.drop 10)).toArray
  else (erase g body.toList).toArray

theorem erase_emit (g : Nat) (is : List Instr) : ∀ (cs : List Nat), erase g (emit g is cs) = is := by
  induction is with
  | nil => intro cs; simp [emit, erase]
  | cons i is ih =>
    intro cs
    cases i <;> cases cs <;>
      simp [emit, erase, ih, isCharge_charge]

/-- Erasing the charges gives back the original body: the translated code is the
original code with fuel checks put in, and nothing else. -/
theorem erase_instrument (g : Nat) (body : Array Instr) : eraseBody g (instrument g body) = body := by
  rw [instrument_eq]
  simp [eraseBody, isCharge_charge, erase_emit]

/-! ## The module -/

/-- What the host needs besides the module: the original imports, in order (import `k`
of the translated module is import `k` here), and the fuel global. -/
structure Plan where
  imports : Array Import
  fuelGlobal : Nat
  deriving Inhabited

def renameImport (k : Nat) (i : Import) : Import := { i with module := importModule, name := importName k }

def isFuncImport (i : Import) : Bool := match i.desc with | .func _ => true | _ => false

/-- The pure part of the translation, applied once the checks have passed. -/
def translateModule (m : Module) (pages : Nat) : Module × Plan :=
  let g := m.importedGlobals.size + m.globals.size
  let mems := m.mems.map fun t =>
    { limits := { t.limits with max := some (min (t.limits.max.getD 65536) pages) } : MemType }
  ({ m with
      imports := m.imports.mapIdx renameImport
      mems
      globals := m.globals.push { type := ⟨true, .i64⟩, init := #[.i64Const 0, .end_] }
      exports := m.exports.push { name := fuelExport, desc := .global g }
      funcs := m.funcs.map fun f => { f with body := instrument g f.body } },
   { imports := m.imports, fuelGlobal := g })

/-- Translate a module (the caller has validated it). Refused: an import that is not a
function, a module without exactly one memory of its own, a memory whose minimum is over
`pages`, an export already named `fuelExport`, and more than 65536 imports. -/
def translate (m : Module) (pages : Nat) : Except String (Module × Plan) := do
  if m.imports.size > 65536 then throw "aot: more than 65536 imports"
  if !m.imports.all isFuncImport then throw "aot: the module imports something other than a function"
  if m.mems.size != 1 then throw "aot: the module must define exactly one memory"
  if m.mems.any (·.limits.min > pages) then throw "aot: the memory's minimum is over the page limit"
  if m.exports.any (·.name == fuelExport) then throw s!"aot: the module already exports {fuelExport}"
  return translateModule m pages

theorem translate_eq {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r) :
    r = translateModule m pages := by
  unfold translate at h
  repeat' split at h
  all_goals simp_all [Except.pure, pure, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] <;> exact h.symm

/-- Import `k` keeps its kind and type. -/
theorem translate_import_desc {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r) :
    r.1.imports.map (·.desc) = m.imports.map (·.desc) := by
  have e := translate_eq h; subst e
  apply Array.ext
  · simp [translateModule]
  · intro i _ _; simp [translateModule, renameImport]

/-- Import `k` is named `importName k` in module `aot`, and the plan routes it back to
original import `k`. -/
theorem translate_import_route {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r)
    (k : Nat) (hk : k < m.imports.size) :
    ∃ hk' : k < r.1.imports.size, r.1.imports[k] = { m.imports[k] with module := importModule, name := importName k } ∧
      r.2.imports[k]? = some m.imports[k] := by
  have e := translate_eq h; subst e
  refine ⟨by simpa [translateModule] using hk, ?_, ?_⟩
  · simp [translateModule, renameImport]
  · simp [translateModule, hk]

/-- The exports are the original exports, then the fuel global. -/
theorem translate_exports {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r) :
    r.1.exports = m.exports.push { name := fuelExport, desc := .global r.2.fuelGlobal } := by
  have e := translate_eq h; subst e
  rfl

/-- Each function keeps its type and locals, and its body is the original body with
charges (`erase_instrument`). -/
theorem translate_funcs {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r) :
    r.1.funcs.map (fun f => (f.type, f.locals, eraseBody r.2.fuelGlobal f.body)) =
      m.funcs.map (fun f => (f.type, f.locals, f.body)) := by
  have e := translate_eq h; subst e
  simp [translateModule, erase_instrument]

/-- Types, tables, data and element segments, the start function and the tags are the
original ones; only the memory's maximum changes, to at most `pages`. -/
theorem translate_rest {m : Module} {pages : Nat} {r : Module × Plan} (h : translate m pages = .ok r) :
    r.1.types = m.types ∧ r.1.tables = m.tables ∧ r.1.datas.size = m.datas.size ∧
    r.1.start = m.start ∧ r.1.tags = m.tags ∧ r.1.mems.size = m.mems.size ∧
    (∀ t ∈ r.1.mems, ∃ x, t.limits.max = some x ∧ x ≤ pages) := by
  have e := translate_eq h; subst e
  refine ⟨rfl, rfl, rfl, rfl, rfl, by simp [translateModule], ?_⟩
  intro t ht
  simp [translateModule] at ht
  obtain ⟨u, _, rfl⟩ := ht
  exact ⟨_, rfl, Nat.min_le_right _ _⟩

end L4Factoidal.WasmVM.Aot
