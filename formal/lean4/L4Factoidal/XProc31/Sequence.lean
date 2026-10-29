import L4Factoidal.XProc31.Core
import Init.Data.List.Monadic
import Init.Control.Lawful.Instances

namespace L4Factoidal.XProc31

-- Lean 4.33.1 does not register the elementary EST monad laws for IO.
-- Keep this proof local: it unfolds the actual state/error representation.
local instance : LawfulMonad IO := .mk'
  (id_map := fun x => funext fun state => by
    simp only [Functor.map, instMonadEIO._aux_1, EST.bind, Function.comp_apply, EST.pure]
    cases x state <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => funext fun state => by
    simp only [bind, instMonadEIO._aux_13, EST.bind]
    cases x state <;> rfl)
  (map_const := fun _ _ => rfl)

/-- Indexed traversal in the exception transformer. An iteration error stops
all later callbacks. The original sequence size is fixed across iterations. -/
def forEachIOFrom (size position : Nat) (docs : List Document)
    (f : Nat → Nat → Document → IO (Result (List Document))) : IO (Result (List Document)) :=
  ExceptT.run (List.flatten <$> (docs.zipIdx position).mapM
    (fun (doc, i) => ExceptT.mk (f i size doc) : Document × Nat → ExceptT ProcError IO (List Document)))

/-- Runtime p:for-each traversal, with one-based position and fixed size. -/
def forEachIO (docs : List Document)
    (f : Nat → Nat → Document → IO (Result (List Document))) : IO (Result (List Document)) :=
  forEachIOFrom docs.length 1 docs f

/-- The action itself is the ordered monadic map, followed by concatenation;
this includes IO effects and short-circuit propagation of ProcError. -/
theorem forEachIO_mapM (docs : List Document)
    (f : Nat → Nat → Document → IO (Result (List Document))) :
    forEachIO docs f = ExceptT.run (List.flatten <$> (docs.zipIdx 1).mapM
      (fun (doc, i) => ExceptT.mk (f i docs.length doc) : Document × Nat → ExceptT ProcError IO (List Document))) := rfl

theorem forEachIOFrom_nil (size position : Nat)
    (f : Nat → Nat → Document → IO (Result (List Document))) :
    forEachIOFrom size position [] f = pure (.ok []) := by
  simp [forEachIOFrom, map_pure, ExceptT.run_pure]

/-- One actual iteration: do not execute the tail after an error. -/
theorem forEachIOFrom_cons (size position : Nat) (doc : Document) (docs : List Document)
    (f : Nat → Nat → Document → IO (Result (List Document))) :
    forEachIOFrom size position (doc :: docs) f = (do
      match ← f position size doc with
      | .error err => pure (.error err)
      | .ok batch =>
        let rest ← forEachIOFrom size (position + 1) docs f
        pure (rest.map (batch ++ ·))) := by
  simp only [forEachIOFrom, List.zipIdx_cons, List.mapM_cons, ExceptT.run_map, ExceptT.run_bind]
  simp only [ExceptT.run, ExceptT.mk, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro result
  cases result <;> simp [Except.map]
  simp only [map_eq_pure_bind]
  apply bind_congr
  intro remaining
  cases remaining <;> rfl

/-- A failure at the first iteration suppresses every later callback. -/
theorem forEachIO_error_head (doc : Document) (docs : List Document)
    (f : Nat → Nat → Document → IO (Result (List Document))) (err : ProcError)
    (h : f 1 (doc :: docs).length doc = pure (.error err)) :
    forEachIO (doc :: docs) f = pure (.error err) := by
  rw [forEachIO, forEachIOFrom_cons, h]
  simp

-- Execute both effects and output checks; later iterations must not run
-- after a processor error, and successful batches retain input order.
#eval (do
  let docs : List Document := [⟨.text "a", "text/plain", "", [], none⟩, ⟨.text "b", "text/plain", "", [], none⟩,
    ⟨.text "c", "text/plain", "", [], none⟩]
  let calls ← IO.mkRef ([] : List Nat)
  let result ← forEachIO docs fun pos size doc => do
    calls.modify (· ++ [pos])
    if size != 3 then throw (IO.userError "wrong iteration size")
    if pos == 2 then return .error ⟨"test:error", "stop", false, [], none⟩
    return .ok [doc]
  if (← calls.get) != [1, 2] then throw (IO.userError "for-each did not short-circuit")
  match result with
  | .error e => if e.code != "test:error" then throw (IO.userError "wrong propagated error")
  | .ok _ => throw (IO.userError "for-each lost the error")
  let result ← forEachIO docs fun pos size doc =>
    pure (.ok [{ doc with node := .text s!"{pos}/{size}" }, doc])
  match result with
  | .ok out =>
    if out.map (·.node.textContent) != ["1/3", "a", "2/3", "b", "3/3", "c"] then
      throw (IO.userError "for-each order or context is wrong")
  | .error _ => throw (IO.userError "for-each unexpectedly failed")
  IO.println "XProc sequence checks: 2 pass" : IO Unit)

#print axioms forEachIO_mapM
#print axioms forEachIOFrom_nil
#print axioms forEachIOFrom_cons
#print axioms forEachIO_error_head
end L4Factoidal.XProc31
