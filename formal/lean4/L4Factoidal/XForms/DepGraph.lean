/-
L4Factoidal.XForms.DepGraph — the dependency graph of XForms
recalculation (XForms 1.1 §4.3.2 and Appendix C), stated over an
arbitrary vertex type and an arbitrary evaluation function.

A vertex is a computed thing (in the engine: a `calculate` or another
model item property expression of one bind on one node). `deps v` lists
the vertices whose values the evaluation of `v` reads. `topoSort` gives
an order in which every vertex comes after the vertices it reads, or
`none` when there is no such order. `recalc` evaluates the vertices in
a given order over a state `σ : V → α`.

The engine (`XForms/Model.lean`) calls `topoSort` for its
recalculation order; the theorems about these definitions are in
`XForms/Theorems.lean`.
-/
namespace L4Factoidal.XForms.DepGraph

variable {V : Type} [DecidableEq V] {α : Type}

/-- No dependency of `v` is among the vertices still to be ordered. A
    vertex that reads itself is never ready. -/
def ready (deps : V → List V) (rem : List V) (v : V) : Bool :=
  (deps v).all (fun u => !rem.contains u)

/-- Kahn's algorithm, one vertex per step: take the first vertex of
    `rem` that is ready, emit it, continue with the others. `acc` holds
    the emitted vertices, newest first. The first argument is a step
    bound (`rem.length` is enough). Tail recursive. -/
def topoLoop (deps : V → List V) : Nat → List V → List V → Option (List V)
  | 0, rem, acc => if rem.isEmpty then some acc.reverse else none
  | n + 1, rem, acc =>
    if rem.isEmpty then some acc.reverse else
    match rem.find? (ready deps rem) with
    | none => none
    | some v => topoLoop deps n (rem.filter (fun x => x != v)) (v :: acc)

/-- An order of `vs` in which each vertex follows the vertices it
    reads, or `none` when the graph restricted to `vs` has a cycle. -/
def topoSort (deps : V → List V) (vs : List V) : Option (List V) :=
  topoLoop deps vs.length vs []

/-- `o` is a topological order: no vertex occurs twice, and no
    dependency of a vertex occurs at or after it. A dependency outside
    `o` is allowed (an input that is not computed). -/
def Topo (deps : V → List V) : List V → Prop
  | [] => True
  | v :: rest => (∀ u, u ∈ deps v → u ≠ v ∧ u ∉ rest) ∧ v ∉ rest ∧ Topo deps rest

/-- A cyclic core: a non-empty set of vertices each of which reads a
    member of the set. A finite graph has a directed cycle exactly when
    it has a cyclic core (follow the dependencies inside the set). -/
def CyclicCore (deps : V → List V) (S : List V) : Prop :=
  S ≠ [] ∧ ∀ v, v ∈ S → ∃ u, u ∈ deps v ∧ u ∈ S

/-- The state with `v` set to `a`. -/
def update (σ : V → α) (v : V) (a : α) : V → α :=
  fun x => if x = v then a else σ x

/-- Evaluate the vertices of `o` in order; each result is stored
    before the next vertex is evaluated. Tail recursive. -/
def recalc (ev : V → (V → α) → α) : List V → (V → α) → (V → α)
  | [], σ => σ
  | v :: rest, σ => recalc ev rest (update σ v (ev v σ))

/-- The evaluation of `v` reads only the vertices in `deps v`. -/
def Local (deps : V → List V) (ev : V → (V → α) → α) : Prop :=
  ∀ v σ σ', (∀ u, u ∈ deps v → σ u = σ' u) → ev v σ = ev v σ'

end L4Factoidal.XForms.DepGraph
