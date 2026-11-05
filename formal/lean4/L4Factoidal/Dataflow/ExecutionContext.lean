/-
Experimental execution grants. These are trusted-host choices, not identities
or certificates accepted from query input. Capture produces immutable provider
snapshots; theorems bound admitted providers, not confidentiality, attempted
lookups, timing, host callback implementations or general resource I/O.
-/
import Init

namespace L4Factoidal.Dataflow.ExecutionContext

structure Grants where
  services : List String := []
  extensions : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- Captured values have no registry references. Payload can be a SERVICE graph. -/
structure Snapshot (α : Type) where
  grants : Grants
  services : List (String × α)
  extensions : List String
  serviceGranted : ∀ entry ∈ services, entry.1 ∈ grants.services
  extensionGranted : ∀ iri ∈ extensions, iri ∈ grants.extensions

/-- Filtering the actual provider tables, not scanning query text. -/
def capture (g : Grants) (services : List (String × α)) (extensions : List String) : Snapshot α :=
  { grants := g
    services := services.filter (fun p => g.services.contains p.1)
    extensions := extensions.filter (fun iri => g.extensions.contains iri)
    serviceGranted := by
      intro entry h
      exact List.contains_iff_mem.mp (List.mem_filter.mp h).2
    extensionGranted := by
      intro iri h
      exact List.contains_iff_mem.mp (List.mem_filter.mp h).2 }

theorem captured_service_granted (g : Grants) (services : List (String × α))
    (extensions : List String) (entry : String × α)
    (h : entry ∈ (capture g services extensions).services) : entry.1 ∈ g.services := by
  exact List.contains_iff_mem.mp (List.mem_filter.mp h).2

theorem captured_service_original (g : Grants) (services : List (String × α))
    (extensions : List String) (entry : String × α)
    (h : entry ∈ (capture g services extensions).services) : entry ∈ services :=
  (List.mem_filter.mp h).1

theorem captured_extension_granted (g : Grants) (services : List (String × α))
    (extensions : List String) (iri : String)
    (h : iri ∈ (capture g services extensions).extensions) : iri ∈ g.extensions := by
  exact List.contains_iff_mem.mp (List.mem_filter.mp h).2

/-- First matching provider, the same association-list rule as SERVICE lookup. -/
def lookup (entries : List (String × α)) (iri : String) : Option α :=
  match entries with
  | [] => none
  | (name, value) :: rest => if name == iri then some value else lookup rest iri

theorem lookup_none_of_absent (entries : List (String × α)) (iri : String)
    (h : ∀ entry ∈ entries, entry.1 ≠ iri) : lookup entries iri = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    have hn := h entry (by simp)
    have ht : ∀ e ∈ rest, e.1 ≠ iri := fun e he => h e (by simp [he])
    cases entry with
    | mk name value => simp [lookup, hn, ih ht]

theorem ungranted_service_unavailable (g : Grants) (services : List (String × α))
    (extensions : List String) (iri : String) (h : iri ∉ g.services) :
    lookup (capture g services extensions).services iri = none := by
  apply lookup_none_of_absent
  intro entry he eq
  exact h (eq ▸ captured_service_granted g services extensions entry he)

theorem ungranted_extension_absent (g : Grants) (services : List (String × α))
    (extensions : List String) (iri : String) (h : iri ∉ g.extensions) :
    iri ∉ (capture g services extensions).extensions := by
  intro hi
  exact h (captured_extension_granted g services extensions iri hi)

/-- Explicit gate for callback providers. A denied name never selects provider. -/
def dispatch (registered : List String) (provider : String → β → Option γ)
    (iri : String) (args : β) : Option γ :=
  if registered.contains iri then provider iri args else none

theorem dispatch_ungranted (g : Grants) (services : List (String × α))
    (extensions : List String) (provider : String → β → Option γ)
    (iri : String) (args : β) (h : iri ∉ g.extensions) :
    dispatch (capture g services extensions).extensions provider iri args = none := by
  have ha := ungranted_extension_absent g services extensions iri h
  simp [dispatch, ha]

#print axioms captured_service_granted
#print axioms ungranted_service_unavailable
#print axioms dispatch_ungranted
end L4Factoidal.Dataflow.ExecutionContext
