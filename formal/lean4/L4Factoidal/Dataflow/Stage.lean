/-
L4Factoidal.Dataflow.Stage — the dataflow frame of the system: wire types,
stages with contracts, IO boundary stages with named assumptions, and
composition (https://github.com/danbri/factoidal/issues/975, phase A3).

Owner, 2026-10-23, verbatim: "the issue infests the whole system ... Some
representation of that data flow and the integration of all the lean-powered
parts is needed, parsers, stores, reasoners, whatever."

## Wire types

The values that travel between components. Each is an existing type of the
tree; this module gives names only.

* `Document`: the bytes of a document, its media type and a source id (the
  system boundary: a file, an HTTP body).
* `RDF.Dataset`: an RDF dataset as a finite value (lists). Its meaning is
  `RDF.DatasetDen` (`Dataset.den`, phase A1): membership per graph, graph names
  with empty named graphs, RDF term equality (`Triple.key`). A stage passes the
  value and states its contract on the meaning. `DatasetDen` is `Prop`-valued,
  so it is the target of contracts and not a runtime value.
* `SPARQL.SolutionSeq`, `SPARQL.QueryResult`: solution sequences with
  multiplicity (a list of `Binding`), and the SELECT/ASK result form.
* `FPP0.Bundle`: derivations and evidence (the FPP0 proof bundle,
  https://github.com/danbri/factoidal/issues/615).
* `SHACL.ValidationReport`: validation reports.

## Stages

`Stage ε α β`: a function `run : α → Except ε β`, a relation
`contract : α → β → Prop`, and `sound`: every successful run satisfies the
contract. A stage that never fails is `Stage.ofFun`.

## IO boundary stages

File, socket, clock and host calls are opaque to Lean. `IOStage ε α β` holds
the contract only: `assumption`, a relation with a name (the name of the
`IOStage` value and of the `Prop` it holds, for example `ReadsWritten`). It
has no proof of soundness. `IOStage.Realised io run` says that a model `run`
of the IO step satisfies the assumption; `IOStage.toStage` makes a `Stage`
from it, and a theorem that uses the stage takes `Realised` as a hypothesis.
So an IO assumption is always a premise with a name, never an `axiom`.

## Composition

`Stage.comp s t` runs `s` and then `t` on its output; an error of `s` stops
the run. Its contract is the relational composition `RelComp s.contract
t.contract`: there is a middle value that satisfies the first contract and,
with the output, the second (`Stage.comp_contract`, `Stage.comp_ok_contract`).
`RelComp.assoc` gives associativity, `Stage.second` runs a stage on the second
component of a pair and keeps the first, `Stage.weaken` replaces a contract by
a weaker one, `Stage.mapError` changes the error type.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetDenotation
import L4Factoidal.SPARQL.Results
import L4Factoidal.Proof.Syntax
import L4Factoidal.SHACL.Validation

namespace L4Factoidal.Dataflow

/-! ## Wire types -/

/-- A document at the system boundary: its bytes, its media type (for example
`text/turtle; charset=utf-8`; the empty string when it is absent, then
`RDF.formatOfDocument` reads the registered extension of the source), and the
id of its source (a path or a URL). The source id is the scope of the blank-node
labels of the document (RDF 1.1 Concepts section 3.4); no parser contract
uses it yet (phase C of issue 975). -/
structure Document where
  bytes : ByteArray
  mediaType : String
  source : String

/-- An RDF dataset on the wire: a finite value; its meaning is `Dataset.den`. -/
abbrev DatasetValue := RDF.Dataset

/-- The meaning of a dataset: the target of contracts. -/
abbrev DatasetMeaning := RDF.DatasetDen

/-- An RDF graph on the wire (the reasoners take and give one graph). -/
abbrev GraphValue := RDF.Graph

/-- A solution sequence with multiplicity. -/
abbrev Solutions := SPARQL.SolutionSeq

/-- A SELECT or ASK result. -/
abbrev Results := SPARQL.QueryResult

/-- Derivations and evidence: an FPP0 proof bundle. -/
abbrev Evidence := FPP0.Bundle

/-- A SHACL validation report. -/
abbrev Report := SHACL.ValidationReport

/-! ## Relational composition -/

/-- The relational composition of two relations. -/
def RelComp {α β γ : Type} (r : α → β → Prop) (q : β → γ → Prop) : α → γ → Prop :=
  fun a c => ∃ b, r a b ∧ q b c

theorem RelComp.assoc {α β γ δ : Type} (r : α → β → Prop) (q : β → γ → Prop)
    (u : γ → δ → Prop) : RelComp (RelComp r q) u = RelComp r (RelComp q u) := by
  funext a d
  apply propext
  constructor
  · rintro ⟨c, ⟨b, hr, hq⟩, hu⟩
    exact ⟨b, hr, c, hq, hu⟩
  · rintro ⟨b, hr, c, hq, hu⟩
    exact ⟨c, ⟨b, hr, hq⟩, hu⟩

theorem RelComp.mono {α β γ : Type} {r r' : α → β → Prop} {q q' : β → γ → Prop}
    (hr : ∀ a b, r a b → r' a b) (hq : ∀ b c, q b c → q' b c) :
    ∀ a c, RelComp r q a c → RelComp r' q' a c := by
  rintro a c ⟨b, h1, h2⟩
  exact ⟨b, hr a b h1, hq b c h2⟩

/-! ## Stages -/

/-- A stage: a run, a contract between input and output, and the proof that
every successful run satisfies the contract. -/
structure Stage (ε α β : Type) where
  run : α → Except ε β
  contract : α → β → Prop
  sound : ∀ a b, run a = .ok b → contract a b

namespace Stage

variable {ε ε' α β γ δ : Type}

/-- A stage that never fails. -/
def ofFun (f : α → β) (c : α → β → Prop) (h : ∀ a, c a (f a)) : Stage ε α β where
  run a := .ok (f a)
  contract := c
  sound := by
    intro a b hr
    cases hr
    exact h a

/-- The stage that passes its input on. -/
def id : Stage ε α α := ofFun (fun a => a) (fun a b => b = a) (fun _ => rfl)

/-- Run `s`, then `t` on its output. -/
def comp (s : Stage ε α β) (t : Stage ε β γ) : Stage ε α γ where
  run a :=
    match s.run a with
    | .ok b => t.run b
    | .error e => .error e
  contract := RelComp s.contract t.contract
  sound := by
    intro a c h
    revert h
    cases hs : s.run a with
    | error e => intro h; cases h
    | ok b => intro h; exact ⟨b, s.sound a b hs, t.sound b c h⟩

/-- **Contracts compose.** The contract of a composition is the relational
composition of the two contracts. -/
theorem comp_contract (s : Stage ε α β) (t : Stage ε β γ) :
    (s.comp t).contract = RelComp s.contract t.contract := rfl

/-- A successful composite run goes through a middle value. -/
theorem comp_ok (s : Stage ε α β) (t : Stage ε β γ) {a : α} {c : γ}
    (h : (s.comp t).run a = .ok c) : ∃ b, s.run a = .ok b ∧ t.run b = .ok c := by
  revert h
  show (match s.run a with | .ok b => t.run b | .error e => .error e) = .ok c → _
  cases hs : s.run a with
  | error e => intro h; cases h
  | ok b => intro h; exact ⟨b, rfl, h⟩

/-- A successful composite run satisfies both contracts at one middle value. -/
theorem comp_ok_contract (s : Stage ε α β) (t : Stage ε β γ) {a : α} {c : γ}
    (h : (s.comp t).run a = .ok c) : ∃ b, s.contract a b ∧ t.contract b c :=
  (s.comp t).sound a c h

/-- Run a stage on the second component; keep the first. -/
def second (s : Stage ε β γ) : Stage ε (α × β) (α × γ) where
  run p :=
    match s.run p.2 with
    | .ok c => .ok (p.1, c)
    | .error e => .error e
  contract p q := q.1 = p.1 ∧ s.contract p.2 q.2
  sound := by
    rintro ⟨a, b⟩ ⟨a', c⟩ h
    dsimp only at h
    cases hs : s.run b with
    | error e => rw [hs] at h; cases h
    | ok c' =>
      rw [hs] at h
      injection h with h
      injection h with h1 h2
      subst h1
      subst h2
      exact ⟨rfl, s.sound b c' hs⟩

/-- Replace the contract by a weaker one. -/
def weaken (s : Stage ε α β) (c : α → β → Prop) (h : ∀ a b, s.contract a b → c a b) :
    Stage ε α β where
  run := s.run
  contract := c
  sound a b hr := h a b (s.sound a b hr)

/-- Change the error type. -/
def mapError (f : ε → ε') (s : Stage ε α β) : Stage ε' α β where
  run a :=
    match s.run a with
    | .ok b => .ok b
    | .error e => .error (f e)
  contract := s.contract
  sound := by
    intro a b h
    cases hs : s.run a with
    | error e => rw [hs] at h; cases h
    | ok b' =>
      rw [hs] at h
      injection h with h
      subst h
      exact s.sound a b' hs

theorem mapError_ok (f : ε → ε') (s : Stage ε α β) {a : α} {b : β}
    (h : (s.mapError f).run a = .ok b) : s.run a = .ok b := by
    dsimp only [mapError] at h
    cases hs : s.run a with
    | error e => rw [hs] at h; cases h
    | ok b' =>
      rw [hs] at h
      injection h with h
      rw [h]

end Stage

/-! ## IO boundary stages -/

/-- An IO stage: only its contract, a named assumption. Lean does not see the
IO action; `Realised` states that a model of it satisfies the assumption. -/
structure IOStage (ε α β : Type) where
  assumption : α → β → Prop

namespace IOStage

variable {ε α β : Type}

/-- The model `run` of the IO step satisfies the named assumption. This is a
hypothesis of every theorem that uses the stage. -/
def Realised (io : IOStage ε α β) (run : α → Except ε β) : Prop :=
  ∀ a b, run a = .ok b → io.assumption a b

/-- The stage of an IO step, under its named assumption. -/
def toStage (io : IOStage ε α β) (run : α → Except ε β) (h : io.Realised run) : Stage ε α β where
  run := run
  contract := io.assumption
  sound := h

theorem toStage_contract (io : IOStage ε α β) (run : α → Except ε β) (h : io.Realised run) :
    (io.toStage run h).contract = io.assumption := rfl

end IOStage

#print axioms RelComp.assoc
#print axioms Stage.comp_contract
#print axioms Stage.comp_ok
#print axioms Stage.comp_ok_contract
#print axioms Stage.second
#print axioms Stage.mapError_ok

end L4Factoidal.Dataflow
