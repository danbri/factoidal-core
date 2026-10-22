import Std.Data.HashMap.Lemmas

namespace L4Factoidal.SPARQL.StableGrouping

/-- A group preserves its first key and the input order of its rows. -/
structure Group (κ α : Type) where
  key : κ
  solutions : List α
  deriving BEq, Repr

/-- Reference insertion deliberately accepts any Boolean matching relation.
    If several existing groups match, every one receives the row. -/
def add (same : κ → κ → Bool) (key : κ) (row : α) (groups : List (Group κ α)) :
    List (Group κ α) :=
  if groups.any (fun group => same key group.key) then
    groups.map fun group =>
      if same key group.key then { group with solutions := group.solutions ++ [row] }
      else group
  else groups ++ [⟨key, [row]⟩]

def reference (same : κ → κ → Bool) (key : α → κ) (value : α → β)
    (rows : List α) : List (Group κ β) :=
  rows.foldl (fun groups row => add same (key row) (value row) groups) []

/-- During accumulation each group's rows run backwards, avoiding append. -/
def addRev (same : κ → κ → Bool) (key : κ) (row : α) (groups : List (Group κ α)) :
    List (Group κ α) :=
  if groups.any (fun group => same key group.key) then
    groups.map fun group =>
      if same key group.key then { group with solutions := row :: group.solutions }
      else group
  else groups ++ [⟨key, [row]⟩]

def finishRev (groups : List (Group κ α)) : List (Group κ α) :=
  groups.map fun group => { group with solutions := group.solutions.reverse }

def fallback (same : κ → κ → Bool) (key : α → κ) (value : α → β)
    (rows : List α) (groups : List (Group κ β)) : List (Group κ β) :=
  finishRev (rows.foldl (fun acc row => addRev same (key row) (value row) acc) groups)

/-- Array positions keep first-appearance order; the hash map addresses
    groups directly. The separate validity predicate is proof-only. -/
structure State (κ η β : Type) [BEq η] [Hashable η] where
  groups : Array (Group κ β)
  positions : Std.HashMap η Nat

def State.empty [BEq η] [Hashable η] : State κ η β := ⟨#[], ∅⟩

def State.add [BEq η] [Hashable η] (state : State κ η β)
    (key : κ) (encoded : η) (row : β) : State κ η β :=
  match state with
  | ⟨groups, positions⟩ =>
    match positions[encoded]? with
    | some index =>
        ⟨groups.modify index (fun group => { group with solutions := row :: group.solutions }), positions⟩
    | none =>
        -- Read the old size before push, so native evaluation need not keep
        -- an extra array reference alive while growing a new group.
        let positions := positions.insert encoded groups.size
        ⟨groups.push ⟨key, [row]⟩, positions⟩

def hashFrom [BEq η] [Hashable η] (same : κ → κ → Bool) (encode : κ → Option η)
    (key : α → κ) (value : α → β) : List α → State κ η β → List (Group κ β)
  | [], state => finishRev state.groups.toList
  | row :: rows, state =>
      let rowKey := key row
      match encode rowKey with
      | some encoded => hashFrom same encode key value rows (state.add rowKey encoded (value row))
      | none => fallback same key value rows (addRev same rowKey (value row) state.groups.toList)

/-- An exact encoder identifies one semantic group. Unsupported keys retain
    arbitrary-relation insertion, including updates to multiple groups. -/
def fast [BEq η] [Hashable η] (same : κ → κ → Bool) (encode : κ → Option η)
    (key : α → κ) (value : α → β) (rows : List α) : List (Group κ β) :=
  hashFrom same encode key value rows State.empty

end L4Factoidal.SPARQL.StableGrouping
