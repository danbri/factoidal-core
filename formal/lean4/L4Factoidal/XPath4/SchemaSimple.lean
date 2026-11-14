/-
L4Factoidal.XPath4.SchemaSimple — atomic values and the simple types of an
in-scope schema: `cast as T`, `castable as T`, the constructor function
`T(...)` and `instance of T` for a simple type `T` that is not built in
(a restriction with facets, a list, a union).

The type is given by its XSD 1.1 Part 2 body (`XSD.SimpleType`, which the
schema reader of `L4Factoidal.XSD11` builds along the base chain), so
validity of a lexical form is `XSD.valueOf`, the one validator of the tree.

Rules (F&O 4.0 §23.3, "Casting to derived types", "Casting to union
types", "Casting to list types"; the same rules as F&O 3.1 §19.3):

* atomic type derived from built-in `B`: cast to `B` by the casting table
  (`castAtomic`); the facets of the type are tested on the lexical form
  (the string itself for a string or untyped value, else the canonical
  form of the result); FORG0001 when they do not hold;
* list type: only a string or an untyped value (XPTY0004 otherwise); the
  whitespace-separated tokens are each cast to the item type; the result
  is the sequence;
* union type: a string or untyped value is cast to the members in order;
  another value that is in the value space of a member is kept; else it
  is cast to the members in order; FORG0001 when no member takes it.

Limit, stated: an atomic value of this tree carries a built-in type only
(`Atomic.ty`), so the result of a cast to a derived atomic type has the
built-in base as its type, and `instance of T` is decided by value
(`atomInBody`: the value's type derives from the base of `T` and its
lexical form is valid for `T`). A value of the base type that lies in the
value space of `T` is therefore an instance of `T` here, which the
specification says only of a value labelled with `T`
(https://github.com/danbri/factoidal/issues/1152 item 2).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XPath4.Atomic
import L4Factoidal.XSD.SimpleType

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-- A string or an untyped value: its cast goes by the lexical form. -/
def Atomic.isLexical (a : Atomic) : Bool := a.is .string || a.ty == .untyped

/-- The XSD canonical lexical form of a value (XSD 1.1 Part 2, the
canonical mapping of its built-in type): what a `pattern` or
`enumeration` facet is tested on when the value did not come from a
string (F&O 4.0 §23.3.1: "the pattern is tested against the canonical
representation of the value"). An `xs:double` 93.7 has the canonical form
`9.37E1`, not its XPath string value `93.7`. -/
def xsdCanon (v : Atomic) : String :=
  match v.ty with
  | .b b =>
    match lexicalMap b v.str with
    | some x => let c := canonicalMap b x; if c == "" then v.str else c
    | none => v.str
  | .untyped => v.str

/-- `instance of` a simple type of the schema, by value: the value's type
derives from the built-in base and its lexical form is valid for the type
(facets included); a union takes what a member takes, when the union's
own facets hold; a list type has no atomic instances. -/
def atomInBodyF : Nat → SimpleType → Atomic → Bool
  | 0, _, _ => false
  | n + 1, t, a =>
    match t with
    | .atomic b _ => b != .anySimpleType && a.ty.derives (.b b) && (valueOf t (xsdCanon a)).isSome
    | .list _ _ => false
    | .union ms _ => ms.any (fun m => atomInBodyF n m a) && (valueOf t (xsdCanon a)).isSome

def atomInBody (t : SimpleType) (a : Atomic) : Bool := atomInBodyF 16 t a

/-- No constraining facet (the `whiteSpace` facet, which does not
constrain the value space, is not looked at). -/
def facetsNone (f : Facets) : Bool :=
  f.length.isNone && f.minLength.isNone && f.maxLength.isNone && f.patterns.isEmpty &&
  f.enumeration.isNone && f.maxInclusive.isNone && f.maxExclusive.isNone &&
  f.minInclusive.isNone && f.minExclusive.isNone && f.totalDigits.isNone &&
  f.fractionDigits.isNone && f.explicitTimezone.isNone && !f.hasAssertion

/-- Is the type a generalized atomic type (XPath 4.0 §3.2.7): an atomic
type, or a pure union type (no facets of its own, every member a
generalized atomic type)? A list type is not. -/
def generalizedF : Nat → SimpleType → Bool
  | 0, _ => false
  | n + 1, t =>
    match t with
    | .atomic b _ => b != .anySimpleType
    | .list _ _ => false
    | .union ms f => facetsNone f && ms.all (generalizedF n)

def generalized (t : SimpleType) : Bool := generalizedF 16 t

/-- The built-in atomic types that a pure union of built-in types (no
facets anywhere) is the union of, in order; `none` for another type. Such
a union is the choice of those types. -/
def pureLeavesF : Nat → SimpleType → Option (List AType)
  | 0, _ => none
  | n + 1, t =>
    match t with
    | .atomic b f => if facetsNone f && b != .anySimpleType then some [.b b] else none
    | .list _ _ => none
    | .union ms f => if facetsNone f then (ms.mapM (pureLeavesF n)).map List.flatten else none

def pureLeaves (t : SimpleType) : Option (List AType) := pureLeavesF 16 t

/-- The first member that takes the value. -/
def firstCast (f : SimpleType → M (List Atomic)) : List SimpleType → Option (List Atomic)
  | [] => none
  | m :: ms =>
    match f m with
    | .ok r => some r
    | .error _ => firstCast f ms

/-- The lexical form the facets are tested on after a cast gave `r`. -/
def lexAfter (a : Atomic) (r : List Atomic) : String :=
  if a.isLexical then a.str
  else match r with
    | [v] => xsdCanon v
    | _ => xsdCanon a

/-- `cast as T` for a simple type `T` of the schema with Part 2 body `t`. -/
def castToBodyF (ns : String → Option String) : Nat → SimpleType → Atomic → M (List Atomic)
  | 0, _, _ => err "FOER0000" "the simple type is nested too deeply"
  | n + 1, t, a =>
    match t with
    | .atomic b _ =>
      if b == .anySimpleType || b == .anyAtomicType then err "XPST0080" "cast to an abstract type"
      else
        match castAtomic a (.b b) ns with
        | .error e => .error e
        | .ok v =>
          if (valueOf t (lexAfter a [v])).isSome then .ok [v]
          else err "FORG0001" ("the value " ++ lexAfter a [v] ++ " does not satisfy the facets of the type")
    | .list item _ =>
      if !a.isLexical then err "XPTY0004" "only a string or an untyped value can be cast to a list type"
      else
        let norm := applyWhiteSpace .collapse a.str
        if (valueOf t norm).isNone then err "FORG0001" ("the value " ++ a.str ++ " is not valid for the list type")
        else
          match ((norm.splitOn " ").filter (· != "")).mapM
              (fun tk => castToBodyF ns n item (Atomic.untypedOf tk)) with
          | .error e => .error e
          | .ok rs => .ok rs.flatten
    | .union ms _ =>
      if !a.isLexical && ms.any (fun m => atomInBodyF n m a) && (valueOf t (xsdCanon a)).isSome then .ok [a]
      else
        match firstCast (fun m => castToBodyF ns n m a) ms with
        | none => err "FORG0001" ("the value " ++ a.str ++ " cannot be cast to any member of the union type")
        | some r =>
          if (valueOf t (lexAfter a r)).isSome then .ok r
          else err "FORG0001" ("the value " ++ lexAfter a r ++ " does not satisfy the facets of the union type")

def castToBody (ns : String → Option String) (t : SimpleType) (a : Atomic) : M (List Atomic) :=
  castToBodyF ns 16 t a

/-! ## Theorems -/

/-- Kind: soundness of the instance test against Part 2 validation.
Says: an atomic value that `atomInBodyF` accepts for an atomic type has a
type that derives from the type's built-in base, and its lexical form is
valid for the type (`XSD.valueOf`, facets included).
Does not say: that the value is labelled with the type (no value of this
tree is), or the converse for a value whose type annotation is a derived
user type. -/
theorem atomInBody_atomic_sound (n : Nat) (b : Builtin) (f : Facets) (a : Atomic)
    (h : atomInBodyF (n + 1) (.atomic b f) a = true) :
    a.ty.derives (.b b) = true ∧ (valueOf (.atomic b f) (xsdCanon a)).isSome = true := by
  simp only [atomInBodyF, Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

/-- Kind: a refusal that must hold.
Says: no atomic value is an instance of a list type.
Does not say: anything about a sequence of values. -/
theorem atomInBody_list (n : Nat) (item : SimpleType) (f : Facets) (a : Atomic) :
    atomInBodyF n (.list item f) a = false := by
  cases n <;> rfl

/-- Kind: soundness of the instance test for a union.
Says: a value accepted for a union type is accepted for one of its member
types, and its lexical form is valid for the union (the union's own
facets hold).
Does not say: which member, or that the members are tried in order. -/
theorem atomInBody_union_sound (n : Nat) (ms : List SimpleType) (f : Facets) (a : Atomic)
    (h : atomInBodyF (n + 1) (.union ms f) a = true) :
    (∃ m ∈ ms, atomInBodyF n m a = true) ∧ (valueOf (.union ms f) (xsdCanon a)).isSome = true := by
  simp only [atomInBodyF, Bool.and_eq_true, List.any_eq_true] at h
  exact ⟨h.1, h.2⟩

/-- Kind: soundness of the cast against the casting table and Part 2
validation.
Says: when a cast to an atomic type derived from built-in `b` succeeds,
the result is the one value that the cast to `b` gives (`castAtomic`),
and the lexical form the facets are tested on is valid for the derived
type (`XSD.valueOf`).
Does not say: that the result is labelled with the derived type (it has
type `b` or the type `castAtomic` gives), or that `castAtomic` agrees with
`XSD.lexicalMap` on every literal. -/
theorem castToBody_atomic_sound (ns : String → Option String) (n : Nat) (b : Builtin) (f : Facets)
    (a : Atomic) (vs : List Atomic) (h : castToBodyF ns (n + 1) (.atomic b f) a = .ok vs) :
    ∃ v, vs = [v] ∧ castAtomic a (.b b) ns = .ok v ∧
      (valueOf (.atomic b f) (lexAfter a [v])).isSome = true := by
  simp only [castToBodyF] at h
  split at h
  · simp [err] at h
  · split at h
    · simp at h
    · rename_i v hv
      split at h
      · rename_i hval
        refine ⟨v, ?_, hv, hval⟩
        cases h; rfl
      · simp [err] at h

/-- Kind: a refusal that must hold (F&O 4.0 §23.3, casting to list types).
Says: a value that is neither a string nor untyped is never cast to a
list type: the result is the error XPTY0004.
Does not say: anything about string or untyped values. -/
theorem castToBody_list_needs_lexical (ns : String → Option String) (n : Nat) (item : SimpleType)
    (f : Facets) (a : Atomic) (h : a.isLexical = false) :
    ∃ e, castToBodyF ns (n + 1) (.list item f) a = .error e ∧ e.code = "XPTY0004" := by
  simp [castToBodyF, h, err]

/-- Kind: identity on members (F&O 4.0 §23.3, casting to union types).
Says: a value that is not a string or untyped, that is in the value space
of a member type and valid for the union, is cast to the union as itself.
Does not say: what a string or untyped value is cast to. -/
theorem castToBody_union_keeps (ns : String → Option String) (n : Nat) (ms : List SimpleType)
    (f : Facets) (a : Atomic) (hl : a.isLexical = false)
    (hm : ms.any (fun m => atomInBodyF n m a) = true)
    (hv : (valueOf (.union ms f) (xsdCanon a)).isSome = true) :
    castToBodyF ns (n + 1) (.union ms f) a = .ok [a] := by
  simp [castToBodyF, hl, hm, hv]

/-- Kind: first match.
Says: when `firstCast` gives a result, some member of the list gives
exactly that result.
Does not say: that it is the first such member (it is, by the
definition, but the statement is existence only). -/
theorem firstCast_mem (f : SimpleType → M (List Atomic)) :
    ∀ (ms : List SimpleType) (r : List Atomic), firstCast f ms = some r → ∃ m ∈ ms, f m = .ok r
  | [], r, h => by simp [firstCast] at h
  | m :: ms, r, h => by
    unfold firstCast at h
    split at h
    · rename_i r' hr
      cases h
      exact ⟨m, List.mem_cons_self, hr⟩
    · obtain ⟨m', hm', hf⟩ := firstCast_mem f ms r h
      exact ⟨m', List.mem_cons_of_mem _ hm', hf⟩

/-! ## Tests (types as a schema document would define them) -/

/-- `xs:integer` restricted to 1..10. -/
def tHat : SimpleType := .atomic .integer { minInclusive := some "1", maxInclusive := some "10" }
/-- A union of `xs:integer` and `xs:date`. -/
def tIntOrDate : SimpleType := .union [.atomic .integer {}, .atomic .date {}] {}
/-- A list of `xs:integer`. -/
def tIntList : SimpleType := .list (.atomic .integer {}) {}

private def okStrs (r : M (List Atomic)) : Option (List (String × String)) :=
  match r with
  | .ok vs => some (vs.map (fun v => (v.ty.name, v.str)))
  | .error _ => none

private def errCode (r : M (List Atomic)) : String :=
  match r with
  | .ok _ => ""
  | .error e => e.code

-- derived atomic type: cast to the base, then the facets
#guard okStrs (castToBody (fun _ => none) tHat (Atomic.ofStr "7")) == some [("integer", "7")]
#guard errCode (castToBody (fun _ => none) tHat (Atomic.ofStr "11")) == "FORG0001"
#guard errCode (castToBody (fun _ => none) tHat (Atomic.ofStr "seven")) == "FORG0001"
#guard okStrs (castToBody (fun _ => none) tHat (Atomic.ofInt 3)) == some [("integer", "3")]
#guard errCode (castToBody (fun _ => none) tHat (Atomic.ofInt 30)) == "FORG0001"
-- union: lexical forms go to the first member that takes them
#guard okStrs (castToBody (fun _ => none) tIntOrDate (Atomic.ofStr "123")) == some [("integer", "123")]
#guard okStrs (castToBody (fun _ => none) tIntOrDate (Atomic.ofStr "2001-01-01")) == some [("date", "2001-01-01")]
#guard errCode (castToBody (fun _ => none) tIntOrDate (Atomic.ofStr "string")) == "FORG0001"
#guard okStrs (castToBody (fun _ => none) tIntOrDate (Atomic.untypedOf "123")) == some [("integer", "123")]
-- union: a value of a member type is kept
#guard okStrs (castToBody (fun _ => none) tIntOrDate (Atomic.ofInt 123)) == some [("integer", "123")]
-- list: tokens, each cast to the item type; only from a string or untyped value
#guard okStrs (castToBody (fun _ => none) tIntList (Atomic.ofStr " 1 2  3 ")) ==
  some [("integer", "1"), ("integer", "2"), ("integer", "3")]
#guard errCode (castToBody (fun _ => none) tIntList (Atomic.ofStr "1 two")) == "FORG0001"
#guard errCode (castToBody (fun _ => none) tIntList (Atomic.ofInt 1)) == "XPTY0004"
-- facets are tested on the XSD canonical form of a value that is not a string
#guard xsdCanon ⟨.b .double, .dbl 93.7⟩ == "9.37E1"
#guard xsdCanon (Atomic.ofInt 3) == "3"
#guard okStrs (castToBody (fun _ => none) (.atomic .double { patterns := [["-?[1-9]\\.[0-9]+E-?[0-9]+"]] })
  ⟨.b .double, .dbl 93.7⟩) == some [("double", "93.7")]
#guard errCode (castToBody (fun _ => none) (.atomic .double { patterns := [["-?[1-9]\\.[0-9]+E-?[0-9]+"]] })
  (Atomic.ofStr "93.7")) == "FORG0001"
-- generalized atomic types and pure unions of built-in types
#guard generalized tHat && generalized tIntOrDate && !generalized tIntList
#guard !generalized (.union [.atomic .integer {}] { minInclusive := some "1" })
#guard !generalized (.union [tIntList] {})
#guard pureLeaves tIntOrDate == some [.b .integer, .b .date]
#guard pureLeaves (.union [tIntOrDate, .atomic .string {}] {}) == some [.b .integer, .b .date, .b .string]
#guard pureLeaves tHat == none
#guard pureLeaves (.union [tHat, .atomic .date {}] {}) == none
-- instance of, by value
#guard atomInBody tHat (Atomic.ofInt 5)
#guard !atomInBody tHat (Atomic.ofInt 50)
#guard !atomInBody tHat (Atomic.ofStr "5")
#guard atomInBody tIntOrDate (Atomic.ofInt 5)
#guard !atomInBody tIntOrDate (Atomic.ofStr "5")
#guard !atomInBody tIntList (Atomic.ofInt 5)

end L4Factoidal.XPath4
