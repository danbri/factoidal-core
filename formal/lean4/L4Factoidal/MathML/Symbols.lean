/-
L4Factoidal.MathML.Symbols — application keys of `Expr` and the OpenMath symbols they name.

A key is the MathML element name of an operator (`plus`, `rem`), or `cd:name` for an OpenMath symbol
with no MathML element of the same application shape (`MathML/Strict.lean` explains the split). The
table gives each key its content dictionary and symbol name, as the "OM Symbols" entry of the operator's
section in MathML 3.0 Second Edition chapter 4 does (section 4.4.2 arithmetic, 4.4.3 relations and
logic, 4.4.7 elementary functions, 4.4.9 linear algebra), in the OpenMath 2 content dictionaries
`arith1`, `integer1`, `minmax1`, `relation1`, `logic1`, `nums1`, `transc1`, `linalg1`, `linalg2`, `set1`,
`list1`, `fns2`.

A key that is not in the table names no symbol: an application of it is an application of an
identifier (`<apply><ci>f</ci>...`, OpenMath `OMV`).
-/
import L4Factoidal.MathML.Core

namespace L4Factoidal.MathML

/-- `(key, content dictionary, symbol name)`. -/
def symbolTable : List (String × String × String) :=
  [ ("plus", "arith1", "plus"), ("times", "arith1", "times"), ("minus", "arith1", "minus"),
    ("divide", "arith1", "divide"), ("power", "arith1", "power"), ("abs", "arith1", "abs"),
    ("gcd", "arith1", "gcd"), ("lcm", "arith1", "lcm"),
    ("arith1:unary_minus", "arith1", "unary_minus"), ("arith1:root", "arith1", "root"),
    ("quotient", "integer1", "quotient"), ("rem", "integer1", "remainder"),
    ("factorial", "integer1", "factorial"),
    ("max", "minmax1", "max"), ("min", "minmax1", "min"),
    ("eq", "relation1", "eq"), ("neq", "relation1", "neq"), ("lt", "relation1", "lt"),
    ("gt", "relation1", "gt"), ("leq", "relation1", "leq"), ("geq", "relation1", "geq"),
    ("and", "logic1", "and"), ("or", "logic1", "or"), ("xor", "logic1", "xor"),
    ("not", "logic1", "not"), ("implies", "logic1", "implies"),
    ("nums1:rational", "nums1", "rational"),
    ("exp", "transc1", "exp"), ("ln", "transc1", "ln"), ("sin", "transc1", "sin"),
    ("cos", "transc1", "cos"), ("tan", "transc1", "tan"),
    ("determinant", "linalg1", "determinant"), ("transpose", "linalg1", "transpose"),
    ("scalarproduct", "linalg1", "scalarproduct"), ("vectorproduct", "linalg1", "vectorproduct"),
    ("outerproduct", "linalg1", "outerproduct"),
    ("linalg1:matrix_selector", "linalg1", "matrix_selector"),
    ("linalg1:vector_selector", "linalg1", "vector_selector"),
    ("linalg2:matrix", "linalg2", "matrix"), ("linalg2:matrixrow", "linalg2", "matrixrow"),
    ("linalg2:vector", "linalg2", "vector"),
    ("set1:set", "set1", "set"), ("list1:list", "list1", "list"),
    ("fns2:predicate_on_list", "fns2", "predicate_on_list") ]

/-- The OpenMath symbol a key names. -/
def symbolOf (key : String) : Option (String × String) :=
  (symbolTable.find? (fun e => e.1 == key)).map (·.2)

/-- The key of an OpenMath symbol. -/
def keyOf (cd name : String) : Option String :=
  (symbolTable.find? (fun e => e.2.1 == cd && e.2.2 == name)).map (·.1)

private theorem table_keyOf :
    symbolTable.all (fun e => keyOf e.2.1 e.2.2 == some e.1) = true := by decide

private theorem table_symbolOf :
    symbolTable.all (fun e => symbolOf e.1 == some e.2) = true := by decide

/-- Theorem (round trip of the table). Says: the symbol a key names has that key.
    Does not say: that every OpenMath symbol has a key (only the 45 in the table do). -/
theorem keyOf_of_symbolOf {key cd name : String} (h : symbolOf key = some (cd, name)) :
    keyOf cd name = some key := by
  unfold symbolOf at h
  cases hf : symbolTable.find? (fun e => e.1 == key) with
  | none => simp [hf] at h
  | some e =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      have hk : e.1 = key := by simpa using List.find?_some hf
      have hm := List.mem_of_find?_eq_some hf
      have := List.all_eq_true.mp table_keyOf e hm
      rw [← hk, ← h] at *
      simpa using this

/-- Theorem (round trip of the table, other direction). Says: the key of a symbol names that symbol.
    Does not say: anything about symbols outside the table. -/
theorem symbolOf_of_keyOf {key cd name : String} (h : keyOf cd name = some key) :
    symbolOf key = some (cd, name) := by
  unfold keyOf at h
  cases hf : symbolTable.find? (fun e => e.2.1 == cd && e.2.2 == name) with
  | none => simp [hf] at h
  | some e =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hp
      have hm := List.mem_of_find?_eq_some hf
      have := List.all_eq_true.mp table_symbolOf e hm
      rw [h] at this
      have h2 : e.2 = (cd, name) := by
        rcases e with ⟨k, c, n⟩
        simp_all
      rw [← h2]
      simpa using this

-- The truth values are symbols of `logic1` that `Expr` holds as `bool`, not as keys.
#guard keyOf "logic1" "true" == none
#guard keyOf "logic1" "false" == none
#guard symbolOf "rem" == some ("integer1", "remainder")
#guard keyOf "integer1" "remainder" == some "rem"
#guard symbolOf "csymbol" == none

end L4Factoidal.MathML
