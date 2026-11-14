/-
L4Factoidal.MathML.StrictTests — build-time checks for `MathML/Strict.lean`, from the examples in
MathML 3.0 Second Edition chapter 4 (the section is named at each check), and the axioms the theorems
rest on.
-/
import L4Factoidal.MathML.Strict

namespace L4Factoidal.MathML

private instance : BEq Expr := ⟨exprEq⟩

private def noEnv : String → Option (Int × Int) := fun _ => none

-- Section 4.4.2.6: `<apply><minus/><cn>3</cn></apply>` is `arith1:unary_minus`; with two arguments
-- the translation is direct.
#guard toStrict (.app "minus" [.int 3]) == .app "arith1:unary_minus" [.int 3]
#guard toStrict (.app "minus" [.sym "x", .sym "y"]) == .app "minus" [.sym "x", .sym "y"]

-- Section 4.4.2.11: `<apply><root/><ci>x</ci></apply>` is `arith1:root(x, 2)`, and a degree comes
-- second.
#guard toStrict (.app "root" [.sym "x"]) == .app "arith1:root" [.sym "x", .int 2]
#guard toStrict (.app "root" [.sym "n", .sym "a"]) == .app "arith1:root" [.sym "a", .sym "n"]

-- Section 4.3.4.3.2, "Rewrite: n-ary relations": `<apply><lt/> a b c d </apply>`.
#guard toStrict (.app "lt" [.sym "a", .sym "b", .sym "c", .sym "d"])
  == .app "fns2:predicate_on_list"
      [.app "csymbol" [.sym "lt"], .app "list1:list" [.sym "a", .sym "b", .sym "c", .sym "d"]]
#guard toStrict (.app "lt" [.sym "a", .sym "b"]) == .app "lt" [.sym "a", .sym "b"]

-- Section 4.3.4.4.2, "Rewrite: n-ary unary set" and "Rewrite: n-ary unary single".
#guard toStrict (.app "max" [.int 2, .int 3, .int 5])
  == .app "max" [.app "set1:set" [.int 2, .int 3, .int 5]]
#guard toStrict (.app "max" [.sym "a"]) == .app "max" [.sym "a"]
#guard toStrict (.app "min" []) == .app "min" [.app "set1:set" []]

-- Section 4.2.1.3, "Rewrite: cn sep": `<cn type="rational">22<sep/>7</cn>`.
#guard toStrict (.rat 22 7) == .app "nums1:rational" [.int 22, .int 7]

-- Sections 4.4.9.1 to 4.4.9.3 and 4.4.9.6.
#guard toStrict (.vec [.app "plus" [.sym "x", .sym "y"], .int 3, .int 7])
  == .app "linalg2:vector" [.app "plus" [.sym "x", .sym "y"], .int 3, .int 7]
#guard toStrict (.mat [[.int 1, .int 2], [.int 3, .rat 1 2]])
  == .app "linalg2:matrix"
      [.app "linalg2:matrixrow" [.int 1, .int 2],
       .app "linalg2:matrixrow" [.int 3, .app "nums1:rational" [.int 1, .int 2]]]
#guard toStrict (.app "selector" [.sym "V", .int 1]) == .app "linalg1:vector_selector" [.int 1, .sym "V"]
#guard toStrict (.app "selector" [.sym "M", .int 1, .int 2])
  == .app "linalg1:matrix_selector" [.int 1, .int 2, .sym "M"]

-- Strict output, fixed point, and the way back.
#guard isStrict (toStrict (.app "minus" [.app "root" [.rat 1 4]]))
#guard !isStrict (.app "root" [.int 4])
#guard !isStrict (.rat 1 2)
#guard unstrict (toStrict (.app "lt" [.int 1, .int 2, .int 3])) == .app "lt" [.int 1, .int 2, .int 3]
#guard unstrict (toStrict (.mat [[.int 1, .int 2], [.int 3, .rat 1 2]])) == .mat [[.int 1, .int 2], [.int 3, .rat 1 2]]
#guard unstrict (.app "root" [.int 2, .int 9]) == .app "root" [.int 9]

-- Values: the strict form evaluates to what the original does.
#guard evalStrict noEnv (toStrict (.app "root" [.int 9])) == some (.num (3, 1))
#guard evalStrict noEnv (toStrict (.app "root" [.int 3, .int 27])) == some (.num (3, 1))
#guard evalStrict noEnv (toStrict (.app "minus" [.rat 1 2])) == some (.num (-1, 2))
#guard evalStrict noEnv (toStrict (.app "lt" [.int 1, .int 2, .int 3])) == some (.bool true)
#guard evalStrict noEnv (toStrict (.app "lt" [.int 1, .int 3, .int 2])) == some (.bool false)
#guard evalStrict noEnv (toStrict (.app "max" [.int 2, .int 3, .int 5])) == some (.num (5, 1))
#guard evalStrict noEnv (toStrict (.app "selector" [.mat [[.int 1, .int 2], [.int 3, .int 4]], .int 2, .int 1]))
  == some (.num (3, 1))
#guard evalStrict noEnv (toStrict (.app "divide" [.int 1, .int 0])) == none

#print axioms toStrict_isStrict
#print axioms toStrict_of_isStrict
#print axioms toStrict_idempotent
#print axioms isStrict_iff_toStrict_eq
#print axioms unstrict_toStrict
#print axioms evalStrict_toStrict
#print axioms evalStrict_of_native

end L4Factoidal.MathML
