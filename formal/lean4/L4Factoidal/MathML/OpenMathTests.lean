/-
L4Factoidal.MathML.OpenMathTests — build-time checks for `MathML/OpenMath.lean` and
`MathML/Symbols.lean`, and the axioms their theorems rest on. The OpenMath objects are the
examples of section 3.1.2 of the OpenMath Standard 2.0 (revision 3, 2019-07-01).
-/
import L4Factoidal.MathML.OpenMath
import L4Factoidal.MathML.FromXml

namespace L4Factoidal.MathML

private def om (inner : String) : String :=
  "<OMOBJ xmlns=\"http://www.openmath.org/OpenMath\" version=\"2.0\">" ++ inner ++ "</OMOBJ>"

private def sameOM (a : Option OMObj) (b : OMObj) : Bool :=
  match a with
  | some x => omEq x b
  | none   => false

private def sameExpr (a : Option Expr) (b : Expr) : Bool :=
  match a with
  | some x => exprEq x b
  | none   => false

/-- Write then parse gives the object back (a test of the XML round trip, per object). -/
private def survives (o : OMObj) : Bool := sameOM (parseOpenMath (writeOpenMath o)) o

-- Section 3.1.2, application: sin x.
#guard sameOM (parseOpenMath (om "<OMA><OMS cd=\"transc1\" name=\"sin\"/><OMV name=\"x\"/></OMA>"))
  (.oma (.oms "transc1" "sin") [.omv "x"])
-- Section 3.1.2, binding: lambda x. sin x.
#guard sameOM (parseOpenMath (om ("<OMBIND><OMS cd=\"fns1\" name=\"lambda\"/><OMBVAR><OMV name=\"x\"/></OMBVAR>" ++
    "<OMA><OMS cd=\"transc1\" name=\"sin\"/><OMV name=\"x\"/></OMA></OMBIND>")))
  (.ombind (.oms "fns1" "lambda") [.omv "x"] (.oma (.oms "transc1" "sin") [.omv "x"]))
-- Section 3.1.2, attribution: the type of a variable.
#guard sameOM (parseOpenMath (om ("<OMATTR><OMATP><OMS cd=\"ecc\" name=\"type\"/><OMS cd=\"ecc\" name=\"real\"/>" ++
    "</OMATP><OMV name=\"x\"/></OMATTR>")))
  (.omattr [.oms "ecc" "type", .oms "ecc" "real"] (.omv "x"))
-- Section 3.1.2, floats in both forms, integers, strings.
#guard sameOM (parseOpenMath (om "<OMF dec=\"1.0e-10\"/>")) (.omf false "1.0e-10")
#guard sameOM (parseOpenMath (om "<OMF hex=\"3DDB7CDFD9D7BDBB\"/>")) (.omf true "3DDB7CDFD9D7BDBB")
#guard sameOM (parseOpenMath (om "<OMI> -120 </OMI>")) (.omi (-120))
#guard sameOM (parseOpenMath (om "<OMSTR>a &lt; b</OMSTR>")) (.omstr "a < b")
-- Refused: an element of another namespace, a non-default cdbase, an empty application.
#guard (parseOpenMath "<OMOBJ><OMI>1</OMI></OMOBJ>").isNone
#guard (parseOpenMath (om "<OMS cdbase=\"http://example.org/cd\" cd=\"a\" name=\"b\"/>")).isNone
#guard (parseOpenMath (om "<OMA/>")).isNone

-- Write then parse.
#guard survives (.omi (-17))
#guard survives (.omstr "a < b & \"c\"")
#guard survives (.omv "x")
#guard survives (.omf false "1.0e-10")
#guard survives (.oma (.oms "arith1" "plus") [.omi 1, .oma (.omv "f") [.omv "x"]])
#guard survives (.ombind (.oms "fns1" "lambda") [.omv "x", .omv "y"] (.omv "x"))
#guard survives (.omattr [.oms "ecc" "type", .oms "ecc" "real"] (.omv "x"))

-- Strict content and OpenMath objects.
#guard omEq (toOpenMath (.app "minus" [.int 3])) (.oma (.oms "arith1" "unary_minus") [.omi 3])
#guard omEq (toOpenMath (.app "root" [.sym "x"])) (.oma (.oms "arith1" "root") [.omv "x", .omi 2])
#guard omEq (toOpenMath (.rat 22 7)) (.oma (.oms "nums1" "rational") [.omi 22, .omi 7])
#guard omEq (toOpenMath (.bool true)) (.oms "logic1" "true")
#guard omEq (toOpenMath (.app "lt" [.sym "a", .sym "b", .sym "c"]))
  (.oma (.oms "fns2" "predicate_on_list")
    [.oms "relation1" "lt", .oma (.oms "list1" "list") [.omv "a", .omv "b", .omv "c"]])
#guard omEq (toOpenMath (.app "f" [.int 1])) (.oma (.omv "f") [.omi 1])
#guard sameExpr (ofOpenMath (.oma (.oms "integer1" "remainder") [.omi 7, .omi 3])) (.app "rem" [.int 7, .int 3])
#guard sameExpr (ofOpenMath (.oms "logic1" "false")) (.bool false)
-- Refused: a shape that is not strict, a symbol outside the table, and objects with no counterpart.
#guard (ofOpenMath (.oma (.oms "arith1" "minus") [.omi 3])).isNone
#guard (ofOpenMath (.oma (.oms "relation1" "lt") [.omi 1, .omi 2, .omi 3])).isNone
#guard (ofOpenMath (.oma (.oms "nosuchcd" "f") [.omi 1])).isNone
#guard (ofOpenMath (.omf false "1.5")).isNone
#guard (ofOpenMath (.ombind (.oms "fns1" "lambda") [.omv "x"] (.omv "x"))).isNone

-- Strict Content MathML markup: written, read back.
#guard toStrictContentMathML (.app "minus" [.int 3])
  == "<math xmlns=\"http://www.w3.org/1998/Math/MathML\"><apply><csymbol cd=\"arith1\">unary_minus</csymbol>" ++
     "<cn type=\"integer\">3</cn></apply></math>"
#guard sameExpr (parseMathML (toStrictContentMathML (.app "lt" [.int 1, .int 2, .int 3])))
  (toStrict (.app "lt" [.int 1, .int 2, .int 3]))
#guard sameExpr (parseMathML (toStrictContentMathML (.mat [[.int 1, .rat 1 2]]))) (toStrict (.mat [[.int 1, .rat 1 2]]))
-- The non-strict writer now names the dictionary of a key that is not an operator element.
#guard sameExpr (parseMathML (toContentMathML (.app "and" [.bool true, .sym "p"]))) (.app "and" [.bool true, .sym "p"])
#guard sameExpr (parseMathML (toContentMathML (.app "g" [.int 1]))) (.app "g" [.int 1])

#print axioms keyOf_of_symbolOf
#print axioms symbolOf_of_keyOf
#print axioms ofOM_toOM
#print axioms ofOpenMath_toOpenMath
#print axioms toOM_ofOM_image

end L4Factoidal.MathML
