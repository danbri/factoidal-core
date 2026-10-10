/-
Wasm.Ops.Maths — the matrix and sigmoid operations.

Envelopes match `bin/npm-entry/entry_jsoo.ml` and `bin/npm-entry/
entry_extras.ml` (`matrix_*_json`, `sigmoid_*_json`) op for op, so the
same JavaScript argument drives either engine
(https://github.com/danbri/factoidal/issues/713, stage 2):

  matrixDeterminant(matrixJson)         -> {"ok":true,"result":"…","reason":"…"}
  matrixScalarProduct(aJson, bJson)     -> same shape
  matrixVectorProduct(aJson, bJson)     -> same shape
  matrixOuterProduct(aJson, bJson)      -> same shape
  sigmoidPoints(paramsJson)             -> {"ok":true,"points":[{"x":S,"y":S},…]}
  sigmoidFormulaMathml()                -> {"ok":true,"mathml":"<math …>…</math>"}

where `S` is `{"mantissa":"…","scale":"…","decimal":"…"}` (all three
strings, so a mantissa above 2^53 survives the JavaScript boundary).

A matrix is a JSON array of rows, a vector a JSON array of cells, a cell
an integer or a `[num, den]` pair. `result` is `Math.Matrix.mresToString`
("undef" for an undefined result) and `reason` is its explanation, or the
empty string.

One difference from the F* entry is recorded here rather than hidden.
`L4Factoidal.Math.Matrix` carries an undefined ENTRY as `none`, with no
reason attached, where the F* `MV_Undef` carries one. The only way a cell
becomes undefined in these operations is a zero denominator, whose F*
reason is `division-by-zero`, so a SCALAR `none` result reports that
reason here. The F* `mres_reason` returns the empty string for a matrix
or vector whose entries include an undefined one, and so does this.

`sigmoidPoints` refuses a point count above `maxSigmoidPoints`. The F*
entry has no cap and would exhaust memory on a count of that size; the
Lean module is one shared wasm heap, so the refusal is an error envelope
instead of a trap.

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Math.Matrix
import L4Factoidal.Math.Sigmoid
import L4Factoidal.MathML.Core
import L4Factoidal.MathML.Present
import L4Factoidal.MathML.Rat
import L4Factoidal.SPARQL.Expr

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Math
open L4Factoidal.MathML

/-! ## Reading the arguments -/

/-- The F* `mk_rat`: a zero denominator is an undefined entry, anything
else is reduced to lowest terms with a positive denominator. -/
private def mkRatEnt (n d : Int) : MEnt :=
  if d == 0 then none else some (normRat n d)

private def badCell (who : String) : String :=
  s!"{who}: each cell must be an integer or a [num,den] pair"

private def cellOf (who : String) : Json → Except String MEnt
  | .number s =>
      match s.toInt? with
      | some n => .ok (mkRatEnt n 1)
      | none   => .error (badCell who)
  | .array [.number a, .number b] =>
      match a.toInt?, b.toInt? with
      | some n, some d => .ok (mkRatEnt n d)
      | _, _           => .error (badCell who)
  | _ => .error (badCell who)

private def vectorOf (who : String) : Json → Except String (List MEnt)
  | .array items => items.mapM (cellOf who)
  | _ => .error s!"{who}: expected a JSON array (vector)"

private def matrixOf (who : String) : Json → Except String (List (List MEnt))
  | .array rows => rows.mapM (vectorOf who)
  | _ => .error s!"{who}: expected a JSON array of rows (matrix)"

private def parseArg (who : String) (src : String) : Except String Json :=
  match parseJson src with
  | .ok j => .ok j
  | .error _ => .error s!"{who}: invalid JSON"

/-- `reason` of a result. See the module header for the scalar case. -/
private def reasonOf : MRes → String
  | .scalar none => "division-by-zero"
  | r => mresReason r

private def mresEnvelope (r : MRes) : String :=
  okWith [("result", .string (mresToString r)), ("reason", .string (reasonOf r))]

/-! ## The four matrix operations -/

def matrixDeterminant (matrixJson : String) : String :=
  let who := "matrixDeterminant"
  match (do
      let j ← parseArg who matrixJson
      let m ← matrixOf who j
      pure (dynDeterminant (mkMatrixRes m)) : Except String MRes) with
  | .error e => errJson e
  | .ok r => mresEnvelope r

private def vectorPair (who aJson bJson : String) :
    Except String (MRes × MRes) := do
  let a ← vectorOf who (← parseArg who aJson)
  let b ← vectorOf who (← parseArg who bJson)
  pure (mkVectorRes a, mkVectorRes b)

def matrixScalarProduct (aJson bJson : String) : String :=
  match vectorPair "matrixScalarProduct" aJson bJson with
  | .error e => errJson e
  | .ok (a, b) => mresEnvelope (dynScalarProduct a b)

def matrixVectorProduct (aJson bJson : String) : String :=
  match vectorPair "matrixVectorProduct" aJson bJson with
  | .error e => errJson e
  | .ok (a, b) => mresEnvelope (dynVectorProduct a b)

def matrixOuterProduct (aJson bJson : String) : String :=
  match vectorPair "matrixOuterProduct" aJson bJson with
  | .error e => errJson e
  | .ok (a, b) => mresEnvelope (dynOuterProduct a b)

/-! ## Sigmoid -/

/-- Largest sample count `sigmoidPoints` serves. -/
def maxSigmoidPoints : Nat := 1000000

private def scaledOfDecimal (who s : String) : Except String Sigmoid.Scaled :=
  match L4Factoidal.SPARQL.parseToScaled s with
  | some sc => .ok (sc.mantissa, sc.scale)
  | none    => .error s!"{who}: not a decimal literal: {s}"

private def paramText (who : String) (fields : List (String × Json)) (name : String) :
    Except String String :=
  match fields.find? (fun f => f.1 == name) with
  | some (_, .string s) => .ok s
  | some (_, .number s) => .ok s
  | _ => .error s!"{who}: missing/invalid field \"{name}\""

private def scaledJson (s : Sigmoid.Scaled) : Json :=
  .object
    [ ("mantissa", .string (toString s.1))
    , ("scale", .string (toString s.2))
    , ("decimal", .string (L4Factoidal.SPARQL.formatScaledValue s.1 s.2)) ]

def sigmoidPoints (paramsJson : String) : String :=
  let who := "sigmoidPoints"
  match (do
      let fields ← match ← parseArg who paramsJson with
        | .object fs => pure fs
        | _ => throw s!"{who}: params must be a JSON object"
      let k    ← scaledOfDecimal who (← paramText who fields "k")
      let x0   ← scaledOfDecimal who (← paramText who fields "x0")
      let l    ← scaledOfDecimal who (← paramText who fields "l")
      let xmin ← scaledOfDecimal who (← paramText who fields "xmin")
      let xmax ← scaledOfDecimal who (← paramText who fields "xmax")
      let nText ← paramText who fields "n"
      let n ← match nText.toInt? with
        | none => throw s!"{who}: n must be an integer: {nText}"
        | some z =>
            if z < 0 then throw s!"{who}: n must not be negative: {nText}"
            else if z.toNat > maxSigmoidPoints then
              throw s!"{who}: n above {maxSigmoidPoints} is refused"
            else pure z.toNat
      pure (Sigmoid.sigmoidPoints k x0 l xmin xmax n) : Except String _) with
  | .error e => errJson e
  | .ok pts =>
      okWith [("points", .array (pts.map fun p =>
        .object [("x", scaledJson p.1), ("y", scaledJson p.2)]))]

/-- `L / (1 + exp(-k*(x - x0)))`, the tree the F* entry serialises. -/
private def sigmoidFormulaExpr : Expr :=
  .app "divide"
    [ .sym "L"
    , .app "plus"
        [ .int 1
        , .app "exp"
            [ .app "minus"
                [ .app "times"
                    [ .sym "k", .app "minus" [.sym "x", .sym "x0"] ] ] ] ] ]

def sigmoidFormulaMathml : String :=
  okWith [("mathml", .string (toPresentationMathML sigmoidFormulaExpr))]

/-! ## Dispatch -/

/-- The op names this module serves. -/
def mathsOpNames : List String :=
  [ "matrixDeterminant", "matrixScalarProduct", "matrixVectorProduct"
  , "matrixOuterProduct", "sigmoidPoints", "sigmoidFormulaMathml" ]

/-- Serve one of `mathsOpNames`, or `none` for any other op. A wrong
argument count is an error envelope naming the op. -/
def callMaths (op : String) (args : List String) : Option String :=
  match op, args with
  | "matrixDeterminant", [a]        => some (matrixDeterminant a)
  | "matrixScalarProduct", [a, b]   => some (matrixScalarProduct a b)
  | "matrixVectorProduct", [a, b]   => some (matrixVectorProduct a b)
  | "matrixOuterProduct", [a, b]    => some (matrixOuterProduct a b)
  | "sigmoidPoints", [a]            => some (sigmoidPoints a)
  | "sigmoidFormulaMathml", []      => some sigmoidFormulaMathml
  | "matrixDeterminant", _ | "sigmoidPoints", _ =>
      some (errJson s!"{op} expects 1 argument, got {args.length}")
  | "matrixScalarProduct", _ | "matrixVectorProduct", _ | "matrixOuterProduct", _ =>
      some (errJson s!"{op} expects 2 arguments, got {args.length}")
  | "sigmoidFormulaMathml", _ =>
      some (errJson s!"{op} expects 0 arguments, got {args.length}")
  | _, _ => none

end L4Wasm.Ops
