/-
L4Factoidal.Geo.FunctionsTests — the geof: extension functions,
exercised exactly as the SPARQL evaluator would call them.
-/
import L4Factoidal.Geo.Functions

namespace L4Factoidal.Geo
open L4Factoidal.SPARQL
open L4Factoidal.RDF

/-- Build a `geo:wktLiteral` argument the way the evaluator presents
    one. The datatype IRI is well-formed by `rfl`, the Lean
    counterpart of F*'s `assert_norm`. -/
private def wktLit (s : String) : EvalResult :=
  .term (.literal ⟨⟨s, ⟨wktLiteralIri, by rfl⟩, none, none⟩, by rfl⟩)

private def sq : String := "POLYGON((0 0,4 0,4 4,0 4,0 0))"

#guard extFns (geofNs ++ "sfWithin") [wktLit "POINT(2 2)", wktLit sq]
       == some (.bool true)
#guard extFns (geofNs ++ "sfWithin") [wktLit "POINT(9 9)", wktLit sq]
       == some (.bool false)

-- A boundary point INTERSECTS but is not WITHIN (Simple Features).
#guard extFns (geofNs ++ "sfIntersects") [wktLit "POINT(0 0)", wktLit sq]
       == some (.bool true)
#guard extFns (geofNs ++ "sfWithin") [wktLit "POINT(0 0)", wktLit sq]
       == some (.bool false)
#guard extFns (geofNs ++ "sfTouches") [wktLit "POINT(0 0)", wktLit sq]
       == some (.bool true)
#guard extFns (geofNs ++ "sfDisjoint") [wktLit "POINT(9 9)", wktLit sq]
       == some (.bool true)

-- Contains is Within with arguments swapped.
#guard extFns (geofNs ++ "sfContains") [wktLit sq, wktLit "POINT(2 2)"]
       == some (.bool true)

-- Equality across decimal scales.
#guard extFns (geofNs ++ "sfEquals") [wktLit "POINT(0.10 0.20)", wktLit "POINT(0.1 0.2)"]
       == some (.bool true)

-- MULTI-GEOMETRIES decompose: a point within ANY member of a
-- multipolygon is within the whole.
#guard extFns (geofNs ++ "sfWithin")
         [wktLit "POINT(2 2)",
          wktLit "MULTIPOLYGON(((0 0,4 0,4 4,0 4,0 0)),((9 9,10 9,10 10,9 9)))"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfIntersects")
         [wktLit "POINT(9.5 9.2)",
          wktLit "MULTIPOLYGON(((0 0,4 0,4 4,0 4,0 0)),((9 9,10 9,10 10,9 9)))"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfDisjoint")
         [wktLit "POINT(100 100)",
          wktLit "MULTIPOLYGON(((0 0,4 0,4 4,0 4,0 0)),((9 9,10 9,10 10,9 9)))"]
       == some (.bool true)

-- A GEOMETRYCOLLECTION decomposes too, including nested ones.
#guard extFns (geofNs ++ "sfIntersects")
         [wktLit "POINT(1 1)",
          wktLit "GEOMETRYCOLLECTION(POINT(5 5),GEOMETRYCOLLECTION(LINESTRING(0 0,2 2)))"]
       == some (.bool true)

-- Linestrings: crossing paths intersect; a point on an endpoint
-- TOUCHES an open curve but a mid-path point does not.
#guard extFns (geofNs ++ "sfIntersects")
         [wktLit "LINESTRING(0 0,2 2)", wktLit "LINESTRING(0 2,2 0)"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfTouches")
         [wktLit "POINT(0 0)", wktLit "LINESTRING(0 0,2 2)"]
       == some (.bool true)
#guard extFns (geofNs ++ "sfTouches")
         [wktLit "POINT(1 1)", wktLit "LINESTRING(0 0,2 2)"]
       == some (.bool false)

-- Reversal-invariant linestring equality (open curves).
#guard extFns (geofNs ++ "sfEquals")
         [wktLit "LINESTRING(0 0,1 1,2 2)", wktLit "LINESTRING(2 2,1 1,0 0)"]
       == some (.bool true)

-- REFUSAL becomes a type error, never a guess: a closed loop written
-- from a different starting vertex is a case the algorithm declines
-- to decide, so the evaluator must raise rather than answer false.
#guard (extFns (geofNs ++ "sfEquals")
         [wktLit "LINESTRING(0 0,1 0,1 1,0 0)",
          wktLit "LINESTRING(1 0,1 1,0 0,1 0)"]).isNone

-- TYPE ERRORS, not `false`: an unknown function, a non-WKT argument,
-- wrong arity, and a cross-CRS pair must all return `none` so the
-- evaluator raises §17.6 rather than silently answering.
#guard (extFns (geofNs ++ "sfNoSuchThing") [wktLit "POINT(0 0)", wktLit sq]).isNone
#guard (extFns "http://example.org/other" [wktLit "POINT(0 0)", wktLit sq]).isNone
#guard (extFns (geofNs ++ "sfWithin") [.num 1, wktLit sq]).isNone
#guard (extFns (geofNs ++ "sfWithin") [wktLit "POINT(0 0)"]).isNone
#guard (extFns (geofNs ++ "sfWithin")
          [wktLit "<http://www.opengis.net/def/crs/EPSG/0/27700> POINT(2 2)",
           wktLit sq]).isNone
-- Unparseable lexical form is a type error too.
#guard (extFns (geofNs ++ "sfWithin") [wktLit "POINT(oops)", wktLit sq]).isNone

/-! ## `geof:distance` and `geof:envelope` through `extFns`

The expected lexical forms are the F\* engine's answers on the same
literals (`tests/parity/geo-fulltext/run-parity.py`; London–Manchester is
post 21's value). -/

/-- The lexical form of a term result, for comparing against the F\* text. -/
private def lexOf : Option EvalResult → Option String
  | some (.term (.literal l)) => some l.val.lexicalForm
  | _ => none

private def dtOf : Option EvalResult → Option String
  | some (.term (.literal l)) => some l.val.datatype.val
  | _ => none

private def iriArg (s : String) : EvalResult :=
  if h : isIri s then .term (.iri ⟨s, h⟩) else .error

private def uomIri (s : String) : EvalResult :=
  iriArg ("http://www.opengis.net/def/uom/OGC/1.0/" ++ s)

private def anyUri (s : String) : EvalResult :=
  .term (.literal (mkTypedLiteral s ⟨"http://www.w3.org/2001/XMLSchema#anyURI", rfl⟩))

private def dist (args : List EvalResult) : Option EvalResult := extFns (geofNs ++ "distance") args
private def env (args : List EvalResult) : Option EvalResult := extFns (geofNs ++ "envelope") args

private def london : EvalResult := wktLit "POINT(-0.1278 51.5074)"
private def manchester : EvalResult := wktLit "POINT(-2.2426 53.4808)"
private def bng (s : String) : EvalResult :=
  wktLit ("<http://www.opengis.net/def/crs/EPSG/0/27700> " ++ s)

-- Two arguments: the F\* answers, typed xsd:double.
#guard lexOf (dist [london, manchester]) == some "2.89252253232364639"
#guard dtOf (dist [london, manchester]) == some "http://www.w3.org/2001/XMLSchema#double"
#guard lexOf (dist [london, london]) == some "0.00000000000000000"
#guard lexOf (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)"]) == some "5.000000000"
-- A CRS84 literal with the CRS IRI written out is the same reference system.
#guard lexOf (dist [wktLit "<http://www.opengis.net/def/crs/OGC/1.3/CRS84> POINT(0 0)",
                    wktLit "POINT(3 4)"]) == some "5.000000000"

-- Refused: a non-point geometry, two different reference systems, a
-- non-WKT argument, an empty point, and the wrong number of arguments.
#guard (dist [wktLit "POINT(0 0)", wktLit sq]).isNone
#guard (dist [wktLit "POINT(0 0)", bng "POINT(3 4)"]).isNone
#guard (dist [.num 1, wktLit "POINT(3 4)"]).isNone
#guard (dist [wktLit "POINT EMPTY", wktLit "POINT(3 4)"]).isNone
#guard (dist [wktLit "POINT(0 0)"]).isNone
#guard (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)", uomIri "degree", uomIri "degree"]).isNone

-- Three arguments (GeoSPARQL 1.1): the answer is given only in the unit of
-- geom1's reference system. CRS84 is in degrees.
#guard lexOf (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)", uomIri "degree"])
         == some "5.000000000"
#guard lexOf (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)",
                    anyUri "http://www.opengis.net/def/uom/OGC/1.0/degree"]) == some "5.000000000"
#guard lexOf (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)",
                    iriArg "http://www.opengis.net/def/uom/EPSG/0/9102"]) == some "5.000000000"
-- EPSG:27700 is in metres.
#guard lexOf (dist [bng "POINT(530000 180000)", bng "POINT(530003 180004)", uomIri "metre"])
         == some "5.000000000"
-- Never a number in a unit other than the one asked for: metres between two
-- CRS84 points (that is a geodesic distance, not done:
-- https://github.com/danbri/factoidal/issues/772), degrees between two
-- EPSG:27700 points, an unknown unit, a reference system whose unit is
-- unknown here, and a unit that is not an IRI.
#guard (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)", uomIri "metre"]).isNone
#guard (dist [bng "POINT(0 0)", bng "POINT(3 4)", uomIri "degree"]).isNone
#guard (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)", uomIri "radian"]).isNone
#guard (dist [wktLit "<http://example.org/crs/unknown> POINT(0 0)",
              wktLit "<http://example.org/crs/unknown> POINT(3 4)", uomIri "metre"]).isNone
#guard (dist [wktLit "POINT(0 0)", wktLit "POINT(3 4)", .term (.literal (Literal.string "degree"))]).isNone

-- geof:envelope: the bounding box as a closed rectangular POLYGON, typed
-- geo:wktLiteral, in the argument's reference system.
#guard lexOf (env [wktLit "LINESTRING(0 0, 3 4, -1 2)"])
         == some "POLYGON((-1 0, 3 0, 3 4, -1 4, -1 0))"
#guard dtOf (env [wktLit "LINESTRING(0 0, 3 4, -1 2)"]) == some wktLiteralIri
#guard lexOf (env [london])
         == some "POLYGON((-0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074, -0.1278 51.5074))"
#guard lexOf (env [bng "POINT(1 2)"])
         == some "<http://www.opengis.net/def/crs/EPSG/0/27700> POLYGON((1 2, 1 2, 1 2, 1 2, 1 2))"
-- The result is itself a WKT argument: it feeds another geof: call.
#guard (env [wktLit "MULTIPOINT((1 1), (5 -2))"]).bind (fun e =>
         extFns (geofNs ++ "sfWithin") [wktLit "POINT(2 0)", e]) == some (.bool true)
-- Refused: an empty geometry has no bounding box; a non-WKT argument; two arguments.
#guard (env [wktLit "POINT EMPTY"]).isNone
#guard (env [.num 1]).isNone
#guard (env [london, london]).isNone

end L4Factoidal.Geo
