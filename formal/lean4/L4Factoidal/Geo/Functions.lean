/-
L4Factoidal.Geo.Functions — the GeoSPARQL SPARQL extension functions,
ported from `formal/fstar/RDF.Geo.Functions.fst`.

GeoSPARQL 1.1 §9 defines its topology predicates as SPARQL functions
named by IRI (`geof:sfIntersects`, …). SPARQL 1.1 §17.6 already gives
those an extension point, and the Lean evaluator exposes it as an
ordinary field: `EvalEnv.ext : String → List EvalResult → Option
EvalResult`. So this module needs NO change to the evaluator — it
builds a function table that a caller installs:

    { EvalEnv.empty with ext := Geo.extFns }

That is the purity doctrine paying off. The F* side reaches the same
functions through a registry the evaluator consults; here the table is
an argument, so nothing global is mutated and the evaluator stays a
total function of explicit inputs.

CRS RULE, inherited: v0 performs NO coordinate transforms. Two
literals in different CRSes produce a type error rather than a
silently wrong answer computed as if the coordinates were comparable.
-/
import L4Factoidal.Geo.Wkt
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.Geo

open L4Factoidal.SPARQL

/-- The `geof:` function namespace. -/
def geofNs : String := "http://www.opengis.net/def/function/geosparql/"

/-- Pull a WKT value out of an argument: it must be a literal typed
    `geo:wktLiteral` whose lexical form parses. Anything else is a
    type error, per §17.6. -/
def wktArg : EvalResult → Option WktValue
  | .term (.literal l) =>
      if l.val.datatype.val == wktLiteralIri then Wkt.parseLiteral l.val.lexicalForm
      else none
  | _ => none

/-- Apply a general geometry predicate to two parsed literals with
    the CRS guard. A REFUSAL from the predicate (`none`) becomes a
    §17.6 type error, exactly like a bad argument — the evaluator must
    never see a guessed boolean. -/
def geoPredicate (f : Geometry → Geometry → Option Bool)
    (a b : EvalResult) : Option EvalResult := do
  let va ← wktArg a
  let vb ← wktArg b
  if !(sameCrs va.crs vb.crs) then none
  else (f va.geom vb.geom).map EvalResult.bool

/-! ## `geof:distance` and `geof:envelope`

Ported from `RDF.Geo.Functions.fst`'s `geo_distance`/`geo_envelope`.
`extFns` below serves both, with the result shapes of the F\*
`eval_geof_call`: an `xsd:double` literal for the distance and a
`geo:wktLiteral` for the envelope. -/

/-- `floor(sqrt n)` by binary search, fuel-bounded by `n + 2` (a
    generous, easy-to-see bound: the search halves its range each
    round, so it converges in `O(log n)` rounds well inside that fuel
    via the early `lo ≥ hi` exit). Structural on the fuel argument, so
    no `partial` is needed — the same shape as `Scaled.pow10` above. -/
def isqrtSearch : Nat → Nat → Nat → Nat → Nat
  | _,        lo, _,  0        => lo
  | n,        lo, hi, fuel + 1 =>
      if lo ≥ hi then lo
      else
        let mid := (lo + hi + 1) / 2
        if mid * mid ≤ n then isqrtSearch n mid hi fuel
        else isqrtSearch n lo (mid - 1) fuel

def isqrt (n : Nat) : Nat :=
  if n == 0 then 0 else isqrtSearch n 0 (n + 1) (n + 2)

/-- Extra decimal digits of precision `geoSqrtApprox` discloses beyond
    the input's own scale. -/
def geoDistancePrecisionExtraDigits : Nat := 9

def geoDistanceSquared (p1 p2 : Point) : Scaled :=
  let dx := Scaled.sub p1.x p2.x
  let dy := Scaled.sub p1.y p2.y
  Scaled.add (Scaled.mul dx dx) (Scaled.mul dy dy)

/-- `floor(sqrt v)` of a nonnegative `Scaled`, to
    `geoDistancePrecisionExtraDigits` extra decimal digits beyond the
    input's own scale. This is the ONE inexact step anywhere in the
    GeoSPARQL v0 surface — an under-approximation (never rounded or
    over-approximated), computed by the pure integer `isqrt` above, so
    the disclosed inexactness is exactly one documented
    `floor(sqrt(...))` call, not a black box. -/
def geoSqrtApprox (v : Scaled) : Scaled :=
  let s := v.scale
  let outScale := s + geoDistancePrecisionExtraDigits
  let shift : Nat := outScale + outScale - s
  let m : Nat := (if v.mantissa < 0 then 0 else v.mantissa).toNat
  let arg : Nat := m * Scaled.pow10 shift
  { mantissa := (isqrt arg : Int), scale := outScale }

/-- `geof:distance(g1,g2)`: the exact squared distance and a disclosed
    approximate square root for point/point; refused (`none`) for
    every other geometry-kind pair — v0 scope limits the exact-
    arithmetic distance function to point/point. -/
def geoDistance (g1 g2 : Geometry) : Option Scaled :=
  match g1, g2 with
  | .point p1, .point p2 => some (geoSqrtApprox (geoDistanceSquared p1 p2))
  | _, _ => none

/-- The bounding box as a closed rectangular exterior ring, no holes. -/
def bboxToPolygon (b : BBox) : Polygon :=
  { ext := [ ⟨b.xmin, b.ymin⟩, ⟨b.xmax, b.ymin⟩, ⟨b.xmax, b.ymax⟩,
             ⟨b.xmin, b.ymax⟩, ⟨b.xmin, b.ymin⟩ ],
    holes := [] }

/-- `geof:envelope(g)`: the geometry's bounding box as a rectangular
    polygon — exact, no approximation involved at all. -/
def geoEnvelope (g : Geometry) : Option Geometry :=
  match BBox.ofGeometry g with
  | none   => none
  | some b => some (.polygon (bboxToPolygon b))

/-! ## Units of measure for `geof:distance`

GeoSPARQL 1.1 gives `geof:distance` a third argument, the unit of
measure of the answer (`units: xsd:anyURI`), and computes the distance
"in the spatial reference system of geom1". This engine performs no
coordinate transformation and computes the planar distance in the
coordinate units of that reference system. So it can answer in exactly
one unit: the unit of the reference system's own axes. `crsUnit` names
that unit for the reference systems whose unit is known here; for every
other unit, and for a reference system not in the table, the call is the
§17.6 error. It never returns a number in a unit other than the one asked
for.

Not done: a geodesic distance in metres between two points of a
geographic (degree-unit) reference system such as CRS84. That needs an
ellipsoid model, and the call is refused:
https://github.com/danbri/factoidal/issues/772.

The F\* engine (`SPARQL11.Algebra.fst`, `eval_geof_call`) accepts only the
two-argument form and refuses every three-argument call; on the
two-argument form the two engines answer the same. -/

/-- The OGC unit-of-measure IRIs, and their EPSG equivalents. -/
def uomDegree : String := "http://www.opengis.net/def/uom/OGC/1.0/degree"
def uomMetre : String := "http://www.opengis.net/def/uom/OGC/1.0/metre"
def uomEpsgDegree : String := "http://www.opengis.net/def/uom/EPSG/0/9102"
def uomEpsgMetre : String := "http://www.opengis.net/def/uom/EPSG/0/9001"

/-- The kind of unit a unit IRI names, when it is one this engine knows. -/
inductive AxisUnit where
  | degree | metre
  deriving DecidableEq, Repr

def unitOfIri (iri : String) : Option AxisUnit :=
  if iri == uomDegree || iri == uomEpsgDegree then some .degree
  else if iri == uomMetre || iri == uomEpsgMetre then some .metre
  else none

/-- The unit of a reference system's coordinate axes. `none` (no CRS IRI
in the literal) is CRS84. CRS84 and EPSG:4326 are geographic (degrees);
EPSG:3857 and EPSG:27700 are projected (metres). Any other reference
system is unknown here, so a unit argument cannot be checked against it. -/
def crsUnit : Option String → Option AxisUnit
  | none => some .degree
  | some c =>
      if c == crs84 || c == "http://www.opengis.net/def/crs/EPSG/0/4326" then some .degree
      else if c == "http://www.opengis.net/def/crs/EPSG/0/3857"
           || c == "http://www.opengis.net/def/crs/EPSG/0/27700" then some .metre
      else none

/-- The unit argument: an IRI, or an `xsd:anyURI` literal holding one
(GeoSPARQL types the argument `xsd:anyURI`). Anything else is a type
error. -/
def unitArg : EvalResult → Option String
  | .term (.iri i) => some i.val
  | .term (.literal l) =>
      if l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#anyURI"
      then some l.val.lexicalForm else none
  | _ => none

/-- The `geof:distance` answer, the F\* `geo_double_result`: an `xsd:double`
literal whose lexical form is the exact decimal `Scaled.toStringDec`
writes. -/
def distanceResult (d : Scaled) : EvalResult :=
  .term (.literal (mkTypedLiteral (Scaled.toStringDec d) L4Factoidal.RDF.xsdDouble))

/-- `geof:distance(g1, g2)`, the F\* two-argument form: both literals must
parse, share a reference system (`sameCrs`), and be points. -/
def geofDistance (a b : EvalResult) : Option EvalResult := do
  let va ← wktArg a
  let vb ← wktArg b
  if !(sameCrs va.crs vb.crs) then none
  else (geoDistance va.geom vb.geom).map distanceResult

/-- `geof:distance(g1, g2, unit)`: the two-argument answer, given only
when `unit` is the unit of geom1's reference system. -/
def geofDistanceIn (a b u : EvalResult) : Option EvalResult := do
  let va ← wktArg a
  let asked ← unitArg u >>= unitOfIri
  let own ← crsUnit va.crs
  if asked != own then none else geofDistance a b

/-- The WKT literal result, the F\* `geo_wkt_result`. -/
def wktResult (v : WktValue) : EvalResult :=
  .term (.literal (mkTypedLiteral (Wkt.serializeValue v) ⟨wktLiteralIri, rfl⟩))

/-- `geof:envelope(g)`: the bounding box, in g's reference system. -/
def geofEnvelope (a : EvalResult) : Option EvalResult := do
  let va ← wktArg a
  let env ← geoEnvelope va.geom
  some (wktResult { crs := va.crs, geom := env })

/-- The function table. Install as `EvalEnv.ext`. Unregistered IRIs
    fall through to `none`, which the evaluator turns into the §17.6
    type error — never into `false`, which would silently change
    query answers. -/
def extFns (iri : String) (args : List EvalResult) : Option EvalResult :=
  if !(iri.startsWith geofNs) then none
  else
    let name := iri.drop geofNs.length
    match args with
    | [a, b] =>
        if name == "sfEquals" then geoPredicate sfEquals a b
        else if name == "sfWithin" then geoPredicate sfWithin a b
        else if name == "sfContains" then geoPredicate sfContains a b
        else if name == "sfIntersects" then geoPredicate sfIntersects a b
        else if name == "sfDisjoint" then geoPredicate sfDisjoint a b
        else if name == "sfTouches" then geoPredicate sfTouches a b
        else if name == "distance" then geofDistance a b
        else none
    | [a, b, u] =>
        if name == "distance" then geofDistanceIn a b u else none
    | [a] =>
        if name == "envelope" then geofEnvelope a else none
    | _ => none

end L4Factoidal.Geo
