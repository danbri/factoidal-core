# PR #1: numeric, cast, and shared identity review

Reviewed head `ed19f0905781008d12275c6fbbff257cb77f044a` against its parent
`906527bae7a741780bb4bab8ccb0f8eb890c85ad` in `review-pr-1`.
This report concerns that branch only, not unrelated current main.

## Finding: preserve the source duration subtype when casting to string (P2)

Location: `formal/lean4/L4Factoidal/Fn/Cast.lean:90`–`96`, particularly
`| .dur d => some (canonicalDuration d)`; reachable through
`formal/lean4/L4Factoidal/RIF/Builtins.lean:287`–`291`.

Casting `"P0M"^^xs:yearMonthDuration` to `xs:string` now returns `"PT0S"`.
The required string is `"P0M"`: the dated
[F&O 2007 §17.1.2](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#casting-to-string)
requires the canonical representation of the source duration subtype;
[§10.3.1.3](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#canonical-ymd)
specifies the zero year-month-duration representation.

`literalValue?` retains only `.dur {months, seconds}`, so the cast helper
cannot distinguish zero yearMonthDuration from zero dayTimeDuration or
duration. The target is now string, so `lexical`'s target-subtype fix at
Cast.lean:82–86 does not recover the source subtype. The same issue applies
to derived string targets through `convert` at lines 124–126.

This is introduced: HEAD^'s `evalFunc` cast fallback checks the target lexical
space and returns the original lexical text; its `cast-string` result for
source `P0M` was `P0M`. This comparison does not endorse that old generic
lexical-only casting implementation.

Reproduction, using the parent's completed build cache, with explicit cwd
`review-pr-1/formal/lean4`:

```sh
lake env lean --stdin <<'EOF'
import L4Factoidal.RIF.Builtins
open L4Factoidal.RIF
#eval castXsd "string" (gLit "P0M" (xsdNs ++ "yearMonthDuration"))
#eval castXsd "string" (gLit "P0Y" (xsdNs ++ "yearMonthDuration"))
#eval castXsd "string" (gLit "PT0S" (xsdNs ++ "dayTimeDuration"))
#eval castXsd "string" (gLit "P0M" (xsdNs ++ "duration"))
EOF
```

Observed: all four return `some (GTerm.const "PT0S" xsd:string)`.
The first two should return `P0M`; the last two are correct controls.

This focused guard was also run and exits 1 with “did not evaluate to true”:

```lean
import L4Factoidal.RIF.Builtins
open L4Factoidal.RIF
#guard evalFunc "cast-string" [gLit "P0M" (xsdNs ++ "yearMonthDuration")] ==
  some (gStr "P0M")
```

Repair direction: retain sufficient source datatype information at the shared
cast boundary or provide a source-aware string projection. Do not change
generic `canonicalDuration` to print every zero as `P0M`; that breaks the
dayTimeDuration/duration controls. Add canonicalizing `P0Y → P0M` coverage,
not just a special case returning the original spelling.

The theorem `Fn.Cast.cast_target_valid` at CastTheorems.lean:7 proves target
membership, not conformance of source-to-target conversion. Both `PT0S` and
`P0M` are strings, so that theorem permits this defect. Its documented
postcondition remains true; it must not be described as a full casting
correctness theorem.

## Rejected suspicions and limits

- Double `1e-40` narrowed to float returns zero. This is not filed as an
  IEEE-nearest regression: the explicitly cited
  [F&O 2007 §17.1.3.1](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#casting-to-float)
  prescribes mantissa truncation and an adjusted-exponent underflow rule.
  Do not substitute a host IEEE cast as its oracle without resolving that
  semantic contract.
- Long exact floating-to-string results for `0.1` and `1.2` were confirmed,
  but are not filed as minimum-digit violations of the cited 2007 contract.
  That edition's §17.1.2 uses unlimited decimal precision in the ordinary
  magnitude range and permits multiple round-tripping scientific forms.
- SUM's positive zero identity was checked against the actual SPARQL 1.1
  definition: even a singleton uses numeric-add with zero. Losing the sign
  of a singleton negative zero therefore is not a defect in the new fold.
- Reviewed shared numeric promotion, exact rational arithmetic, unary
  rounding, numeric input validation, XSD value membership, calendar edition
  conversion, enumeration/identity separation and RDF sameTerm changes.
  No additional introduced numeric/RDF-identity defect was confirmed in
  this pass. This is not a complete correctness proof or conformance claim.
- Existing generic unsupported-cast fallbacks, legacy store/join XMLLiteral
  identity, and ORDER BY's unrounded scaled-number policy remain limits;
  the PR documents them. They were not relabeled as introduced defects.

No checkout source was edited and no build was launched by this reviewer.
Only cache-backed `lake env lean --stdin` probes were run after the parent
reported the cache ready. `git status --short` remained empty.
