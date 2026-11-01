# Paired SVG dash values and unit provenance

`NativeSVGDash.Length` in `SVGDashUnits.lean` stores a resolved Float magnitude
and its percentage-origin flag together. Both the dash array and dash offset
use this record. SVG style inheritance copies records; odd-list normalization
repeats whole records. The former parallel `dashArray`/`dashPercent` lists and
zip/count guard are removed. A consumer cannot truncate one independently of
the other because there is only one list.

The percentage distinction remains necessary after resolving a value against
the viewport: [SVG 2 §9.6.1](https://www.w3.org/TR/SVG2/paths.html#PathLengthAttribute)
exempts percentage distances from pathLength calibration. This representation
change preserves that behavior without adding CSS or changing sampling.

`normalizeLengths` reuses the existing numeric normalizer for validation,
zero-total behavior and bounds, then retains or duplicates complete input
records. `Length.calibrated` applies scaling only to nonpercentage records.

## Kernel evidence and its limits

`SVGDashUnitProofs.lean` proves over the actual returned normalizer result:

- `normalizeLengths_structure`: the result is empty, the original list, or two
  copies of that list.
- `normalizeLengths_provenance`: every surviving record came from the input,
  preserving its value and unit flag together.
- `normalizeLengths_even`: the result has even cardinality for dash/gap pairs.

The checked axioms printed for provenance and cardinality are propext,
Classical.choice and Quot.sound; no sorry or new axiom is used. These theorems do
not establish real-number geometry, Float accuracy, viewport resolution or
browser pixel agreement.

A temporary mutation changed the normalizer's even-list branch to flip each
percentage flag. The mutated module compiled, but the actual structure theorem
failed with an unsolved result-equality goal; the proof file exited 1. Thus the
check reaches the producer semantics rather than failing on missing files or
syntax. The production module/proofs were not changed by this control.
Temporary mutation files are under /private/tmp/svg-unit-provenance-mutation.

## Executable and artifact checks

Seven direct unit controls pass, including mixed odd patterns, equal magnitudes
with different units, zero patterns, negative input and calibration selection.
Existing pathLength, dash and percentage source suites also pass using isolated
oleans with the existing checked dependencies. The lab build now compiles and
links SVGDashUnits and runs its tests and proofs.

The unchanged official pathlength-001 scene was exported through SVGArtifact
before and after this representation change. The complete paired shader/data/
checks JSON is byte-for-byte equal:
SHA-256 `07edb2b27eac7d518321c495d2bf3af6c7d29044c178882d87f34973a4f5a16a`.
Files: /private/tmp/solving-pathlength-001.json and
/private/tmp/solving-pathlength-001-paired.json. This finite artifact equality
preserves the prior measured GPU result; it does not turn that result into a
visual pass. Its existing 1,512-pixel edge-coverage mismatch remains recorded in
the pathLength note.

No heavy build, WASM replacement, graphics sampling change or fixture change was
made. Public binary/release correspondence remains a separate build obligation.
