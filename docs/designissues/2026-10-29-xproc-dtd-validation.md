# XProc DTD revalidation — 2026-10-29

`ValidationSteps.validationPorts` returns both `result` and `report`; the
`validationStep` convenience API returns the primary result. The implementation
reuses serialization, external-resource loading, XML parsing and XML validity
checking. Source document serialization properties take precedence over the
step's supplied serialization map, matching the tests that deliberately supply
an invalid system identifier while storing a valid one on the document.

Reparsing applies DTD default attributes and normalization through the existing
parser. Validation reports contain actual loader, parser or XML validity
messages as XVrl detections. `assert-valid=true` raises XC0210 for invalidity;
false returns result and report. Incomplete external parameter entity processing
remains explicitly unsupported. No XML Schema typing/PSVI claim is made.

Module build passed (137 jobs). The exported IO regression creates a real DTD
and checks successful validation/defaulting, invalid-child rejection and
permissive diagnostic output; it returned true. Full upstream DTD fixture
measurement belongs to the integrated Runtime/Runner build.
