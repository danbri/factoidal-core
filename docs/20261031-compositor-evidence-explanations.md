# Readable component and connection evidence

Tracking: https://github.com/danbri/factoidal/issues/1213.

Evidence mode uses steady cyan borders and glow, explicit on/off text and
keyboard-operable labels. It does not flash, shimmer continuously, or rank human
value by assurance colour. Reduced-motion and forced-colour preferences have
explicit styles. Node labels open the evidence inspector and move focus to its
heading; wires have the same keyboard route. Fit includes actual node heights.

The pipeline retains the actual published 0.27 registry entries alongside run
records. Explanations identify reader scoping/set semantics, RDF merge, RDFS
soundness versus completeness, and the evaluator's named assumption boundary.
Formal source links are pinned to the published engine commit. Registry notes,
theorem names and test references remain visible, with raw records in expandable
sections. Empty runtime assumption arrays are not described as proof that no
assumptions exist. Test references are not presented as a fresh test-suite run.

Each connection describes the actual recipe, established checks and outstanding
preservation/precondition obligations. Only the existing tagged-input merge
subgraph has a checked graph-composition claim. Graph assignment, selection,
results transport/projection and browser rendering do not acquire proofs from
neighbouring nodes. New adapter and whole-pipeline proof work is requested;
this presentation change does not manufacture those proofs.

Validation: ten focused compositor tests passed; two shared highlighting tests
passed after including their vendored Shiki files in the sparse checkout. A real
Eleventy app build passed with the Pages prefix. Chrome ran the actual published
WASM pipeline and exercised source edits, slider, evidence, table/source/export,
drag/zoom, invalid input and reset without browser errors. Focused browser checks
cover keyboard label activation, focus transfer, real registry theorem/test scope,
pinned source links, reduced motion, forced colours and hiding evidence again.
The initial manual build used the repository rather than docs working directory;
rerunning in docs succeeded. No engine or npm release is changed here.
