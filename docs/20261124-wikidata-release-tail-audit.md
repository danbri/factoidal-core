# Wikidata stack use in the browser release audit

The Linux release audit in build 45436081050 reported 15 unlisted Wikidata
routines. Issue [#928](https://github.com/danbri/factoidal-core/issues/928)
tracks the release impact.

The source-edit splice, service scan, named subquery scans, ORDER BY flag
scan and triples formatter now accumulate their results in tail position.
The source-edit splice includes a proof that its list of output chunks is
identical to the original definition for every offset, suffix and edit list.

The label rule uses explicit work lists for binding and visibility. Its
termination measures are erased by Lean. The binding pass evaluates both
children in source order and preserves list order and duplicates across joins
and UNION intersections. The visibility pass keeps the original rules for
sibling UNION, OPTIONAL, BIND and SERVICE scopes.

The seven remaining private ARQ renderers share the existing fuel of 128 at
the sole public entry point, which already limits UTF-8 input to 8192 bytes.
Each recursive descent consumes fuel. The audit entries name the seven
declarations individually and record that bound.

The production checks are the full Lean build, the Wikidata rewrite guards,
and the Linux audit of the emitted C.
