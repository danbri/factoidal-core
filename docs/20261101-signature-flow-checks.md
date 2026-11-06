# XML signature flow checks

The library umbrella now imports XML.SignatureFlow and SignatureFlowTests.
The normal `lake build L4Factoidal.XML.SignatureFlowTests` completed (84 jobs).
The module exposes installed/permitted capability admission, bounded stages
and actual composition of root selection, canonicalization, digest/signature
verification and exact canonical coverage. Its tests include a synthetic RSA
callback for control-flow tests; these are not cryptographic oracle tests.

Separately, Node 22 ran xml-signature-native.test.mjs and
xml-signature-oracle.test.mjs sequentially: all ten groups passed, no skips.
The native path was /private/tmp/srx-routing-native/l4wasm-cli, the earlier
locally linked experimental adapter, not a new package release. Independent
JDK checks verify the frozen signatures and reject covered tampering.

The native coverage adapter still calls the existing restricted DSig verifier;
it does not yet instantiate every new SignatureFlow admission obligation.
Do not present this as a proved public end-to-end pipeline, full XML Signature
1.1/2.0 conformance, or rebuilt WASM validation. The RSA callback/FFI, trusted
key selection, and caller-supplied intended content remain explicit boundaries.

Six printed theorem audits use standard Lean axioms only. restrictedStage_sound
includes Classical.choice through its imported definitions; other reported
dependencies are propext and Quot.sound. No new cryptographic primitive was added.
