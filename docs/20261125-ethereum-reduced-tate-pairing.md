# Independent BLS reduced Tate pairing — 25 November 2026

Tracks #995 and #725. Isolated branch from draft #991 head 6ee55be835385778ba4b5dd1bf3ccc594fa1d31d. [Actual predecessor Linux log](https://github.com/danbri/factoidal-core/actions/runs/45523160948/job/138899829448) confirms 318/318 native target-field cases (1173.274449 ms), five comparator controls and four axiom-inventory controls. Five actual theorem reports depend on propext and Quot.sound; checkedOutput_ok depends on propext only. This evidence is for the predecessor merge commit 5f286901414f15eeba0378a8dd9418367c40f191, not the new implementation.

## Executable change

The existing standalone target-field executable now accepts six decimal coordinates for a reduced Tate calculation. It checks width and field canonicality, verifies both curve equations, untwists the G2 coordinates with x/w² and y/w³, and evaluates a fixed 254-iteration binary Miller recurrence on G1 (initial leading bit represented by P). It tracks complete line and vertical factors, checks that the running point ends at infinity, refuses zero numerator/denominator, checks the target-field inverse and calls the existing finalPower on the full quotient. The result is checked for canonical representation. The recurrence uses bounded base inversion by Fermat and the existing 4572-fuel target power. No cryptographic host call. Existing multiply, power and finalPower definitions and six statements are unchanged.

The coordinate interface is **not** an Ethereum pairing precompile or BLS verifier: no G2 subgroup admission, compressed byte integration, infinity input semantics, pairing-product ABI, message hash or signature decision. The G1 end-point check is not a proved mathematical subgroup equivalence. Full field and group refinement, Tate/optimal-Ate pairing equation equivalence, degeneracy completeness and side-channel/runtime bounds remain open. The experimental standalone executable is not wired into any production path; no production risk accepted. Mathematical parameters referenced from [CFRG pairing-friendly curves draft-16](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-pairing-friendly-curves-16) (informational draft), and [RFC 9380](https://www.rfc-editor.org/rfc/rfc9380). No external code imported.

## Verification

Executed the actual new oracle generation/comparator body in an isolated JS engine (Node I/O excluded): 16 expectations, five positive full target-field outputs, eleven rejection expectations, five falsification controls. The independent oracle works in the polynomial basis w^12−2w^6+2, uses Euclidean base inversion, polynomial untwist inversion, left-to-right exponentiation and explicitly checks reduction of all vertical denominators to one. It checks nondegeneracy, order r, G1 multiplication by 2, 3 and −1 and G2 negation. A separate ephemeral tower-arithmetic model of the proposed full quotient algorithm matched all 16 oracle expectations; this is not native Lean execution or a checked theorem. No local pinned Lean or shared Mac/coding subagent available.

The hosted gate requires the retained 318 native cases and all 16 new native cases, actual ten exact theorem reports, permitted axiom sets, source and native-link checks. New proof statements: tate_width, tate_noncanonical, tate_curve and tate_ok. No new theorem is claimed checked until the actual compiler reports pass. Lean compiler/runtime and line transport are trusted; input line allocation precedes the transport limit. No broader Linux premerge gate or main merge claimed.

## Exact source pins

- formal/lean4/ethereum-consensus/PairingTarget.lean e265d96dddeaaed548b54d29688e959a7ff61227
- formal/lean4/ethereum-consensus/scripts/check-tate-pairing.mjs 5a512faf25850483dc265800e7b6d827e1f8f871
- formal/lean4/ethereum-consensus/scripts/check-pairing-target.mjs ad47b702dad594b2173d3f6d5bd17c67eed84a59
- formal/lean4/ethereum-consensus/lean-toolchain a8afa7d1b02d96f0671eba854a8dc4b416beb473
- formal/lean4/ethereum-consensus/lake-manifest.json 15728fe01a01ed2369565ec5be9afdf6abcf2f91
- formal/lean4/ethereum-consensus/lakefile.toml b08203129886735a8fbfc2c31fb7027024665d1f
- .github/workflows/ethereum-bls-pairing-target.yml 5d8956c0a97c4787831065a26cf9dbc9f4e86b9a

Toolchain remains 4.33.1; empty external package graph. Reproduction (from the isolated consensus project directory): use the commands in the dedicated workflow to compile the actual entry point, run both oracle scripts against the native executable and audit the emitted theorem reports. The branch remains a draft checkpoint pending native CI.