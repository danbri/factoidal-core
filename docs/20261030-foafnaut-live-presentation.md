# FOAFNaut live presentation admission

The native FOAFNaut window now applies the shared Lean geometry policy to
interactive frames. Previously only checked SVG/artifact exports enforced it;
interactive frames reported diagnostics. Graphics work:
<https://github.com/danbri/factoidal-core/pull/271> and
<https://github.com/danbri/factoidal/issues/1209>.

## Behavior and boundaries

`FoafPresentation.lean` keeps the fixed application configuration, pending
model, latest approved offer and last host-acknowledged scene. Candidate
transitions do not round-trip through caller-editable JSON. Failed or deferred
admission retains the previous approved geometry. Resize clears it and emits
an empty-node placeholder; the admission timestamp is retained. A backwards
clock cannot move that timestamp backwards or resurrect a cleared scene.

Pointer-down uses the acknowledged scene's shared painted parts. The native
host acknowledges an offer only after `session.render` returns success, with
no input dispatch between submission and acknowledgment. A stale token cannot
acknowledge a newer offer. Acknowledgment means successful surface submission,
not GPU completion or proof of displayed pixel equality. Frame payloads describe
the latest approved offer; they are not claims that it has reached the screen.

The controller handles clipboard/editor effects separately from visible
geometry. Admission retries continue while physics is paused. A closed session
is quiet. The time bound is the minimum interval between admission checks,
not a proof that the host calls the controller frequently enough.

`FoafLiveBridge.lean` caches drawing data and layout diagnostics per offer token.
Deferred input, unchanged retries and acknowledgment reuse that cache. Changing
the offer or viewport refreshes it. Dynamic effects/status are overlaid on each
response. `foafnaut_live.ts` transports input/time and validates the wire format;
it contains no duplicate layout, overlap or admission algorithm.

The C bridge owns one opaque Lean value per WASM instance. Invalid event/time
input reports an error while retaining valid state. Each instance permits one
initialization attempt, including after disposal: another session requires a
fresh instance. This prevents a failed reinitialization destroying a valid
session and prevents old tokens acknowledging a restarted session. The legacy
stateless ABI is retained for existing callers and static export commands.

## Proofs and verification

The Lean proofs connect accepted/acknowledged scenes to the shared application
overlap bound; a successful pick belongs to the acknowledged scene's painted
geometry and satisfies its hit predicate. Blank placeholders have no node
footprints. Revision fencing and stale-token acknowledgment properties are
proved. These are integer-geometry/policy results, not Float/GPU or scheduling
equivalence claims.

Native compilation passed all six new controller groups, the presentation
proofs, existing policy/protocol tests, 12 FOAF adapter groups, ten FOAFNaut
state groups, four scene serializer groups and three SVG capacity groups.
The fresh WASM/host suite passed **64 tests, zero failures**, plus **12 C
coordinate checks**. Six live WASM groups cover rejected drags, acknowledged
picking, stale tokens, resize/clock rollback, fixed policy, clipboard while
paused, malformed input retention, disposal and repeated initialization.

Independent source review found the reinitialization/token-reuse defect before
the final run; the single-use holder and sixth WASM regression address it.
Cache invalidation, effect handling, host acknowledgment ordering and C
reference ownership were also reviewed. The native GUI event loop still needs
a desktop interaction check; manual acknowledgment in a WASM test does not
constitute a surface/GPU test.

The warm build initially reached linking then failed because the installed
Emscripten cache was outside writable paths. Linking succeeded using a copied
50 MiB tool cache under `/private/tmp`; no cold Lean runtime build was needed.
The build script now prints linker stderr on failure instead of leaving its
diagnostic only in a side file. Local logs are `/private/tmp/foafnaut-live-build.log`,
`foafnaut-live-link.log`, and `foafnaut-live-tests.log`.

This change does not add SVG input features or change the official WPT score.
The browser component remains a checked static-export demonstration. General
text shaping/layout, a CPU backend and live browser integration remain work.
