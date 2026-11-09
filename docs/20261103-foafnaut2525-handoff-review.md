# foafnaut2525 handoff review, 3 November 2026

> Note, 2026-11-09: This handoff is of 3 November and is superseded. Current state:
> [Foafnaut handoff](designissues/2026-11-09-foafnaut-handoff.md) and
> [skills/foafnaut/SKILL.md](../skills/foafnaut/SKILL.md).

Main-thread review at approximately 12:20 UTC of the
[side-thread handoff](20261103-foafnaut2525-side-thread-handoff.md) and
[runtime maturity record](designissues/2026-11-03-foafnaut2525-runtime-maturity.md).
The requested product is a standalone macOS `foafnaut2525` application with
the FOAFNaut graph, embedded LWS and its own native presentation. iPhone/iPad
delivery remains a separate target. The renderer CLI and external-browser
development bundle are intermediate artifacts.

## Rechecked artifacts and release state

The loopback browser at `http://127.0.0.1:8099/` still serves the frozen
host `b578816b0` with engine source `63a73ff4a`. Its live app and WASM hashes
match the tested bundle. The native ARM64 renderer CLI still hashes to
`ee90a9317456104a6104f9219cfe536774fad9aa6888f94cfa18e6a1e7e3c7de`.
It emits scene JSON and optional CPU pixels; it is not a windowed application.
The HTML RDF view is an N-Triples subject/predicate/object view, not the
FOAFNaut graph diagram.

The exact `63a73ff4a` full Lean CI run `41622704531` and Builds web-gates
`41622813132` pass. Builds' macOS package job failed. Another coordinator
pushed `98896de16950c39d19f7791d49e31b3c9d5e607c`, a one-line macOS relocation
permission change, to PR 308. Builds main `3cc3612` requests that exact source;
run `41634305667` is queued and fresh Core CI `41634118597` is running.
The root coordinator is preserving that change and has not dispatched a
duplicate build. Previous green checks do not qualify the new head.

Host/package PR 314 remains stacked on PR 308. Its browser-host and
dataflow/npm workflows pass. Its bundle archive SHA-256 is
`45e9979923c189f84bfd04ab5bfeddafd48ad1f76d1019715219f1f5cd6c70dd`.
There is no browser npm alpha or standalone `foafnaut2525.app` release yet.

The relocation change grants the trusted Deno UI host unrestricted filesystem
read/write access, subject to OS permissions, in place of the former relative
directory grants. It does not itself expose filesystem operations to QuickJS
page scripts. Existing unrestricted FFI already prevents treating Deno's JS
permissions as a process sandbox. Relocation, export and explicit input-path
tests must qualify this new executable; native GPU presentation is separate.

## Fresh native and JavaScript probes

A fresh 16x16 native CPU probe returns all 768 RGB samples. The existing
compiled FOAF host passes its engine check with eight people, nine links and
399 shapes. Its diagnostic reports the main thread, granted FFI and a WebGPU
API. None of those establishes a visible native frame.

Fresh Deno 2.9.4 adapter requests return null for default, low-power,
high-performance and fallback preferences, including the explicit Metal
backend. Native GPU window presentation remains blocked and unverified.
No application bundle or new native GPU implementation was created by this
review. The first native acceptance target is a relocated application opening
the bundled FOAF graph, with actual frame capture, selection, drag/pin, resize
and close. Existing AppKit/CAMetalLayer and Lean interaction code are reusable
inputs; local LWS operations are not yet connected to that application.

Fresh commands, working directories, binary hashes and results are recorded in
`/private/tmp/factoidal-foafnaut2525-native-assessment-20261103.json` and its
adjacent `.log`. The FOAF check used the existing compiled UI executable in
`source/factoidal-foafnaut/labs/demos/foafnaut/.build/dist/`, not a newly built
application from this browser checkpoint.

Issue [1232](https://github.com/danbri/factoidal/issues/1232) is now reproduced
against the actual QuickJS worker and existing Lean WASM, without a host-browser
DOM. Setting a child's text leaves its parent's cached text stale; replacing
the parent's text leaves the detached child discoverable by `getElementById`
in the guest. Replaying the emitted commands through Lean removes the connected
child correctly. This is an observed guest-binding defect, not just a proposed
test. Reproduction: `/tmp/factoidal-issue1232-repro.mjs`.

The guest reports `WebAssembly`, `setTimeout`, `getComputedStyle` and
`XSLTProcessor` as undefined. `Promise` exists, but this does not establish a
browser event loop or Promise job draining. The next JS milestone is live,
same-turn DOM reads and connected-node identity, tested against Lean replay.
Layout-query flush semantics must be explicit before exposing those methods.

The existing Lean XSLT string APIs remain reusable engine components. Neither
XML stylesheet association nor `XSLTProcessor` is wired into this browser.
The maturity record's proposed order remains appropriate: document loading and
stylesheet association first, then the synchronous script API with defined
XML DOM ownership and resource limits.

The XSLT 1.0 engine accepts explicit document/import maps, but its public
two-string wrapper supplies neither. Unresolved imports can be skipped during
stylesheet reading and are not uniformly rejected. XSLT4's one-module wrapper
strictly refuses unresolved includes/imports with `XTSE0165`. A future loader
must test the selected engine's actual resolution behavior.

## External tests and resilience

Reopened the last complete external run record:
`/tmp/factoidal-overnight-corpus-curves-web-wasm-ready/run.json`.
It completed at 00:49 UTC: 601 relations, 29 matches, 21 mismatches,
264 unsupported, 30 rejected and 257 unavailable. It used older engines and
does not qualify the current bundle. Preserve distinct failure categories,
unchanged fixtures and actual/expected/diff evidence. Native/WASM agreement
is a consistency check, not the independent standards oracle.

Free disk was approximately 375 MiB during this review, below the 3 GiB
build/capture floor. No heavy local build or new corpus capture was started.
The earlier read-only audit found no safe task-owned reclamation large enough
to restore that floor; no foreign files or raw evidence were deleted.

The HTML host still calls synchronous renderer `ccall` on the UI thread.
AbortController cannot interrupt that computation. A terminable renderer
worker/process is therefore the first resilience boundary to establish.
Bounded simplification must retain original bytes and diagnostics, label the
adapted result and remain separate from unchanged-input conformance tests.
Recovery, page-facing guest WASM and shader-playground integration remain
implementation work; this documentation checkpoint does not claim them.
