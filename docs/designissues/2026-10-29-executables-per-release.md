# Build executables for each package release

Proposal, 2026-10-29. Requested after testing the Mac 0.26.0 executable.
This document does not change or dispatch release workflows.

## Current wiring

[`exe.yml`](https://github.com/danbri/factoidal-builds/blob/main/.github/workflows/exe.yml)
runs after successful general engine builds, or by manual dispatch. Its
automatic path reads `latest/web.json`, rather than the release identity
of the triggering run. It compiles six targets, runs full executable tests
on Linux x86_64 and macOS arm64, and uses `--quick` on Windows x86_64. That
Windows run does not exercise WebDAV. Three other artifacts are built but
not executed by this matrix.

[`npm-publish.yml`](https://github.com/danbri/factoidal-builds/blob/main/.github/workflows/npm-publish.yml)
is a separate manual workflow with exact `core_ref`, `confirm` version and
`dist_tag`. It verifies the corresponding web build, packs and publishes
the npm tarball. There is no dependency between that publication and the
executable gate. Thus npm can advance while `latest/exe.json` remains at an
older version. Re-running the old core commit also reuses its old test
harness, so repairing tests in main does not repair checks of that commit.

## Recommended release sequence

1. Prepare one release manifest after the existing pack/check steps. Record
   package name and version, exact core SHA, web release, npm tarball SHA-512
   integrity, WASM SHA-256, build-tools/test commit and Deno version.
2. Compile the six executables from that exact tarball via
   `FACTOIDAL_PKG` and `tools/build-exe.sh`. A tarball that is already
   published is also a valid input for backfilling 0.26.0. Never resolve
   an unqualified npm version or a moving `latest/web.json` at this step.
3. Test the actual executable on each supported runner. At minimum retain
   Linux x86_64 and Mac arm64 checks and add full Windows WebDAV tests.
   Give other architectures a matching runner or label them built-only;
   cross-compilation is not execution evidence.
4. Check `version --json` against the manifest, not just the presence of a
   digest line. Test LWS authorization, WebDAV user/mount restrictions,
   read-only behavior, large-file integrity, and recovery after failures.
   The executable must work with no Node executable on its runtime PATH;
   the test driver may use Node separately.
5. Publish versioned executable assets and their checksums only after the
   gates pass. Include the manifest, test results and run links. Preserve
   existing assets on retry; fail if a conflicting artifact already exists
   instead of deleting a published release.
6. Update a release status manifest with separate npm and executable
   states: pending, passed, failed, published. Update a latest pointer only
   after publication, with package version as well as source SHA. An older
   retry must not move the latest pointer backwards.

The preferred long-term structure is a shared release workflow that packs
once, builds and checks both forms, then publishes them. Extract reusable
executable jobs into a `workflow_call` that accepts the immutable manifest
and tarball artifact. Keep npm OIDC publication in its registered workflow.
An executable test failure then prevents a release being announced as
complete across all supported distribution formats.

## Smallest transition: immediately after npm publication

Add a dependent reusable executable job to `npm-publish.yml`, with
`needs: publish`, passing the exact confirmed version and core SHA from that
job. Retrieve `@factoidal/core@VERSION` and validate its registry integrity
and embedded stamp. The same reusable job supports a manual backfill of
already-published versions. Pin the test harness separately when fixing
release tooling for old versions; show both commits in the manifest.

This transition does not make npm publication depend on executable success:
if an executable gate fails, npm remains published and the combined release
status must say that the binaries failed. It is a practical first change;
building and checking before publication removes that interval later.

Use a concurrency key per immutable release, not one global pending slot
that can discard a queued version. Serialize latest-pointer promotion and
check version ordering there. Preserve failure logs and server stderr as
artifacts with `if: always()`. A failure needs a visible workflow failure
and a link from the release status, not an old executable presented as the
matching version.

## Immediate blocker

The local Mac 0.26.0 executable passes the 33-check access/login suite but
fails the complete desktop gate on a large read and an encoded resource
name. [Measurements](../20261029-webdav-executable-gate.md). Repair those
engine defects (https://github.com/danbri/factoidal/issues/1202) before
declaring the full executable gate green. Keep the
read-only restrictions and public LWS boundary in place.
