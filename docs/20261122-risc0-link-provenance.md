# RISC Zero archive linking and compiler cache provenance

Tracking: <https://github.com/danbri/factoidal-core/issues/745>.

## Link the exact archive bytes that passed verification

The initial guest build script checked the runtime archive's SHA-256
against its manifest, then supplied the mutable runtime directory as a
link search path. The linker reopened that archive later. A concurrent
runtime rebuild could therefore change the linked bytes after verification.

The build script now retains the exact byte vector it hashed and approved.
`runtime_snapshot.rs` writes those bytes under Cargo's `OUT_DIR`, into a
private directory named from the computed lowercase SHA-256. The snapshot
archive is read-only after creation. Existing snapshots are never replaced:
their regular-file type, read-only state and exact bytes must match.
Symlink snapshots and symlink directories are refused.

Only the snapshot directory is emitted as the runtime archive search path.
Cargo still tracks the original archive and manifest as build inputs, so
source changes trigger a new verification and a new content-named snapshot.
The name comes from the digest computed from the bytes, not a pathname or
name taken from the manifest. Installed toolchain libraries remain separate
link inputs governed by their own pinned installation.

Five standalone Rust controls pass, using the pinned host Rust 1.97.1.
They check that replacing the original source both before and after snapshot
creation cannot alter the linked copy; identical snapshots can be reused;
different bytes cannot overwrite a snapshot; path-like/noncanonical digest
names fail; and file/directory symlinks fail. These tests compile only the
small standard-library helper, not the guest or Lean computation. The final
guest must still be rebuilt and its exact image and journal checked before
producing release evidence.

## Bind cached objects to the installed compiler tree

The earlier object cache included GCC's version text and recorded the two
driver hashes only in the final manifest. That did not invalidate an object
when `cc1`, the assembler, a compiler header or a bundled library changed
without changing the reported version. The builder now computes one SHA-256
over the entire installed `--cpp` tree before selecting cached objects.

The versioned, length-framed encoding binds sorted relative paths, entry
types, file lengths and executable bits, streamed regular-file bytes, and
the exact spelling of symlink targets. Directory symlinks are not traversed;
all targets must resolve within the same tree. Broken or external links,
special files and observed changes to a file during its scan are refused.
Absolute install locations and timestamps do not affect the digest.

Every object fingerprint now includes this tree digest and the independently
hashed selected C and C++ compiler binaries. The manifest records those same
values. These hashes identify the installed build inputs; they do not by
themselves authenticate upstream releases. The separately pinned installer
checks the toolchain release archives. The installed tree must remain
unchanged throughout an ordinary build. Host system libraries outside that
tree are outside this fingerprint.

GCC's inherited search-path overrides could otherwise select headers,
compiler executables or libraries outside the fingerprinted tree. Before
creating any build output or invoking any build step, the builder now
refuses `CPATH`, `C_INCLUDE_PATH`, `CPLUS_INCLUDE_PATH`, `COMPILER_PATH`,
`GCC_EXEC_PREFIX` and `LIBRARY_PATH` whenever any is present, including an
empty value. It names the offending variables without printing their
values. A targeted regression calls the actual build entry point with
each of the six variables set to both empty and nonempty values and
confirms refusal before the output directory is created. An environment
with all six variables absent passes this guard.

Nine focused Python controls pass: the environment guard and eight
fingerprint controls. The latter cover changes to the assembler,
`cc1`, headers and libraries with an unchanged driver; path and executable-bit
changes; relocation and timestamp stability; exact symlink spelling;
directory-link traversal; external/broken links; streamed large files;
special/empty trees; and a symlinked root.

A read-only scan of the installed C++ tree covered 1,598 regular files,
150 directories, six symlinks and 1,718,298,873 regular-file bytes. It produced
SHA-256 `5cb9ad559d47dc9f9eef6d603b852db6dc791b5721faa79939f333cfacf75980`
in 3.763 seconds with 14,952 KiB maximum process RSS. This check did not
rebuild the runtime. Final integration must rebuild through the corrected
cache fingerprint and check the resulting linked guest image before using
its proof as release evidence.
