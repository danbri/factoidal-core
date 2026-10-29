# XProc local filesystem steps — 2026-10-29

`FileSteps.lean` implements local store, file-info, directory-list, file-mkdir,
file-delete, file-copy and file-move using Lean filesystem IO. Runtime supplies
an explicit authorized write root. Missing authorization, paths escaping the
canonical root (including through an existing ancestor), and mutation of the
root itself are refused. Recursive deletion uses Lean's operation that deletes
symlinks without following them. Runner owns temporary fixture mirroring and
cleanup; no fixture source directory is a write root.

Store serializes the actual XPath payload at the boundary, merges stored and
explicit serialization options, and selects a default method from content type.
Non-UTF-8 output encoding is explicitly unsupported. Copy supports recursive
directory content, source-directory nesting, default overwrite, and skip when
overwrite is false. Listing supports sequence-valued regex filters, relative
paths with directory separators, depth, detailed metadata and content-type
pattern overrides. Readability and modification time come from actual IO.

No writable flag is fabricated: Lean's exposed IO metadata lacks permission
bits/access checks. Four detailed directory listing fixtures therefore remain
failures. File-touch is not advertised: Lean's exposed IO API lacks a timestamp
setter; rewriting files or pretending to touch directories is not a substitute.

Validation: FileSteps module build passed. The exported `fileStepsRegression`
returned true after temporary store/readback/copy/delete and root-confinement
checks. Real upstream fixtures via Runner yielded file-copy 35 pass, zero fail,
three unsupported; directory-list 47 pass, four fail, eight unsupported; store
2 pass. The directory-list counts combine the complete targeted interpreter run
with the isolated passing rerun of fixture 051 after its directory content-type
fix. Unsupported fixture setup metadata remains explicit. Full-suite results
are measured separately by the root agent; no executable was rebuilt here.

## Exclusive temporary files

Added p:file-create-tempfile with prefix/suffix and optional href directory.
The existing Lean `.writeNew` handle mode uses O_CREAT|O_EXCL, so creation never
replaces an existing file. Names are generated randomly and collisions retry;
files are restricted to owner read/write. Both explicit and default directories
remain inside the authorized write root. No href means the authorized root,
not an unconfined operating-system temporary directory. Invalid/non-directory
locations and fail-on-error behavior use the corresponding XProc error codes.

All 24 ab-file-create-tempfile fixtures were executed through Runner: 21 pass,
zero fail, three unsupported fixture permission setups. The exported IO
regression now creates two distinct real temporary files and checks prefix,
suffix and existence; it returns true. Module build passed. Unknown-extension
file-info content type now defaults to application/octet-stream.
