# Paralliverse editor Run control — 2026-11-19

The published editor had no explicit Run control. It registered a 150 ms debounced input handler; the reported lack of automatic updates has not yet been independently reproduced. The missing visible Run action is established from the actual source and live HTML.

The page now has a keyboard-accessible Run CPU + GPU button. It sends the current editor text immediately through the existing worker pipeline, even when a text replacement emitted no input event. Automatic input updates remain, with a change-event path too. Edits during initialisation state that they will run once the CPU runtime is ready; terminal runtime errors remain visible. The Run control is disabled until initialisation succeeds.

The browser acceptance script adds explicit submission without an input event and another automatic edit afterwards to the existing mixed/changed/zero/reused-buffer cases. These checks run the actual released compiled Lean CPU function and actual WebGPU shaders. They are runtime tests, not new equivalence proofs. Lean source, shader source, ABI and validation remain unchanged; no new engine build is required.

Local syntax and diff checks passed. Exact-source browser acceptance and live deployment evidence are to be recorded on the PR before claiming publication. Local desktop CUA was unavailable in this session; it is not claimed as verification.

The dispatch delay is still 150 ms for automatic input and zero for explicit Run/change. No engine/GPU speed improvement is claimed.

