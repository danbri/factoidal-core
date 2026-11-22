# ASK guest execution parity runner

Date: 2026-11-22

Tracking: [local ASK attestations](https://github.com/danbri/factoidal-core/issues/745).

`zkvm/risc0/check-guest.py` turns the native fixture evidence into a
repeatable local guest execution gate. It accepts explicit paths for the
host tool, pinned executor, packaged programme, native evidence and a new
output directory. It never starts a compiler or a proof operation.

The native gate must have passed its complete 24-file-case and 28-self-test
inventories. Its recorded source hashes, including the native gate itself,
must equal the current source/import inventory. Successful fixture journals
must match both their retained independent oracle and the current fixture
bytes' public commitments. Python performs byte framing and SHA-256 checks;
RDF parsing, policy admission, closure and ASK remain in the guest's Lean
implementation.

The guest gate adds four refusal controls: trailing bytes, a truncated
field, regime byte 2 and 257 retained triples. Success requires the host's
execution-only JSON result, the expected Boolean, one consistent image ID
and valid cycle/time fields. Refusal requires exit 1, empty stdout and the
specified diagnostic category. A signal, timeout, wrong error, missing case
or missing journal fails the gate. Partial runs retain a non-passing result.

The output keeps private input frames, comparison journals, separate logs,
programme/tool/input/journal hashes and actual execution measurements.
It records supplied binaries rather than asserting their source provenance.
It generates no cryptographic receipt. The invocation and the lightweight
refusal tests are documented in the [backend README](../zkvm/risc0/README.md).

The lightweight validator suite passed 13 tests in 9.3 seconds before the
real guest run. These cover inventory/source drift, journal and input
tampering, false answers, refusal isolation, JSON result validation and
refusal to overwrite an existing output directory. They do not execute a
guest; real execution measurements belong to the runner's result record.
