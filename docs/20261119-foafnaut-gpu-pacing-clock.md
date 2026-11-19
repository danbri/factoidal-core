# Foafnaut GPU pacing test clock, 2026-11-19

The macOS package job completed native control geometry parity, including the
anonymous control case, then failed one pure test. The GPU pacing test expected
the second heavy frame's poll to be due in at most 120 ms. It was due in
122.43825380000021 ms. [macOS package job for the earlier source revision](https://github.com/danbri/factoidal-builds/actions/runs/44439728332/job/135290132725).

The first poll was scheduled at 100 ms, the cap for an unmeasured prior. If the
queue has finished when polled, the elapsed time divided by the work cost is an
upper bound on the GPU rate. With two frames of the same cost in this fixture,
the next prediction is the first poll's elapsed time times the 1.1 margin. The
old fixture used a real timer to drive the first poll. A delay past 109.09 ms
could pass its rate check, which allowed for late polls, and still fail its
120 ms check. On the same gate, controlled polls at 100, 109 and 111.3075 ms
predicted 110, 119.9 and 122.43825380000021 ms respectively. The last case
reproduced the reported failure.

`gpu_pacing_test.ts` now drives the window turns with a test clock. It checks
that a poll is due at 100 ms, that a turn at 99 ms does not poll and that the
turn at 100 ms polls once and releases the submission. It checks the learned
rate against 0.08 ms per unit and keeps the 120 ms cap for the next predicted
wait. The test drains scheduled polls before it restores the clock.

The TypeScript check and all 23 pacing tests passed on pinned Deno 2.9.4. The
fixture no longer waits for 100 ms of elapsed host time. The local package
pure-test command needs the generated demo engine. Running the 13 test files
that start without generated engines gave 84 passes and four missing-file
failures from the sparse checkout. Three need the font fixtures and one needs
the Textnaut host source. The full pure suite remains a package CI check.

This change covers host timing in one unit test. Production pacing, the Lean
host pipeline model and its trace checker are unchanged. The reproductions
used the TypeScript gate in this checkout and did not require a Lean build, a
Wasm engine or GPU hardware. No native package result is claimed for this
change.

## Package check

The [fresh complete package run](https://github.com/danbri/factoidal-builds/actions/runs/44456094827)
at e089543af9d390626ffd62809f4cd7c6b94c830b passed the pure test suite
with this fixture, alongside Linux/macOS Lean, Wasm and native checks.
PR606 has merged; that candidate success does not itself publish a new main app.
