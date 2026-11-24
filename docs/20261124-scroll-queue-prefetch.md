# Queue scroll prefetch behind script work

On the frozen BBC desktop replay, a prefetch target existed from scroll row 240, while one pending worker request kept the main thread from queueing it. Later, the first frame outside the old keep range ran before the scroll sweep reached its final offset. The latest requested scroll had to wait for a layout after more script commands.

Let the prefetch use the worker's existing low-priority lane instead of requiring an empty worker on the main thread. The queue serves input and ordinary jobs first. Existing checks still prevent speculative work during a foreground render and reject a result from another document state.

In the [alternating desktop experiment](https://github.com/danbri/factoidal-builds/actions/runs/45421479567), with the same engine and frozen HTML, the 20-event scroll p95 went from 17.12 and 18.23 s to 2.69 and 2.66 s. In each trial the first prefetched band became stale; the following foreground frame covered the requested scroll before the script-driven relayout. This is host scheduling evidence. In particular it does not show a reduction in full layout time or a prefetch swap.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).
