# Lazy image request ordering

The pinned image and flex comparison at c6b8034830a0 observed 62 net
additional passes across 141 files. Three previous passes were lost in
lazy-image tests. Two timed out and the third missed the deadline for
reuse of an available image.

Handle an empty source and consult the document's completed-image list
before deferring a request. An unavailable lazy request registers with
the existing intersection observer. The observer resumes on
isIntersecting, which includes a zero-area intersection. The request
keeps the existing generation, decode-waiter and resource checks when
resumed. Clearing or forcing a deferred request removes the observer
registration.

All 25 source-extracted JavaScript checks passed locally. These exercise
the prelude request and observer logic. Native WPT still needs to check
the document code, actual geometry and delivery of its frame callbacks.
