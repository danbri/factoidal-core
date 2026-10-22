# PR1 independent review evidence

This is the unchanged review of head `ed19f0905781008d12275c6fbbff257cb77f044a`,
not a result for the integration branch. Start at [the review](REVIEW-PR-1.md).
The source probes that characterize a defect deliberately expect the old
wrong answer; the separate acceptance probes fail on that head. They are
historical evidence, not replacement integration tests.

The original 31-file archive has SHA256
`469033f46c7be90b614b9ec406309ea1782b5f554b18e68853d57e929fb856b5`.
Its [manifest](logs/pr1-review-manifest.json) records file hashes and provenance.
The [posted review receipt](logs/pr1-review-posted.json) was captured after
that archive. Its addition and this README do not change the original files.
Paths naming other checkouts are original test provenance, not portable
commands. Rebuild the integrated source and use the maintained tests for
acceptance. See [the integration record](../../20261022-pr-integration.md).
