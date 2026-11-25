# Partition the first page's synchronous requests during script startup

The native window prepares its first page before assigning the active document. During this interval, the script engine can return a synchronous resource request. The connection pool tried to read that active document to derive the request partition. Liberal mode caught the initialization error and presented the page with its scripts omitted.

The script start has the page URL already. Carry it through the synchronous replies and use that origin first. Keep the existing active-document rule for later requests. An opaque or unavailable origin uses a session partition. [Issue 1031](https://github.com/danbri/factoidal-core/issues/1031) and [native BBC A/B logs](https://github.com/danbri/factoidal-builds/actions/runs/45623938910).
