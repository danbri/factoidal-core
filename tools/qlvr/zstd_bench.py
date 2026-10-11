#!/usr/bin/env python3
"""Time libzstd (the `zstandard` package) on the frames that
`l4qlvr-zstd-check blocks` decodes, for the throughput comparison in
docs/designissues/2026-10-11-qlever-index-format.md.

Usage: python3 -I tools/qlvr/zstd_bench.py INDEXDIR TSV [REPEATS]

TSV is the output of `probe_index.py --zstd-tsv`. Prints the best of
REPEATS (default 5) runs: decode time only, output bytes per second, and
the peak resident set size of this process.
"""
import os
import resource
import sys
import time

import zstandard


def main():
    d, tsv = sys.argv[1], sys.argv[2]
    repeats = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    files = {}
    frames = []
    for line in open(tsv):
        if line.startswith("#") or not line.strip():
            continue
        name, off, length, _size, _sha = line.split("\t")
        if name not in files:
            with open(os.path.join(d, name), "rb") as f:
                files[name] = f.read()
        off, length = int(off), int(length)
        frames.append(files[name][off:off + length])
    dctx = zstandard.ZstdDecompressor()
    best = None
    out_bytes = 0
    for _ in range(repeats):
        out_bytes = 0
        t0 = time.perf_counter()
        for fr in frames:
            out_bytes += len(dctx.decompress(fr))
        t = time.perf_counter() - t0
        best = t if best is None else min(best, t)
    print("libzstd %s: %d frames, %d bytes of output in %.1f ms (%.0f MB/s), best of %d"
          % (".".join(map(str, zstandard.ZSTD_VERSION)), len(frames), out_bytes,
             best * 1000, out_bytes / best / 1e6, repeats))
    print("peak RSS (ru_maxrss): %d kB" % resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


if __name__ == "__main__":
    main()
