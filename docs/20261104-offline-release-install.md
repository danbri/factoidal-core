# Offline release input for the verified installer

4 November 2026. `tools/fetch-builds.sh --release-dir` separates an authorized
download step from installation when the installer's network access is unavailable.
It does not change network routing or retry through another transport.

Supply the official release's `build-info.json` and `web.tar.gz` in one directory:

```sh
bash tools/fetch-builds.sh --set web --commit FULL_40_HEX_SOURCE_SHA \
  --release-dir /path/to/downloaded-release --strict --check
```

Remove `--check` to run the normal installer and existing stamp writer after
verification. Offline input requires one explicit set, the full source SHA and
that commit in the checkout's history; `--allow-unrelated` is refused. Previewing
an older ancestor without `--strict` preserves the drift warning and stamps the
older release identity. It must not be represented as an exact newer build.

Before any writes for the selected set, verification checks repository/set/source
identity, archive digest and size, exact file inventory, individual file digests
and sizes, duplicate keys/paths, path traversal and archive links/special files.
It extracts regular files into private staging and checks destination types,
symlink ancestry and existing hardlinks, including receipt/stamp destinations.
Receipts use a private copy of the verified manifest. Offline input never skips
verification merely because a tag is already recorded as installed. `--check`
does not write destination payloads, metadata, stamps or legacy native links.

Hashes establish consistency with the supplied manifest, not the manifest's
authenticity. The operator must obtain the official manifest/archive through a
trusted authorized channel. The installer does not authenticate GitHub offline,
prove source-to-binary correctness or perform an independent reproducible build.
`--strict` compares relevant committed source with HEAD, not dirty working files;
its failure now stops before installation rather than only setting a final error
code while continuing to copy files.

The online multi-set path remains per-set, with no all-sets transaction or
rollback. Its inherited already-installed-tag shortcut still skips verification
and later invokes the stamper; destination-link protections for that cached
online path are outside this change. Offline and new-install paths use the new
staging verification. Post-copy stamp failures retain the existing behavior.

Validation: **13 fixture test groups pass**, including non-check error paths
that prove no destination write, hardlinked external sentinels, check-only
metadata/link controls and a curl tripwire. Inputs are tiny local text archives
and disposable Git histories; no network, real binary installation or build is
performed. Checks remain active with `PYTHONOPTIMIZE=1`. Run:

```sh
python3 tools/test-fetch-builds-offline.py
bash -n tools/fetch-builds.sh
```
