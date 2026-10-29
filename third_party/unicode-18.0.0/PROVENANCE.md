# Unicode 18.0.0 data files: provenance

- Source: https://www.unicode.org/Public/18.0.0/ — `idna/IdnaMappingTable.txt`
  (UTS #46 version 18.0.0, dated 2026-06-29), `ucd/extracted/DerivedBidiClass.txt`,
  `ucd/extracted/DerivedJoiningType.txt`, `ucd/extracted/DerivedGeneralCategory.txt`,
  `ucd/extracted/DerivedCombiningClass.txt`; https://www.unicode.org/license.txt
  as `license.txt`.
- Copied unchanged on 2026-10-29.
- Licence: Unicode License v3 (`license.txt`).
- Use: `tools/whatwg/gen-idna-data.py` writes
  `formal/lean4/L4Factoidal/WHATWG/URL/IdnaData.lean` from these files;
  `--check` (run by `tests/whatwg-url/run.sh`) fails when it is stale.
- Why 18.0.0: the web-platform-tests `IdnaTestV2.json` that
  `tests/whatwg-url/run.sh` runs is generated from IdnaTestV2.txt 18.0.0
  (see `third_party/testing/wpt-url-PROVENANCE.md`).
