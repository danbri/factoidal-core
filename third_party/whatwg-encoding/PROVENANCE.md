# WHATWG Encoding Standard resources: provenance

- Source: https://github.com/whatwg/encoding, branch `main`, commit
  `be17ac5c49881336538acfc7b40dba3c8009144b` ("Fix off-by-one error in peek",
  2026-10-19).
- Copied unchanged: `encodings.json` (the label table of section 4.2),
  `indexes.json` (every index of section 5; the non-normative JSON form of the
  `index-*.txt` files) and `LICENSE`.
- Copied on 2026-10-29.
- Licence: Creative Commons Attribution 4.0 International (`LICENSE`); the
  portions incorporated into source code (the generated `Data.lean`) are under
  the BSD 3-Clause License, as `LICENSE` says.
- Use: `tools/whatwg/gen-encoding-data.py` writes
  `formal/lean4/L4Factoidal/WHATWG/Encoding/Data.lean` from these two files;
  `--check` (run by `tests/whatwg-encoding/run.sh`) fails when it is stale.
