# Unicode 18.0.0 conformance test files: provenance

- Source: https://www.unicode.org/Public/18.0.0/ucd/ — `NormalizationTest.txt`,
  `BidiTest.txt`, `BidiCharacterTest.txt`, `auxiliary/LineBreakTest.txt`,
  `auxiliary/GraphemeBreakTest.txt`, `auxiliary/WordBreakTest.txt`,
  `auxiliary/SentenceBreakTest.txt`. Each file names its version in its
  first line (`# <name>-18.0.0.txt`).
- Copied unchanged on 2026-10-29 into `third_party/testing/unicode-18.0.0/`.
- Licence: Unicode License v3 (`third_party/unicode-18.0.0/license.txt`).
- Use: `tests/unicode/run.sh` runs `l4unicode` (formal/lean4,
  `Harness/UnicodeConformance.lean`) over each file
  (https://github.com/danbri/factoidal/issues/1167, milestone 4).
