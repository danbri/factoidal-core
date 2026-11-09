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

## Added 2026-10-29 (milestone 4, Unicode algorithms)

- Source: https://www.unicode.org/Public/18.0.0/ucd/ — `UnicodeData.txt`,
  `DerivedNormalizationProps.txt`, `CompositionExclusions.txt`,
  `BidiBrackets.txt`, `BidiMirroring.txt`, `LineBreak.txt`,
  `EastAsianWidth.txt`, `DerivedCoreProperties.txt`,
  `auxiliary/GraphemeBreakProperty.txt`, `auxiliary/WordBreakProperty.txt`,
  `auxiliary/SentenceBreakProperty.txt`, `emoji/emoji-data.txt`, `ReadMe.txt`.
- Copied unchanged on 2026-10-29.
- Use: the generators in `tools/unicode/` write the data modules under
  `formal/lean4/L4Factoidal/Unicode/` from these files; `--check` (run by
  `tests/unicode/run.sh`) fails when a module is stale.

## Added 2026-11-04 (font shaping, https://github.com/danbri/factoidal/issues/1233)

- Source: https://www.unicode.org/Public/18.0.0/ucd/ — `Scripts.txt`
  (sha256 `0071fd81b6aeae25f6e8bce8efec3066a6476a91b49bdb2f52dc76e817862a6a`),
  `PropertyValueAliases.txt`
  (sha256 `06c4c8eaf7b0bf34abe73b113da1215bd784ac254d4c223600b90267caa4bbbd`).
- Copied unchanged on 2026-11-04.
- Use: `tools/unicode/gen-script-data.py` writes
  `formal/lean4/L4Factoidal/Unicode/ScriptData.lean` (the Script property,
  with ISO 15924 codes); the Lean shaper chooses OpenType script tags from it.

## Added 2026-11-06 (font coverage metric, https://github.com/danbri/factoidal/issues/1245)

- Source: https://www.unicode.org/Public/18.0.0/emoji/ — `emoji-sequences.txt`
  (sha256 `1823dce71f3dd9cb0ad1976797baee4ffbdc1909756f43af8ce4c57f732843a4`),
  `emoji-zwj-sequences.txt`
  (sha256 `f61b5213bdf85a57741a9f903cb38d0f39a3d13be6ff4aca3b39857e859a9191`).
- Copied unchanged on 2026-11-06.
- Use: `tools/render-dashboard/font_coverage.py` reads the sequence totals
  from these files.

## Added 2026-11-08 (Arabic joining, https://github.com/danbri/factoidal/issues/1275)

- Source: https://www.unicode.org/Public/18.0.0/ucd/ — `ArabicShaping.txt`
  (dated 2026-08-18, sha256
  `8ccde4ebd070500a68e8bcb9d5514522fb0bebe57b9ebad3ff925b8e1e669f83`), the file
  HarfBuzz 15.0.0 generates its Arabic joining table from.
- Copied unchanged on 2026-11-08.
- Use: `tools/unicode/gen-joining-data.py` writes
  `formal/lean4/L4Factoidal/Unicode/JoiningData.lean` (Joining_Type, with the
  Syriac joining groups ALAPH and DALATH RISH) from it and
  `DerivedGeneralCategory.txt`; the Lean shaper's Arabic joining forms read it.

## Added 2026-11-09 (colour emoji, https://github.com/danbri/factoidal/issues/1276)

- Source: https://www.unicode.org/Public/18.0.0/emoji/emoji-test.txt
  (UTS #51 version 18.0, dated 2026-04-30, sha256
  `8f3735cda1f92a779d78af67cf86066bb1f07143dc22f2ac29394d9bc57ab21a`).
- Copied unchanged on 2026-11-09.
- Use: `labs/demos/foafnaut/fallback_fonts.py` cuts Noto Color Emoji into slices by
  the groups of this file (Smileys & Emotion, People & Body, ...), and
  `tools/unicode/gen-emoji-data.py` writes
  `formal/lean4/L4Factoidal/Unicode/EmojiData.lean` (Emoji_Presentation and the other
  emoji properties) from `emoji-data.txt`.
