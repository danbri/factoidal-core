# Unicode 17.0.0 data files: provenance

- Source: https://www.unicode.org/Public/17.0.0/ — `ucd/extracted/DerivedGeneralCategory.txt`, `ucd/Scripts.txt`, `ucd/ScriptExtensions.txt`, `ucd/PropList.txt`, `ucd/DerivedCoreProperties.txt`, `ucd/DerivedNormalizationProps.txt`, `ucd/extracted/DerivedBinaryProperties.txt`, `ucd/emoji/emoji-data.txt`, `emoji/emoji-sequences.txt`, `emoji/emoji-zwj-sequences.txt`, `ucd/PropertyAliases.txt`, `ucd/PropertyValueAliases.txt`; https://www.unicode.org/license.txt as `license.txt`.
- Copied unchanged on 2026-11-15. SHA-256:

      13dd09d35a9377e33eb388a01e6581d4bfec6b2685316078c341982fa444071a  DerivedBinaryProperties.txt
      24c7fed1195c482faaefd5c1e7eb821c5ee1fb6de07ecdbaa64b56a99da22c08  DerivedCoreProperties.txt
      d62e5bab70ca74f099343f71224fa051cb1fdd61a1ab45c0488c44cfc0b6102e  DerivedGeneralCategory.txt
      71fd6a206a2c0cdd41feb6b7f656aa31091db45e9cedc926985d718397f9e488  DerivedNormalizationProps.txt
      2cb2bb9455cda83e8481541ecf5b6dfda66a3bb89efa3fa7c5297eccf607b72b  emoji-data.txt
      12cc8267dc33cbd11ed32bcf6fc5dc2ad9c7a77bae1bdfba2f41b1b9b3ead8dd  emoji-sequences.txt
      5b25441daed2322b068c5e70cda522946a4f0274df864445a1965a92e5fc5cad  emoji-zwj-sequences.txt
      e7a93b009565cfce55919a381437ac4db883e9da2126fa28b91d12732bc53d96  license.txt
      4441f573caf952ffece1d7c892e7715bd7136dfc26f96eb6f268bf1e474715fb  PropertyAliases.txt
      64e9a5f76f7a1e8b5a47d6a1f9a26522a251208f5276bdfa1559dac7cf2e827a  PropertyValueAliases.txt
      130dcddcaadaf071008bdfce1e7743e04fdfbc910886f017d9f9ac931d8c64dd  PropList.txt
      ec2107e58825a1586acee8e0911ce18260394ac8b87e535ca325f1ccbeb06bc6  ScriptExtensions.txt
      9f5e50d3abaee7d6ce09480f325c706f485ae3240912527e651954d2d6b035bf  Scripts.txt

- Licence: Unicode License v3 (`license.txt`).
- Use: `tools/unicode/gen-regex-prop-data.py` writes `formal/lean4/L4Factoidal/Unicode/RegexPropData.lean`, the code points of the RegExp property escapes of BubblePopJS (ECMA-262 §22.2.2.9).
- Why 17.0.0 and not the 18.0.0 of the other tables: the RegExp property escape tests of Test262 at the commit the Test262 workflow pins (2e58f87d83) are generated from Unicode 17.0.0, and a test that compares every code point fails (slowly, one character at a time) on any difference. Move to 18.0.0 when Test262 does.
