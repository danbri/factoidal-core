# MathML Core operator dictionary (data)

- File: `operator-dictionary.json`, copied unchanged.
- Source: web-platform-tests, `mathml/support/operator-dictionary.json`
  (https://github.com/web-platform-tests/wpt/blob/master/mathml/support/operator-dictionary.json), from the WPT
  checkout at commit 2358bd4835 (the commit of the full runs of 2026-11-14).
- Retrieved: 2026-11-14. SHA-256: ec331ebfcd13db2286572ef0a60a0059104b3c3cfb092cb581c4cdfeac090340.
- Licence: 3-Clause BSD (web-platform-tests contributors).
- What it is: the operator dictionary of MathML Core appendix B
  (https://w3c.github.io/mathml-core/#operator-dictionary) as data: for each operator content and form, the
  `lspace` and `rspace` indices (in 1/18 em) and the properties `stretchy`, `symmetric`, `largeop`,
  `movablelimits` and whether it stretches along the inline axis (`horizontal`). The file says it was generated
  by the specification's `operator-dictionary.py`.
- Use: `tools/mathml-operator-dictionary.py` writes
  `formal/lean4/L4Factoidal/Rendering/Math/OperatorDictionaryData.lean` from it. Nothing reads the JSON at run time.
