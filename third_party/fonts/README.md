# Fonts

Open-licence fonts that the Foafnaut browser engine reads. The Lean code reads,
shapes and draws them; no font library runs.

| Directory | Font | Version | Licence | Source |
|---|---|---|---|---|
| `noto-sans/` | Noto Sans Regular, unhinted | 2.015 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSans/unhinted/ttf |
| `noto-sans-armenian/` | Noto Sans Armenian Regular, unhinted | 2.008 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSansArmenian/unhinted/ttf (commit 1aaeb679c581) |

`NotoSans-Regular.ttf` SHA-256:
`f3961a9cde016d41a4879aecda1474d3a36d6bf54fa0e4643de029cc2248b0e8`.

`NotoSansArmenian-Regular.ttf` SHA-256:
`73bde9f3c63aa5ed39236e8a2837224605210a98b54d65724676c0119fcaa24c`.
It is the first fallback font: the engine draws Armenian with it, after Noto Sans,
which has no Armenian. The fallback tests in `labs/demos/foafnaut` use it.

The files are not changed. OFL 1.1 lets us copy and bundle them with software
if the licence stays with them, and it does not let us sell a font on its own.
