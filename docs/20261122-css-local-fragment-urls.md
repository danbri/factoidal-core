# CSS background fragment URLs

Fragment-only CSS URLs stay local and serialize as fragments. The background resource inventory skips them so it does not fetch the document or the stylesheet as an image. An external image URL with a fragment still resolves against the stylesheet base.

The full-run comparison showed four losses in `css/css-values/urls/fragment-only.html`. Two came from inline CSS and two from linked stylesheets. The custom property case continued to pass. The Lean guards cover quoted and unquoted local fragments and an external URL with a fragment.

[CSS Values and Units Level 4 §4.5.1.1](https://www.w3.org/TR/css-values-4/#local-urls)
