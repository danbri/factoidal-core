# Keep replaced controls out of anonymous table construction

GOV.UK uses a table layout around its search form. The input itself is assigned an internal table display. The November 22 browser reported a 12px input on the live source and a 4px input in an independent reduced version. The reduced inline-block control occupied 564px.

CSS Display 3 §2.4 treats a replaced element with internal display as inline for box generation. Use the existing atomic inline path for those elements before anonymous table construction. The cascade keeps the original computed display value for CSSOM. Ordinary table cells and other non-replaced boxes retain their display.

The Lean theorem states that non-replaced boxes keep their display. The build also checks guards for a replaced internal cell, an ordinary cell and hidden display.

This changes search field width. GOV.UK's separate zero-height float row and the form's behaviour in the desktop window still need verification.

[Desktop acceptance](https://github.com/danbri/factoidal-core/issues/712) · [CSS Display 3](https://drafts.csswg.org/css-display-3/#layout-internal)
