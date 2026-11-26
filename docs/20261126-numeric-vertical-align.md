# Numeric vertical alignment on horizontal inline lines

CSS 2.2 §10.8.1 measures an inline from its parent's baseline. A positive length raises the box. A percentage uses the element's own computed line height. The archived BBC stylesheet uses negative fractional em and rem offsets. Class matches establish where those declarations could apply. They do not establish visible pixel changes.

The cascade resolves the winning declaration after the font size and line height, retaining its absolute value for explicit inheritance. The document element supplies the rem basis. The numeric displacement accumulates through ordinary inline descendants. The children of an inline-block start in its local coordinate system. A block and a table cell do not pass their own numeric value to their lines.

The line measures shifted ascent and descent alongside the block strut. The text and fragment boxes, glyph coordinates, outlines, backgrounds and underlines use the displaced baseline. Atomic content uses the existing translation of a complete layout result. The table-cell keyword path and existing subscript and superscript metrics are separate.

The candidate accepts signed CSS absolute lengths, em, rem, lh, percentages and unitless zero. The font profile supplies ascent and descent. Adding ex needs the selected face's x-height through both style resolution and the coordinate properties used by the references. Mixing numeric offsets with line-relative keywords on nested non-atomic inlines, non-default reader text magnification and vertical writing need further checks.

## Validation

The module guards cover positive and negative offsets, physical unit conversion, a root-relative inline-block, a percentage with its own line height, hit boxes, glyph runs and paint coordinates. The two theorems state when an inline adds its numeric displacement and when an inline-block starts an unshifted child context. These statements do not establish end-to-end rendering equivalence.

The selected visual cases use the exact WPT revision from [baseline run 45732559655](https://github.com/danbri/factoidal-builds/actions/runs/45732559655). The eighteen numeric failures include the two ex cases. Three signed-zero controls use the same line-box directory. The adjacent JSON supplies the static inputs to factoidal-builds branch-reftests.yml. Add the candidate build run and full core commit SHA to its inputs. Candidate pass counts, engine sizes, browser timings and a before/after BBC render require runs on the resulting package.

## Review changes

An inline contributes its line height even when two numeric offsets cancel. Nested inline flex and grid containers emit a pending atomic item. Both intrinsic measurement and the containing line resolve that item through the same flex/grid layout path as a direct child, using the enclosing inline-block's available width. Root-relative line-height calculations use the document element's font size before vertical-align resolves a percentage.

Glyph runs carry the first source and cluster of their layout line, or the first atomic box's source. Text selection and Find use that identity across displaced glyphs. Selection rectangles retain the painted positions. Producers without layout line information keep the geometry fallback.

The first [exact build](https://github.com/danbri/factoidal-builds/actions/runs/45749114504) rejected the inline-propagation proof. The revised proof supplies the missing display equality. The new guards exercise cancellation with a 100px inline, nested flex and grid boxes, a 2rem line height under a 24px document element, and adjacent displaced text through copy and Find. The two ex cases depend on [selected-font x-height](https://github.com/danbri/factoidal/issues/1307). Kernel checks, pixel outcomes and timings for this revision await its exact build.
