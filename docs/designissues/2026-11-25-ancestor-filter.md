# Ancestor filter for CSS rule matching (2026-11-25)

Tracking: https://github.com/danbri/factoidal-core/issues/871 (style-independent table part, realperf).
Code: `formal/lean4/L4Factoidal/Rendering/Style.lean`, section "The ancestor filter".
Checks: `formal/lean4/L4Factoidal/Rendering/CascadeTests.lean`.

## Measured cause (page wp-us, Wikipedia "United States", snapshot 2026-11-15)

Profile on main (total render 39 s): `CSS.RuleIndex.matched` 11.6 %, of it `CSS.matchEntry` 11.2 %;
`DOM.Selectors.matchFrom` 8.3 %, `matchCompound` 7.0 %.

The rules of the page's two style sheets and its `style` elements were read (2,555 selectors;
1,063 of them go through `DOM.Selectors` because they have a child or sibling combinator, an
attribute selector, `:not()`, `:is()` or `:has()`). A model of the bucket index and of the
matcher walk, run over the 21,861 elements of the page (script
`labs`-free, kept in the session scratchpad, not in the tree), gave:

- 1,754,904 (element, selector) tests from the buckets.
- 1,213,677 of them pass the rightmost-compound prefilter and reach `DOM.Selectors`
  (`complexMatches`); 198,249 of those match (16 %). They walk 7,465,122 compound steps.
- 527,069 pass `selectorPartsMatchK` for selectors of compounds; 359,191 of those have
  descendant combinators and walk 5,827,458 compound steps; 18,284 match (5 %).

So the cost is both causes in the task: complex selectors (about three quarters of the
`matchEntry` time) and descendant walks (the rest), and in both most walks fail after a walk
to the root, because the element has no ancestor with a key that the selector names (for
example `.ns-100 .mw-parser-output :not(.notheme)`: 21,861 tests, no match).

With the filter below, the same model refuses 813,469 complex and 340,785 compound
tests before any walk, leaves 400,208 complex tests (871,727 steps, a 88 % cut) and 18,406
compound walks (135,363 steps, a 98 % cut), and the match counts are unchanged.

## Mechanism

Each element has a bit set (`ElemKey.anc`, 9 words of 60 bits) with the hashes of the type
(`lname`), `id` and classes of all its ancestors (`ancOf`, built once per page in
`ElemKeys.of`). Each selector has the list of hashes that it requires of ancestors
(`Selector.need`): for a selector of compounds, the type, `id` and classes of each compound
after the rightmost; for a selector with `complex`, the same for the compounds reached from
the subject by descendant and child combinators only, outside `:not()`, `:is()` and the
other functional pseudo-classes. `RuleIndex.matched` tries a selector only when
`ancAdmits` finds every required bit; a hash collision costs one matcher call. A key table
with no filter (`ElemKey.read`, `readKeys`) admits everything. The plain function is
`RuleIndex.matchedPlain`; the matcher functions are unchanged.

## What is proved and what is checked

- `selectorPartsMatchK_need`, `needSound_plain`, `ElemKeys.get_covers`: a selector of
  compounds that matches an element has each required key in the filter of the table.
- `matchSelsA_eq`, `matchEntryA_eq`, `RuleIndex.matched_eq_plain`,
  `RuleIndex.build_matched_eq_plain`: the filtered matches are the plain ones, given the
  necessary condition (`NeedSound`) for each selector.
- For a selector with `complex` the necessary condition is not proved: `DOM.Selectors.matchFrom`
  walks ancestors in `for` loops. `CascadeTests.refusals` checks it on every
  (element, selector) pair of several pages (refused pairs must not match), and the A/B run on
  real pages compares pictures. A proof about `matchFrom` is open work.

The scoped index (`ScopedIndex`, pages with shadow trees) and the partial-restyle key memo of
`WebDocument.RuleMatcher.keysMemo` have no filter (their keys carry an empty one, which admits
all). `WebDocument.RuleMatcher.make_matched_keys` (unused) is removed: the filtered matcher is
equal to the plain one by `RuleIndex.matched_eq_plain`, not by `readKeys` alone.
