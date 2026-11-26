# Textarea live-value cloning

Base: `21a8f7532d4afdadc04603cdf6a8ae893ea15d9f`, 26 November 2026.

The pinned [WPT cloning test](https://github.com/web-platform-tests/wpt/blob/94e2796a2aa59a232e4e43e8a218ae967e9fac77/html/semantics/forms/the-textarea-element/cloning-steps.html)
sets `.value = "foo bar"` and calls `cloneNode()` in both cases. Both clones are shallow
and dirty. The second sets the copy's `value` content attribute; that attribute does not
control a textarea's value, so it is not a sufficient independent test of dirtiness.

The supplied baseline is [WPT run 45738300795](https://github.com/danbri/factoidal-builds/actions/runs/45738300795),
engine `8a782f5af6c1`, WPT `94e2796a2aa59a232e4e43e8a218ae967e9fac77`: 0 pass, 2 fail
(out of 2) for this file, both returning empty. The main prelude blob remains
`0ae96c93da3060594e867ac157b6829226ecb656`. This change has no candidate WPT result yet.

The [HTML Standard textarea steps](https://html.spec.whatwg.org/multipage/form-elements.html#the-textarea-element)
copy raw value and dirty value flag, regardless of subtree copying. Children changed steps
update raw value only while clean; reset clears dirtiness and takes child text. The API
getter normalizes newlines. The setter sets raw value and dirtiness even when API value is
unchanged; selection moves only if API value changes.

## Representation and mutation paths

`DOM.Node.dirtyValue` stores the dirty raw value for a textarea as well as the existing input
state. `none` means clean. `textareaValue` is an optional clean raw-value snapshot, set by
`cloneSingle`: a shallow pristine clone must preserve raw value despite having no children.
Without that snapshot, a clean textarea reads its direct Text children. This keeps parser
construction unchanged and prevents a dirty value from modifying text nodes/default value.

`textareaChildrenChanged` discards the clean snapshot. Child insertion and removal clear it
in the existing parent-node update; text replacement, CharacterData replacement and
normalization invoke the same steps. Both ordinary and live-range mutations participate.
Form reset clears both the dirty value and snapshot. Deep clones preserve dirty raw values;
their pristine raw values follow the children inserted during cloning. Attributes do not
invalidate this state. Text includes CDATA and excludes nested element descendants.

The existing host query 169 accepts textarea reads (`v`) and raw writes (`s` plus value).
It runs before the unchanged input value-mode dispatch. The existing `setValue` command
accepts either control. The shared prelude getter/setter forwards this state and retains
WebIDL conversion, newline normalization and selection handling. Output and input property
implementations are unchanged.

## Assurance boundary

`Dom.textareaRawValue_dirty` states only that a dirty textarea reads its stored raw value.
It does not prove clone or mutation preservation. Ten new DOM guard expressions exercise
dirty/pristine shallow/deep clones, independent defaults, empty dirty values, default-text
replacement, CharacterData edits, insertion/removal, form reset and raw newline preservation.
They await compilation in CI; the theorem's printed axiom report also awaits CI.

`node --test tests/dom/textarea-prelude.test.mjs`: 6 pass, 0 fail, 0 skipped (out of 6).
These execute the actual prelude textarea property body with a native-query recorder;
they test ABI forwarding, conversions, API normalization and selection, not native DOM
execution. `node --check tools/wasmvm/quickjs/prelude.js` and `bash -n tests/dom/run.sh` pass.
The source suite is wired into the existing DOM CI runner.

No local Lean/native/Wasm build, WPT run or performance comparison was run: disk was below
the repository's build limit. Exact candidate package and selected testharness WPT CI are
required. The PR stays draft until those results exist. A focused run is a development
check, not a full WPT score. Request the textarea directory, input cloning controls and a
regression selection at the same pinned WPT revision. Visual editing/rendering and the
full A/B rendering gate remain unmeasured.
