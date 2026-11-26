# Foafnaut: held keys, page focus on commit, Canvas 2D font family

Date: 2026-11-25. Issues:
https://github.com/danbri/factoidal-core/issues/1074 (a held key reached the page as a tap),
https://github.com/danbri/factoidal-core/issues/1077 (the address bar kept the focus after a load),
https://github.com/danbri/factoidal-core/issues/1075 (Canvas 2D text ignored the font family).
All three were found with Particle Rex (`labs/demos/foafnaut/pages/particle-rex.html`).

## 1. Key events of the window (issue 1074)

Window event ABI (`native_window.m`, `native_window_linux.c`, read by `native_window.ts`):

| kind | a | b | flags |
|---|---|---|---|
| 5 (macOS), 16 (Linux) key down | key code (macOS virtual key; SDL key code) | modifiers | bit 0 auto-repeat, bit 1 "this window reports key releases" |
| 17 (macOS), 18 (Linux) key up | key code | modifiers | bit 1 |
| 9 text | Unicode scalar | the key code of the key down that typed it, when flags bit 1 | bit 0 repeat, bit 1 |

`native_window.ts` gives Linux kinds 16 and 18 to the host as 5 and 17, with the macOS code in
`a` and the SDL code in `keyId`. An older window library sets no flags: the host then sends
whole presses, as before.

Host (`run_html.ts`): when the window reports releases, the engine says `keyPhases` in its
script `info`, and no Command or Control key is held, a key down goes to the page as the `key`
action with `phase:"down"` and a key up with `phase:"up"`. A key with text has no actions for
its code alone (`HostKeys.ofMac` gives `none`); its text then goes down as its key and is held
until the key's up (`pageKeysHeld`, by the window's key code). Space goes down as its named key
and its text is dropped. When the window loses the focus (kind 14), every key the page holds
goes up. A chord with Command or Control stays a whole press, because AppKit sends no key up for
a key released while Command is held.

Decisions in Lean (`L4Factoidal/WebDriver/HostKeys.lean`, `actionsAt`): `downFrom` and
`upFrom` read the key names the session holds (`Actions.State.keys`). A down changes the
modifiers to the host's bits, then presses the key; a key already held goes down again, which
`Actions.step` marks `again`, so the page sees `KeyboardEvent.repeat`. An up releases the key,
and the modifiers when no other key is held. Theorems `down_ends_with_key` and
`up_starts_with_key`; `#guard`s check that a down then an up from nothing held equals a whole
press for five keys and modifier sets.

Measurement: `native-html-gesture` with `gesture:"key"` and `queuedToActionMs` (window queue
to the page's answer), and `gestures` in `--perf-summary`.

## 2. Focus when a page commits (issue 1077)

`WebShell.focusOnCommit url newTab addressFocused typedSince` (engine op `shellCommitFocus`):
the page takes the focus, as in Chrome, Firefox and Safari. The address bar keeps it only when
the person typed in it after the navigation started, and takes it for a new tab page or
`about:blank`. The window asks at its start (the page it opens has committed) and at each new
page. Decision of this session: a window that opens a page starts with the page focused; before,
every new window started in the address bar (issue 1268's start state). `--edit-sweep` now
starts with `"unfocused"` and focuses the bar with Command-L (Control-L on Linux). An older
engine has no `shellCommitFocus`: the host then keeps the old behaviour.

## 3. Canvas 2D font family (issue 1075)

`PageCanvas.Text.familyFaces` gives the faces a `font` family list draws with before the held
fonts, as the page's text picks them (`familyFontsWith` in `WebDocument.lean`): for each family
in order, the page's `@font-face` faces of that name; a name that asks for the monospace face
(`monospace`, Courier New, ... or the monospace face's own family) or the serif face ends the
list with that face; a name that asks for the held fonts (`sans-serif`, a held family) ends it
with nothing. The engine finds the page's faces at the start of its script session
(`canvasFaceFonts`) and keeps them as `canvasFaces`: one engine worker holds one tab.
Fonts are the pinned OFL set; the font policy (`FontPolicy`) checked each one when it was loaded.

## 4. Keys go to the page before their scroll command (issue 1139)

https://github.com/danbri/factoidal-core/issues/1139 (Particle Rex went blank on Space on the Hub).
The Hub host looked up Lean's key table (`WebHistory.keyTable`) first and ran the command
(Space pages down), so the page never had the key. Now a key with no Command or Control goes to
the page first as the `key` action (`pageKey` in `browser-worker.mjs`), with `phase` when the
engine has `keyPhases`; the table's command runs as the default action only when the turn's
`keyDefault` (Lean, `PageEvents.key`: the keydown was not cancelled and did not edit) is not
false. A page with no script session takes the command at once. The key's release goes to the
page too. The window host (`run_html.ts`) already worked this way: `scriptKey` runs the command
after `keyDefault`. Check: `node labs/demos/foafnaut/hub_keys_check.mjs [--runtime DIR]`
(headless Chromium, the Hub's CPU drawing path).
