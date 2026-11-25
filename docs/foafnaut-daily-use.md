# Foafnaut: everyday use

What a person does in the first ten minutes with a new browser, each item tried in the Mac app
(`foafnaut`) and kept by a host test. The test for most items is
`labs/demos/foafnaut/daily_use_check.ts` (in `test.sh`): `run_html.ts --offscreen --steps FILE`
drives the window's real event queue against a local site (`daily_use_server.ts`, original pages
only). The other items are kept by the sweeps of `sweeps.sh` named below.

Measured on 2026-11-17 against the installed release `c91b7d21d0a9` (head of `main` then), with
`run_html.ts` from `main` at `528b04055` (no host change since that release). "After" is the
branch `wip/daily-basics`: the host changes were run against that same engine; the engine changes
need a build of the branch (marked "needs the branch's engine" until one is measured).

## Checklist

| Item | How it is tested | Before | After |
| --- | --- | --- | --- |
| Follow a link, go back, go forward | `--back-sweep`, `--history-sweep`, daily "link, back, reload" | pass | pass |
| Reload (Command-R, R) | `--shortcut-sweep`, daily "link, back, reload" | pass | pass |
| Tabs: open, close, reopen, switch (Command-T, W, Shift-T, 1-9) | `--shortcut-sweep` | pass | pass |
| Scroll: trackpad, wheel, Space, Page Up/Down, Home, End, arrows | `--scroll-sweep`, `--scroll-end-sweep`, `--shortcut-sweep` | pass | pass |
| Swipe back and forward | `--swipe-sweep` | pass | pass |
| Find in page (Command-F, G, Shift-G, Escape) | `--find-sweep` | pass | pass |
| Zoom (Command-=, -, 0) | `--command-sweep` | pass | pass |
| Copy page text (drag, Command-A, Command-C) | `--command-sweep` | pass | pass |
| Address bar as a text field: type, select, cut, copy, paste, undo | `--edit-sweep`, `--paste-sweep` | pass | pass |
| Type words that are not an address: the built-in search page | by hand (`foafnaut:search/...`) | pass (local only: nothing leaves the browser) | same |
| A redirect is followed | daily "a redirect is followed" | pass | pass |
| A server's "not found" (404) or other error page is shown | daily "a server's 404 page is shown" | **fail**: "Page refused" | pass |
| Start on an address that does not answer | daily "a start address that does not answer..." | **fail**: the program stopped (`TypeError: fetch failed`) | pass: an error page |
| An address that does not answer, typed later | by hand (Command-L) | pass: an error page | pass |
| Press a text field, it takes the focus | daily search cases | **fail**: no focus (the press reached the page's events, but focus was only on the WebDriver path) | needs the branch's engine |
| Type into a text field on a page with no script | daily "type in a search box with no script..." | **fail**: a page with no script had no script session, so keys went nowhere | host part done (a session starts on the first press); needs the branch's engine |
| See what you typed in the field | screenshot | **fail**: input values are not painted | `look:` (control painting, wip/look-sites) |
| Press Enter in a search box: the form is submitted (GET) | daily "type in a search box ... press Enter" | **fail**: no implicit submission, and no form navigated the page itself | needs the branch's engine |
| Press a form's button | daily "... press its button" | **fail**: the page's own navigation was not done | needs the branch's engine |
| Submit a POST form | daily "post a form" | **fail**: POST was not planned | needs the branch's engine |
| Sign in to a simple site; cookies kept across a restart | daily "sign in: the cookie is kept", "after a restart, still signed in" | **fail**: page loads carry no cookies | branch `wip/daily-cookies`: the engine's jar for page loads (`Net.Cookies.navCookie`, `navSet`), redirects hop by hop, lasting cookies in `cookies.txt` (mode 0600) of the data folder; needs that branch's engine |
| A `target=_blank` link opens a new tab | daily "a target=_blank link..." (XFAIL) | **fail**: opens in the same tab | open (gap 3) |
| Download a file | daily "a download is saved, the page stays" | **fail**: the file is shown as a page | saved to ~/Downloads under a safe name (`safeName_safe`); said in the console only (needs the branch's engine) |
| A page script sets the title: the tab shows it | by hand | **fail**: the tab keeps the parsed title | open |
| IME (composition, dead keys) in page fields | not tested | unknown | open |

## Blockers, worst first

1. **Forms.** Without a press that focuses a field, keys that reach a page with no script, and a
   submission that navigates, no search box and no sign-in form works. Fixed on the branch:
   `PageEvents.pointer` gives the press its default action (focus), as `lowPointer` did;
   `FormControls.implicitSubmission` (Enter) with theorem `implicitSubmission_sound`;
   `FormSubmission.plan` plans POST (urlencoded, http(s) only: `plan_post_http`, `plan_method`);
   DomOps op 170 tells the embedder of a navigation of the page itself (`navigate` in a turn);
   the window starts a script session on the first press of a page with none, and makes GET and
   POST navigations. Painting the typed value is `look:`'s.
2. **Cookies for page loads.** On `wip/daily-cookies`: a browser-wide jar for navigations with
   the rules and theorems of `Net.Cookies` (a cookie is its host's; `Secure` only over https;
   `sentNav_safe`: no `Strict` cookie on a cross-site navigation, only `SameSite=None` on a
   cross-site POST), redirects of documents hop by hop so a sign-in's `Set-Cookie` on the
   redirect is kept, and on disk only cookies with an expiry (`persistent_no_session`: a
   session cookie is never written); the file is read back through `Jar.ofWire`
   (`ofWire_wellformed`). Open: the page's scripts still have their own jar per page
   (`document.cookie` does not see the browser's cookies yet), subresources and `fetch` carry no
   browser cookies, and there is no "clear cookies" command yet.
3. **New-tab links.** `target=_blank` and Command-click should open a tab (with no `opener`).
4. **Downloads.** Done on the branch: the engine decides from the type and
   `Content-Disposition` (`Net.Subresource.navigated`), the name is made safe (`safeName_safe`:
   not empty, no separator or control character, no leading dot), the host writes the body to
   `~/Downloads` (`--downloads DIR`) under a free name and the page stays. Open: the person is
   told only in the console (no download bar yet). The app is now compiled with `--allow-write`
   (the host writes downloads and Save Page As; page content can not write files).
5. **Script-set titles** in the tab and window title.

## Timings (installed engine, off screen, M-series Mac)

- A press on a page with no script now starts a session there: 68 to 88 ms of engine time once
  per page (two runs), then 0.2 to 0.7 ms a key. A press on a link starts none, and a page nobody
  presses pays nothing.
- The 404 page and the start error page cost what any page costs; nothing is added to a page
  that loads.
