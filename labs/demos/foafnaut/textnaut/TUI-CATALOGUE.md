# Terminal UI techniques and widgets: what users may expect

For https://github.com/danbri/factoidal-core/issues/371 (textnaut). Compiled 2026-11-09 from
three projects the owner named:

- Textual widget gallery: https://github.com/Textualize/textual (`docs/widget_gallery.md`).
- Rich: https://github.com/Textualize/rich (renderables, from its documentation as remembered;
  not re-read line by line).
- pyTermTk widget list: https://ceccopierangiolieugenio.github.io/pyTermTk-Docs/info/features/widgets.html

The textnaut column is the state on 2026-11-09 and goes stale: check `README.md` and the code.
"Web source" is what would drive the widget in a browser. Page content decides what is drawn;
textnaut only chooses how a standard thing looks in cells.

## Widgets

| Widget | Textual | Rich | pyTermTk | Web source | textnaut |
|---|---|---|---|---|---|
| Label, static text | Label, Static | Text | TTkLabel | text | yes |
| Link | Link | links (OSC 8) | | `<a>` | yes, numbered; OSC 8 when detected |
| Heading | Markdown | Markdown H1 panel | | `<h1>`..`<h6>` | colour only; bands in progress |
| Rule | Rule | Rule | | `<hr>` | in progress |
| Panel, frame, box | (CSS borders) | Panel | TTkFrame, TTkResizableFrame | borders, `<fieldset>`, `<section>` | no |
| Code block | TextArea, Markdown | Syntax | TTkTextEdit | `<pre>`, `<code>` | in progress |
| Blockquote | Markdown | Markdown | | `<blockquote>` | in progress |
| List | ListView, OptionList | Markdown | TTkList | `<ul>`, `<ol>` | bullets as text |
| Table | DataTable | Table | TTkTable | `<table>` | text placed by layout; borders in progress |
| Tree | Tree, DirectoryTree | Tree | TTkTree, TTkFileTree | `<details>`, nested lists | no |
| Collapsible | Collapsible | | | `<details>` | no |
| Tabs | Tabs, TabbedContent, ContentSwitcher | | TTkTabWidget, TTkKodeTab | browser tabs; ARIA tablist | no |
| Button | Button | | TTkButton | `<button>`, submit | no |
| Checkbox | Checkbox | | TTkCheckbox | `<input type=checkbox>` | no |
| Switch | Switch | | | `role=switch` | no |
| Radio | RadioButton, RadioSet | | TTkRadioButton | `<input type=radio>` | no |
| Select, combo box | Select, SelectionList | | TTkComboBox | `<select>` | no |
| Text input | Input, MaskedInput | Prompt | TTkLineEdit | `<input>` | no |
| Multi-line editor | TextArea | | TTkTextEdit | `<textarea>` | no |
| Number spinner | | | TTkSpinBox | `<input type=number>` | no |
| Date and time | | | TTkDate, TTkTime, TTkDateTime | `<input type=date>` and others | no |
| Colour picker | | | TTkColorButtonPicker | `<input type=color>` | no |
| File picker | DirectoryTree | | TTkFileButtonPicker | `<input type=file>` | no |
| Menu | (command palette) | | TTkMenu | browser menu; `<menu>` | no |
| Message box, dialog | (screens) | | TTkMessageBox | `<dialog>`, `alert`, `confirm` | no |
| Window, splitter | (layers, docks) | Layout | TTkWindow, TTkSplitter | browser panes | no |
| Scroll bar, scroll area | (built in) | | TTkScrollBar, TTkScrollArea | overflow | page scroll; status percentage |
| Header and footer | Header, Footer | | TTkAppTemplate | browser chrome | yes, gradient bars |
| Progress bar | ProgressBar | Progress | TTkFancyProgressBar | `<progress>` | no |
| Spinner, status | LoadingIndicator | Status, Spinner | | page load | no |
| Meter, sparkline, big digits | Sparkline, Digits | | TTkGraph | `<meter>`, charts | no |
| Log, console | Log, RichLog | Console, Traceback | TTkLogViewer | console tab | no |
| Image | | | TTkImage | `<img>`, SVG, canvas | no |
| Embedded terminal | | | TTkTerminal | none | out of scope |

## Techniques

| Technique | What it gives | textnaut |
|---|---|---|
| Alternate screen, restore on exit and on signals | terminal left clean | yes |
| 24-bit, 256, 16 colour with detection (`COLORTERM`, `TERM`, `NO_COLOR`) | colour on every terminal | yes |
| Damage-only redraw, minimum bytes | speed, SSH | changed lines only |
| Synchronized output (mode 2026) | no tearing | when detected |
| Resize with SIGWINCH, bursts combined | quick reflow | yes |
| Grapheme clusters and cell width | correct alignment | small table, approximate |
| Half blocks, quadrants, Braille, box drawing | higher-resolution shapes, charts | screensavers only |
| OSC 8 hyperlinks | clickable links | when detected |
| SGR 1006 mouse, hover, wheel | pointer use | no |
| Keyboard focus ring, Tab order, key hints | keyboard use | Tab between links |
| Command palette, search in page | fast navigation | no |
| Kitty keyboard protocol | every key distinct | no |
| Bracketed paste, OSC 52 clipboard | safe paste, copy over SSH | no |
| Text selection and copy | reading | terminal's own |
| Kitty graphics, iTerm2 images, Sixel | real images | no |
| Double-size text (DEC, Kitty OSC 66) | large headings | in progress |
| Undercurl, coloured underlines, dim, italic | richer text | no |
| Themes, light and dark detection (OSC 11) | fits the terminal | no |
| Animation with a frame budget | motion | screensavers |
| Layout: docks, grid, split panes | app structure | no |
| Terminal title (OSC 2), focus events | integration | no |
| Output to pipes and dumb terminals | scripting | `--dump` |
| Control characters stripped from content | safety | yes, tested |

## Order suggested for a browser

Form controls first (button, input, checkbox, radio, select, textarea), because pages cannot be
used without them. Then mouse, search in page and focus order, then images, then the rest.
