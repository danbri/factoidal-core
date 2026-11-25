import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! The console tab, `foafnaut:console` (owner, 2026-11-08: "the browser console as another
tab", with "page problems logged by System").

The hosts keep, for each page they show, the entries of its console: the lines that its
scripts wrote (`console.log` and the other console methods, which the QuickJS-NG prelude
sends as one kind of line), the errors of its scripts, and the entries of the source
"System": what liberal mode skipped (`WebAccept.Diagnostic.json`), refusals, and fetches
that failed. They give the entries to the op `consolePage`, and this module writes the page
as HTML, which this engine then lays out and draws like any other page.

Request: `tab` (1-based, the tab whose page the entries are of), `title`, `url`, `entries`
(objects with `source`, `severity`, `message`, and optional `feature`, `where`, `action`),
and `tabs` (`{title,url}` of each open tab), so the page can link to the console of the
others (`foafnaut:console/N`). At most `maxEntries` entries are shown, the last ones. -/
namespace WebConsole
open L4Factoidal

def maxEntries : Nat := 500

private def str (j : JSON.Json) (key : String) (fallback : String := "") : String :=
  match j.field? key with | some (.string s) => s | _ => fallback

def escape (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c == '"' then "&quot;" else if c.toNat < 32 && c != '\n' then " " else c.toString)

/-- The class of a severity: "error", "warning", "info", "debug" or "log". -/
def severityClass (severity : String) : String :=
  if severity == "error" then "error" else if severity == "warning" || severity == "warn" then "warning"
  else if severity == "info" then "info" else if severity == "debug" then "debug" else "log"

/-- The levels in the order the page counts them, with the word it shows for each. -/
def levels : List (String × String) :=
  [("error","errors"),("warning","warnings"),("info","info"),("log","logs"),("debug","debug")]

/-- A script line of another level than log starts with the level between two U+0001 marks
(the prelude's `console.warn`, `error`, `info`, `debug`): the level and the text. -/
def level (message : String) : Option (String × String) :=
  match message.toList with
  | '\u0001' :: rest =>
    let (name,after) := rest.span (· != '\u0001')
    match after with
    | '\u0001' :: text => some (String.ofList name,String.ofList text)
    | _ => none
  | _ => none

/-- The level class of an entry: the level of its script line, else its severity. -/
def entryClass (e : JSON.Json) : String :=
  severityClass (((level (str e "message")).map (·.1)).getD (str e "severity" "log"))

/-- One entry as a block of the page: a coloured bar and tag for its level, the source and
level as text ("page warn", "System warning"), the message in a fixed-width font, and the
feature, place and action of a System entry. -/
def entryHTML (e : JSON.Json) : String :=
  let source := str e "source" "page"
  let (named,message) := match level (str e "message") with
    | some (l,text) => (some l,text)
    | none => (none,str e "message")
  let severity := severityClass (named.getD (str e "severity" "log"))
  let shown := named.getD severity
  let detail := [("feature",str e "feature"),("where",str e "where"),("action",str e "action")].filter (!·.2.isEmpty)
  "<div class=\"entry " ++ severity ++ "\"><p><span class=\"tag t-" ++ severity ++ "\">" ++ escape source ++ " " ++ escape shown ++
    "</span></p><p class=\"msg\">" ++ escape message ++ "</p>" ++
    (if detail.isEmpty then "" else
      "<p class=\"dim\">" ++ "; ".intercalate (detail.map fun (k,v) => k ++ ": " ++ escape v) ++ "</p>") ++ "</div>"

private def count (es : List JSON.Json) (p : JSON.Json → Bool) : Nat := (es.filter p).length

/-- The style of the console page. Light colours (pages are drawn light); no fixed widths, so
the page reads in a window as narrow as a phone; long messages and addresses break anywhere. -/
def style : String :=
  "<style>body{margin:0;font-family:sans-serif;font-size:14px;line-height:20px;color:#1f2328;background:#eef1f5}" ++
  "p{margin:0;padding-top:2px}a{color:#1a4fa0}" ++
  ".top{padding:14px 16px 12px;background:#14213d;color:#ffffff}" ++
  ".top h1{margin:0;font-size:22px;line-height:30px;color:#ffffff}.top p{color:#d6deee}.top a{color:#9cc4ff}" ++
  ".url{font-family:monospace;font-size:13px;overflow-wrap:anywhere}" ++
  ".counts{padding:12px 16px 4px}.chip{display:inline-block;margin:0 6px 6px 0;padding:2px 12px;border-radius:12px;font-weight:bold;font-size:13px;line-height:22px}" ++
  ".c-error{background:#fde2e1;color:#a4161a}.c-warning{background:#fff1c2;color:#7a5200}.c-info{background:#dceaff;color:#14467a}" ++
  ".c-log{background:#e3e6eb;color:#3a424d}.c-debug{background:#ece3fb;color:#4b2a86}.c-system{background:#14213d;color:#ffffff}.c-none{background:#ffffff;color:#8a929c}" ++
  ".list{padding:4px 16px 8px}" ++
  ".entry{margin:6px 0 0;padding:6px 10px 8px;background:#ffffff;border:1px solid #d5dae2;border-left:6px solid #9aa3ae}" ++
  ".entry.error{background:#fff6f6;border-left:6px solid #c62828}.entry.warning{background:#fffaeb;border-left:6px solid #d39e00}" ++
  ".entry.info{border-left:6px solid #2f6fd0}.entry.debug{border-left:6px solid #7b4fc9}" ++
  ".tag{display:inline-block;padding:0 8px;border-radius:4px;font-size:12px;line-height:18px;font-weight:bold}" ++
  ".t-error{background:#c62828;color:#ffffff}.t-warning{background:#d39e00;color:#1f1600}.t-info{background:#2f6fd0;color:#ffffff}" ++
  ".t-log{background:#5d6773;color:#ffffff}.t-debug{background:#7b4fc9;color:#ffffff}" ++
  ".msg{padding-top:4px;font-family:monospace;font-size:13px;line-height:19px;white-space:pre-wrap;overflow-wrap:anywhere}" ++
  ".dim{color:#5a6270;font-size:13px}.empty{margin:6px 0 0;padding:12px;background:#ffffff;border:1px dashed #b8c0cc;color:#5a6270}" ++
  ".foot{padding:8px 16px 16px}.tabs{padding:0 16px 4px}</style>"

/-- The console page: `(source, title)`. -/
def page (request : JSON.Json) : String × String := Id.run do
  let entries := match request.field? "entries" with | some (.array es) => es | _ => []
  let shown := entries.drop (entries.length - maxEntries)
  let tab := match request.field? "tab" with | some (.number n) => n | _ => "1"
  let tabs := match request.field? "tabs" with | some (.array ts) => ts | _ => []
  let system := count entries (str · "source" == "System")
  let errors := count entries fun e => entryClass e == "error"
  -- The title says the counts, so a tab strip (and a check) reads them.
  let title := s!"Console ({system} System, {entries.length-system} page)"
  let pageTitle := str request "title"
  let head := "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width\"><title>" ++
    title ++ "</title>" ++ style ++ "</head><body><main>"
  -- One chip for each level that has entries, then System; "no entries" when there are none.
  let chips := levels.filterMap fun (cls,word) =>
    let n := count entries fun e => entryClass e == cls
    if n == 0 then none else some s!"<span class=\"chip c-{cls}\">{n} {word}</span>"
  let chips := chips ++ (if system == 0 then [] else [s!"<span class=\"chip c-system\">{system} System</span>"])
  let counts := "<p class=\"counts\">" ++
    (if chips.isEmpty then "<span class=\"chip c-none\">no entries</span>" else " ".intercalate chips) ++ "</p>"
  let summary := s!"<p class=\"dim\">{entries.length} entries: {system} from System, {entries.length-system} from the page; {errors} errors." ++
    (if shown.length < entries.length then s!" The last {shown.length} are shown." else "") ++ "</p>"
  let others := tabs.zipIdx.filterMap fun (t,i) =>
    if toString (i+1) == tab then none
    else some ("<a href=\"foafnaut:console/" ++ toString (i+1) ++ "\">" ++ toString (i+1) ++ ": " ++
      escape (let t' := str t "title"; if t'.isEmpty then str t "url" else t') ++ "</a>")
  let body := "<div class=\"top\"><h1>Console</h1><p>Tab " ++ escape tab ++ ": " ++
    escape (if pageTitle.isEmpty then "(no title)" else pageTitle) ++
    "</p><p class=\"url\">" ++ escape (str request "url") ++ "</p></div>" ++ counts ++
    "<div class=\"list\">" ++ summary ++
    (if shown.isEmpty then "<p class=\"empty\">Nothing was logged for this page.</p>" else String.join (shown.map entryHTML)) ++ "</div>" ++
    (if others.isEmpty then "" else "<p class=\"tabs\">The console of another tab: " ++ " · ".intercalate others ++ "</p>") ++
    "<p class=\"dim foot\">System entries say what this browser skipped or refused on the page, and fetches that failed. " ++
    "Page entries are what the page's scripts wrote. Reload this tab to see new entries.</p></main></body></html>"
  return (head ++ body, title)

/-- The op `consolePage`: `{source,title}`. -/
def answer (request : JSON.Json) : String :=
  let (source,title) := page request
  (JSON.Json.object [("source",.string source),("title",.string title)]).toString

#guard (page (.object [])).1.startsWith "<!doctype html>"
#guard ((page (.object [("entries",.array [.object [("source",.string "System"),("severity",.string "warning"),
  ("message",.string "unsupported JavaScript module script"),("feature",.string "module script")]])])).1.splitOn
  "System warning").length == 2
#guard level "\u0001warn\u0001careful" == some ("warn","careful") && level "plain" == none
#guard ((page (.object [("entries",.array [.object [("source",.string "page"),("severity",.string "log"),
  ("message",.string "\u0001warn\u0001careful")]])])).1.splitOn "entry warning").length == 2
#guard escape "<a href=\"x\">&" == "&lt;a href=&quot;x&quot;&gt;&amp;"
-- Counts per level: one chip for each level with entries, coloured by its class.
#guard let src := (page (.object [("entries",.array [.object [("source",.string "page"),("message",.string "\u0001error\u0001bad")],
  .object [("source",.string "page"),("message",.string "\u0001error\u0001worse")],
  .object [("source",.string "page"),("message",.string "\u0001info\u0001note")],
  .object [("source",.string "System"),("severity",.string "warning"),("message",.string "skipped")]])])).1
  (src.splitOn "chip c-error\">2 errors").length == 2 && (src.splitOn "chip c-info\">1 info").length == 2 &&
  (src.splitOn "chip c-warning\">1 warnings").length == 2 && (src.splitOn "chip c-system\">1 System").length == 2 &&
  (src.splitOn "c-log").length == 2 && (src.splitOn "entry info").length == 2
#guard ((page (.object [])).1.splitOn "no entries").length == 2
#guard severityClass "info" == "info" && severityClass "debug" == "debug" && severityClass "trace" == "log"

end WebConsole
