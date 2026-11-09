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

/-- The class of a severity: "error", "warning" or "log". -/
def severityClass (severity : String) : String :=
  if severity == "error" then "error" else if severity == "warning" || severity == "warn" then "warning" else "log"

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

/-- One entry as a block of the page. -/
def entryHTML (e : JSON.Json) : String :=
  let source := str e "source" "page"
  let (named,message) := match level (str e "message") with
    | some (l,text) => (some l,text)
    | none => (none,str e "message")
  let severity := severityClass (named.getD (str e "severity" "log"))
  let shown := named.getD severity
  let detail := [("feature",str e "feature"),("where",str e "where"),("action",str e "action")].filter (!·.2.isEmpty)
  "<div class=\"entry " ++ severity ++ "\"><p><span class=\"tag\">" ++ escape source ++ " " ++ escape shown ++ "</span> " ++
    escape message ++ "</p>" ++
    (if detail.isEmpty then "" else
      "<p class=\"dim\">" ++ "; ".intercalate (detail.map fun (k,v) => k ++ ": " ++ escape v) ++ "</p>") ++ "</div>"

private def count (es : List JSON.Json) (p : JSON.Json → Bool) : Nat := (es.filter p).length

/-- The console page: `(source, title)`. -/
def page (request : JSON.Json) : String × String := Id.run do
  let entries := match request.field? "entries" with | some (.array es) => es | _ => []
  let shown := entries.drop (entries.length - maxEntries)
  let tab := match request.field? "tab" with | some (.number n) => n | _ => "1"
  let tabs := match request.field? "tabs" with | some (.array ts) => ts | _ => []
  let system := count entries (str · "source" == "System")
  let errors := count entries fun e =>
    severityClass (((level (str e "message")).map (·.1)).getD (str e "severity")) == "error"
  -- The title says the counts, so a tab strip (and a check) reads them.
  let title := s!"Console ({system} System, {entries.length-system} page)"
  let pageTitle := str request "title"
  let head := "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>" ++ title ++ "</title><style>" ++
    "body{margin:16px;font-size:14px;line-height:20px;color:#202830;background:#f6f6f2}" ++
    "h1{margin:0 0 6px;font-size:20px;line-height:28px;color:#184078}p{margin:0;padding-top:2px}" ++
    ".dim{color:#5a6270}.entry{margin:6px 0 0;padding:4px 8px;border:1px solid #c8ccd4;background:#ffffff}" ++
    ".error{border:2px solid #b02020;background:#fff0f0}.warning{border:2px solid #b08a1e;background:#fff8dc}" ++
    ".tag{font-weight:bold;color:#184078}.tabs{padding-top:8px}a{color:#1a4fa0}</style></head><body><main>"
  let summary := s!"<p class=\"dim\">{entries.length} entries: {system} from System, {entries.length-system} from the page; {errors} errors." ++
    (if shown.length < entries.length then s!" The last {shown.length} are shown." else "") ++ "</p>"
  let others := tabs.zipIdx.filterMap fun (t,i) =>
    if toString (i+1) == tab then none
    else some ("<a href=\"foafnaut:console/" ++ toString (i+1) ++ "\">" ++ toString (i+1) ++ ": " ++
      escape (let t' := str t "title"; if t'.isEmpty then str t "url" else t') ++ "</a>")
  let body := "<h1>Console</h1><p>Tab " ++ escape tab ++ ": " ++ escape (if pageTitle.isEmpty then "(no title)" else pageTitle) ++
    "</p><p class=\"dim\">" ++ escape (str request "url") ++ "</p>" ++ summary ++
    (if shown.isEmpty then "<p>Nothing was logged for this page.</p>" else String.join (shown.map entryHTML)) ++
    (if others.isEmpty then "" else "<p class=\"tabs\">The console of another tab: " ++ " ".intercalate others ++ "</p>") ++
    "<p class=\"dim\">System entries say what this browser skipped or refused on the page, and fetches that failed. " ++
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

end WebConsole
