/-! The engine's own build facts: release number, commit and build time.

`build-web-render.sh` writes `.build/web-render/engine-build.txt` from git and
`npm/factoidal/package.json` before the engine's modules compile, and `include_str` puts
its text into this module when it compiles. So the facts are in the engine's code: no host
file is read for them when the engine runs, and an engine says which build it is whatever
program loads it. One `key=value` line each: `version`, `commit` (full), `builtAt` (UTC),
`dirty` (`true` when the working tree had uncommitted changes) and `release` (`true` for a
clean commit tagged `v<version>`). After the hygiene ratchet (`LabHygiene.lean`, theorem
`lab_ratchet`) has run in the same build, `hygieneLab` and `hygieneFormal` hold its counts,
and this module and those after it are compiled again. -/
namespace WebBuild

/-- The record as the build wrote it. -/
def record : String := include_str ".build/web-render/engine-build.txt"

/-- The value of `key` in a record of `key=value` lines, or "" when there is none. -/
def field (text key : String) : String :=
  ((text.splitOn "\n").findSome? fun line => match line.splitOn "=" with
    | k :: rest => if k == key then some ("=".intercalate rest) else none
    | [] => none).getD ""

#guard field "version=0.36.0\ncommit=abc\nurl=a=b" "url" == "a=b"
#guard field "version=0.36.0" "commit" == ""

def version : String := field record "version"
def commit : String := field record "commit"
def builtAt : String := field record "builtAt"
def dirty : Bool := field record "dirty" == "true"
def release : Bool := field record "release" == "true"
def hygieneLab : String := field record "hygieneLab"
def hygieneFormal : String := field record "hygieneFormal"

end WebBuild
