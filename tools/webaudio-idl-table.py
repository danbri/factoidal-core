#!/usr/bin/env python3
"""Write formal/lean4/L4Factoidal/WebAudio/Idl.lean from the Web Audio API IDL.

    curl -sS https://raw.githubusercontent.com/web-platform-tests/wpt/master/interfaces/webaudio.idl \
        -o /tmp/webaudio.idl
    python3 tools/webaudio-idl-table.py /tmp/webaudio.idl \
        > formal/lean4/L4Factoidal/WebAudio/Idl.lean
    python3 tools/webaudio-idl-table.py --check /tmp/webaudio.idl     # exit 1 when the file differs

The input is WPT's `interfaces/webaudio.idl` (extracted from the Web Audio API 1.1 by Reffy). The
header of the output records the fetch date and the SHA-256 of the input; the WPT commit could not
be read in the session that first wrote the file (`RECORDED_FETCHED`). Pass the same input file to
reproduce the output byte for byte. Run it from the repository root.

Kept: for each interface its name, parent, extended attributes, constructor (fewest arguments and
argument types of each overload), attributes (name, IDL type, read-only), operations (name, fewest
arguments, argument types of each overload) and static operations; for each enum its values; for
each dictionary its parent and members (name, type, required, default); for each callback its
return type and argument types. Argument types are letters as in `tools/webgl-idl-table.py`, see
`SCALARS`; an attribute or member type is the IDL text. Not kept: extended attributes on members
(`SameObject`, `SecureContext`, `Default`), operation return types, argument names, `maplike`
members (listed as text in `other`), and argument conversion rules.
"""
import hashlib
import re
import sys

RECORDED_FETCHED = "2026-11-26"
OUT_PATH = "formal/lean4/L4Factoidal/WebAudio/Idl.lean"

# One letter per IDL type the page glue converts (Web IDL section 3.2); `?` after it: nullable.
SCALARS = {
    "unsigned long": "u", "long": "i", "unsigned long long": "l", "float": "f", "double": "d",
    "boolean": "b", "DOMString": "s", "object": "a", "undefined": "v", "DOMHighResTimeStamp": "d",
    "EventHandler": "h",
}


def strip_comments(text):
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//[^\n]*", "", text)


def split_top(s, sep):
    """Split at `sep` outside any bracket pair."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "<([{":
            depth += 1
        elif ch in ">)]}":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [a.strip() for a in out]


def norm(s):
    return " ".join(s.split())


def drop_extattrs(s):
    s = norm(s)
    while s.startswith("["):
        s = s[s.index("]") + 1:].strip()
    return s


def type_code(ty):
    ty = norm(ty)
    if ty.startswith("(") and (ty.endswith(")") or ty.endswith(")?")):
        nullable = ty.endswith(")?")
        inner = ty[1:-2] if nullable else ty[1:-1]
        return "(" + "/".join(type_code(p) for p in re.split(r"\s+or\s+", inner)) + ")" + ("?" if nullable else "")
    nullable = ty.endswith("?")
    if nullable:
        ty = ty[:-1]
    m = re.fullmatch(r"(sequence|FrozenArray)<(.*)>", ty)
    if m:
        code = ("Q" if m.group(1) == "sequence" else "Z") + type_code(m.group(2))
    elif ty in SCALARS:
        code = SCALARS[ty]
    elif re.fullmatch(r"\w+", ty):
        code = "O" + ty
    elif ty.startswith("record<"):
        code = "R"
    elif re.fullmatch(r"Promise<.*>", ty):
        code = "P" + type_code(ty[len("Promise<"):-1])
    else:
        raise SystemExit(f"type not read: {ty!r}")
    return code + ("?" if nullable else "")


def arg_code(arg):
    a = drop_extattrs(arg)
    opt = a.startswith("optional ")
    if opt:
        a = a[len("optional "):]
    a = split_top(a, "=")[0].strip()
    ty = a.rsplit(" ", 1)[0].strip()
    return ("~" if opt else "") + type_code(ty)


def required(args):
    n = 0
    for a in args:
        a = drop_extattrs(a)
        if a.startswith("optional ") or "..." in a:
            break
        n += 1
    return n


def add_op(ops, name, args_text):
    args = split_top(args_text, ",")
    n = required(args)
    sig = ",".join(arg_code(a) for a in args)
    if name in ops:
        ops[name] = (min(ops[name][0], n), ops[name][1] + [sig])
    else:
        ops[name] = (n, [sig])


def parse(text):
    text = strip_comments(text)
    stmts = split_top(text, ";")
    ifaces, enums, dicts, cbs = [], [], [], []
    for st in stmts:
        st = st.strip()
        ext = ""
        m = re.match(r"^\[(.*?)\]\s*(?=(interface|dictionary|enum|callback)\b)", st, flags=re.S)
        if m:
            ext, st = norm(m.group(1)), st[m.end():]
        m = re.match(r"^enum\s+(\w+)\s*\{(.*)\}$", st, flags=re.S)
        if m:
            enums.append((m.group(1), re.findall(r'"([^"]*)"', m.group(2))))
            continue
        m = re.match(r"^callback\s+(\w+)\s*=\s*(.*?)\s*\((.*)\)$", st, flags=re.S)
        if m:
            args = split_top(m.group(3), ",")
            cbs.append((m.group(1), type_code(m.group(2)), ",".join(arg_code(a) for a in args)))
            continue
        m = re.match(r"^dictionary\s+(\w+)\s*(?::\s*(\w+))?\s*\{(.*)\}$", st, flags=re.S)
        if m:
            members = []
            for mem in split_top(m.group(3), ";"):
                mem = drop_extattrs(mem)
                req = mem.startswith("required ")
                if req:
                    mem = mem[len("required "):]
                parts = split_top(mem, "=")
                default = norm(parts[1]) if len(parts) > 1 else ""
                decl = parts[0].strip()
                ty, name = decl.rsplit(" ", 1)
                members.append((name, norm(ty), req, default))
            dicts.append((m.group(1), m.group(2) or "", members))
            continue
        m = re.match(r"^interface\s+(\w+)\s*(?::\s*(\w+))?\s*\{(.*)\}$", st, flags=re.S)
        if m:
            attrs, ops, statics, other = [], {}, {}, []
            ctor = {}
            for mem in split_top(m.group(3), ";"):
                mem = drop_extattrs(mem)
                if not mem:
                    continue
                c = re.match(r"^constructor\s*\((.*)\)$", mem)
                if c:
                    add_op(ctor, "constructor", c.group(1))
                    continue
                if "maplike<" in mem:
                    other.append(mem)
                    continue
                a = re.match(r"^(readonly )?attribute (.+) (\w+)$", mem)
                if a:
                    attrs.append((a.group(3), norm(a.group(2)), bool(a.group(1))))
                    continue
                is_static = mem.startswith("static ")
                if is_static:
                    mem = mem[len("static "):]
                o = re.match(r"^(.*?)\s*(\w+)\s*\((.*)\)$", mem)
                if not o:
                    raise SystemExit(f"{m.group(1)}: member not read: {mem}")
                add_op(statics if is_static else ops, o.group(2), o.group(3))
            ifaces.append(dict(name=m.group(1), parent=m.group(2) or "", ext=ext, ctor=ctor.get("constructor"),
                               attrs=attrs, ops=ops, statics=statics, other=other))
            continue
        if st:
            raise SystemExit(f"statement not read: {st[:80]!r}")
    return ifaces, enums, dicts, cbs


def q(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_list(items, fmt, indent="  "):
    if not items:
        return "[]"
    return "[\n" + ",\n".join(indent + "  " + fmt(i) for i in items) + "]"


def op_list(ops):
    return lean_list(list(ops.items()), lambda o: f'⟨{q(o[0])}, {o[1][0]}, {q("|".join(o[1][1]))}⟩', "    ")


STRUCTS = """
/-- An attribute: name, IDL type text, read-only. -/
structure Attr where
  name : String
  type : String
  readOnly : Bool

/-- An operation or constructor: name, the fewest arguments an overload takes, and the argument types
of each overload. -/
structure Op where
  name : String
  minArgs : Nat
  sigs : String

/-- An interface. `ext` is the text of its extended attributes (`Exposed=Window`, ...); `ctor` is the
`constructor` operation, none when the IDL gives none; `other` holds members not kept as data
(`maplike`). -/
structure Iface where
  name : String
  parent : String
  ext : String
  ctor : Option Op
  attrs : List Attr
  ops : List Op
  statics : List Op
  other : List String

/-- An enum: name and values. -/
structure Enum where
  name : String
  values : List String

/-- A dictionary member: name, IDL type text, required, and default value text (empty: no default). -/
structure Member where
  name : String
  type : String
  required : Bool
  default : String

/-- A dictionary: name, parent (empty: none) and its own members. -/
structure Dict where
  name : String
  parent : String
  members : List Member

/-- A callback type: name, return type letter, argument type letters. -/
structure Callback where
  name : String
  ret : String
  args : String
"""

LOOKUPS = """
/-! ## Lookups -/

def findInterface (n : String) : Option Iface := interfaces.find? (·.name == n)

def findEnum (n : String) : Option Enum := enums.find? (·.name == n)

def findDict (n : String) : Option Dict := dicts.find? (·.name == n)

/-- The values of an enum. -/
def enumValues (n : String) : Option (List String) := (findEnum n).map (·.values)

/-- The parents of an interface, nearest first, up to eight steps (the IDL's deepest chain has three). -/
def ancestors (n : String) : List String :=
  go 8 n
where
  go : Nat → String → List String
    | 0, _ => []
    | k + 1, n =>
      match findInterface n with
      | none => []
      | some i => if i.parent == "" then [] else i.parent :: go k i.parent

/-- The fewest arguments of the operation `op` that the interface itself declares. -/
def opMinArgs (iface op : String) : Option Nat :=
  (findInterface iface).bind fun i => (i.ops.find? (·.name == op)).map (·.minArgs)

/-- Whether the attribute `a` that the interface itself declares is read-only. -/
def attrReadOnly (iface a : String) : Option Bool :=
  (findInterface iface).bind fun i => (i.attrs.find? (·.name == a)).map (·.readOnly)

/-- The default text of a member of the dictionary itself (empty: the member has no default). -/
def dictDefault (dict m : String) : Option String :=
  (findDict dict).bind fun d => (d.members.find? (·.name == m)).map (·.default)
"""

GUARDS = r'''
/-! ## Checks against the IDL text

Each fact below can be read off `webaudio.idl`. A `#guard` that fails stops the build, so a change
of the IDL that the generator reads is seen here first. -/

#guard interfaces.length == @NIFACE@
#guard enums.length == @NENUM@
#guard dicts.length == @NDICT@
#guard callbacks.length == @NCB@
#guard (enums.map (·.name)).eraseDups.length == enums.length
#guard (dicts.map (·.name)).eraseDups.length == dicts.length

-- Parents.
#guard (findInterface "OfflineAudioContext").map (·.parent) == some "BaseAudioContext"
#guard (findInterface "AudioContext").map (·.parent) == some "BaseAudioContext"
#guard (findInterface "AudioBufferSourceNode").map (·.parent) == some "AudioScheduledSourceNode"
#guard (findInterface "OscillatorNode").map (·.parent) == some "AudioScheduledSourceNode"
#guard (findInterface "AudioScheduledSourceNode").map (·.parent) == some "AudioNode"
#guard (findInterface "BaseAudioContext").map (·.parent) == some "EventTarget"
#guard (findInterface "AudioParam").map (·.parent) == some ""
#guard ancestors "OscillatorNode" == ["AudioScheduledSourceNode", "AudioNode", "EventTarget"]

-- AudioNode.
#guard (findInterface "AudioNode").map (·.attrs.map (·.name)) ==
  some ["context", "numberOfInputs", "numberOfOutputs", "channelCount", "channelCountMode",
    "channelInterpretation"]
#guard attrReadOnly "AudioNode" "context" == some true
#guard attrReadOnly "AudioNode" "channelCount" == some false
#guard opMinArgs "AudioNode" "connect" == some 1
#guard opMinArgs "AudioNode" "disconnect" == some 0

-- BaseAudioContext factory methods and their fewest arguments.
#guard opMinArgs "BaseAudioContext" "createGain" == some 0
#guard opMinArgs "BaseAudioContext" "createBuffer" == some 3
#guard opMinArgs "BaseAudioContext" "createIIRFilter" == some 2
#guard opMinArgs "BaseAudioContext" "createPeriodicWave" == some 2
#guard opMinArgs "BaseAudioContext" "createDelay" == some 0
#guard opMinArgs "BaseAudioContext" "createChannelMerger" == some 0
#guard opMinArgs "BaseAudioContext" "decodeAudioData" == some 1
#guard ((findInterface "BaseAudioContext").map (fun i => (i.ops.filter (·.name.startsWith "create")).length)) ==
  some 18
#guard attrReadOnly "BaseAudioContext" "onstatechange" == some false

-- AudioParam.
#guard (findInterface "AudioParam").map (·.ops.map (·.name)) ==
  some ["setValueAtTime", "linearRampToValueAtTime", "exponentialRampToValueAtTime", "setTargetAtTime",
    "setValueCurveAtTime", "cancelScheduledValues", "cancelAndHoldAtTime"]
#guard opMinArgs "AudioParam" "setTargetAtTime" == some 3
#guard opMinArgs "AudioParam" "setValueCurveAtTime" == some 3
#guard opMinArgs "AudioParam" "cancelScheduledValues" == some 1
#guard attrReadOnly "AudioParam" "value" == some false
#guard attrReadOnly "AudioParam" "defaultValue" == some true

-- Constructors.
#guard ((findInterface "OfflineAudioContext").bind (·.ctor)).map (·.minArgs) == some 1
#guard ((findInterface "AudioContext").bind (·.ctor)).map (·.minArgs) == some 0
#guard ((findInterface "OscillatorNode").bind (·.ctor)).map (·.minArgs) == some 1
#guard ((findInterface "AudioNode").bind (·.ctor)).isNone

-- Enums.
#guard enumValues "OscillatorType" == some ["sine", "square", "sawtooth", "triangle", "custom"]
#guard enumValues "BiquadFilterType" ==
  some ["lowpass", "highpass", "bandpass", "lowshelf", "highshelf", "peaking", "notch", "allpass"]
#guard enumValues "ChannelCountMode" == some ["max", "clamped-max", "explicit"]
#guard enumValues "ChannelInterpretation" == some ["speakers", "discrete"]
#guard enumValues "AutomationRate" == some ["a-rate", "k-rate"]
#guard enumValues "AudioContextState" == some ["suspended", "running", "closed", "interrupted"]
#guard enumValues "OverSampleType" == some ["none", "2x", "4x"]

-- Dictionary defaults.
#guard dictDefault "AudioBufferSourceOptions" "detune" == some "0"
#guard dictDefault "AudioBufferSourceOptions" "loop" == some "false"
#guard dictDefault "AudioBufferSourceOptions" "playbackRate" == some "1"
#guard dictDefault "AudioBufferSourceOptions" "buffer" == some ""
#guard dictDefault "OscillatorOptions" "type" == some "\"sine\""
#guard dictDefault "OscillatorOptions" "frequency" == some "440"
#guard dictDefault "BiquadFilterOptions" "type" == some "\"lowpass\""
#guard dictDefault "BiquadFilterOptions" "frequency" == some "350"
#guard dictDefault "BiquadFilterOptions" "Q" == some "1"
#guard (findDict "AudioNodeOptions").map (·.members.map (·.name)) ==
  some ["channelCount", "channelCountMode", "channelInterpretation"]
#guard (findDict "AudioNodeOptions").map (fun d => d.members.all (·.default == "")) == some true
#guard (findDict "OscillatorOptions").map (·.parent) == some "AudioNodeOptions"
#guard (findDict "OfflineAudioContextOptions").map (fun d => (d.members.filter (·.required)).map (·.name)) ==
  some ["sampleRate"]

/-- Invariant. Says: no two interfaces of the table have the same name. Does not say: that the table
holds every interface of the Web Audio API (it holds those of `webaudio.idl`). -/
theorem interface_names_nodup : (interfaces.map (·.name)).Nodup := by decide

end L4Factoidal.WebAudio.Idl
'''


def render(path):
    raw = open(path, "rb").read()
    sha = hashlib.sha256(raw).hexdigest()
    ifaces, enums, dicts, cbs = parse(raw.decode("utf-8"))
    o = []
    o.append("/-")
    o.append("L4Factoidal.WebAudio.Idl: the interfaces, enums, dictionaries and callbacks of the Web Audio API")
    o.append("as the page sees them (record: docs/designissues/2026-11-26-foafnaut-audio-plan.md, sections 2 and 9).")
    o.append("")
    o.append("Written by `tools/webaudio-idl-table.py` from the Web Platform Tests' `interfaces/webaudio.idl`")
    o.append("(Web Audio API 1.1, extracted by Reffy). Change the IDL and run the tool; do not edit the lists.")
    o.append(f"Source file: fetched {RECORDED_FETCHED} from")
    o.append("https://raw.githubusercontent.com/web-platform-tests/wpt/master/interfaces/webaudio.idl")
    o.append(f"(WPT commit not recorded), SHA-256 {sha}.")
    o.append("")
    o.append("Operation signatures are letters, as in `PageGl.Table`: u unsigned long, i long, l unsigned long")
    o.append("long, f float, d double, b boolean, s DOMString, a object, v undefined, h EventHandler,")
    o.append("`O` and a name for an interface, dictionary, enum or typed array, `Q` sequence, `Z` FrozenArray,")
    o.append("`R` record, `P` promise, `(x/y)` a union, `?` after a type nullable, `~` before an optional")
    o.append("argument; `|` separates overloads. Not kept: extended attributes of members, return types,")
    o.append("argument names.")
    o.append("-/")
    o.append("")
    o.append("namespace L4Factoidal.WebAudio.Idl")
    o.append(STRUCTS)
    o.append("/-- Every interface of `webaudio.idl`, in IDL order. -/")
    o.append("def interfaces : List Iface :=")

    def iface_fmt(i):
        ctor = "none" if i["ctor"] is None else f'some ⟨"constructor", {i["ctor"][0]}, {q("|".join(i["ctor"][1]))}⟩'
        attrs = lean_list(i["attrs"], lambda a: f'⟨{q(a[0])}, {q(a[1])}, {"true" if a[2] else "false"}⟩', "    ")
        other = "[" + ", ".join(q(x) for x in i["other"]) + "]"
        return (f'{{ name := {q(i["name"])}, parent := {q(i["parent"])}, ext := {q(i["ext"])},\n'
                f'      ctor := {ctor},\n      attrs := {attrs},\n      ops := {op_list(i["ops"])},\n'
                f'      statics := {op_list(i["statics"])},\n      other := {other} }}')
    o.append(lean_list(ifaces, iface_fmt))
    o.append("")
    o.append("/-- Every enum of `webaudio.idl`, in IDL order. -/")
    o.append("def enums : List Enum :=")
    o.append(lean_list(enums, lambda e: f'⟨{q(e[0])}, [' + ", ".join(q(v) for v in e[1]) + "]⟩"))
    o.append("")
    o.append("/-- Every dictionary of `webaudio.idl`, in IDL order. -/")
    o.append("def dicts : List Dict :=")
    o.append(lean_list(dicts, lambda d: f'⟨{q(d[0])}, {q(d[1])}, ' + lean_list(
        d[2], lambda m: f'⟨{q(m[0])}, {q(m[1])}, {"true" if m[2] else "false"}, {q(m[3])}⟩', "    ") + "⟩"))
    o.append("")
    o.append("/-- Every callback type of `webaudio.idl`, in IDL order. -/")
    o.append("def callbacks : List Callback :=")
    o.append(lean_list(cbs, lambda c: f'⟨{q(c[0])}, {q(c[1])}, {q(c[2])}⟩'))
    o.append(LOOKUPS)
    g = (GUARDS.lstrip("\n").replace("@NIFACE@", str(len(ifaces))).replace("@NENUM@", str(len(enums)))
         .replace("@NDICT@", str(len(dicts))).replace("@NCB@", str(len(cbs))))
    o.append(g)
    return "\n".join(o)


def main():
    args = sys.argv[1:]
    check = "--check" in args
    args = [a for a in args if a != "--check"]
    if len(args) != 1:
        raise SystemExit("usage: webaudio-idl-table.py [--check] webaudio.idl")
    out = render(args[0])
    if check:
        cur = open(OUT_PATH, encoding="utf-8").read()
        if cur != out:
            sys.stderr.write(f"{OUT_PATH} differs from the generator output\n")
            sys.exit(1)
        return
    sys.stdout.write(out)


if __name__ == "__main__":
    main()
