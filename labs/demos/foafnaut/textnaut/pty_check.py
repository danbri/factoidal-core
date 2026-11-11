#!/usr/bin/env python3
# Drives textnaut on a pseudo-terminal: keys, a burst of window resizes, quit and signals.
# Each check prints PASS or FAIL; the exit code is the number of failed checks.
# Run from labs/demos/foafnaut: python3 textnaut/pty_check.py pages/showcase.html
import fcntl, os, pty, re, select, signal, struct, sys, termios, time, unicodedata

PAGE = sys.argv[1] if len(sys.argv) > 1 else "pages/showcase.html"
CMD = ["deno", "run", "--no-prompt", "--allow-read", "--allow-ffi", "--allow-net", "--allow-env",
       "--import-map=textnaut/import_map.json", "textnaut/textnaut.ts", PAGE]
failed = 0

def check(name, ok, detail=""):
    global failed
    print(("PASS " if ok else "FAIL ") + name + ((" (" + detail + ")") if detail else ""))
    failed += 0 if ok else 1

def width(text):
    n = 0
    for ch in text:
        if unicodedata.combining(ch) or unicodedata.category(ch) in ("Mn", "Me", "Cf"):
            continue
        n += 2 if unicodedata.east_asian_width(ch) in "WF" else 1
    return n

def visible(segment):
    segment = re.sub(rb"\x1b\]8;;[^\x1b]*\x1b\\", b"", segment)
    segment = re.sub(rb"\x1b\[[0-9;?$]*[@-~]", b"", segment)
    return segment.decode("utf-8", "replace")

SAVER_CMD = CMD[:-1] + ["--screensaver"]

class Session:
    def __init__(self, rows, cols, env, args=(), saver=None):
        self.pid, self.fd = pty.fork()
        if self.pid == 0:
            os.environ.update(env)
            if saver is not None:
                os.execvp(CMD[0], SAVER_CMD[:-1] + SAVER_CMD[-1:] + ([saver] if saver else []) + list(args))
            os.execvp(CMD[0], CMD[:-1] + list(args) + CMD[-1:])
        self.resize(rows, cols, signal_child=False)
        self.out = b""
    def resize(self, rows, cols, signal_child=True):
        fcntl.ioctl(self.fd, termios.TIOCSWINSZ, struct.pack("HHHH", rows, cols, 0, 0))
        if signal_child:
            os.kill(self.pid, signal.SIGWINCH)
    def send(self, data):
        os.write(self.fd, data)
    def pump(self, seconds, until=None):
        end = time.time() + seconds
        while time.time() < end:
            ready, _, _ = select.select([self.fd], [], [], 0.02)
            if ready:
                try:
                    chunk = os.read(self.fd, 65536)
                except OSError:
                    return False
                if not chunk:
                    return False
                self.out += chunk
                # A terminal that answers nothing to the capability queries is the worst case.
            if until and until(self.out):
                return True
        return False
    def mark(self):
        self.out = b""
    def finish(self, seconds=5):
        end = time.time() + seconds
        while time.time() < end:
            self.pump(0.1)
            pid, status = os.waitpid(self.pid, os.WNOHANG)
            if pid:
                return os.waitstatus_to_exitcode(status)
        os.kill(self.pid, signal.SIGKILL)
        os.waitpid(self.pid, 0)
        return None

ENTER_ALT = b"\x1b[?1049h"; LEAVE_ALT = b"\x1b[?1049l"; SHOW = b"\x1b[?25h"
ENV = {"TERM": "xterm-256color", "COLORTERM": "truecolor", "LANG": "en_GB.UTF-8"}

def last_frame(out):
    # The rows written since the last screen clear.
    start = out.rfind(b"\x1b[2J")
    lines = {}
    if start < 0: return None
    for match in re.finditer(rb"\x1b\[(\d+);1H((?:(?!\x1b\[\d+;1H).)*)", out[start:], re.S):
        lines[int(match.group(1))] = visible(match.group(2))
    return lines

def screen_of(out):
    # The rows on the screen after the whole output: clears empty it, a row write sets that row.
    rows = {}
    marks = list(re.finditer(rb"\x1b\[2J|\x1b\[(\d+);1H", out))
    for i, m in enumerate(marks):
        if m.group(0) == b"\x1b[2J":
            rows = {}
            continue
        end = marks[i + 1].start() if i + 1 < len(marks) else len(out)
        rows[int(m.group(1))] = visible(out[m.end():end])
    return rows

def screen_problem(out, rows, cols):
    screen = screen_of(out)
    if sorted(screen) != list(range(1, rows + 1)): return f"rows {len(screen)} of {rows}"
    bad = [r for r, text in screen.items() if width(text) != cols]
    return f"row widths wrong {bad[:5]}: {[width(screen[r]) for r in bad[:5]]}" if bad else ""

def first_saver_frame(out, rows, cols):
    # The first synchronized frame of a screensaver, whole: a later frame may be cut by the read.
    start = out.find(b"\x1b[?2026h")
    end = out.find(b"\x1b[?2026l", start)
    if start < 0 or end < 0: return "no frame"
    return full_frame(out[start:end], rows, cols)

def full_frame(out, rows, cols):
    # The last complete redraw: starts at the last screen clear.
    lines = last_frame(out)
    if lines is None: return "no clear"
    if sorted(lines) != list(range(1, rows + 1)):
        return f"rows {sorted(lines)[:3]}..{len(lines)} of {rows}"
    bad = [r for r, text in lines.items() if width(text) != cols]
    return f"row widths wrong {bad[:5]}: {[width(lines[r]) for r in bad[:5]]}" if bad else ""

for label, env in [("24-bit", ENV), ("256", {"TERM": "xterm-256color", "COLORTERM": "", "LANG": "en_GB.UTF-8"}),
                   ("16", {"TERM": "xterm", "COLORTERM": "", "LANG": "C"}), ("none", {**ENV, "NO_COLOR": "1"})]:
    s = Session(24, 80, env)
    s.pump(8, lambda o: "TEXTNAUT" in visible(o) and o.count(b";1H") >= 24)
    s.pump(0.3)
    check(f"{label}: alternate screen on", ENTER_ALT in s.out)
    check(f"{label}: TEXTNAUT header drawn", "TEXTNAUT" in visible(s.out))
    detail = full_frame(s.out, 24, 80)
    check(f"{label}: first frame fills 24 rows of 80 columns", not detail, detail)
    s.send(b"\x1b[B\x1b[B\x1b[6~ ")
    s.pump(0.5)
    s.send(b"q")
    code = s.finish()
    check(f"{label}: q exits with 0", code == 0, str(code))
    check(f"{label}: terminal restored", s.out.rstrip().endswith(LEAVE_ALT) or LEAVE_ALT in s.out[-40:])
    check(f"{label}: no answer gives no large text", b"\x1b#3" not in s.out and not re.search(rb"\x1b\]66;s=2;[^ ]", s.out))

s = Session(24, 80, ENV)
s.pump(8, lambda o: "TEXTNAUT" in visible(o) and o.count(b";1H") >= 24)
s.send(b"\x1b[6~\x1b[6~")
s.pump(0.3)
sizes = [(24, 80), (30, 100), (40, 120), (50, 160), (35, 90), (28, 110), (45, 132), (25, 70), (60, 200), (33, 140)]
s.mark()
start = time.time()
for rows, cols in sizes * 3:
    s.resize(rows, cols)
    s.pump(0.015)
s.resize(41, 127)
settled = s.pump(4, lambda o: not full_frame(o, 41, 127) and b"\x1b[41;1H" in o)
elapsed = time.time() - start
detail = full_frame(s.out, 41, 127)
check("burst of 31 resizes ends with a full frame of 41 rows of 127 columns", settled and not detail, detail)
print(f"INFO burst time {elapsed*1000:.0f} ms for 31 resizes in {31*15} ms of signals; output {len(s.out)} bytes")
s.mark()
t0 = time.time()
s.resize(30, 101)
done = s.pump(3, lambda o: not full_frame(o, 30, 101))
detail = full_frame(s.out, 30, 101)
check("one resize settles to a full frame", done and not detail, detail)
print(f"INFO one resize to a full frame: {(time.time()-t0)*1000:.0f} ms")
s.pump(0.5)
s.mark()
s.send(b"\x1b[B")
s.pump(0.3)
lines = len(re.findall(rb"\x1b\[\d+;1H", s.out))
check("down arrow redraws only changed lines", 0 < lines <= 30, f"{lines} rows")
s.send(b"q")
check("q after resizes exits with 0", s.finish() == 0)

for sig, name in [(signal.SIGTERM, "SIGTERM"), (signal.SIGHUP, "SIGHUP")]:
    s = Session(24, 80, ENV)
    s.pump(8, lambda o: "TEXTNAUT" in visible(o))
    os.kill(s.pid, sig)
    code = s.finish()
    check(f"{name}: terminal restored", LEAVE_ALT in s.out and SHOW in s.out, str(code))

s = Session(24, 80, ENV)
s.pump(8, lambda o: "TEXTNAUT" in visible(o))
s.send(b"\x03")
check("Ctrl-C exits with 0 and restores", s.finish() == 0 and LEAVE_ALT in s.out)
s = Session(24, 80, ENV)
s.pump(8, lambda o: "TEXTNAUT" in visible(o))
s.send(b"999\r")
s.pump(1, lambda o: "no link 999" in visible(o))
check("a number with no link gives a message", "no link 999" in visible(s.out))
s.send(b"1\r")
s.pump(3, lambda o: o.count(b"\x1b[2J") >= 2)
s.send(b"b")
s.pump(2)
s.send(b"q")
code = s.finish()
check("follow, back, quit exit with 0", code == 0, str(code))
# A terminal that answers the probes as a DECDWL or an OSC 66 terminal does.
for name, answer, want in [("DEC", b"\x1b[1;1R\x1b[1;40R\x1b[?62c", b"\x1b#3"), ("OSC 66", b"\x1b[1;3R\x1b[1;80R\x1b[?62c", b"\x1b]66;s=2;f")]:
    s = Session(24, 80, ENV)
    s.pump(8, lambda o: b"\x1b[c" in o)
    s.send(answer)
    s.pump(8, lambda o: "TEXTNAUT" in visible(o) and o.count(b";1H") >= 20)
    s.pump(0.3)
    check(f"{name}: H1 sent at large size after the terminal answers", want in s.out)
    s.send(b"\x1b[B\x1b[B\x1b[6~")
    s.pump(0.5)
    s.send(b"q")
    code = s.finish()
    check(f"{name}: q exits with 0 and restores", code == 0 and LEAVE_ALT in s.out, str(code))
s = Session(24, 80, ENV, ["--big-headings=off"])
s.pump(8, lambda o: b"\x1b[c" in o)
s.send(b"\x1b[1;3R\x1b[1;40R\x1b[?62c")
s.pump(8, lambda o: "TEXTNAUT" in visible(o) and o.count(b";1H") >= 24)
s.pump(0.3)
check("--big-headings=off: no large text", b"\x1b#3" not in s.out and not re.search(rb"\x1b\]66;s=2;[^ ]", s.out))
s.send(b"q")
s.finish()
here = os.path.dirname(os.path.abspath(__file__))
wasm_dirs = [os.environ.get("TEXTNAUT_WASM_DIR"), os.path.join(here, "../.build/native-html/runtime"), os.path.join(here, "../../../../.scratch/wasm")]
if any(d and os.path.isfile(os.path.join(d, "web-render.mjs")) for d in wasm_dirs):
    s = Session(24, 80, ENV, ["--wasm"])
    s.pump(15, lambda o: "wasm engine" in visible(o))
    s.pump(0.3)
    check("--wasm: the header names the Wasm engine", "wasm engine" in visible(s.out))
    s.send(b"q")
    check("--wasm: q exits with 0", s.finish() == 0)
else:
    print("SKIP --wasm checks: no Wasm runtime (set TEXTNAUT_WASM_DIR)")

# ---- screensavers on their own: every colour level, the keys, the resize, the exits
SAVER_ENVS = [("24-bit", ENV), ("256", {"TERM": "xterm-256color", "COLORTERM": "", "LANG": "en_GB.UTF-8"}),
              ("16", {"TERM": "xterm", "COLORTERM": "", "LANG": "en_GB.UTF-8"}), ("none", {**ENV, "NO_COLOR": "1"}),
              ("16 and no UTF-8", {"TERM": "xterm", "COLORTERM": "", "LANG": "C"})]
for label, env in SAVER_ENVS:
    s = Session(24, 80, env, saver="plasma")
    s.pump(8, lambda o: b"plasma: " in o and o.count(b";1H") >= 24)
    s.pump(0.3)
    check(f"saver {label}: alternate screen on, cursor hidden", ENTER_ALT in s.out and b"\x1b[?25l" in s.out)
    detail = first_saver_frame(s.out, 24, 80)
    check(f"saver {label}: first frame fills 24 rows of 80 columns", not detail, detail)
    s.mark(); s.send(b"\t"); s.pump(3, lambda o: "tunnel: " in visible(o))
    check(f"saver {label}: Tab goes to the next saver", "tunnel: " in visible(s.out))
    s.mark(); s.send(b" "); s.pump(3, lambda o: "fire: " in visible(o))
    check(f"saver {label}: Space goes to the next saver", "fire: " in visible(s.out))
    s.mark(); s.send(b"b"); s.pump(3, lambda o: "tunnel: " in visible(o))
    check(f"saver {label}: b goes back one", "tunnel: " in visible(s.out))
    s.mark(); s.send(b"n"); s.pump(3, lambda o: "fire: " in visible(o))
    check(f"saver {label}: n goes to the next saver", "fire: " in visible(s.out))
    s.send(b"q")
    code = s.finish()
    check(f"saver {label}: q exits with 0 and restores the terminal", code == 0 and LEAVE_ALT in s.out and SHOW in s.out, str(code))
    if label in ("none", "16 and no UTF-8"):
        check(f"saver {label}: no half blocks", "\u2580".encode() not in s.out)
    if label == "none":
        check(f"saver {label}: no colour", not re.search(rb"\x1b\[[0-9;]*(38|48);", s.out))

# Every saver starts, draws a full frame and quits on a key.
for name in ["plasma", "tunnel", "fire", "rain", "stars", "life", "snakes", "sponge", "sponge4d", "lissajous", "metaballs", "torus", "waves", "maze", "cyclic", "xmas-tree", "xmas-lights"]:
    s = Session(24, 80, ENV, saver=name)
    s.pump(8, lambda o: (name + ": ").encode() in o and o.count(b";1H") >= 24)
    s.pump(0.2)
    detail = first_saver_frame(s.out, 24, 80)
    s.send(b"x")
    code = s.finish()
    check(f"saver {name}: a full frame, and any other key quits with 0 and restores", not detail and code == 0 and LEAVE_ALT in s.out, detail or str(code))

# A hidden saver outside December: Tab walks the hidden ones only.
s = Session(24, 80, ENV, saver="xmas")
s.pump(8, lambda o: b"xmas-tree: " in o)
s.mark(); s.send(b"\t"); s.pump(3, lambda o: b"xmas-lights: " in o)
check("hidden: Tab goes to the other hidden saver", b"xmas-lights: " in s.out)
s.send(b"q"); s.finish()

# Resize in a saver: a burst, then a full frame of the new size.
s = Session(24, 80, ENV, saver="metaballs")
s.pump(8, lambda o: b"metaballs: " in o)
s.mark()
for rows, cols in [(30, 100), (20, 60), (50, 160), (10, 40), (35, 120)] * 2:
    s.resize(rows, cols); s.pump(0.03)
s.pump(2, lambda o: not screen_problem(o, 35, 120))
detail = screen_problem(s.out, 35, 120)
check("saver resize: the last size gets a full frame", not detail, detail)
s.send(b"q"); check("saver resize: q exits with 0", s.finish() == 0)

# Frame rate and load: bytes and CPU time over a few seconds.
s = Session(24, 80, ENV, saver="sponge")
s.pump(5, lambda o: b"sponge: " in o)
s.mark(); t0 = time.time(); c0 = os.times()
s.pump(3)
frames = s.out.count(b"\x1b[?2026h")
print(f"INFO sponge 80x24: {frames/3:.0f} frames a second, {len(s.out)/3/1000:.0f} kB a second")
check("saver frame cap: no more than 35 frames a second", frames / 3 <= 35, f"{frames/3:.0f}")
check("saver is drawing", frames >= 30, str(frames))
s.send(b"q"); s.finish()

for sig, name in [(signal.SIGTERM, "SIGTERM"), (signal.SIGHUP, "SIGHUP"), (signal.SIGINT, "SIGINT")]:
    s = Session(24, 80, ENV, saver="life")
    s.pump(8, lambda o: b"life: " in o)
    os.kill(s.pid, sig)
    code = s.finish()
    check(f"saver {name}: terminal restored", LEAVE_ALT in s.out and SHOW in s.out, str(code))
s = Session(24, 80, ENV, saver="life")
s.pump(8, lambda o: b"life: " in o)
s.send(b"\x03")
check("saver Ctrl-C exits with 0 and restores", s.finish() == 0 and LEAVE_ALT in s.out)

# ---- the help screen of the browser
def body(screen, rows):
    return {r: t for r, t in screen.items() if 2 <= r <= rows - 1}

FOOTER = "back to the page"
s = Session(24, 80, ENV)
s.pump(8, lambda o: "TEXTNAUT" in visible(o) and o.count(b";1H") >= 24)
s.pump(0.3)
check("hint line names the help key", "? help" in visible(s.out))
s.send(b"\x1b[6~\x1b[B\x1b[B"); s.pump(0.6)
s.send(b"\x1b[6~"); s.pump(0.6)
before = screen_of(s.out)
check("page: scrolled to a position in the middle", len(before) == 24 and "TEXTNAUT" in before[1], str(len(before)))
s.send(b"?")
s.pump(3, lambda o: FOOTER in visible(o))
s.pump(0.2)
detail = screen_problem(s.out, 24, 80)
check("help: ? opens a full screen of help", "TEXTNAUT HELP" in screen_of(s.out)[1] and not detail, detail)
text = " ".join(screen_of(s.out).values())
check("help: lists keys and the first screensavers", "follow link number n" in text and "plasma" in text and "tunnel" in text)
check("help: hidden savers are not listed", "xmas" not in text)
s.send(b"\x1b[F"); s.pump(0.5)   # End: the last screensaver
text = " ".join(screen_of(s.out).values())
check("help: End shows the last screensavers", "sponge4d" in text and "cyclic" in text)
s.send(b"q"); s.pump(3, lambda o: "HELP" not in screen_of(o).get(1, "HELP")); s.pump(0.3)
after = screen_of(s.out)
check("help: q returns to the same page position", len(after) == 24 and body(before, 24) == body(after, 24), f"{len(before)} rows before, {len(after)} after")
s.send(b"h"); s.pump(3, lambda o: "TEXTNAUT HELP" in screen_of(o).get(1, "")); s.pump(0.3)
check("help: h opens it too", "TEXTNAUT HELP" in screen_of(s.out).get(1, ""))
# Start the second saver from help with Down and Enter; return with q.
s.send(b"\x1b[H\x1b[B"); s.pump(0.3); s.mark(); s.send(b"\r")
s.pump(5, lambda o: "tunnel: " in visible(o))
check("help: Down and Enter start the second saver", "tunnel: " in visible(s.out))
s.mark(); s.send(b"\t"); s.pump(3, lambda o: "fire: " in visible(o))
check("help: Tab inside the saver goes to the next", "fire: " in visible(s.out))
s.send(b"q"); s.pump(3, lambda o: "TEXTNAUT HELP" in screen_of(o).get(1, "") and FOOTER in visible(o[-3000:])); s.pump(0.2)
detail = screen_problem(s.out, 24, 80)
check("help: q in the saver returns to the help screen", "TEXTNAUT HELP" in screen_of(s.out).get(1, "") and not detail, detail)
# A number then Enter.
s.mark(); s.send(b"6\r"); s.pump(5, lambda o: "life: " in visible(o))
check("help: a number and Enter start that saver", "life: " in visible(s.out))
s.send(b"z"); s.pump(3, lambda o: "TEXTNAUT HELP" in visible(o))
check("help: any other key in the saver returns to help", "TEXTNAUT HELP" in visible(s.out))
# The hidden key.
s.mark(); s.send(b"x"); s.pump(5, lambda o: "xmas-tree: " in visible(o))
check("help: the hidden key starts a hidden saver", "xmas-tree: " in visible(s.out))
s.send(b"q"); s.pump(3, lambda o: "TEXTNAUT HELP" in visible(o))
s.send(b"q"); s.pump(3, lambda o: "HELP" not in screen_of(o).get(1, "HELP")); s.pump(0.3)
after = screen_of(s.out)
check("help: back on the page, in the same place", len(after) == 24 and body(before, 24) == body(after, 24))
# Resize while help is open.
s.send(b"?"); s.pump(1)
s.mark(); s.resize(30, 100); s.pump(2, lambda o: not screen_problem(o, 30, 100))
detail = screen_problem(s.out, 30, 100)
check("help: a resize redraws help at the new size", not detail, detail)
s.send(b"\x03")
code = s.finish()
check("help: Ctrl-C quits the browser with 0 and restores", code == 0 and LEAVE_ALT in s.out and SHOW in s.out, str(code))
# Ctrl-C inside a saver started from help ends the whole program.
s = Session(24, 80, ENV)
s.pump(8, lambda o: "TEXTNAUT" in visible(o))
s.send(b"?"); s.pump(2, lambda o: "HELP" in visible(o)); s.send(b"\r"); s.pump(3, lambda o: "plasma: " in visible(o))
s.send(b"\x03")
code = s.finish()
check("help: Ctrl-C in a saver started from help quits with 0 and restores", code == 0 and LEAVE_ALT in s.out and SHOW in s.out, str(code))
# Signals while a saver runs inside the browser.
for sig, name in [(signal.SIGTERM, "SIGTERM"), (signal.SIGHUP, "SIGHUP")]:
    s = Session(24, 80, ENV)
    s.pump(8, lambda o: "TEXTNAUT" in visible(o))
    s.send(b"?"); s.pump(2, lambda o: "HELP" in visible(o)); s.send(b"\r"); s.pump(3, lambda o: "plasma: " in visible(o))
    os.kill(s.pid, sig)
    code = s.finish()
    check(f"saver inside the browser, {name}: terminal restored", LEAVE_ALT in s.out and SHOW in s.out, str(code))
sys.exit(failed)
