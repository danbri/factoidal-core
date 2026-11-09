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

class Session:
    def __init__(self, rows, cols, env, args=()):
        self.pid, self.fd = pty.fork()
        if self.pid == 0:
            os.environ.update(env)
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

def full_frame(out, rows, cols):
    # The last complete redraw: starts at the last screen clear.
    start = out.rfind(b"\x1b[2J")
    if start < 0: return "no clear"
    lines = {}
    for match in re.finditer(rb"\x1b\[(\d+);1H((?:(?!\x1b\[\d+;1H).)*)", out[start:], re.S):
        lines[int(match.group(1))] = visible(match.group(2))
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
s = Session(24, 80, ENV, ["--wasm"])
s.pump(15, lambda o: "wasm engine" in visible(o))
s.pump(0.3)
check("--wasm: the header names the Wasm engine", "wasm engine" in visible(s.out))
s.send(b"q")
check("--wasm: q exits with 0", s.finish() == 0)
sys.exit(failed)
