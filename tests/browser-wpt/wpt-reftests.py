#!/usr/bin/env python3
"""WPT reftests on Foafnaut's native engine, by WPT's own rules (skills/wpt-runs, section 10).

  run      run every reftest of the WPT manifest under --prefix (e.g. svg/), compare, write results
  compare  two results.json files: newly passing and newly failing tests (changes.md)
  clusters the tests that do not pass, grouped by cause (the engine's skip messages first,
           then the test's directory and markup), with how many Chrome passes

    wpt-reftests.py run --manifest MANIFEST.json --wpt-root WPT --native-engine LIB --prefix svg/ \
        --out DIR [--chrome-summary chrome-summary_v2.json] [--jobs 3] [--only a,b] [--shard k --shards n]

What is run: every `reftest` item of the WPT manifest at the WPT commit (wpt.fyi's
/api/manifest?sha=...) whose URL starts with /PREFIX: HTML, XHTML and standalone SVG/XML
documents alike, `==` and `!=` references, reference chains (a reference that is itself a
reftest in the manifest), each test's fuzzy annotations and viewport size (default 800x600).
`print-reftest` items are a separate kind and are not run here.

How a test is judged: wptrunner's RefTestImplementation (tools/wptrunner/wptrunner/executors/
base.py), step for step. The references of a node are tried in order; an edge holds when the
two pictures compare as its relation says; when a reference has references of its own, the
search goes on from it; the test passes when some path from the test reaches a reference with
no references of its own with every edge holding (wptrunner's stack). Comparison: both pictures
as RGB; per pixel, the largest difference of the three channels; `maxDifference` is the largest
of those and `totalPixels` the count of pixels that differ at all. With no fuzzy annotation (or
0-0;0-0) the pictures must be identical. With one, the edge holds when
(totalPixels == 0 and the allowed pixel range starts at 0) or (maxDifference == 0 and the
allowed difference range starts at 0) or both numbers are inside their ranges. The fuzzy
annotation is looked up as wptrunner does: (node, reference, relation), then the reference
alone, then the node's default, on the node being compared (the test, or a reference in a chain).

Statuses: EXCLUDED (a test of DEFECTIVE, defective upstream data with an open issue: reported apart,
not in the passed count or the total; the run exits 1 if one passes), PASS, FAIL (a picture that does not hold, or the engine refusing a page: its message
is kept); TIMEOUT when a page on the path kept `reftest-wait` for the page-time budget; ERROR
when the harness failed (a fetch, the runner, a picture missing); CRASH when the drawing
process died on a page; STALL when a page took longer than --stall seconds of wall time (the
process is ended and the rest of its pages go to a new one). Like wpt.fyi, a reftest is one
test: PASS or not. Valid: every test has a status and ERROR is under 0.5% of tests; CRASH and
STALL are the engine's defects, listed with their pages.

Pages are served from --wpt-root by a server of this script on 127.0.0.1 (a random port; it
never uses wptserve's port 8000, so it can run beside a WPT run): files as they are, the
Content-Type of a `.headers` file when there is one, `.sub.` files with the host and port
substituted. Drawing: reftest-render.ts (the engine's CPU raster, Noto Sans with the Hub's
fallback fonts from third_party/fonts).

Output in --out: results.json (every test, its edges with their numbers, timings, the run's
metadata and totals, Chrome's status when --chrome-summary is given), summary.md, and
failures/ (for each test that did not pass: the test picture, the reference picture and a
difference picture: changed pixels red on a faded test picture), pictures/ (every drawn page;
removed with --no-pictures after the comparison).
"""
import argparse, collections, hashlib, http.server, json, os, re, shutil, socket, socketserver, struct, subprocess, sys, threading, time, zlib
from urllib.parse import unquote, urljoin, urlsplit

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

# ---- the manifest ------------------------------------------------------------------------

# Tests with defective upstream data (owner rule, 2026-10-21: "Dont list bad tests as our failing";
# skills/test-suites/SKILL.md, "Defective test data"). Each is reported apart: status EXCLUDED, not
# in the passed count or the total. If one PASSES, the run exits 1 (stale exclusion). Use this
# table only with evidence in the open issue.
_I883 = "https://github.com/danbri/factoidal-core/issues/883"
_REASON_CFF_REF = ("the WOFF2 font is TrueType (upm 2048, hhea 1454/-20) but the reference uses the CFF font "
                   "SFNT-CFF-Reference.otf (upm 1000, typo 750/-250): the line boxes differ")
DEFECTIVE = {
    "/css/WOFF2/directory-knowntags-001.xht": (_REASON_CFF_REF, _I883),
    "/css/WOFF2/tabledata-glyf-origlength-001.xht": (_REASON_CFF_REF, _I883),
    "/css/WOFF2/tabledata-glyf-origlength-002.xht": (_REASON_CFF_REF, _I883),
    "/css/WOFF2/tabledata-glyf-origlength-003.xht": (_REASON_CFF_REF, _I883),
    "/css/WOFF2/tabledata-glyf-bbox-001.xht": (
        "the WOFF2 font is CFF (upm 1000, typo 750/-250) but the reference uses the TrueType font "
        "SFNT-TTF-Reference.ttf (upm 2048, hhea 1454/-20): the line boxes differ", _I883),
}


def apply_exclusions(rows, defective=None):
    """Mark the rows of DEFECTIVE tests EXCLUDED (the measured status goes to `measured`).
    Returns the tests that passed: stale exclusions, which fail the run."""
    defective = DEFECTIVE if defective is None else defective
    stale = []
    for r in rows:
        d = defective.get(r["test"])
        if not d:
            continue
        r["measured"] = r["status"]
        r["status"] = "EXCLUDED"
        r["exclusion"] = {"reason": d[0], "issue": d[1]}
        if r["measured"] == "PASS":
            stale.append(r["test"])
    return stale


def manifest_items(path, kind="reftest"):
    """{url: (references, extras)} of the manifest's items of `kind` (manifest version 8 or 9)."""
    m = json.load(open(path))
    out = {}
    def walk(d, p):
        for k, v in d.items():
            if isinstance(v, dict):
                walk(v, p + "/" + k)
            else:
                for item in v[1:]:
                    url = item[0] or (p + "/" + k)
                    out[url] = (item[1], item[2] if len(item) > 2 else {})
    walk(m["items"].get(kind, {}), "")
    return out


def fuzzy_table(extras):
    """wptrunner's fuzzy dict of a node: key None, a reference URL, or (node, reference, relation)."""
    table = {}
    for key, ranges in extras.get("fuzzy", []) or []:
        k = tuple(key) if isinstance(key, list) else key
        table[k] = ((ranges[0][0], ranges[0][1]), (ranges[1][0], ranges[1][1]))
    return table


def fuzzy_for(node_url, node_extras, ref_url, relation):
    table = fuzzy_table(node_extras)
    for key in [(node_url, ref_url, relation), ref_url, None]:
        if key in table:
            return table[key]
    return None


def viewport_of(extras):
    vs = extras.get("viewport_size")
    if vs:
        m = re.match(r"^\s*(\d+)\s*[xX]\s*(\d+)\s*$", str(vs))
        if m:
            return int(m.group(1)), int(m.group(2))
    return 800, 600

# ---- PNG (no filter, as reftest-render.ts writes them) ----------------------------------

def png_read_rgb(path):
    """(width, height, RGB bytes) of an 8-bit RGBA or RGB PNG written with filter 0 rows."""
    data = open(path, "rb").read()
    assert data[:8] == b"\x89PNG\r\n\x1a\n", path
    at, idat = 8, []
    w = h = ctype = None
    while at < len(data):
        n, t = struct.unpack(">I4s", data[at:at + 8])
        body = data[at + 8:at + 8 + n]
        if t == b"IHDR":
            w, h, depth, ctype = struct.unpack(">IIBB", body[:10])
            assert depth == 8 and ctype in (2, 6), "unsupported PNG"
        elif t == b"IDAT":
            idat.append(body)
        at += 12 + n
    raw = zlib.decompress(b"".join(idat))
    bpp = 4 if ctype == 6 else 3
    stride = w * bpp + 1
    out = bytearray(w * h * 3)
    for y in range(h):
        row = raw[y * stride:(y + 1) * stride]
        assert row[0] == 0, "filtered PNG rows are not read here"
        px = row[1:]
        if bpp == 3:
            out[y * w * 3:(y + 1) * w * 3] = px
        else:
            o = out
            base = y * w * 3
            o[base:base + w * 3:3] = px[0::4]
            o[base + 1:base + w * 3:3] = px[1::4]
            o[base + 2:base + w * 3:3] = px[2::4]
    return w, h, bytes(out)


def png_write_rgb(path, w, h, rgb):
    def chunk(t, b):
        return struct.pack(">I", len(b)) + t + b + struct.pack(">I", zlib.crc32(t + b) & 0xffffffff)
    raw = b"".join(b"\x00" + rgb[y * w * 3:(y + 1) * w * 3] for y in range(h))
    with open(path, "wb") as f:
        f.write(b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 2, 0, 0, 0))
                + chunk(b"IDAT", zlib.compress(raw, 6)) + chunk(b"IEND", b""))


def differences(a, b, width=800):
    """wptrunner get_differences: (largest channel difference, pixels with any difference).
    Pure Python: rows that are equal as bytes are skipped, so equal pictures cost one compare."""
    if a == b:
        return 0, 0
    if len(a) != len(b):
        return 255, max(len(a), len(b)) // 3
    stride = width * 3
    maxd = count = 0
    for y in range(0, len(a), stride):
        ra, rb = a[y:y + stride], b[y:y + stride]
        if ra == rb:
            continue
        for x in range(0, len(ra), 3):
            if ra[x:x + 3] != rb[x:x + 3]:
                d = max(abs(ra[x] - rb[x]), abs(ra[x + 1] - rb[x + 1]), abs(ra[x + 2] - rb[x + 2]))
                count += 1
                if d > maxd:
                    maxd = d
    return maxd, count


def holds(a, b, relation, fuzzy, width=800):
    """wptrunner check_pass, with pixels in place of hashes (equal pixels have equal hashes)."""
    maxd, count = differences(a, b, width)
    if not fuzzy or fuzzy == ((0, 0), (0, 0)):
        equal = maxd == 0 and count == 0
    else:
        (dmin, dmax), (pmin, pmax) = fuzzy
        equal = ((count == 0 and pmin == 0) or (maxd == 0 and dmin == 0) or
                 (dmin <= maxd <= dmax and pmin <= count <= pmax))
    return (equal if relation == "==" else not equal), maxd, count


def diff_picture(path, w, h, test, ref):
    """Changed pixels red on the test picture faded to a quarter."""
    out = bytearray(255 - (255 - v) // 4 for v in test)
    stride = w * 3
    for y in range(0, len(test), stride):
        if test[y:y + stride] == ref[y:y + stride]:
            continue
        for x in range(y, y + stride, 3):
            if test[x:x + 3] != ref[x:x + 3]:
                out[x:x + 3] = b"\xff\x00\x00"
    png_write_rgb(path, w, h, bytes(out))

# ---- the page server ---------------------------------------------------------------------

TYPES = {".html": "text/html", ".htm": "text/html", ".xht": "application/xhtml+xml", ".xhtml": "application/xhtml+xml",
         ".svg": "image/svg+xml", ".xml": "application/xml", ".css": "text/css", ".js": "text/javascript",
         ".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg", ".gif": "image/gif", ".webp": "image/webp",
         ".ttf": "font/ttf", ".otf": "font/otf", ".woff": "font/woff", ".woff2": "font/woff2", ".json": "application/json",
         ".txt": "text/plain", ".ico": "image/x-icon", ".bmp": "image/bmp", ".avif": "image/avif"}


def serve(wpt_root):
    class Handler(http.server.BaseHTTPRequestHandler):
        def log_message(self, *a):
            pass

        def do_GET(self):
            parts = urlsplit(self.path)
            rel = unquote(parts.path).lstrip("/")
            full = os.path.realpath(os.path.join(wpt_root, rel))
            if not full.startswith(os.path.realpath(wpt_root)) or not os.path.isfile(full):
                self.send_response(404); self.send_header("Content-Length", "0"); self.end_headers(); return
            body = open(full, "rb").read()
            ext = os.path.splitext(full)[1].lower()
            ctype = TYPES.get(ext, "application/octet-stream")
            extra = []
            if os.path.isfile(full + ".headers"):
                for line in open(full + ".headers", encoding="utf-8", errors="replace"):
                    if ":" in line:
                        k, v = line.split(":", 1)
                        if k.strip().lower() == "content-type":
                            ctype = v.strip()
                        else:
                            extra.append((k.strip(), v.strip()))
            if ".sub." in os.path.basename(full):
                host, port = self.server.server_address[:2]
                text = body.decode("utf-8", "replace")
                text = re.sub(r"\{\{host\}\}|\{\{domains\[\]\}\}", host, text)
                text = re.sub(r"\{\{ports\[http\]\[0\]\}\}", str(port), text)
                text = re.sub(r"\{\{location\[path\]\}\}", parts.path, text)
                body = text.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(body)))
            for k, v in extra:
                self.send_header(k, v)
            self.end_headers()
            self.wfile.write(body)

    class Server(socketserver.ThreadingMixIn, http.server.HTTPServer):
        daemon_threads = True
    s = Server(("127.0.0.1", 0), Handler)
    threading.Thread(target=s.serve_forever, daemon=True).start()
    return s

# ---- drawing -----------------------------------------------------------------------------

def draw_all(jobs, a, pictures, log):
    """Draw each job (url, w, h, file) in --jobs processes of reftest-render.ts. A process that
    dies is restarted after the page it died on (CRASH); a page over --stall seconds ends its
    process (STALL). Answer: {file: {status, ms, sha, waited, message}}."""
    results = {}
    lock = threading.Lock()
    queues = [jobs[i::a.jobs] for i in range(a.jobs)]

    def worker(k, queue):
        pending = list(queue)
        while pending:
            listfile = os.path.join(pictures, f".jobs-{k}.jsonl")
            with open(listfile, "w") as f:
                for j in pending:
                    f.write(json.dumps(j) + "\n")
            cmd = ["deno", "run", "-A", "--unstable-ffi", os.path.join(HERE, "reftest-render.ts"),
                   "--native-engine", a.native_engine, "--list", listfile, "--out", pictures,
                   "--wait-ms", str(a.wait_ms)] + (["--bitmap-font"] if a.bitmap_font else [])
            p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=open(os.path.join(pictures, f".stderr-{k}.log"), "a"),
                                 text=True, start_new_session=True)
            current, last = None, time.time()
            done_here = 0
            timer_state = {"stalled": False}

            def watchdog():
                while p.poll() is None:
                    time.sleep(1)
                    if current is not None and time.time() - last > a.stall:
                        timer_state["stalled"] = True
                        try:
                            os.killpg(p.pid, 9)
                        except OSError:
                            pass
                        return
            threading.Thread(target=watchdog, daemon=True).start()
            for line in p.stdout:
                if line.startswith("__job "):
                    current = json.loads(line[6:])["i"]; last = time.time()
                elif line.startswith("__done "):
                    r = json.loads(line[7:])
                    with lock:
                        results[pending[r["i"]]["file"]] = r
                    done_here = r["i"] + 1
                    current = None
            p.wait()
            if current is None and done_here >= len(pending):
                break
            # the process died (or was ended) on job `current`
            i = current if current is not None else done_here
            if i < len(pending):
                status = "stall" if timer_state["stalled"] else "crash"
                with lock:
                    results[pending[i]["file"]] = {"status": status, "ms": int((time.time() - last) * 1000),
                                                   "message": f"drawing process {'ended after ' + str(a.stall) + ' s' if status == 'stall' else 'exited ' + str(p.returncode)}"}
                log(f"{status.upper()} {pending[i]['url']}")
            pending = pending[i + 1:]
        return

    threads = [threading.Thread(target=worker, args=(k, q)) for k, q in enumerate(queues) if q]
    for t in threads:
        t.start()
    total = len(jobs)
    while any(t.is_alive() for t in threads):
        time.sleep(10)
        with lock:
            n = len(results)
        log(f"drawn {n}/{total}")
    for t in threads:
        t.join()
    return results


def picture_name(url, w, h):
    return hashlib.sha1(f"{url} {w}x{h}".encode()).hexdigest()[:16] + ".png"


def run(a):
    t0 = time.time()
    log = lambda m: print(f"[{time.strftime('%H:%M:%S')}] {m}", file=sys.stderr, flush=True)
    items = manifest_items(a.manifest)
    prefix = "/" + a.prefix.strip("/") + "/"
    tests = sorted(u for u in items if u.startswith(prefix))
    if a.only:
        wanted = [w.strip() for w in a.only.split(",") if w.strip()]
        tests = [u for u in tests if any(u.startswith(w) or u == w for w in wanted)]
    if a.shards > 1:
        tests = tests[a.shard::a.shards]
    log(f"{len(tests)} reftests under {prefix}")
    # every page to draw: the tests and each reference along their chains, at the test's size
    needed = {}
    def visit(url, size, seen):
        key = (url, size)
        if key not in needed:
            needed[key] = picture_name(url, *size)
        refs = items.get(url, ([], {}))[0] if url in items else []
        for ref, _rel in refs:
            ref_abs = urljoin(url, ref)
            if ref_abs in seen:
                continue
            visit(ref_abs, size, seen | {ref_abs})
    for u in tests:
        visit(u, viewport_of(items[u][1]), {u})
    server = serve(a.wpt_root)
    base = f"http://127.0.0.1:{server.server_address[1]}"
    pictures = os.path.join(a.out, "pictures")
    os.makedirs(pictures, exist_ok=True)
    jobs = [{"url": base + url, "width": w, "height": h, "file": f} for (url, (w, h)), f in sorted(needed.items()) if url != "about:blank"]
    log(f"{len(jobs)} pages to draw with {a.jobs} processes")
    t1 = time.time()
    drawn = draw_all(jobs, a, pictures, log)
    draw_s = time.time() - t1
    server.shutdown()
    cache = {}

    def pixels(url, size):
        if url == "about:blank":  # a browser draws an empty page white
            return {"status": "ok"}, b"\xff" * (size[0] * size[1] * 3)
        f = needed[(url, size)]
        r = drawn.get(f, {"status": "missing"})
        if r.get("status") not in ("ok", "timeout"):
            return r, None
        if f not in cache:
            cache.clear()  # keep memory small: pages are compared in test order
            cache[f] = png_read_rgb(os.path.join(pictures, f))[2]
        return r, cache[f]

    chrome = json.load(open(a.chrome_summary)) if a.chrome_summary else {}
    failures = os.path.join(a.out, "failures")
    os.makedirs(failures, exist_ok=True)
    rows = []
    for u in tests:
        refs0, extras0 = items[u]
        size = viewport_of(extras0)
        stack = [((u, urljoin(u, r)), rel) for r, rel in reversed(refs0)]
        edges, status, message, worst = [], None, None, None
        tested = set()
        while stack:
            (node, ref), rel = stack.pop()
            if (node, ref, rel) in tested:
                continue
            tested.add((node, ref, rel))
            node_extras = items[node][1] if node in items else {}
            fz = fuzzy_for(node, node_extras, ref, rel)
            rn, pn = pixels(node, size)
            rr, pr = pixels(ref, size)
            bad = rn if pn is None else rr if pr is None else None
            if bad is not None:
                st = {"error": "ERROR", "crash": "CRASH", "stall": "STALL", "missing": "ERROR"}.get(bad.get("status"), "ERROR")
                # the engine refusing a page is the engine's failure, as a wrong picture is
                # (FAIL); ERROR is kept for the harness (a fetch, the runner, a missing picture)
                if st == "ERROR" and str(bad.get("message") or "").startswith("Lean HTML:"):
                    st = "FAIL"
                edges.append({"from": node, "to": ref, "relation": rel, "status": st, "message": bad.get("message")})
                status = status or st; message = message or bad.get("message")
                continue
            ok, maxd, count = holds(pn, pr, rel, fz, size[0])
            edge = {"from": node, "to": ref, "relation": rel, "fuzzy": fz, "maxDifference": maxd, "totalPixels": count, "holds": ok}
            edges.append(edge)
            if not ok and worst is None:
                worst = (node, ref, pn, pr)
            if ok:
                sub = items[ref][0] if ref in items else []
                if sub:
                    stack.extend(((ref, urljoin(ref, r)), r2) for r, r2 in reversed(sub))
                else:
                    status = "PASS"; message = None
                    break
        timeouts = [p for p in [u] + [e["to"] for e in edges] if drawn.get(needed.get((p, size), ""), {}).get("status") == "timeout"]
        if status != "PASS":
            if timeouts and status is None:
                status = "TIMEOUT"; message = "reftest-wait still set after the page-time budget: " + ", ".join(timeouts)
            elif status is None:
                status = "FAIL"
                e = next((e for e in edges if "holds" in e and not e["holds"]), None)
                if e:
                    message = (f"{e['relation']} {e['to']}: maxDifference {e['maxDifference']}, totalPixels {e['totalPixels']}"
                               + (f" (fuzzy {e['fuzzy'][0][0]}-{e['fuzzy'][0][1]};{e['fuzzy'][1][0]}-{e['fuzzy'][1][1]})" if e.get("fuzzy") else ""))
        row = {"test": u, "status": status, "message": message, "edges": edges,
               "ms": sum(drawn.get(needed.get((p, size), ""), {}).get("ms", 0) for p in {u, *[e["to"] for e in edges]}),
               "scripted": bool(drawn.get(needed[(u, size)], {}).get("scripted"))}
        # what the engine skipped (its liberal-mode diagnostics) on the test and on each reference
        skipped = {p: drawn.get(needed.get((p, size), ""), {}).get("skipped") for p in [u] + [e["to"] for e in edges]}
        skipped = {p: v for p, v in skipped.items() if v}
        if skipped:
            row["skipped"] = skipped
        errs = {p: drawn.get(needed.get((p, size), ""), {}).get("scriptErrors") for p in [u] + [e["to"] for e in edges]}
        errs = {p: v for p, v in errs.items() if v}
        if errs:
            row["scriptErrors"] = errs
        c = chrome.get(u)
        if c:
            row["chrome"] = {"P": "PASS", "F": "FAIL", "T": "TIMEOUT", "E": "ERROR", "C": "CRASH"}.get(c.get("s"), c.get("s"))
        rows.append(row)
        if status != "PASS" and worst and not a.no_failure_pictures:
            node, ref, pn, pr = worst
            stem = u.strip("/").replace("/", "__")
            w, h = size
            png_write_rgb(os.path.join(failures, stem + ".test.png"), w, h, pn)
            png_write_rgb(os.path.join(failures, stem + ".ref.png"), w, h, pr)
            diff_picture(os.path.join(failures, stem + ".diff.png"), w, h, pn, pr)
    stale = apply_exclusions(rows)
    excluded = [r for r in rows if r["status"] == "EXCLUDED"]
    for r in excluded:
        log(f"EXCLUDED {r['test']}: defective test data, {r['exclusion']['issue']}")
    for t in stale:
        log(f"STALE EXCLUSION {t}: the test now passes; remove it from DEFECTIVE")
    all_rows = rows
    rows = [r for r in rows if r["status"] != "EXCLUDED"]
    counts = collections.Counter(r["status"] for r in rows)
    passed = counts.get("PASS", 0)
    chrome_rows = [r for r in rows if "chrome" in r]
    chrome_pass = sum(1 for r in rows if r.get("chrome") == "PASS")
    # validity counts the harness's failures only; CRASH and STALL are the engine's defects,
    # reported with their pages, as in the full WPT and Test262 runs
    harness = counts.get("ERROR", 0)
    meta = {
        "format": "factoidal-wpt-reftests-v1", "prefix": prefix, "startedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t0)),
        "finishedAt": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "wallSeconds": round(time.time() - t0, 1),
        "drawSeconds": round(draw_s, 1), "pagesDrawn": len(jobs),
        "engine": {"path": os.path.abspath(a.native_engine), "sha256": hashlib.sha256(open(a.native_engine, "rb").read()).hexdigest()},
        "renderer": "CPU raster (SVGRaster) through op render cpu:true; fonts: " + ("bitmap face (diagnostic)" if a.bitmap_font else "Noto Sans + Hub fallback fonts (third_party/fonts)"),
        "scriptEngine": "bubblepop", "manifest": os.path.abspath(a.manifest),
        "manifestSha256": hashlib.sha256(open(a.manifest, "rb").read()).hexdigest(),
        "shard": [a.shard, a.shards],
        "totals": {"tests": len(rows), "passed": passed, "share": round(100 * passed / len(rows), 4) if rows else 0,
                   "statuses": dict(counts), "excluded": len(excluded), "harnessErrors": harness,
                   "harnessErrorShare": round(100 * harness / len(rows), 4) if rows else 0,
                   "chromeTests": len(chrome_rows), "chromePassed": chrome_pass,
                   "chromeShare": round(100 * chrome_pass / len(rows), 4) if rows and chrome_rows else None,
                   "passedWhereChromePasses": sum(1 for r in rows if r["status"] == "PASS" and r.get("chrome") == "PASS"),
                   # passes where the engine skipped something on the test or a reference (liberal
                   # mode): both pictures may lack the same part, so such a pass says less
                   "passedWithSkips": sum(1 for r in rows if r["status"] == "PASS" and r.get("skipped"))},
    }
    meta["valid"] = bool(rows) and harness < 0.005 * len(rows) and all(r["status"] for r in rows)
    meta["invalidReason"] = None if meta["valid"] else f"harness errors {harness} of {len(rows)} (limit 0.5%)"
    json.dump({**meta, "tests": all_rows}, open(os.path.join(a.out, "results.json"), "w"), indent=1)
    write_summary(a.out, meta, rows, all_rows)
    if a.no_pictures:
        shutil.rmtree(pictures, ignore_errors=True)
    t = meta["totals"]
    log(f"{prefix}: {passed}/{len(rows)} PASS ({t['share']}%), Chrome {chrome_pass}/{len(rows)}; {dict(counts)}; {len(excluded)} excluded (defective test data); {meta['wallSeconds']} s")
    return 1 if stale else 0


def directory_table(rows, depth=2):
    by = collections.defaultdict(lambda: [0, 0, 0])
    for r in rows:
        d = "/".join(r["test"].strip("/").split("/")[:depth]) + "/"
        by[d][0] += 1
        by[d][1] += r["status"] == "PASS"
        by[d][2] += r.get("chrome") == "PASS"
    return sorted(by.items())


def write_summary(out, meta, rows, all_rows=None):
    t = meta["totals"]
    lines = [f"# WPT reftests {meta['prefix']}", "",
             f"**{t['passed']} of {t['tests']} pass ({t['share']:.2f}%)**" + (f"; Chrome {t['chromePassed']} ({t['chromeShare']:.2f}%) at the same WPT commit" if t.get("chromeShare") is not None else ""),
             "", f"Of the passes, {t['passedWithSkips']} are of pages where the engine skipped something (test or reference).",
             "", f"Statuses: {', '.join(f'{k} {v}' for k, v in sorted(t['statuses'].items()))}. Valid: {meta['valid']}" + (f" ({meta['invalidReason']})" if not meta['valid'] else ""),
             f"{meta['pagesDrawn']} pages drawn in {meta['drawSeconds']} s. {meta['renderer']}.", "",
             "| directory | tests | Foafnaut | Chrome |", "|---|---:|---:|---:|"]
    for d, (n, p, c) in directory_table(rows):
        lines.append(f"| {d} | {n} | {p} | {c} |")
    lines += ["", "## Not passing where Chrome passes", ""]
    for r in rows:
        if r["status"] != "PASS" and r.get("chrome") == "PASS":
            lines.append(f"- {r['status']} `{r['test']}`" + (f": {r['message']}" if r.get("message") else ""))
    excl = [r for r in (all_rows or rows) if r["status"] == "EXCLUDED"]
    if excl:
        lines += ["", f"## {len(excl)} excluded (defective test data)", "", "Not in the passed count or the total.", ""]
        for r in excl:
            lines.append(f"- `{r['test']}`: {r['exclusion']['reason']}; {r['exclusion']['issue']}")
    open(os.path.join(out, "summary.md"), "w").write("\n".join(lines) + "\n")


def compare(a):
    # EXCLUDED tests (defective test data) are in neither run's counts
    prev = {r["test"]: r["status"] for r in json.load(open(a.prev))["tests"] if r["status"] != "EXCLUDED"}
    cur_doc = json.load(open(a.cur))
    cur = {r["test"]: r["status"] for r in cur_doc["tests"] if r["status"] != "EXCLUDED"}
    up = sorted(t for t in cur if cur[t] == "PASS" and prev.get(t) not in (None, "PASS"))
    down = sorted(t for t in cur if cur[t] != "PASS" and prev.get(t) == "PASS")
    new = sorted(t for t in cur if t not in prev)
    gone = sorted(t for t in prev if t not in cur)
    pp = sum(1 for s in prev.values() if s == "PASS"); cp = sum(1 for s in cur.values() if s == "PASS")
    lines = [f"# Reftest changes", "", f"Passed {pp} -> {cp} ({cp - pp:+d}) of {len(prev)} -> {len(cur)}.", "",
             f"## Newly passing ({len(up)})", ""] + [f"- `{t}` (was {prev[t]})" for t in up] + \
            ["", f"## Newly not passing ({len(down)})", ""] + [f"- `{t}`: {cur[t]}" for t in down] + \
            ["", f"## New tests ({len(new)}), gone ({len(gone)})", ""] + [f"- new `{t}`: {cur[t]}" for t in new] + [f"- gone `{t}`" for t in gone]
    text = "\n".join(lines) + "\n"
    if a.out:
        open(a.out, "w").write(text)
    else:
        print(text)
    # each newly passing test under the cause it had before (clusters of the previous run)
    cause = {}
    prev_doc = json.load(open(a.prev))
    for r in prev_doc["tests"]:
        if r["status"] in ("PASS", "EXCLUDED"):
            continue
        skips = [m for v in (r.get("skipped") or {}).values() for m in v]
        for name, kind, pat in CLUSTERS:
            if (kind == "status" and r["status"] == pat) or \
               (kind == "skip" and any(re.search(pat, m.split(": ", 1)[-1]) for m in skips)) or \
               (kind == "path" and re.search(pat, r["test"])):
                cause[r["test"]] = name
                break
    by = collections.Counter(cause.get(t, "?") for t in up)
    before = collections.Counter(cause.values())
    table = ["", "| cause (previous run) | not passing before | newly passing |", "|---|---:|---:|"] + \
        [f"| {n} | {before[n]} | {by.get(n, 0)} |" for n, _ in before.most_common()]
    if a.out:
        open(a.out, "a").write("\n".join(table) + "\n")
    else:
        print("\n".join(table))
    if a.json:
        json.dump({"passedBefore": pp, "passedAfter": cp, "newlyPassing": up, "newlyFailing": down, "new": new, "gone": gone,
                   "newlyPassingByCause": dict(by)}, open(a.json, "w"), indent=1)


# Causes, in order: the first that fits a test names its cluster. A pattern is matched against
# the engine's skip messages for the test and its references ("skip"), or the test's path ("path").
CLUSTERS = [
    ("scripted page never ended reftest-wait (SMIL API, load events of images, use)", "status", "TIMEOUT"),
    ("SVG <style> selectors beyond the slice", "skip", r"CSS selector"),
    ("event handler attributes", "skip", r"attribute on \w+: on[a-z]+"),
    ("colours beyond hex and rgb()", "skip", r"color|rgb\(\)"),
    ("markers", "skip", r"marker"),
    ("external <use> references", "skip", r"external use|use reference"),
    ("foreignObject", "skip", r"foreignObject|foreign/non-SVG element"),
    ("SVG images and data: URLs", "skip", r"data URI|svg\+xml"),
    ("CSS geometry properties (cx, r, rx, x, d ...)", "skip", r"CSS property: (cx|cy|r|rx|ry|x|y|d)$|CSS geometry property"),
    ("transform on the outer svg, CSS transform", "skip", r"transform"),
    ("masking, clipping, filters, blending", "skip", r"mask|clip|filter|blend"),
    ("patterns", "skip", r"pattern"),
    ("gradients", "skip", r"[Gg]radient"),
    ("CSS values: calc(), var(), strings, units", "skip", r"calc|var\(|strings|unit"),
    ("pathLength", "skip", r"pathLength|path-length"),
    ("other features the reader skips", "skip", r"."),
    ("text layout and painting", "path", r"/text/"),
    ("svgView and media fragments", "path", r"svgview|media-fragment"),
    ("linked parameters", "path", r"css-linked-parameters"),
    ("embedded and as-image", "path", r"/embedded/|/as-image/"),
    ("other, nothing skipped", "path", r"."),
]


def clusters(a):
    doc = json.load(open(a.results))
    if a.chrome_summary:
        ch = json.load(open(a.chrome_summary))
        for r in doc["tests"]:
            if r["test"] in ch:
                r["chrome"] = {"P": "PASS", "F": "FAIL"}.get(ch[r["test"]].get("s"), ch[r["test"]].get("s"))
    out = collections.OrderedDict((name, []) for name, _, _ in CLUSTERS)
    for r in doc["tests"]:
        if r["status"] in ("PASS", "EXCLUDED"):
            continue
        skips = [m for v in (r.get("skipped") or {}).values() for m in v]
        for name, kind, pat in CLUSTERS:
            if (kind == "status" and r["status"] == pat) or \
               (kind == "skip" and any(re.search(pat, m.split(": ", 1)[-1]) for m in skips)) or \
               (kind == "path" and re.search(pat, r["test"])):
                out[name].append(r)
                break
    rows = sorted(((n, len(v), sum(1 for r in v if r.get("chrome") == "PASS")) for n, v in out.items() if v), key=lambda x: (-x[2], -x[1]))
    lines = ["| cause | not passing | Chrome passes |", "|---|---:|---:|"] + [f"| {n} | {k} | {c} |" for n, k, c in rows]
    text = "\n".join(lines) + "\n"
    if a.json:
        json.dump({n: [r["test"] for r in v] for n, v in out.items() if v}, open(a.json, "w"), indent=1)
    print(text)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--manifest", required=True)
    r.add_argument("--wpt-root", required=True)
    r.add_argument("--native-engine", required=True)
    r.add_argument("--prefix", default="svg/")
    r.add_argument("--out", required=True)
    r.add_argument("--chrome-summary")
    r.add_argument("--jobs", type=int, default=3)
    r.add_argument("--only", default="")
    r.add_argument("--shard", type=int, default=0)
    r.add_argument("--shards", type=int, default=1)
    r.add_argument("--stall", type=float, default=90)
    r.add_argument("--wait-ms", type=int, default=6000)
    r.add_argument("--bitmap-font", action="store_true")
    r.add_argument("--no-pictures", action="store_true")
    r.add_argument("--no-failure-pictures", action="store_true")
    c = sub.add_parser("compare")
    c.add_argument("--prev", required=True)
    c.add_argument("--cur", required=True)
    c.add_argument("--out")
    c.add_argument("--json")
    k = sub.add_parser("clusters")
    k.add_argument("--results", required=True)
    k.add_argument("--json")
    k.add_argument("--chrome-summary")
    a = p.parse_args()
    sys.exit(run(a) if a.cmd == "run" else compare(a) if a.cmd == "compare" else clusters(a))


if __name__ == "__main__":
    main()
