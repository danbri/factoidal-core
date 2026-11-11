#!/usr/bin/env python3
"""Real-world JavaScript on each engine named: does it run, is the answer the same, how long, how much memory.

A workload is one script: `var N = n;`, the host shims of `realworld/prelude.js`, the single-file
build of a library, and a driver of `realworld/drivers/` that does work of size N and prints one
line `RESULT <checksum>`. `realworld/manifest.json` lists the workloads. Library code is not in
this repository: an npm package is fetched by exact version (`npm pack --ignore-scripts`), the
sha256 of its tarball is checked, and it is unpacked into the cache directory. A `local` entry
names a file by path (relative to the root of this checkout) and sha256.

For each workload the script runs three sizes on each engine: 0 (load the library only), N and 4N.
It reports, for each engine:

  status   ok; WRONG (the RESULT line differs from the reference engine's); ERROR (no RESULT
           line; the first error text is printed); TIMEOUT; OUT OF MEMORY (the resident memory
           passed --mem-mb and the run was killed)
  load ms  CPU time at size 0: parse and top-level evaluation of the library
  run ms   CPU time at 4N less the load
  x ref    run ms over the reference engine's run ms
  MB       peak resident memory at 4N

The reference engine is the LAST one named. CPU time is user plus system time of the child
process (`os.wait4`), least of --runs runs. Every run is under a watchdog: a script can make an
engine take all memory (`new Array(4294967295)` did on BubblePopJS, 2026-11-09).

  realworld.py [--cache DIR] [--only a,b] [--runs R] [--mem-mb M] [--timeout S] [--json OUT] NAME=CMD [NAME=CMD ...]
      e.g.  main='formal/lean4/.lake/build/bin/leanjs run'  qjs=/path/qjs  v8-jitless='node --jitless'  v8=node
      Each CMD gets the script path as its last argument.
  realworld.py [--cache DIR] [--only a,b] --emit DIR
      Write the scripts (NAME-0.js, NAME-N.js, NAME-4N.js) into DIR and stop: for a profiler.

It does not measure a page: no DOM, no events, no network. It runs classic scripts only.

Exit status: 0 every engine gave the reference answer on every workload; 1 some run was WRONG,
ERROR, TIMEOUT or OUT OF MEMORY (the table is printed all the same); 2 usage; 3 a library could
not be fetched or its sha256 differs.
"""
import hashlib
import json
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(HERE))))
DATA = os.path.join(HERE, 'realworld')


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as fh:
        for block in iter(lambda: fh.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def library_path(w, cache):
    """The path of the library file of workload `w`; fetches and checks an npm package once."""
    if w['source'] == 'local':
        path = os.path.normpath(os.path.join(REPO, w['path']))
        if not os.path.isfile(path):
            raise SystemExit('%s: no file %s (a `local` workload needs that checkout beside this one)' % (w['name'], path))
        if sha256(path) != w['sha256']:
            raise SystemExit('%s: sha256 of %s is not the one in the manifest' % (w['name'], path))
        return path
    home = os.path.join(cache, '%s-%s' % (w['package'], w['version']))
    lib = os.path.join(home, 'x', 'package', w['file'])
    if not os.path.isfile(lib):
        os.makedirs(home, exist_ok=True)
        p = subprocess.run(['npm', 'pack', '--silent', '--ignore-scripts', '%s@%s' % (w['package'], w['version'])],
                           cwd=home, capture_output=True, text=True)
        tarballs = [f for f in os.listdir(home) if f.endswith('.tgz')]
        if p.returncode != 0 or len(tarballs) != 1:
            raise SystemExit('%s: npm pack failed: %s' % (w['name'], (p.stderr or p.stdout).strip()[:300]))
        tarball = os.path.join(home, tarballs[0])
        if sha256(tarball) != w['sha256']:
            raise SystemExit('%s: sha256 of %s is not the one in the manifest' % (w['name'], tarballs[0]))
        os.makedirs(os.path.join(home, 'x'), exist_ok=True)
        subprocess.run(['tar', '-xzf', tarball, '-C', os.path.join(home, 'x')], check=True)
    if not os.path.isfile(lib):
        raise SystemExit('%s: the package has no file %s' % (w['name'], w['file']))
    return lib


def run_once(cmd, script, mem_mb, timeout):
    """(status, RESULT line or error text, CPU seconds, peak MB) for one run under the watchdog."""
    out = tempfile.TemporaryFile()
    err = tempfile.TemporaryFile()
    p = subprocess.Popen(cmd + [script], stdout=out, stderr=err)
    t0 = time.time()
    killed = None
    while True:
        pid, status, usage = os.wait4(p.pid, os.WNOHANG)
        if pid:
            break
        try:
            with open('/proc/%d/status' % p.pid) as fh:
                for line in fh:
                    if line.startswith('VmRSS:') and int(line.split()[1]) / 1024.0 > mem_mb:
                        killed = 'OUT OF MEMORY'
        except OSError:
            pass
        if killed is None and time.time() - t0 > timeout:
            killed = 'TIMEOUT'
        if killed:
            p.kill()
            pid, status, usage = os.wait4(p.pid, 0)
            break
        time.sleep(0.005)
    p.returncode = os.waitstatus_to_exitcode(status)
    out.seek(0)
    err.seek(0)
    text = out.read().decode('utf-8', 'replace')
    errors = err.read().decode('utf-8', 'replace')
    cpu = usage.ru_utime + usage.ru_stime
    peak = usage.ru_maxrss / 1024.0
    if killed:
        return killed, '', cpu, peak
    results = [l for l in text.split('\n') if l.startswith('RESULT ')]
    if p.returncode != 0 or len(results) != 1:
        first = (errors.strip() or text.strip() or 'exit status %d' % p.returncode).replace('\n', ' | ')
        return 'ERROR', first[:300], cpu, peak
    return 'ok', results[0], cpu, peak


def main(argv):
    opts = {'--cache': os.path.join(tempfile.gettempdir(), 'bubblepop-realworld-cache'), '--only': '', '--runs': '3',
            '--mem-mb': '2000', '--timeout': '120', '--json': '', '--emit': ''}
    engines = []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a in opts:
            if i + 1 >= len(argv):
                print(__doc__)
                return 2
            opts[a] = argv[i + 1]
            i += 2
        elif '=' in a and not a.startswith('-'):
            name, cmd = a.split('=', 1)
            engines.append((name, shlex.split(cmd)))
            i += 1
        else:
            print(__doc__)
            return 2
    if not engines and not opts['--emit']:
        print(__doc__)
        return 2
    manifest = json.load(open(os.path.join(DATA, 'manifest.json')))
    only = [x for x in opts['--only'].split(',') if x]
    workloads = [w for w in manifest['workloads'] if not only or w['name'] in only]
    runs, mem_mb, timeout = int(opts['--runs']), float(opts['--mem-mb']), float(opts['--timeout'])
    prelude = open(os.path.join(DATA, 'prelude.js')).read()
    if opts['--emit']:
        os.makedirs(opts['--emit'], exist_ok=True)
        for w in workloads:
            try:
                lib = library_path(w, opts['--cache'])
            except SystemExit as e:
                print(e, file=sys.stderr)
                return 3
            source = open(lib, encoding='utf-8', errors='replace').read()
            driver = open(os.path.join(DATA, 'drivers', w['driver'])).read()
            for n in (0, w['n'], 4 * w['n']):
                with open(os.path.join(opts['--emit'], '%s-%d.js' % (w['name'], n)), 'w') as fh:
                    fh.write('var N = %d;\n%s\n%s\n;\n%s\n' % (n, prelude, source, driver))
        return 0
    ref = engines[-1][0]
    tmp = tempfile.mkdtemp(prefix='bubblepop-realworld-')
    rows = []
    bad = 0
    try:
        for w in workloads:
            try:
                lib = library_path(w, opts['--cache'])
            except SystemExit as e:
                print(e, file=sys.stderr)
                return 3
            source = open(lib, encoding='utf-8', errors='replace').read()
            driver = open(os.path.join(DATA, 'drivers', w['driver'])).read()
            sizes = [0, w['n'], 4 * w['n']]
            scripts = {}
            for n in sizes:
                path = os.path.join(tmp, '%s-%d.js' % (w['name'], n))
                with open(path, 'w') as fh:
                    fh.write('var N = %d;\n%s\n%s\n;\n%s\n' % (n, prelude, source, driver))
                scripts[n] = path
            got = {}
            for name, cmd in engines:
                for n in sizes:
                    best = None
                    for _ in range(runs):
                        r = run_once(cmd, scripts[n], mem_mb, timeout)
                        if best is None or (r[0] == 'ok' and r[2] < best[2]) or best[0] != 'ok':
                            best = r if best is None or r[0] == 'ok' or best[0] != 'ok' else best
                        if r[0] != 'ok':
                            best = r
                            break
                    got[(name, n)] = best
                    if best[0] != 'ok':
                        break
            for name, cmd in engines:
                row = {'workload': w['name'], 'engine': name, 'n': w['n'], 'bytes': len(source)}
                status, detail = 'ok', ''
                for n in sizes:
                    r = got.get((name, n))
                    if r is None:
                        break
                    if r[0] != 'ok':
                        status, detail = r[0], 'at size %d: %s' % (n, r[1])
                        break
                    want = got.get((ref, n))
                    if want and want[0] == 'ok' and r[1] != want[1]:
                        status, detail = 'WRONG', 'at size %d: %s; the reference engine gave %s' % (n, r[1], want[1])
                        break
                row['status'], row['detail'] = status, detail
                if (name, 0) in got and got[(name, 0)][0] == 'ok':
                    row['load_ms'] = got[(name, 0)][2] * 1000
                if status == 'ok':
                    row['run_ms'] = max(got[(name, sizes[2])][2] - got[(name, 0)][2], 0.0) * 1000
                    row['mid_ms'] = max(got[(name, sizes[1])][2] - got[(name, 0)][2], 0.0) * 1000
                    row['peak_mb'] = got[(name, sizes[2])][3]
                else:
                    bad += 1
                rows.append(row)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    by = {(r['workload'], r['engine']): r for r in rows}
    print('reference engine for answers and ratios: %s; CPU ms, least of %d runs; sizes 0, N and 4N' % (ref, runs))
    print('%-14s %-12s %-14s %9s %10s %8s %7s' % ('workload', 'engine', 'status', 'load ms', 'run ms', 'x ref', 'MB'))
    for w in workloads:
        for name, _ in engines:
            r = by[(w['name'], name)]
            base = by[(w['name'], ref)].get('run_ms')
            ratio = '%8.1f' % (r['run_ms'] / base) if 'run_ms' in r and base and base > 0.5 else '       -'
            print('%-14s %-12s %-14s %9s %10s %s %7s' % (
                w['name'], name, r['status'],
                '%.1f' % r['load_ms'] if 'load_ms' in r else '-',
                '%.1f' % r['run_ms'] if 'run_ms' in r else '-', ratio,
                '%.0f' % r['peak_mb'] if 'peak_mb' in r else '-'))
            if r['detail']:
                print('    %s' % r['detail'])
    ok = {name: sum(1 for w in workloads if by[(w['name'], name)]['status'] == 'ok') for name, _ in engines}
    print('; '.join('%s: %d ok, %d not ok (out of %d)' % (name, ok[name], len(workloads) - ok[name], len(workloads))
                    for name, _ in engines))
    if opts['--json']:
        with open(opts['--json'], 'w') as fh:
            json.dump(rows, fh, indent=1)
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
