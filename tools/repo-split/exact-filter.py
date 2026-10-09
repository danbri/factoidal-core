#!/usr/bin/env python3
"""Exact path-filtered history rewrite for danbri/factoidal-core.

Every rewritten commit's tree is the original commit's tree with only the
kept formal/ paths, computed directly from the original tree object. This
avoids the fast-export behaviour where a merge's file changes are emitted
relative to its ORIGINAL first parent; when that parent is pruned, the
merge's content is applied to the wrong base (seen 2026-10-09 with
git-filter-repo: 3 files at the tip carried pre-merge content).

Pruning:
  * a non-merge whose filtered tree equals its (mapped) parent's tree is
    dropped and maps to that parent;
  * a merge whose mapped parents collapse to one, or where one mapped
    parent is an ancestor of another, is reduced; if one parent remains
    and the tree is unchanged, it is dropped.

Identity: author and committer pass through the mailmap given (iron rule
13: attribution to the responsible human). Messages lose Claude trailers.

Usage: exact-filter.py SRC_GIT_DIR REF EXCLUDE_PY MAILMAP OUT_REF
Writes objects into SRC_GIT_DIR and points OUT_REF at the new tip.
"""
import subprocess, sys, re

src, ref, exclude_py, mailmap_path, out_ref = sys.argv[1:6]
ns = {}
exec(open(exclude_py).read(), ns)
excluded = ns['excluded']

def git(*args, inp=None):
    return subprocess.run(['git', '-C', src] + list(args), input=inp,
                          capture_output=True, check=True).stdout

# --- mailmap -------------------------------------------------------------
mailmap = {}
for line in open(mailmap_path, encoding='utf-8'):
    m = re.match(r'^(.*?) <([^>]+)>\s+(.*?) <([^>]+)>\s*$', line.strip())
    if m:
        mailmap[(m.group(3), m.group(4))] = (m.group(1), m.group(2))

def map_ident(raw: bytes) -> bytes:
    m = re.match(rb'^(.*) <([^>]*)> (.*)$', raw)
    if not m:
        return raw
    name, email, rest = m.group(1).decode(), m.group(2).decode(), m.group(3)
    if (name, email) in mailmap:
        name, email = mailmap[(name, email)]
    return f'{name} <{email}> '.encode() + rest

def clean_message(msg: bytes) -> bytes:
    out = []
    for line in msg.split(b'\n'):
        l = line.strip().lower()
        if l.startswith(b'co-authored-by: claude') or l.startswith(b'claude-session:'):
            continue
        if b'generated with [claude code]' in l or l.startswith(b'https://claude.ai/code/session_'):
            continue
        out.append(line)
    m = b'\n'.join(out).rstrip(b'\n') + b'\n'
    return m

# --- object reading --------------------------------------------------------
cat = subprocess.Popen(['git', '-C', src, 'cat-file', '--batch'],
                       stdin=subprocess.PIPE, stdout=subprocess.PIPE)
def read_obj(oid: str):
    cat.stdin.write(oid.encode() + b'\n'); cat.stdin.flush()
    header = cat.stdout.readline().split()
    if header[1] == b'missing':
        raise RuntimeError('missing object ' + oid)
    size = int(header[2])
    data = cat.stdout.read(size); cat.stdout.read(1)
    return header[1].decode(), data

def parse_tree(data: bytes):
    entries = []
    i = 0
    while i < len(data):
        sp = data.index(b' ', i); nul = data.index(b'\0', sp)
        mode = data[i:sp].decode(); name = data[sp+1:nul]
        oid = data[nul+1:nul+21].hex()
        entries.append((mode, name, oid)); i = nul + 21
    return entries

mktree = subprocess.Popen(['git', '-C', src, 'mktree', '--batch', '--missing'],
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE)
def write_tree(entries):
    lines = []
    for mode, name, oid in entries:
        typ = 'tree' if mode == '40000' else ('commit' if mode == '160000' else 'blob')
        m = '040000' if mode == '40000' else mode
        lines.append(f'{m} {typ} {oid}\t'.encode() + name)
    mktree.stdin.write(b'\n'.join(lines) + b'\n\n'); mktree.stdin.flush()
    return mktree.stdout.readline().strip().decode()

EMPTY = None
tree_cache = {}
def filter_tree(path: str, oid: str):
    """Return filtered tree oid for the tree at `path` (no trailing slash),
    or None when nothing under it is kept."""
    key = (path, oid)
    if key in tree_cache:
        return tree_cache[key]
    _, data = read_obj(oid)
    kept = []
    for mode, name, coid in parse_tree(data):
        p = path + '/' + name.decode('utf-8', 'surrogateescape')
        if mode == '40000':
            sub = filter_tree(p, coid)
            if sub is not None:
                kept.append((mode, name, sub))
        else:
            if not excluded(p):
                kept.append((mode, name, coid))
    res = write_tree(kept) if kept else None
    tree_cache[key] = res
    return res

def root_filtered(root_oid: str):
    _, data = read_obj(root_oid)
    for mode, name, oid in parse_tree(data):
        if name == b'formal' and mode == '40000':
            f = filter_tree('formal', oid)
            return write_tree([('40000', b'formal', f)]) if f else None
    return None

# --- commit walk -----------------------------------------------------------
revs = git('rev-list', '--topo-order', '--reverse', '--parents', ref).decode().split('\n')
cmap = {}        # original -> new commit oid or None
new_tree = {}    # new commit -> tree oid
ancestors_memo = {}

def is_ancestor(a: str, b: str) -> bool:
    if a == b:
        return True
    k = (a, b)
    if k not in ancestors_memo:
        r = subprocess.run(['git', '-C', src, 'merge-base', '--is-ancestor', a, b])
        ancestors_memo[k] = (r.returncode == 0)
    return ancestors_memo[k]

kept = pruned = 0
for n, line in enumerate(revs):
    if not line:
        continue
    parts = line.split()
    c, parents = parts[0], parts[1:]
    _, raw = read_obj(c)
    hdr, _, msg = raw.partition(b'\n\n')
    headers = hdr.split(b'\n')
    tree = headers[0].split()[1].decode()
    author = committer = None; encoding = None
    for h in headers[1:]:
        if h.startswith(b'author '): author = h[7:]
        elif h.startswith(b'committer '): committer = h[10:]
        elif h.startswith(b'encoding '): encoding = h[9:]
    t = root_filtered(tree)
    mp = []
    for p in parents:
        q = cmap.get(p)
        if q is not None and q not in mp:
            mp.append(q)
    # drop parents that are ancestors of another mapped parent
    if len(mp) > 1:
        reduced = [p for p in mp if not any(o != p and is_ancestor(p, o) for o in mp)]
        mp = reduced
    if len(mp) == 0 and t is None:
        cmap[c] = None; pruned += 1; continue
    if len(mp) == 1 and new_tree.get(mp[0]) == t:
        cmap[c] = mp[0]; pruned += 1; continue
    if t is None:
        t = write_tree([])
    body = f'tree {t}\n'.encode()
    for p in mp:
        body += f'parent {p}\n'.encode()
    body += b'author ' + map_ident(author) + b'\n'
    body += b'committer ' + map_ident(committer) + b'\n'
    if encoding:
        body += b'encoding ' + encoding + b'\n'
    body += b'\n' + clean_message(msg)
    newc = subprocess.run(['git', '-C', src, 'hash-object', '-t', 'commit', '-w', '--stdin'],
                          input=body, capture_output=True, check=True).stdout.strip().decode()
    cmap[c] = newc; new_tree[newc] = t; kept += 1
    if kept % 250 == 0:
        print(f'{n} commits read, {kept} written, {pruned} pruned', file=sys.stderr, flush=True)

tip = cmap[revs[-2].split()[0]] if revs[-1] == '' else cmap[revs[-1].split()[0]]
git('update-ref', out_ref, tip)
with open(src + '/exact-filter-commit-map', 'w') as f:
    for k, v in cmap.items():
        f.write(f'{k} {v or "0"*40}\n')
print(f'done: {kept} written, {pruned} pruned, tip {tip}')
